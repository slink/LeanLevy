/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.PiecewisePath
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.BorelCantelli

/-!
# Drivers for the compound Poisson process

A **compound Poisson driver** packages the two independent sources of randomness that build a
compound-Poisson-with-drift path: an i.i.d. sequence of exponential *interarrival times* `τ n` and
an i.i.d. sequence of *marks* `Y n`, all jointly independent on a common probability space.

The interarrival times generate the *arrival times*

`arrival τ n ω = ∑ i ∈ Finset.range (n + 1), τ i ω`,

the partial sums that mark when the jumps occur. This file records their almost-sure structure —
positivity, strict monotonicity, and divergence to `+∞`, and uses it to build the compound-Poisson
sample path itself and prove its almost-sure càdlàg regularity and pathwise Itô formula.

## Main definitions

* `ProbabilityTheory.arrival` — the arrival-time partial sums of the interarrival sequence.
* `ProbabilityTheory.IsCompoundPoissonDriver` — the joint independence and marginal-law data of the
  interarrival/mark sequences.
* `ProbabilityTheory.compoundPoisson` — the compound-Poisson-with-drift sample path, the
  `piecewisePath` built from the random arrival times and marks.

## Main results

* `ProbabilityTheory.exists_isCompoundPoissonDriver` — a compound Poisson driver exists for any
  positive rate `r` and any probability law `ν'` of the marks, on a canonical probability space.
* `ProbabilityTheory.measurable_compoundPoisson` — the compound Poisson path is measurable at each
  fixed time, so it is a genuine random variable.
* `ProbabilityTheory.IsCompoundPoissonDriver.ae_interarrival_pos` — the interarrival times are almost
  surely all positive.
* `ProbabilityTheory.IsCompoundPoissonDriver.ae_strictMono_arrival` — the arrival times are almost
  surely strictly increasing.
* `ProbabilityTheory.IsCompoundPoissonDriver.ae_tendsto_arrival` — the arrival times almost surely
  tend to `+∞`.
* `ProbabilityTheory.compoundPoisson_ae_start` — the compound Poisson path almost surely starts at
  `0`.
* `ProbabilityTheory.compoundPoisson_ae_isCadlag` — the compound Poisson process almost surely has
  càdlàg sample paths.
* `ProbabilityTheory.compoundPoisson_pathwise_ito` — **the pathwise Itô formula**: almost every
  sample path decomposes the increment of a `C¹` function along the process into the drift integral
  plus the sum of jump increments, with no stochastic integral needed.

## Implementation notes

The joint independence is stored as a single `iIndepFun` over the combined index type `ℕ ⊕ ℕ`, with
the interarrival family on the `Sum.inl` block and the mark family on the `Sum.inr` block, glued by
`Sum.elim τ Y`. This one-family spelling is what lets later layers extract *any* disjoint-block
independence (interarrivals ⟂ marks, or finite subfamilies of either): the per-block families are
exposed as `IsCompoundPoissonDriver.iIndepFun_interarrival` / `.iIndepFun_mark`, and finer splits
follow via `iIndepFun.precomp` and `iIndepFun.indepFun_finset`.

Because `isProbabilityMeasure_expMeasure` requires a strictly positive rate, the existence theorem
and every almost-sure lemma carries a hypothesis `hr : 0 < r`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*}

/-- The `n`-th arrival time of the interarrival sequence `τ`: the partial sum of the first `n + 1`
interarrival times. -/
def arrival (τ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range (n + 1), τ i ω

lemma arrival_zero (τ : ℕ → Ω → ℝ) (ω : Ω) : arrival τ 0 ω = τ 0 ω := by
  simp [arrival]

lemma arrival_succ (τ : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    arrival τ (n + 1) ω = arrival τ n ω + τ (n + 1) ω :=
  Finset.sum_range_succ (fun i => τ i ω) (n + 1)

variable [MeasurableSpace Ω]

/-- A **compound Poisson driver**: an i.i.d. exponential interarrival sequence `τ` (rate `r`) and an
i.i.d. mark sequence `Y` (law `ν'`), jointly independent on the probability space `(Ω, μ)`.

The joint independence is a single `iIndepFun` over `ℕ ⊕ ℕ` via `Sum.elim τ Y`, so that any
disjoint-block independence between the two families (or within a family) is recoverable. -/
structure IsCompoundPoissonDriver (τ Y : ℕ → Ω → ℝ) (r : ℝ≥0) (ν' : Measure ℝ)
    (μ : Measure Ω) : Prop where
  /-- Each interarrival time is measurable. -/
  measurable_interarrival : ∀ n, Measurable (τ n)
  /-- Each mark is measurable. -/
  measurable_mark : ∀ n, Measurable (Y n)
  /-- The interarrival and mark families are jointly independent, as one `ℕ ⊕ ℕ`-indexed family. -/
  indep : iIndepFun (Sum.elim τ Y) μ
  /-- Each interarrival time is exponentially distributed with rate `r`. -/
  law_interarrival : ∀ n, HasLaw (τ n) (expMeasure r) μ
  /-- Each mark has law `ν'`. -/
  law_mark : ∀ n, HasLaw (Y n) ν' μ

namespace IsCompoundPoissonDriver

variable {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}

/-- The arrival times of a compound Poisson driver are measurable. -/
lemma measurable_arrival (h : IsCompoundPoissonDriver τ Y r ν' μ) (n : ℕ) :
    Measurable (arrival τ n) :=
  Finset.measurable_sum _ fun i _ => h.measurable_interarrival i

/-- A compound Poisson driver lives on a probability space. -/
lemma isProbabilityMeasure (h : IsCompoundPoissonDriver τ Y r ν' μ) : IsProbabilityMeasure μ :=
  h.indep.isProbabilityMeasure

/-- The interarrival family of a compound Poisson driver is jointly independent: restrict the
combined `ℕ ⊕ ℕ`-indexed independence to the left summand. -/
lemma iIndepFun_interarrival (h : IsCompoundPoissonDriver τ Y r ν' μ) : iIndepFun τ μ := by
  have := h.indep.precomp (g := Sum.inl) Sum.inl_injective
  simpa [Function.comp] using this

/-- The mark family of a compound Poisson driver is jointly independent: restrict the combined
`ℕ ⊕ ℕ`-indexed independence to the right summand. -/
lemma iIndepFun_mark (h : IsCompoundPoissonDriver τ Y r ν' μ) : iIndepFun Y μ := by
  have := h.indep.precomp (g := Sum.inr) Sum.inr_injective
  simpa [Function.comp] using this

/-- The interarrival times of a compound Poisson driver are almost surely all positive. -/
theorem ae_interarrival_pos (h : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, ∀ n, 0 < τ n ω := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  haveI : IsProbabilityMeasure (expMeasure (r : ℝ)) := isProbabilityMeasure_expMeasure hr'
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  have hset : {ω | ¬ 0 < τ n ω} = (τ n) ⁻¹' (Set.Iic 0) := by
    ext ω; simp [Set.mem_Iic, not_lt]
  rw [hset, ← Measure.map_apply (h.measurable_interarrival n) measurableSet_Iic,
    (h.law_interarrival n).map_eq, ← ofReal_cdf (expMeasure (r : ℝ)) 0, cdf_expMeasure_eq hr' 0]
  simp

/-- The arrival times of a compound Poisson driver are almost surely strictly increasing. -/
theorem ae_strictMono_arrival (h : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, StrictMono (fun n => arrival τ n ω) := by
  filter_upwards [h.ae_interarrival_pos hr] with ω hpos
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [arrival_succ]
  exact lt_add_of_pos_right _ (hpos (n + 1))

/-- The first arrival time of a compound Poisson driver is almost surely positive. -/
theorem ae_arrival_pos (h : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, 0 < arrival τ 0 ω := by
  filter_upwards [h.ae_interarrival_pos hr] with ω hpos
  rw [arrival_zero]
  exact hpos 0

/-- The events `{1 < τ n}` are jointly independent: they are measurable with respect to the
interarrival σ-algebras, which form an independent subfamily of the driver. -/
private lemma iIndepSet_interarrival_gt (h : IsCompoundPoissonDriver τ Y r ν' μ) :
    iIndepSet (fun n => (τ n) ⁻¹' Set.Ioi 1) μ := by
  have hτ : iIndepFun τ μ := h.iIndepFun_interarrival
  rw [iIndepSet_iff_meas_biInter fun n => (h.measurable_interarrival n) measurableSet_Ioi]
  intro s
  exact hτ.meas_biInter fun i _ => ⟨Set.Ioi 1, measurableSet_Ioi, rfl⟩

/-- Each event `{1 < τ n}` has the same positive probability `expMeasure r (Ioi 1)`. -/
private lemma measure_interarrival_gt (h : IsCompoundPoissonDriver τ Y r ν' μ) (n : ℕ) :
    μ ((τ n) ⁻¹' Set.Ioi 1) = expMeasure (r : ℝ) (Set.Ioi 1) := by
  rw [← Measure.map_apply (h.measurable_interarrival n) measurableSet_Ioi,
    (h.law_interarrival n).map_eq]

private lemma expMeasure_Ioi_one_ne_zero (hr : 0 < r) :
    expMeasure (r : ℝ) (Set.Ioi 1) ≠ 0 := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  haveI : IsProbabilityMeasure (expMeasure (r : ℝ)) := isProbabilityMeasure_expMeasure hr'
  have hcompl : Set.Ioi (1 : ℝ) = (Set.Iic 1)ᶜ := Set.compl_Iic.symm
  rw [hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    ← ofReal_cdf (expMeasure (r : ℝ)) 1, cdf_expMeasure_eq hr' 1]
  have hlt : ENNReal.ofReal (if (0 : ℝ) ≤ 1 then 1 - Real.exp (-((r : ℝ) * 1)) else 0) < 1 := by
    rw [if_pos (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_lt_one]
    have := Real.exp_pos (-((r : ℝ) * 1))
    linarith
  exact (tsub_pos_iff_lt.mpr hlt).ne'

/-- The arrival times of a compound Poisson driver almost surely tend to `+∞`.

The proof uses the second Borel–Cantelli lemma: the events `{1 < τ n}` are independent with constant
positive probability, so almost surely infinitely many interarrival times exceed `1`. Combined with
the almost-sure positivity of all interarrival times, the arrival partial sums are then unbounded,
and being monotone they diverge. -/
theorem ae_tendsto_arrival (h : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => arrival τ n ω) atTop atTop := by
  haveI := h.isProbabilityMeasure
  -- Almost surely infinitely many interarrival times exceed 1, via the second Borel–Cantelli lemma.
  have hsum : (∑' n, μ ((τ n) ⁻¹' Set.Ioi 1)) = ∞ := by
    simp_rw [h.measure_interarrival_gt]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (expMeasure_Ioi_one_ne_zero hr)
  have hlimsup : μ (limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop) = 1 :=
    measure_limsup_eq_one (fun n => (h.measurable_interarrival n) measurableSet_Ioi)
      h.iIndepSet_interarrival_gt hsum
  have hmeas : MeasurableSet (limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop) :=
    MeasurableSet.measurableSet_limsup fun n => (h.measurable_interarrival n) measurableSet_Ioi
  have hae_limsup : ∀ᵐ ω ∂μ, ω ∈ limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop := by
    rw [ae_iff, show {ω | ω ∉ limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop}
        = (limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop)ᶜ from rfl,
      measure_compl hmeas (measure_ne_top _ _), measure_univ, hlimsup, tsub_self]
  filter_upwards [h.ae_interarrival_pos hr, hae_limsup] with ω hpos hlim
  -- Rewrite membership in the limsup as a frequently statement, then as an infinite index set.
  rw [mem_limsup_iff_frequently_mem] at hlim
  have hfreq : ∃ᶠ n in atTop, 1 < τ n ω := by
    refine hlim.mono fun n hn => ?_
    simpa [Set.mem_preimage, Set.mem_Ioi] using hn
  have hinf : {n | 1 < τ n ω}.Infinite := Nat.frequently_atTop_iff_infinite.mp hfreq
  -- The monotone arrival sequence is unbounded, hence tends to `+∞`.
  refine tendsto_atTop_atTop_of_monotone ?_ fun b => ?_
  · exact monotone_nat_of_le_succ fun n => by
      rw [arrival_succ]; exact le_add_of_nonneg_right (hpos (n + 1)).le
  · obtain ⟨t, hts, htcard⟩ := hinf.exists_subset_card_eq ⌈b⌉₊
    refine ⟨t.sup id, ?_⟩
    have hsubset : t ⊆ Finset.range (t.sup id + 1) := fun i hi =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    have h1 : (⌈b⌉₊ : ℝ) ≤ ∑ i ∈ t, τ i ω := by
      calc (⌈b⌉₊ : ℝ) = ∑ _i ∈ t, (1 : ℝ) := by rw [Finset.sum_const, htcard, nsmul_eq_mul, mul_one]
        _ ≤ ∑ i ∈ t, τ i ω :=
            Finset.sum_le_sum fun i hi => (le_of_lt (hts hi))
    have h2 : ∑ i ∈ t, τ i ω ≤ arrival τ (t.sup id) ω :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i _ _ => (hpos i).le
    exact (Nat.le_ceil b).trans (h1.trans h2)

end IsCompoundPoissonDriver

/-- **Existence of a compound Poisson driver.** For any positive rate `r` and any probability law
`ν'` of the marks, there is a canonical probability space carrying an i.i.d. exponential interarrival
sequence and an i.i.d. mark sequence that are jointly independent.

The space is the countable product indexed by `ℕ ⊕ ℕ` (`exists_hasLaw_indepFun`), with the
interarrival coordinates on the `Sum.inl` block and the marks on the `Sum.inr` block. The hypothesis
`hr : 0 < r` is required because the exponential distribution is only a probability measure for a
positive rate. -/
theorem exists_isCompoundPoissonDriver (r : ℝ≥0) (hr : 0 < r) (ν' : Measure ℝ)
    [IsProbabilityMeasure ν'] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (τ Y : ℕ → Ω → ℝ),
      IsProbabilityMeasure μ ∧ IsCompoundPoissonDriver τ Y r ν' μ := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  haveI : IsProbabilityMeasure (expMeasure (r : ℝ)) := isProbabilityMeasure_expMeasure hr'
  -- Law family over the combined index `ℕ ⊕ ℕ`: exponential on `inl`, `ν'` on `inr`.
  haveI hfam : ∀ i : ℕ ⊕ ℕ,
      IsProbabilityMeasure (Sum.elim (fun _ => expMeasure (r : ℝ)) (fun _ => ν') i) := by
    rintro (n | n)
    · show IsProbabilityMeasure (expMeasure (r : ℝ)); exact isProbabilityMeasure_expMeasure hr'
    · show IsProbabilityMeasure ν'; infer_instance
  obtain ⟨Ω, mΩ, μ, X, hmeas, hlawX, hindep, hμ⟩ :=
    @exists_hasLaw_indepFun (ℕ ⊕ ℕ) (fun _ => ℝ) (fun _ => inferInstance)
      (Sum.elim (fun _ => expMeasure (r : ℝ)) (fun _ => ν')) hfam
  refine ⟨Ω, mΩ, μ, fun n => X (Sum.inl n), fun n => X (Sum.inr n), hμ, ?_⟩
  have hXelim : Sum.elim (fun n => X (Sum.inl n)) (fun n => X (Sum.inr n)) = X := by
    funext x; cases x <;> rfl
  exact
    { measurable_interarrival := fun n => hmeas (Sum.inl n)
      measurable_mark := fun n => hmeas (Sum.inr n)
      indep := by rw [hXelim]; exact hindep
      law_interarrival := fun n => hlawX (Sum.inl n)
      law_mark := fun n => hlawX (Sum.inr n) }

section CompoundPoisson

variable {b : ℝ} {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}

/-- The **compound-Poisson-with-drift sample path**: the deterministic `piecewisePath` starting at
`0`, drifting at rate `b`, with jump times given by the random arrival times `arrival τ · ω` and
jump sizes given by the random marks `Y · ω`. At a fixed time `t` this is a random variable in `ω`. -/
noncomputable def compoundPoisson (b : ℝ) (τ Y : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  piecewisePath 0 b (fun n => arrival τ n ω) (fun n => Y n ω) t

/-- Characterization of `Nat.sInf s = k` as a Boolean combination of membership statements: either
`k` is in `s` and nothing below it is, or `s` is empty and `k = 0`. This is what makes the random
jump count measurable without any pointwise monotonicity of the arrival times. -/
private lemma nat_sInf_eq_iff (s : Set ℕ) (k : ℕ) :
    sInf s = k ↔ (k ∈ s ∧ ∀ j < k, j ∉ s) ∨ (s = ∅ ∧ k = 0) := by
  constructor
  · intro h
    rcases s.eq_empty_or_nonempty with hs | hs
    · exact Or.inr ⟨hs, by rw [hs, Nat.sInf_empty] at h; exact h.symm⟩
    · exact Or.inl ⟨h ▸ Nat.sInf_mem hs, fun j hj => Nat.notMem_of_lt_sInf (h ▸ hj)⟩
  · rintro (⟨hk, hlt⟩ | ⟨hs, hk⟩)
    · refine le_antisymm (Nat.sInf_le hk) ?_
      by_contra hlt'
      push Not at hlt'
      exact hlt _ hlt' (Nat.sInf_mem ⟨k, hk⟩)
    · rw [hs, hk]; exact Nat.sInf_empty

/-- The random jump count `ω ↦ jumpCount (arrival τ · ω) t` is measurable: for each `k`, the event
that exactly `k` arrivals have occurred by time `t` is a countable Boolean combination of the
measurable events `{t < arrival τ n ω}`. -/
lemma measurable_jumpCount_arrival (hτ : ∀ n, Measurable (τ n)) (t : ℝ) :
    Measurable (fun ω => jumpCount (fun n => arrival τ n ω) t) := by
  have harr : ∀ n, Measurable (fun ω => arrival τ n ω) := fun n =>
    Finset.measurable_sum _ fun i _ => hτ i
  have hA : ∀ n, MeasurableSet {ω : Ω | t < arrival τ n ω} := fun n =>
    measurableSet_lt measurable_const (harr n)
  refine measurable_to_countable' fun k => ?_
  have hset : (fun ω => jumpCount (fun n => arrival τ n ω) t) ⁻¹' {k}
      = ({ω : Ω | t < arrival τ k ω} ∩ ⋂ j, ⋂ _ : j < k, {ω : Ω | ¬ t < arrival τ j ω})
        ∪ ((⋂ n, {ω : Ω | ¬ t < arrival τ n ω}) ∩ {_ω : Ω | k = 0}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, jumpCount]
    rw [nat_sInf_eq_iff]
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Set.eq_empty_iff_forall_notMem]
  rw [hset]
  refine ((hA k).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    (hA j).compl)).union ((MeasurableSet.iInter fun n => (hA n).compl).inter ?_)
  exact MeasurableSet.const _

/-- At each fixed time `t`, the compound Poisson path `ω ↦ compoundPoisson b τ Y t ω` is measurable,
given that the interarrival times and marks are measurable. It is therefore a random variable. -/
lemma measurable_compoundPoisson (hτ : ∀ n, Measurable (τ n)) (hY : ∀ n, Measurable (Y n)) (t : ℝ) :
    Measurable (compoundPoisson b τ Y t) := by
  have hF : Measurable (fun p : Ω × ℕ => ∑ n ∈ Finset.range p.2, Y n p.1) :=
    measurable_from_prod_countable_left fun k =>
      Finset.measurable_sum (Finset.range k) fun n _ => hY n
  have hg : Measurable
      (fun ω => ∑ n ∈ Finset.range (jumpCount (fun n => arrival τ n ω) t), Y n ω) :=
    hF.comp (measurable_id.prodMk (measurable_jumpCount_arrival hτ t))
  have hcp : compoundPoisson b τ Y t
      = fun ω => 0 + b * t + ∑ n ∈ Finset.range (jumpCount (fun n => arrival τ n ω) t), Y n ω := rfl
  rw [hcp]
  exact hg.const_add _

/-- The compound Poisson path almost surely starts at `0`: on the almost-sure event that the first
arrival is positive, no jump has occurred by time `0`, so the path equals its starting value. -/
theorem compoundPoisson_ae_start (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, compoundPoisson b τ Y 0 ω = 0 := by
  filter_upwards [hd.ae_arrival_pos hr] with ω hpos
  exact piecewisePath_zero hpos

/-- **The compound Poisson process has almost surely càdlàg sample paths.** On the almost-sure event
that the arrival times are strictly increasing and diverge to `+∞`, every sample path is a
piecewise-affine jump path, hence right-continuous with left limits everywhere. -/
theorem compoundPoisson_ae_isCadlag (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t => compoundPoisson b τ Y t ω) := by
  filter_upwards [hd.ae_strictMono_arrival hr, hd.ae_tendsto_arrival hr] with ω hmono htop
  exact isCadlag_piecewisePath hmono htop

/-- **The pathwise Itô formula for a compound Poisson process.** For a `C¹` function `f` (given by
`HasDerivAt` data with continuous derivative `f'`), almost every sample path of the
compound-Poisson-with-drift process satisfies, at every time `t ≥ 0`,

`f (Xₜ) − f (X₀) = ∫₀ᵗ f'(Xₛ)·b ds + ∑ₙ, Tₙ ≤ t (f(X_{Tₙ}) − f(X_{Tₙ} − Yₙ))`,

i.e. the increment of `f` along the path splits into the drift integral plus the sum, over the
arrivals `Tₙ = arrival τ n ω` up to time `t`, of the jump increments `f(X_{Tₙ}) − f(X_{Tₙ} − Yₙ)`.

There is **no stochastic integral**: the compound Poisson process has finite activity — only
finitely many jumps in any bounded interval — so the formula holds pathwise and deterministically for
each fixed `ω` in the almost-sure event. The whole time-quantifier `∀ t, 0 ≤ t → …` lives *inside*
the almost-everywhere quantifier: a single null set is discarded, after which the identity holds
simultaneously for all `t`. (The null set depends only on the arrival structure, not on `f`.) -/
theorem compoundPoisson_pathwise_ito (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r)
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t →
      f (compoundPoisson b τ Y t ω) - f (compoundPoisson b τ Y 0 ω)
        = (∫ s in (0:ℝ)..t, f' (compoundPoisson b τ Y s ω) * b)
          + ∑ n ∈ Finset.range (jumpCount (fun m => arrival τ m ω) t),
              (f (compoundPoisson b τ Y (arrival τ n ω) ω)
                - f (compoundPoisson b τ Y (arrival τ n ω) ω - Y n ω)) := by
  filter_upwards [hd.ae_strictMono_arrival hr, hd.ae_arrival_pos hr, hd.ae_tendsto_arrival hr]
    with ω hmono hpos htop
  intro t ht
  exact piecewisePath_ito hf hf' hmono htop hpos ht

end CompoundPoisson

end ProbabilityTheory
