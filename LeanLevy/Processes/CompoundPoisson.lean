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
positivity, strict monotonicity, and divergence to `+∞` — which the pathwise Itô construction in the
next layer consumes.

## Main definitions

* `ProbabilityTheory.arrival` — the arrival-time partial sums of the interarrival sequence.
* `ProbabilityTheory.IsCompoundPoissonDriver` — the joint independence and marginal-law data of the
  interarrival/mark sequences.

## Main results

* `ProbabilityTheory.exists_isCompoundPoissonDriver` — a compound Poisson driver exists for any
  positive rate `r` and any probability law `ν'` of the marks, on a canonical probability space.
* `ProbabilityTheory.IsCompoundPoissonDriver.ae_interarrival_pos` — the interarrival times are almost
  surely all positive.
* `ProbabilityTheory.IsCompoundPoissonDriver.ae_strictMono_arrival` — the arrival times are almost
  surely strictly increasing.
* `ProbabilityTheory.IsCompoundPoissonDriver.ae_tendsto_arrival` — the arrival times almost surely
  tend to `+∞`.

## Implementation notes

The joint independence is stored as a single `iIndepFun` over the combined index type `ℕ ⊕ ℕ`, with
the interarrival family on the `Sum.inl` block and the mark family on the `Sum.inr` block, glued by
`Sum.elim τ Y`. This one-family spelling is what lets later layers extract *any* disjoint-block
independence (interarrivals ⟂ marks, or finite subfamilies of either) via `iIndepFun.precomp` and
`iIndepFun.indepFun_finset`.

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
  have hτ : iIndepFun τ μ := by
    have := h.indep.precomp (g := Sum.inl) Sum.inl_injective
    simpa [Function.comp] using this
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

end ProbabilityTheory
