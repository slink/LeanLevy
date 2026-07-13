/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import LeanLevy.RandomMeasure.PoissonPointFamily

/-!
# The Poisson random measure

Given a Poisson point family `IsPoissonPointFamily K X m μ` for a σ-finite intensity `m` on `E`
(a count `K k` and points `X k n` on each finite-mass partition piece, all jointly independent), the
**Poisson random measure** places a unit atom at each realized point:
`poissonRandomMeasure K X ω = ∑ₖ ∑_{n < K k ω} δ_{X k n ω}`. This file constructs it as a genuine
`Measure E`-valued random object — not an axiomatized one — and identifies the laws of its set
evaluations.

## Main definitions

* `ProbabilityTheory.poissonRandomMeasure` — the random measure itself, a `Measure E` for each `ω`.

## Main results

* `ProbabilityTheory.poissonRandomMeasure_apply` — the evaluation on a measurable set `A` is the total
  number of realized points landing in `A`, `∑ₖ thinnedCount K X A k`.
* `ProbabilityTheory.measurable_poissonRandomMeasure_apply` — that evaluation is a measurable function
  of `ω`.
* `ProbabilityTheory.map_poissonRandomMeasure_apply` — **superposition**: the count of points in a
  finite-mass set `A` is Poisson-distributed with mean `m A`.
* `ProbabilityTheory.indepFun_poissonRandomMeasure_apply` — the counts in two disjoint finite-mass
  sets are independent (the two-set API).
* `ProbabilityTheory.iIndepFun_poissonRandomMeasure_apply` — **mutual independence**: the counts in a
  finite pairwise-disjoint family of finite-mass sets are mutually independent.

The evaluation laws are read off the thinning and within-piece factorization of
`PoissonPointFamily` by superposing the independent pieces: the count in `A` is the sum of the
per-piece thinned counts, whose partial sums are Poisson by convolution and whose independence across
pieces comes from the prefix-versus-next-block splitting of the point family.
-/

open MeasureTheory Filter Complex
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {A B : Set E} {ω : Ω}

/-- **The Poisson random measure** of a Poisson point family: for each `ω`, the measure placing a
unit Dirac mass at each of the realized points `X k n ω` (for `n < K k ω`) across all pieces `k`.
Equivalently `∑ₖ ∑_{n < K k ω} δ_{X k n ω}`. -/
noncomputable def poissonRandomMeasure (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (ω : Ω) : Measure E :=
  Measure.sum fun k => Measure.sum fun n =>
    if n < K k ω then Measure.dirac (X k n ω) else 0

omit [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] in
/-- The `ℝ≥0∞`-cast of the thinned count as a finite sum of point-membership indicators. -/
private lemma thinnedCount_toENNReal :
    (thinnedCount K X A k ω : ℝ≥0∞)
      = ∑ n ∈ Finset.range (K k ω), A.indicator (1 : E → ℝ≥0∞) (X k n ω) := by
  classical
  rw [thinnedCount, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hx : X k n ω ∈ A
  · rw [Set.indicator_of_mem hx, if_pos hx, Pi.one_apply, Nat.cast_one]
  · rw [Set.indicator_of_notMem hx, if_neg hx, Nat.cast_zero]

omit [MeasurableSpace Ω] [Nonempty E] in
/-- **Evaluation of the Poisson random measure.** On a measurable set `A`, the random measure counts
the total number of realized points across all pieces landing in `A`. -/
theorem poissonRandomMeasure_apply (hA : MeasurableSet A) :
    poissonRandomMeasure K X ω A = ∑' k, (thinnedCount K X A k ω : ℝ≥0∞) := by
  classical
  rw [poissonRandomMeasure, Measure.sum_apply _ hA]
  refine tsum_congr fun k => ?_
  rw [Measure.sum_apply _ hA]
  have hterm : ∀ n, (if n < K k ω then Measure.dirac (X k n ω) else 0) A
      = if n < K k ω then A.indicator (1 : E → ℝ≥0∞) (X k n ω) else 0 := by
    intro n
    rw [apply_ite (fun ν : Measure E => ν A), Measure.dirac_apply' _ hA, Measure.coe_zero,
      Pi.zero_apply]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (K k ω)) fun n hn => by
    rw [if_neg (by simpa [Finset.mem_range] using hn)]]
  rw [thinnedCount_toENNReal]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (by simpa [Finset.mem_range] using hn)]

omit [Nonempty E] in
/-- The set evaluation of the Poisson random measure is a measurable function of `ω`. -/
theorem measurable_poissonRandomMeasure_apply (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) :
    Measurable fun ω => poissonRandomMeasure K X ω A := by
  simp_rw [poissonRandomMeasure_apply hA]
  refine Measurable.ennreal_tsum fun k => ?_
  exact measurable_from_top.comp (measurable_thinnedCount (hK k) (hX k) hA)

/-! ### Superposition: the law of the count in a set

The count of realized points in a measurable set `A` is the superposition `∑ₖ thinnedCount K X A k`
of the per-piece thinned counts. Its partial sums `prmPartialCount K X A n` are Poisson-distributed
(by convolution, using the prefix-versus-next-block independence of the point family), and passing to
the limit — legitimate because the total count is almost surely finite, with `E[count] = m A < ⊤` —
identifies the count in `A` as Poisson with mean `m A`. -/

omit [Nonempty E] in
/-- The rates of the per-piece thinned counts sum to the total mass: `∑ₖ m (piece k ∩ A) = m A`,
since the pieces intersected with `A` partition `A`. -/
private lemma tsum_measure_prmPiece_inter (hA : MeasurableSet A) :
    ∑' k, m (prmPiece m k ∩ A) = m A := by
  rw [← measure_iUnion (fun i j hij =>
        (pairwise_disjoint_prmPiece hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun k => measurableSet_prmPiece.inter hA),
    ← Set.iUnion_inter, iUnion_prmPiece, Set.univ_inter]

/-- The `ℝ≥0∞`-mean of `poissonMeasure r` is `r`. -/
private lemma lintegral_id_poissonMeasure (r : ℝ≥0) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(poissonMeasure r) = (r : ℝ≥0∞) := by
  rw [lintegral_countable' (fun n : ℕ => (n : ℝ≥0∞))]
  have hsingle : ∀ n : ℕ, poissonMeasure r {n} = ENNReal.ofReal (poissonPMFReal r n) := by
    intro n
    rw [poissonMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]; rfl
  have hterm : ∀ n : ℕ, (n : ℝ≥0∞) * poissonMeasure r {n}
      = ENNReal.ofReal ((n : ℝ) * poissonPMFReal r n) := by
    intro n
    rw [hsingle, ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (Nat.cast_nonneg n) poissonPMFReal_nonneg)
      (poissonExpectation_hasSum r).summable, (poissonExpectation_hasSum r).tsum_eq,
    ENNReal.ofReal_coe_nnreal]

/-- The `ℝ≥0∞`-mean of the thinned count is the mass of the piece intersected with `A`. -/
private lemma lintegral_thinnedCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) :
    ∫⁻ ω, (thinnedCount K X A k ω : ℝ≥0∞) ∂μ = m (prmPiece m k ∩ A) := by
  have hTA : Measurable (thinnedCount K X A k) :=
    measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA
  have hmap : ∫⁻ ω, (thinnedCount K X A k ω : ℝ≥0∞) ∂μ
      = ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂(μ.map (thinnedCount K X A k)) :=
    (lintegral_map (f := fun n : ℕ => (n : ℝ≥0∞)) measurable_from_top hTA).symm
  rw [hmap, map_thinnedCount hd hA, lintegral_id_poissonMeasure,
    ENNReal.coe_toNNReal (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      measure_prmPiece_lt_top).ne]

/-- The total count in `A` has `ℝ≥0∞`-mean `m A`. -/
private lemma lintegral_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) :
    ∫⁻ ω, poissonRandomMeasure K X ω A ∂μ = m A := by
  simp_rw [poissonRandomMeasure_apply hA]
  rw [lintegral_tsum (f := fun k ω => (thinnedCount K X A k ω : ℝ≥0∞)) fun k =>
    (measurable_from_top.comp
      (measurable_thinnedCount (hd.measurable_count k) (hd.measurable_point k) hA)).aemeasurable]
  simp_rw [lintegral_thinnedCount hd hA]
  exact tsum_measure_prmPiece_inter hA

/-- The total count in a finite-mass set is almost surely finite. -/
private lemma ae_poissonRandomMeasure_apply_lt_top [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    ∀ᵐ ω ∂μ, poissonRandomMeasure K X ω A < ⊤ :=
  ae_lt_top (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA)
    (by rw [lintegral_poissonRandomMeasure_apply hd hA]; exact hfin.ne)

/-- **The partial superposition count**: the number of realized points landing in `A` coming from the
first `n + 1` pieces. Its `n → ∞` limit is the total count in `A`. -/
private noncomputable def prmPartialCount (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (A : Set E) (n : ℕ)
    (ω : Ω) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), thinnedCount K X A k ω

omit [Nonempty E] in
open Classical in
/-- Measurability skeleton for the count of points of a single piece landing in `A`, phrased over an
abstract coordinate space `D` supplying the count `cnt` and the points `pt`. Both the thinned-count
extractors used in the superposition independence step are instances. -/
private lemma measurable_filterCard {D : Type*} [MeasurableSpace D] (hA : MeasurableSet A)
    (cnt : D → ℕ) (pt : ℕ → D → E) (hcnt : Measurable cnt) (hpt : ∀ n', Measurable (pt n')) :
    Measurable fun g => ((Finset.range (cnt g)).filter fun n' => pt n' g ∈ A).card := by
  have hcard : (fun g => ((Finset.range (cnt g)).filter fun n' => pt n' g ∈ A).card)
      = fun g => ∑ n' ∈ Finset.range (cnt g), (if pt n' g ∈ A then (1 : ℕ) else 0) := by
    funext g; rw [Finset.card_filter]
  rw [hcard]
  have hP : Measurable
      fun p : D × ℕ => ∑ n' ∈ Finset.range p.2, (if pt n' p.1 ∈ A then (1 : ℕ) else 0) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n' _ =>
        Measurable.ite (hpt n' hA) measurable_const measurable_const
  exact hP.comp (measurable_id.prodMk hcnt)

omit [Nonempty E] in
/-- The partial superposition count is measurable. -/
private lemma measurable_prmPartialCount (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) (n : ℕ) :
    Measurable (prmPartialCount K X A n) :=
  Finset.measurable_sum _ fun k _ => measurable_thinnedCount (hK k) (hX k) hA

/-- **Prefix-versus-next-piece independence of the superposition count.** The partial count from the
first `n + 1` pieces is independent of the thinned count of piece `n + 1`, since they read disjoint
blocks of the point family. -/
private lemma indepFun_prmPartialCount_thinnedCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (n : ℕ) :
    IndepFun (prmPartialCount K X A n) (thinnedCount K X A (n + 1)) μ := by
  classical
  set φ : Fin (n + 1) ⊕ Fin (n + 1) × ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun k => Sum.inl (k : ℕ)) (fun p => Sum.inr ((p.1 : ℕ), p.2)) with hφ_def
  set ψ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun _ => Sum.inl (n + 1)) (fun n' => Sum.inr (n + 1, n')) with hψ_def
  have hφ_inj : Function.Injective φ := by
    rintro (a | ⟨a, a'⟩) (b | ⟨b, b'⟩) hab <;>
      simp_all [Fin.val_inj]
  have hψ_inj : Function.Injective ψ := by
    rintro (⟨⟩ | a) (⟨⟩ | b) hab <;> simp_all
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (a | ⟨a, a'⟩) (⟨⟩ | t) <;> simp only [hφ_def, hψ_def, Sum.elim_inl, Sum.elim_inr,
      ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, not_false_eq_true, Prod.mk.injEq]
    · exact fun h => (Nat.ne_of_lt a.isLt) h
    · exact fun h => (Nat.ne_of_lt a.isLt) h.1
  have hsplit := hd.indepFun_pointFamily_split φ ψ hφ_inj hψ_inj hST
  -- Extraction of the prefix count from the left block process.
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ, pointFamilyIndexType E (φ i)) → ℕ :=
    fun g => ∑ k : Fin (n + 1),
      ((Finset.range (g (Sum.inl k))).filter fun n' => g (Sum.inr (k, n')) ∈ A).card with hG_def
  set H : (∀ j : Unit ⊕ ℕ, pointFamilyIndexType E (ψ j)) → ℕ :=
    fun g => ((Finset.range (g (Sum.inl ()))).filter fun n' => g (Sum.inr n') ∈ A).card with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact Finset.measurable_sum _ fun k _ =>
      measurable_filterCard
        (D := (i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ) → pointFamilyIndexType E (φ i))
        hA (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hH : Measurable H := by
    rw [hH_def]
    exact measurable_filterCard
      (D := (j : Unit ⊕ ℕ) → pointFamilyIndexType E (ψ j))
      hA (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
      (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hGeq : (fun ω => G fun i => pointFamilyCombined K X (φ i) ω) = prmPartialCount K X A n := by
    funext ω
    simp only [hG_def]
    unfold prmPartialCount
    rw [← Fin.sum_univ_eq_sum_range (fun j => thinnedCount K X A j ω) (n + 1)]
    rfl
  have hHeq : (fun ω => H fun j => pointFamilyCombined K X (ψ j) ω)
      = thinnedCount K X A (n + 1) := by
    funext ω; rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rwa [hGeq, hHeq] at key

/-- Poisson measures convolve by adding rates, at the `ℕ` level. -/
private lemma poissonMeasure_conv (a b : ℝ≥0) :
    poissonMeasure a ∗ poissonMeasure b = poissonMeasure (a + b) :=
  poissonMeasure_add_conv a b

/-- **The partial superposition count is Poisson.** The count of points landing in `A` from the first
`n + 1` pieces is Poisson-distributed with mean `∑ₖ m (piece k ∩ A)`. Proved by induction on `n`:
each new piece contributes an independent thinned count, and Poisson laws convolve by adding rates. -/
private lemma map_prmPartialCount [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (n : ℕ) :
    μ.map (prmPartialCount K X A n)
      = poissonMeasure (∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal) := by
  induction n with
  | zero =>
    have h0 : prmPartialCount K X A 0 = thinnedCount K X A 0 := by
      funext ω; rw [prmPartialCount, Finset.sum_range_one]
    rw [h0, map_thinnedCount hd hA, Finset.sum_range_one]
  | succ n ih =>
    have hsucc : prmPartialCount K X A (n + 1)
        = prmPartialCount K X A n + thinnedCount K X A (n + 1) := by
      funext ω; simp only [prmPartialCount, Pi.add_apply, Finset.sum_range_succ]
    have hlawP : HasLaw (prmPartialCount K X A n)
        (poissonMeasure (∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal)) μ :=
      ⟨(measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n).aemeasurable, ih⟩
    have hlawT : HasLaw (thinnedCount K X A (n + 1))
        (poissonMeasure (m (prmPiece m (n + 1) ∩ A)).toNNReal) μ :=
      ⟨(measurable_thinnedCount (hd.measurable_count _) (hd.measurable_point _) hA).aemeasurable,
        map_thinnedCount hd hA⟩
    have hsum := (indepFun_prmPartialCount_thinnedCount hd hA n).hasLaw_add hlawP hlawT
    rw [hsucc, hsum.map_eq, poissonMeasure_conv]
    congr 1
    exact (Finset.sum_range_succ (fun k => (m (prmPiece m k ∩ A)).toNNReal) (n + 1)).symm

/-! ### The superposition law: the count in a finite-mass set is Poisson

The partial counts `prmPartialCount K X A n` increase to the total count `poissonRandomMeasure K X · A`
almost surely (the total count being finite by `ae_poissonRandomMeasure_apply_lt_top`), so their
Poisson laws pass to the limit. The identification is carried out through characteristic functions and
dominated convergence: the characteristic function of each partial count is the Poisson pgf with the
accumulated rate `∑_{k ≤ n} m (piece k ∩ A)`, and these rates increase to `m A`. -/

/-- The characteristic function of the `ℝ`-pushforward of the partial superposition count is the
Poisson pgf with the accumulated rate `∑_{k ≤ n} m (piece k ∩ A)`, read off `map_prmPartialCount`. -/
private lemma charFun_natCast_prmPartialCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (n : ℕ) (ξ : ℝ) :
    charFun (μ.map fun ω => (prmPartialCount K X A n ω : ℝ)) ξ
      = Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
          * (Complex.exp (↑ξ * I) - 1)) := by
  have hmeas := measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n
  have hcoe : ((∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toNNReal : ℝ≥0) : ℝ)
      = ∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal := by
    rw [NNReal.coe_sum]
    exact Finset.sum_congr rfl fun k _ => ENNReal.coe_toNNReal_eq_toReal _
  rw [show (fun ω => ((prmPartialCount K X A n ω : ℕ) : ℝ))
        = (Nat.cast : ℕ → ℝ) ∘ prmPartialCount K X A n from rfl,
    ← Measure.map_map measurable_from_top hmeas, map_prmPartialCount hd hA n,
    charFun_poissonMeasure_eq, hcoe]

omit [Nonempty E] in
/-- The accumulated rates increase to the total mass `m A`, as a real limit; used to identify the
limit of the partial-count characteristic functions. -/
private lemma tendsto_rate_prmPartialCount (hA : MeasurableSet A) (hfin : m A < ⊤) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
      atTop (𝓝 (m A).toReal) := by
  have hsum : ∑' k, m (prmPiece m k ∩ A) = m A := tsum_measure_prmPiece_inter hA
  have hHS : HasSum (fun k => (m (prmPiece m k ∩ A)).toReal)
      (∑' k, (m (prmPiece m k ∩ A)).toReal) :=
    ENNReal.hasSum_toReal (by rw [hsum]; exact hfin.ne)
  have hval : (∑' k, (m (prmPiece m k ∩ A)).toReal) = (m A).toReal := by
    rw [← ENNReal.tsum_toReal_eq fun k => (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      measure_prmPiece_lt_top).ne, hsum]
  rw [hval] at hHS
  exact hHS.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

omit [Nonempty E] [MeasurableSpace Ω] in
/-- Almost surely the partial superposition counts increase to the total count in `A`: the partial
sums of the `ℝ≥0∞`-valued thinned counts tend to their tsum, which is finite on the almost-sure
finiteness event, so `ENNReal.toReal` is continuous there. -/
private lemma tendsto_natCast_prmPartialCount (hA : MeasurableSet A) (ω : Ω)
    (hω : poissonRandomMeasure K X ω A < ⊤) :
    Tendsto (fun n => (prmPartialCount K X A n ω : ℝ)) atTop
      (𝓝 (poissonRandomMeasure K X ω A).toReal) := by
  have hHS : HasSum (fun k => (thinnedCount K X A k ω : ℝ≥0∞)) (poissonRandomMeasure K X ω A) := by
    rw [poissonRandomMeasure_apply hA]; exact ENNReal.summable.hasSum
  have hcast : ∀ n, ((prmPartialCount K X A n ω : ℕ) : ℝ≥0∞)
      = ∑ i ∈ Finset.range (n + 1), (thinnedCount K X A i ω : ℝ≥0∞) := by
    intro n; rw [prmPartialCount]; exact Nat.cast_sum _ _
  have hpart : Tendsto (fun n => ((prmPartialCount K X A n ω : ℕ) : ℝ≥0∞)) atTop
      (𝓝 (poissonRandomMeasure K X ω A)) := by
    simp_rw [hcast]
    exact hHS.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hlim := (ENNReal.tendsto_toReal hω.ne).comp hpart
  simpa only [Function.comp_def, ENNReal.toReal_natCast] using hlim

/-- The characteristic function of the `ℝ`-pushforward of the total count in a finite-mass set `A` is
the Poisson pgf with mean `m A`. Obtained by dominated convergence from the partial counts: their
characteristic functions are the Poisson pgfs at the accumulated rates (`charFun_natCast_prmPartialCount`),
the rates increase to `m A` (`tendsto_rate_prmPartialCount`), and the integrands are bounded by `1`
and converge almost surely (`tendsto_natCast_prmPartialCount`). -/
private lemma charFun_natCast_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hfin : m A < ⊤) (ξ : ℝ) :
    charFun (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) ξ
      = Complex.exp (↑(m A).toReal * (Complex.exp (↑ξ * I) - 1)) := by
  have hSn_meas : ∀ n, Measurable fun ω => (prmPartialCount K X A n ω : ℝ) := fun n =>
    measurable_from_top.comp
      (measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n)
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  have hFmeas : ∀ n, Measurable
      fun ω => Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I) := fun n =>
    Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp (hSn_meas n)).const_mul (↑ξ)).mul_const I)
  have hbound : ∀ n, ∀ᵐ ω ∂μ,
      ‖Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I)‖ ≤ (fun _ : Ω => (1 : ℝ)) ω := by
    intro n
    filter_upwards with ω
    have : ‖Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I)‖ = 1 := by
      rw [show (↑ξ : ℂ) * ↑(prmPartialCount K X A n ω : ℝ) * I
          = ↑(ξ * (prmPartialCount K X A n ω : ℝ)) * I from by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    exact le_of_eq this
  have hlim : ∀ᵐ ω ∂μ,
      Tendsto (fun n => Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I)) atTop
        (𝓝 (Complex.exp (↑ξ * ↑(poissonRandomMeasure K X ω A).toReal * I))) := by
    filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hA hfin] with ω hω
    have hc : Continuous fun x : ℝ => Complex.exp (↑ξ * ↑x * I) := by fun_prop
    exact (hc.tendsto _).comp (tendsto_natCast_prmPartialCount hA ω hω)
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => (1 : ℝ)) (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  have key : ∀ n, ∫ ω, Complex.exp (↑ξ * ↑(prmPartialCount K X A n ω : ℝ) * I) ∂μ
      = charFun (μ.map fun ω => (prmPartialCount K X A n ω : ℝ)) ξ := fun n => by
    rw [charFun_apply_real, integral_map (hSn_meas n).aemeasurable (by fun_prop)]
  have keyN : ∫ ω, Complex.exp (↑ξ * ↑(poissonRandomMeasure K X ω A).toReal * I) ∂μ
      = charFun (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) ξ := by
    rw [charFun_apply_real, integral_map hN_meas.aemeasurable (by fun_prop)]
  simp_rw [key, charFun_natCast_prmPartialCount hd hA] at hdct
  rw [keyN] at hdct
  have hrate : Tendsto
      (fun n => Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
        * (Complex.exp (↑ξ * I) - 1))) atTop
      (𝓝 (Complex.exp (↑(m A).toReal * (Complex.exp (↑ξ * I) - 1)))) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun r : ℝ =>
      Complex.exp (↑r * (Complex.exp (↑ξ * I) - 1))) _)).comp
      (tendsto_rate_prmPartialCount hA hfin)
  exact tendsto_nhds_unique hdct hrate

/-- **Superposition (the evaluation law).** The total number of realized points landing in a
finite-mass measurable set `A` is Poisson-distributed with mean `m A`. This is the defining property
of a Poisson random measure. The `ℝ≥0∞`-valued count is identified via its `ℝ`-pushforward, whose
characteristic function matches the Poisson pgf (`charFun_natCast_poissonRandomMeasure_apply`), and
then descended along `ENNReal.ofReal` using the almost-sure finiteness of the count. -/
theorem map_poissonRandomMeasure_apply [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hA : MeasurableSet A) (hfin : m A < ⊤) :
    μ.map (fun ω => poissonRandomMeasure K X ω A)
      = (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  have hN_meas : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  have hRlaw : (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal)
      = (poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ) := by
    haveI : IsProbabilityMeasure (μ.map fun ω => (poissonRandomMeasure K X ω A).toReal) :=
      Measure.isProbabilityMeasure_map hN_meas.aemeasurable
    haveI : IsProbabilityMeasure ((poissonMeasure (m A).toNNReal).map (Nat.cast : ℕ → ℝ)) :=
      Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable
    apply Measure.ext_of_charFun
    funext ξ
    rw [charFun_natCast_poissonRandomMeasure_apply hd hA hfin, charFun_poissonMeasure_eq,
      ENNReal.coe_toNNReal_eq_toReal]
  have hae : (fun ω => poissonRandomMeasure K X ω A)
      =ᵐ[μ] fun ω => ENNReal.ofReal ((poissonRandomMeasure K X ω A).toReal) := by
    filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hA hfin] with ω hω
    rw [ENNReal.ofReal_toReal hω.ne]
  rw [Measure.map_congr hae,
    show (fun ω => ENNReal.ofReal ((poissonRandomMeasure K X ω A).toReal))
      = ENNReal.ofReal ∘ fun ω => (poissonRandomMeasure K X ω A).toReal from rfl,
    ← Measure.map_map ENNReal.continuous_ofReal.measurable hN_meas, hRlaw,
    Measure.map_map ENNReal.continuous_ofReal.measurable measurable_from_top]
  congr 1
  funext n
  rw [Function.comp_apply, ENNReal.ofReal_natCast]

/-! ### Pairwise independence of the counts in disjoint sets

For two disjoint finite-mass sets `A` and `B`, the counts `poissonRandomMeasure K X · A` and
`poissonRandomMeasure K X · B` are independent. The proof is the joint analogue of the superposition
law: the pair of partial counts `(prmPartialCount A n, prmPartialCount B n)` has a joint
characteristic function that factorizes — each piece contributes an independent pair (the
prefix-versus-next-block splitting), and within each piece the two counts are independent because `A`
and `B` are disjoint (`indepFun_thinnedCount_thinnedCount`, packaged in `charFunDual_prod_thinnedCount`).
Passing to the limit by dominated convergence identifies the joint characteristic function of the pair
`(count A, count B)` as a product, hence independence. This two-set statement is retained as API;
mutual independence over a finite pairwise-disjoint family is delivered below by
`iIndepFun_poissonRandomMeasure_apply`. -/

/-- A real linear form on `ℝ` acts by scaling: `M r = r · M 1`. -/
private lemma real_dual_apply (M : StrongDual ℝ ℝ) (r : ℝ) : M r = r * M 1 := by
  conv_rhs => rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- On `ℝ`, the characteristic function through a real linear form is the ordinary characteristic
function evaluated at `M 1`; the bridge turning the marginal `charFunDual` factors into the scalar
`charFun` computed in `charFun_natCast_poissonRandomMeasure_apply`. -/
private lemma charFunDual_real_eq_charFun (ν : Measure ℝ) (M : StrongDual ℝ ℝ) :
    charFunDual ν M = charFun ν (M 1) := by
  rw [charFunDual_apply, charFun_apply_real]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show Complex.exp (↑(M x) * I) = Complex.exp (↑(M 1) * ↑x * I)
  rw [real_dual_apply M x]
  congr 1
  push_cast
  ring

/-- **Prefix-versus-next-piece independence of the superposition-count pair.** The pair of partial
counts from the first `n + 1` pieces is independent of the pair of thinned counts of piece `n + 1`,
built from the public split engine with the same injections as the single-set version, extracting
both the `A`- and `B`-counts from each block. -/
private lemma indepFun_prmPartialCountPair_thinnedCountPair [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    IndepFun (fun ω => (prmPartialCount K X A n ω, prmPartialCount K X B n ω))
      (fun ω => (thinnedCount K X A (n + 1) ω, thinnedCount K X B (n + 1) ω)) μ := by
  classical
  set φ : Fin (n + 1) ⊕ Fin (n + 1) × ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun k => Sum.inl (k : ℕ)) (fun p => Sum.inr ((p.1 : ℕ), p.2)) with hφ_def
  set ψ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun _ => Sum.inl (n + 1)) (fun n' => Sum.inr (n + 1, n')) with hψ_def
  have hφ_inj : Function.Injective φ := by
    rintro (a | ⟨a, a'⟩) (b | ⟨b, b'⟩) hab <;> simp_all [Fin.val_inj]
  have hψ_inj : Function.Injective ψ := by
    rintro (⟨⟩ | a) (⟨⟩ | b) hab <;> simp_all
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (a | ⟨a, a'⟩) (⟨⟩ | t) <;> simp only [hφ_def, hψ_def, Sum.elim_inl, Sum.elim_inr,
      ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, not_false_eq_true, Prod.mk.injEq]
    · exact fun h => (Nat.ne_of_lt a.isLt) h
    · exact fun h => (Nat.ne_of_lt a.isLt) h.1
  have hsplit := hd.indepFun_pointFamily_split φ ψ hφ_inj hψ_inj hST
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ, pointFamilyIndexType E (φ i)) → ℕ × ℕ :=
    fun g => (∑ k : Fin (n + 1),
        ((Finset.range (g (Sum.inl k))).filter fun n' => g (Sum.inr (k, n')) ∈ A).card,
      ∑ k : Fin (n + 1),
        ((Finset.range (g (Sum.inl k))).filter fun n' => g (Sum.inr (k, n')) ∈ B).card) with hG_def
  set H : (∀ j : Unit ⊕ ℕ, pointFamilyIndexType E (ψ j)) → ℕ × ℕ :=
    fun g => (((Finset.range (g (Sum.inl ()))).filter fun n' => g (Sum.inr n') ∈ A).card,
      ((Finset.range (g (Sum.inl ()))).filter fun n' => g (Sum.inr n') ∈ B).card) with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact (Finset.measurable_sum _ fun k _ => measurable_filterCard
        (D := (i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ) → pointFamilyIndexType E (φ i))
        hA (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _).prodMk
      (Finset.measurable_sum _ fun k _ => measurable_filterCard
        (D := (i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ) → pointFamilyIndexType E (φ i))
        hB (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _)
  have hH : Measurable H := by
    rw [hH_def]
    exact (measurable_filterCard (D := (j : Unit ⊕ ℕ) → pointFamilyIndexType E (ψ j))
        hA (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _).prodMk
      (measurable_filterCard (D := (j : Unit ⊕ ℕ) → pointFamilyIndexType E (ψ j))
        hB (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _)
  have hGeq : (fun ω => G fun i => pointFamilyCombined K X (φ i) ω)
      = fun ω => (prmPartialCount K X A n ω, prmPartialCount K X B n ω) := by
    funext ω
    simp only [hG_def]
    rw [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · unfold prmPartialCount
      rw [← Fin.sum_univ_eq_sum_range (fun j => thinnedCount K X A j ω) (n + 1)]
      rfl
    · unfold prmPartialCount
      rw [← Fin.sum_univ_eq_sum_range (fun j => thinnedCount K X B j ω) (n + 1)]
      rfl
  have hHeq : (fun ω => H fun j => pointFamilyCombined K X (ψ j) ω)
      = fun ω => (thinnedCount K X A (n + 1) ω, thinnedCount K X B (n + 1) ω) := by
    funext ω; rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rwa [hGeq, hHeq] at key

/-- The `ℝ²`-cast form of the previous lemma, ready to feed the characteristic-function factorization
of the pair partial sums. -/
private lemma indepFun_prmPartialCountPair_real [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    IndepFun (fun ω => ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ)))
      (fun ω => ((thinnedCount K X A (n + 1) ω : ℝ), (thinnedCount K X B (n + 1) ω : ℝ))) μ := by
  have h := (indepFun_prmPartialCountPair_thinnedCountPair hd hA hB n).comp
    (φ := Prod.map (Nat.cast : ℕ → ℝ) (Nat.cast : ℕ → ℝ))
    (ψ := Prod.map (Nat.cast : ℕ → ℝ) (Nat.cast : ℕ → ℝ))
    (measurable_from_top.prodMap measurable_from_top)
    (measurable_from_top.prodMap measurable_from_top)
  simpa only [Function.comp_def, Prod.map_apply] using h

/-- **Joint characteristic function of the pair of partial superposition counts.** It factorizes into
the two Poisson pgfs with the accumulated `A`- and `B`-rates, by induction on the number of pieces:
the base case is the within-piece factorization `charFunDual_prod_thinnedCount`, and each step adds an
independent pair block. -/
private lemma charFunDual_prmPartialCountPair [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (n : ℕ) (L : StrongDual ℝ (ℝ × ℝ)) :
    charFunDual (μ.map fun ω =>
        ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ))) L
      = Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A)).toReal)
          * (Complex.exp (↑(L.comp (.inl ℝ ℝ ℝ) 1) * I) - 1))
        * Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ B)).toReal)
          * (Complex.exp (↑(L.comp (.inr ℝ ℝ ℝ) 1) * I) - 1)) := by
  induction n with
  | zero =>
    have h0 : (fun ω => ((prmPartialCount K X A 0 ω : ℝ), (prmPartialCount K X B 0 ω : ℝ)))
        = fun ω => ((thinnedCount K X A 0 ω : ℝ), (thinnedCount K X B 0 ω : ℝ)) := by
      funext ω
      rw [prmPartialCount, prmPartialCount, Finset.sum_range_one, Finset.sum_range_one]
    rw [h0, charFunDual_prod_thinnedCount hd hA hB hAB L, Finset.sum_range_one,
      Finset.sum_range_one]
  | succ n ih =>
    have mPn : Measurable
        fun ω => ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ)) :=
      (measurable_from_top.comp
          (measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n)).prodMk
        (measurable_from_top.comp
          (measurable_prmPartialCount hd.measurable_count hd.measurable_point hB n))
    have mQn : Measurable
        fun ω => ((thinnedCount K X A (n + 1) ω : ℝ), (thinnedCount K X B (n + 1) ω : ℝ)) :=
      (measurable_from_top.comp
          (measurable_thinnedCount (hd.measurable_count _) (hd.measurable_point _) hA)).prodMk
        (measurable_from_top.comp
          (measurable_thinnedCount (hd.measurable_count _) (hd.measurable_point _) hB))
    have hpA : ∀ ω, (prmPartialCount K X A (n + 1) ω : ℝ)
        = (prmPartialCount K X A n ω : ℝ) + (thinnedCount K X A (n + 1) ω : ℝ) := by
      intro ω; rw [prmPartialCount, Finset.sum_range_succ, Nat.cast_add]; rfl
    have hpB : ∀ ω, (prmPartialCount K X B (n + 1) ω : ℝ)
        = (prmPartialCount K X B n ω : ℝ) + (thinnedCount K X B (n + 1) ω : ℝ) := by
      intro ω; rw [prmPartialCount, Finset.sum_range_succ, Nat.cast_add]; rfl
    have hsucc : (fun ω =>
          ((prmPartialCount K X A (n + 1) ω : ℝ), (prmPartialCount K X B (n + 1) ω : ℝ)))
        = fun ω => ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ))
            + ((thinnedCount K X A (n + 1) ω : ℝ), (thinnedCount K X B (n + 1) ω : ℝ)) := by
      funext ω; rw [Prod.mk_add_mk, ← hpA, ← hpB]
    rw [hsucc, IndepFun.charFunDual_map_fun_add_eq_mul mPn.aemeasurable mQn.aemeasurable
        (indepFun_prmPartialCountPair_real hd hA hB n), Pi.mul_apply, ih,
      charFunDual_prod_thinnedCount hd hA hB hAB L,
      Finset.sum_range_succ (fun k => (m (prmPiece m k ∩ A)).toReal) (n + 1),
      Finset.sum_range_succ (fun k => (m (prmPiece m k ∩ B)).toReal) (n + 1)]
    push_cast
    rw [add_mul, add_mul, Complex.exp_add, Complex.exp_add]
    ring

/-- **Joint characteristic function of the pair of counts in `A` and `B`.** By dominated convergence
from the pair partial counts: the pairs converge almost surely on the joint finiteness event, the
integrands are bounded by `1`, and the accumulated rates increase to `m A` and `m B`. -/
private lemma charFunDual_poissonRandomMeasurePair [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hfinA : m A < ⊤) (hfinB : m B < ⊤) (L : StrongDual ℝ (ℝ × ℝ)) :
    charFunDual (μ.map fun ω =>
        ((poissonRandomMeasure K X ω A).toReal, (poissonRandomMeasure K X ω B).toReal)) L
      = Complex.exp (↑(m A).toReal * (Complex.exp (↑(L.comp (.inl ℝ ℝ ℝ) 1) * I) - 1))
        * Complex.exp (↑(m B).toReal * (Complex.exp (↑(L.comp (.inr ℝ ℝ ℝ) 1) * I) - 1)) := by
  have mPn : ∀ n, Measurable
      fun ω => ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ)) := fun n =>
    (measurable_from_top.comp
        (measurable_prmPartialCount hd.measurable_count hd.measurable_point hA n)).prodMk
      (measurable_from_top.comp
        (measurable_prmPartialCount hd.measurable_count hd.measurable_point hB n))
  have mN : Measurable fun ω =>
      ((poissonRandomMeasure K X ω A).toReal, (poissonRandomMeasure K X ω B).toReal) :=
    ((measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
        hA).ennreal_toReal).prodMk
      ((measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
        hB).ennreal_toReal)
  have hFmeas : ∀ n, Measurable fun ω => Complex.exp
      (↑(L ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ))) * I) := fun n =>
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (L.continuous.measurable.comp (mPn n))).mul_const I)
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Complex.exp
      (↑(L ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ))) * I)‖
        ≤ (fun _ : Ω => (1 : ℝ)) ω := by
    intro n; filter_upwards with ω
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Complex.exp
      (↑(L ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ))) * I)) atTop
      (𝓝 (Complex.exp (↑(L ((poissonRandomMeasure K X ω A).toReal,
        (poissonRandomMeasure K X ω B).toReal)) * I))) := by
    filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hA hfinA,
      ae_poissonRandomMeasure_apply_lt_top hd hB hfinB] with ω hωA hωB
    have hc : Continuous fun p : ℝ × ℝ => Complex.exp (↑(L p) * I) := by fun_prop
    exact (hc.tendsto _).comp
      ((tendsto_natCast_prmPartialCount hA ω hωA).prodMk_nhds
        (tendsto_natCast_prmPartialCount hB ω hωB))
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => (1 : ℝ)) (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  have key : ∀ n, ∫ ω, Complex.exp
        (↑(L ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ))) * I) ∂μ
      = charFunDual (μ.map fun ω =>
          ((prmPartialCount K X A n ω : ℝ), (prmPartialCount K X B n ω : ℝ))) L := fun n => by
    rw [charFunDual_apply, integral_map (mPn n).aemeasurable (by fun_prop)]
  have keyN : ∫ ω, Complex.exp
        (↑(L ((poissonRandomMeasure K X ω A).toReal,
          (poissonRandomMeasure K X ω B).toReal)) * I) ∂μ
      = charFunDual (μ.map fun ω =>
          ((poissonRandomMeasure K X ω A).toReal, (poissonRandomMeasure K X ω B).toReal)) L := by
    rw [charFunDual_apply, integral_map mN.aemeasurable (by fun_prop)]
  simp_rw [key, charFunDual_prmPartialCountPair hd hA hB hAB] at hdct
  rw [keyN] at hdct
  have hrate := (((Continuous.tendsto (by fun_prop : Continuous fun r : ℝ =>
        Complex.exp (↑r * (Complex.exp (↑(L.comp (.inl ℝ ℝ ℝ) 1) * I) - 1))) _)).comp
      (tendsto_rate_prmPartialCount hA hfinA)).mul
    (((Continuous.tendsto (by fun_prop : Continuous fun r : ℝ =>
        Complex.exp (↑r * (Complex.exp (↑(L.comp (.inr ℝ ℝ ℝ) 1) * I) - 1))) _)).comp
      (tendsto_rate_prmPartialCount hB hfinB))
  exact tendsto_nhds_unique hdct hrate

/-- The `ℝ`-valued counts in two disjoint finite-mass sets are independent: their joint
characteristic function is the product of the marginals (`charFunDual_poissonRandomMeasurePair`
matched against `charFun_natCast_poissonRandomMeasure_apply` through `charFunDual_real_eq_charFun`). -/
private lemma indepFun_natCast_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤) (hAB : Disjoint A B) :
    IndepFun (fun ω => (poissonRandomMeasure K X ω A).toReal)
      (fun ω => (poissonRandomMeasure K X ω B).toReal) μ := by
  have mNA : Measurable fun ω => (poissonRandomMeasure K X ω A).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hA).ennreal_toReal
  have mNB : Measurable fun ω => (poissonRandomMeasure K X ω B).toReal :=
    (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point hB).ennreal_toReal
  rw [indepFun_iff_map_prod_eq_prod_map_map mNA.aemeasurable mNB.aemeasurable]
  refine charFunDual_eq_prod_iff.mp fun L => ?_
  rw [charFunDual_poissonRandomMeasurePair hd hA hB hAB hfinA hfinB L,
    charFunDual_real_eq_charFun, charFunDual_real_eq_charFun,
    charFun_natCast_poissonRandomMeasure_apply hd hA hfinA,
    charFun_natCast_poissonRandomMeasure_apply hd hB hfinB]

/-- **Pairwise independence of the counts in disjoint sets.** For two disjoint finite-mass measurable
sets `A` and `B`, the counts `poissonRandomMeasure K X · A` and `poissonRandomMeasure K X · B` are
independent. The `ℝ`-valued counts are independent (`indepFun_natCast_poissonRandomMeasure_apply`), and
this is transported to the `ℝ≥0∞`-valued counts through `ENNReal.ofReal` using the almost-sure
finiteness. This is the two-set API; mutual independence over a finite pairwise-disjoint family is
`iIndepFun_poissonRandomMeasure_apply`. -/
theorem indepFun_poissonRandomMeasure_apply [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤) (hAB : Disjoint A B) :
    IndepFun (fun ω => poissonRandomMeasure K X ω A) (fun ω => poissonRandomMeasure K X ω B) μ := by
  have hcomp := (indepFun_natCast_poissonRandomMeasure_apply hd hA hB hfinA hfinB hAB).comp
    (φ := ENNReal.ofReal) (ψ := ENNReal.ofReal)
    ENNReal.continuous_ofReal.measurable ENNReal.continuous_ofReal.measurable
  refine hcomp.congr ?_ ?_
  · filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hA hfinA] with ω hω
    rw [Function.comp_apply, ENNReal.ofReal_toReal hω.ne]
  · filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hB hfinB] with ω hω
    rw [Function.comp_apply, ENNReal.ofReal_toReal hω.ne]

/-! ### Mutual independence of the counts in a finite disjoint family

The pairwise statement above upgrades verbatim to a finite family `A : ι → Set E` of pairwise disjoint
finite-mass sets: the counts `poissonRandomMeasure K X · (A i)` are **mutually** independent. The proof
is the `ι`-indexed mirror of the pairwise chain — the pair `(A, B)` is replaced by the family `A`, the
codomain `ℝ × ℝ` by `ι → ℝ`, and the two-set factorizations by the joint pgf identity
`charFunDual_pi_thinnedCount` (PoissonPointFamily). The joint characteristic function of the partial-count vector
factorizes across coordinates (by induction on the number of pieces), passes to the limit by dominated
convergence, and identifies the joint characteristic function of the count vector as a product; the
mathlib vehicle `iIndepFun_iff_charFunDual_pi` then delivers mutual independence. -/

/-- **Prefix-versus-next-piece independence of the superposition-count vector.** The family of partial
counts from the first `n + 1` pieces is independent of the family of thinned counts of piece `n + 1`,
built from the public split engine with the same injections as the pairwise version, extracting the
`A i`-count for every `i` from each block. -/
private lemma indepFun_prmPartialCountVec_thinnedCountVec {ι : Type} [Fintype ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    IndepFun (fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ))
      (fun ω (i : ι) => (thinnedCount K X (A i) (n + 1) ω : ℝ)) μ := by
  classical
  set φ : Fin (n + 1) ⊕ Fin (n + 1) × ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun k => Sum.inl (k : ℕ)) (fun p => Sum.inr ((p.1 : ℕ), p.2)) with hφ_def
  set ψ : Unit ⊕ ℕ → ℕ ⊕ ℕ × ℕ :=
    Sum.elim (fun _ => Sum.inl (n + 1)) (fun n' => Sum.inr (n + 1, n')) with hψ_def
  have hφ_inj : Function.Injective φ := by
    rintro (a | ⟨a, a'⟩) (b | ⟨b, b'⟩) hab <;> simp_all [Fin.val_inj]
  have hψ_inj : Function.Injective ψ := by
    rintro (⟨⟩ | a) (⟨⟩ | b) hab <;> simp_all
  have hST : ∀ s t, φ s ≠ ψ t := by
    rintro (a | ⟨a, a'⟩) (⟨⟩ | t) <;> simp only [hφ_def, hψ_def, Sum.elim_inl, Sum.elim_inr,
      ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, not_false_eq_true, Prod.mk.injEq]
    · exact fun h => (Nat.ne_of_lt a.isLt) h
    · exact fun h => (Nat.ne_of_lt a.isLt) h.1
  have hsplit := hd.indepFun_pointFamily_split φ ψ hφ_inj hψ_inj hST
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ, pointFamilyIndexType E (φ i)) → (ι → ℕ) :=
    fun g (i : ι) => ∑ k : Fin (n + 1),
      ((Finset.range (g (Sum.inl k))).filter fun n' => g (Sum.inr (k, n')) ∈ A i).card with hG_def
  set H : (∀ j : Unit ⊕ ℕ, pointFamilyIndexType E (ψ j)) → (ι → ℕ) :=
    fun g (i : ι) =>
      ((Finset.range (g (Sum.inl ()))).filter fun n' => g (Sum.inr n') ∈ A i).card with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun k _ =>
      measurable_filterCard (D := (i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ) → pointFamilyIndexType E (φ i))
        (hA i) (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hH : Measurable H := by
    rw [hH_def]
    exact measurable_pi_lambda _ fun i =>
      measurable_filterCard (D := (j : Unit ⊕ ℕ) → pointFamilyIndexType E (ψ j))
        (hA i) (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hGeq : (fun ω => G fun i => pointFamilyCombined K X (φ i) ω)
      = fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℕ) := by
    funext ω i
    simp only [hG_def]
    unfold prmPartialCount
    rw [← Fin.sum_univ_eq_sum_range (fun j => thinnedCount K X (A i) j ω) (n + 1)]
    rfl
  have hHeq : (fun ω => H fun j => pointFamilyCombined K X (ψ j) ω)
      = fun ω (i : ι) => (thinnedCount K X (A i) (n + 1) ω : ℕ) := by
    funext ω i; rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rw [hGeq, hHeq] at key
  have hcast := key.comp (φ := fun v (i : ι) => ((v i : ℕ) : ℝ))
    (ψ := fun v (i : ι) => ((v i : ℕ) : ℝ))
    (measurable_pi_lambda _ fun i => measurable_from_top.comp (measurable_pi_apply i))
    (measurable_pi_lambda _ fun i => measurable_from_top.comp (measurable_pi_apply i))
  simpa only [Function.comp_def] using hcast

/-- **Joint characteristic function of the partial superposition-count vector.** It factorizes across
the family into the Poisson pgfs with the accumulated `A i`-rates, by induction on the number of
pieces: the base case is the within-piece factorization `charFunDual_pi_thinnedCount`, and each
step adds an independent block. -/
private lemma charFunDual_prmPartialCountVec {ι : Type} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A)) (n : ℕ)
    (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ)) L
      = ∏ i, Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A i)).toReal)
          * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by
  induction n with
  | zero =>
    have h0 : (fun ω (i : ι) => (prmPartialCount K X (A i) 0 ω : ℝ))
        = fun ω (i : ι) => (thinnedCount K X (A i) 0 ω : ℝ) := by
      funext ω i; rw [prmPartialCount, Finset.sum_range_one]
    rw [h0, charFunDual_pi_thinnedCount hd hA hdisj L]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  | succ n ih =>
    have mPn : Measurable fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ) :=
      measurable_pi_lambda _ fun i => measurable_from_top.comp
        (measurable_prmPartialCount hd.measurable_count hd.measurable_point (hA i) n)
    have mQn : Measurable fun ω (i : ι) => (thinnedCount K X (A i) (n + 1) ω : ℝ) :=
      measurable_pi_lambda _ fun i => measurable_from_top.comp
        (measurable_thinnedCount (hd.measurable_count _) (hd.measurable_point _) (hA i))
    have hsucc : (fun ω (i : ι) => (prmPartialCount K X (A i) (n + 1) ω : ℝ))
        = fun ω => (fun i => (prmPartialCount K X (A i) n ω : ℝ))
            + fun i => (thinnedCount K X (A i) (n + 1) ω : ℝ) := by
      funext ω i
      simp only [Pi.add_apply]
      rw [prmPartialCount, Finset.sum_range_succ, Nat.cast_add]; rfl
    rw [hsucc, IndepFun.charFunDual_map_fun_add_eq_mul mPn.aemeasurable mQn.aemeasurable
        (indepFun_prmPartialCountVec_thinnedCountVec hd hA n), Pi.mul_apply, ih,
      charFunDual_pi_thinnedCount hd hA hdisj L, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ (fun k => (m (prmPiece m k ∩ A i)).toReal) (n + 1), ← Complex.exp_add]
    congr 1
    push_cast
    ring

/-- **Joint characteristic function of the count vector.** By dominated convergence from the partial
counts: the count vectors converge almost surely on the (finite) intersection of the coordinatewise
finiteness events, the integrands are bounded by `1`, and the accumulated rates increase to `m (A i)`
per coordinate. -/
private lemma charFunDual_poissonRandomMeasureVec {ι : Type} [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal) L
      = ∏ i, Complex.exp (↑(m (A i)).toReal * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)) := by
  have mPn : ∀ n, Measurable fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ) := fun n =>
    measurable_pi_lambda _ fun i => measurable_from_top.comp
      (measurable_prmPartialCount hd.measurable_count hd.measurable_point (hA i) n)
  have mN : Measurable fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal :=
    measurable_pi_lambda _ fun i =>
      (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
        (hA i)).ennreal_toReal
  have hFmeas : ∀ n, Measurable fun ω =>
      Complex.exp (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I) := fun n =>
    Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp (L.continuous.measurable.comp (mPn n))).mul_const I)
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Complex.exp
      (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I)‖ ≤ (fun _ : Ω => (1 : ℝ)) ω := by
    intro n; filter_upwards with ω
    exact le_of_eq (Complex.norm_exp_ofReal_mul_I _)
  have hae : ∀ᵐ ω ∂μ, ∀ i, poissonRandomMeasure K X ω (A i) < ⊤ := by
    rw [ae_all_iff]
    exact fun i => ae_poissonRandomMeasure_apply_lt_top hd (hA i) (hfin i)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => Complex.exp
      (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I)) atTop
      (𝓝 (Complex.exp (↑(L fun i => (poissonRandomMeasure K X ω (A i)).toReal) * I))) := by
    filter_upwards [hae] with ω hω
    have hc : Continuous fun p : ι → ℝ => Complex.exp (↑(L p) * I) := by fun_prop
    exact (hc.tendsto _).comp
      (tendsto_pi_nhds.mpr fun i => tendsto_natCast_prmPartialCount (hA i) ω (hω i))
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun _ => (1 : ℝ)) (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  have key : ∀ n, ∫ ω, Complex.exp
        (↑(L fun i => (prmPartialCount K X (A i) n ω : ℝ)) * I) ∂μ
      = charFunDual (μ.map fun ω (i : ι) => (prmPartialCount K X (A i) n ω : ℝ)) L := fun n => by
    rw [charFunDual_apply, integral_map (mPn n).aemeasurable (by fun_prop)]
  have keyN : ∫ ω, Complex.exp
        (↑(L fun i => (poissonRandomMeasure K X ω (A i)).toReal) * I) ∂μ
      = charFunDual (μ.map fun ω (i : ι) => (poissonRandomMeasure K X ω (A i)).toReal) L := by
    rw [charFunDual_apply, integral_map mN.aemeasurable (by fun_prop)]
  simp_rw [key, charFunDual_prmPartialCountVec hd hA hdisj] at hdct
  rw [keyN] at hdct
  have hrate : Tendsto (fun n => ∏ i,
      Complex.exp (↑(∑ k ∈ Finset.range (n + 1), (m (prmPiece m k ∩ A i)).toReal)
        * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1))) atTop
      (𝓝 (∏ i, Complex.exp (↑(m (A i)).toReal * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1)))) := by
    refine tendsto_finset_prod _ fun i _ => ?_
    exact ((Continuous.tendsto (by fun_prop : Continuous fun r : ℝ =>
        Complex.exp (↑r * (Complex.exp (↑(L (Pi.single i 1)) * I) - 1))) _)).comp
      (tendsto_rate_prmPartialCount (hA i) (hfin i))
  exact tendsto_nhds_unique hdct hrate

/-- The `ℝ`-valued counts in a finite pairwise disjoint family of finite-mass sets are mutually
independent: their joint characteristic function is the product of the marginals
(`charFunDual_poissonRandomMeasureVec` matched against `charFun_natCast_poissonRandomMeasure_apply`
through `charFunDual_real_eq_charFun`). -/
private lemma iIndepFun_natCast_poissonRandomMeasure_apply {ι : Type} [Fintype ι]
    [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E}
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun i ω => (poissonRandomMeasure K X ω (A i)).toReal) μ := by
  classical
  rw [iIndepFun_iff_charFunDual_pi
    (X := fun i ω => (poissonRandomMeasure K X ω (A i)).toReal)
    fun i => (measurable_poissonRandomMeasure_apply hd.measurable_count hd.measurable_point
      (hA i)).ennreal_toReal.aemeasurable]
  intro L
  rw [charFunDual_poissonRandomMeasureVec hd hA hfin hdisj L]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [charFunDual_real_eq_charFun, charFun_natCast_poissonRandomMeasure_apply hd (hA i) (hfin i)]
  rfl

/-- **Mutual independence of the counts in a finite disjoint family.** For a pairwise disjoint finite
family `A i` of finite-mass measurable sets, the counts `poissonRandomMeasure K X · (A i)` are mutually
independent. The `ℝ`-valued counts are mutually independent
(`iIndepFun_natCast_poissonRandomMeasure_apply`), and this is transported to the `ℝ≥0∞`-valued counts
through `ENNReal.ofReal` using the almost-sure finiteness. -/
theorem iIndepFun_poissonRandomMeasure_apply {ι : Type} [Fintype ι] [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {A : ι → Set E} (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, m (A i) < ⊤) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    iIndepFun (fun i ω => poissonRandomMeasure K X ω (A i)) μ := by
  have hcomp := (iIndepFun_natCast_poissonRandomMeasure_apply hd hA hfin hdisj).comp
    (fun _ => ENNReal.ofReal) (fun _ => ENNReal.continuous_ofReal.measurable)
  refine (iIndepFun_congr fun i => ?_).mp hcomp
  filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd (hA i) (hfin i)] with ω hω
  rw [Function.comp_apply, ENNReal.ofReal_toReal hω.ne]

end ProbabilityTheory
