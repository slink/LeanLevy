/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.RandomMeasure.LevyJumpLaw
import LeanLevy.Processes.Cadlag

/-!
# Pathwise banded jump sums

For a mark set `A ⊆ ℝ`, the **banded jump sum** `bandJumpSum K X A t ω` accumulates the marks of the
realized points that fall in the space-time window `(0, t] × A`, written as a series of piece sums.
It generalizes the large-jump sum `levyLargeJumpSum` (the mark set `{x | 1 ≤ |x|}`) to an arbitrary
band.

When the band has finite `ν`-mass, only finitely many pieces are active in any bounded time window
`(0, T]`, so almost surely each sample path `t ↦ bandJumpSum K X A t ω` agrees on `(-∞, T)` with a
finite sum of right-continuous jump steps. Such finite step sums are càdlàg, hence so is the sample
path. This gives the sample-path regularity of the large-jump component of a Lévy process.

## Main definitions

* `ProbabilityTheory.bandJumpSum` — the sum of the marks of the realized points in the window
  `(0, t] × A`, as a series of piece sums.

## Main results

* `ProbabilityTheory.bandJumpSum_zero` — the banded jump sum vanishes at time zero.
* `ProbabilityTheory.levyLargeJumpSum_eq_bandJumpSum` — the large-jump sum is the banded jump sum on
  the mark set `{x | 1 ≤ |x|}`.
* `ProbabilityTheory.measurable_bandJumpSum` — the banded jump sum is a measurable function of the
  sample point.
* `ProbabilityTheory.ae_isCadlag_bandJumpSum` — for a band of finite `ν`-mass, almost every sample
  path `t ↦ bandJumpSum K X A t ω` is càdlàg (a.e. in `ω`, for every `t`).
* `ProbabilityTheory.ae_isCadlag_levyLargeJumpSum` — almost every sample path of the large-jump sum
  `t ↦ levyLargeJumpSum K X t ω` is càdlàg.
-/

open MeasureTheory Filter Topology

namespace ProbabilityTheory

variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω} {A : Set ℝ}

/-- The **banded jump sum**: the sum of the marks of the realized points in the space-time window
`(0, t] × A`, as a series of piece sums. Almost surely, when `A` has finite `ν`-mass, this is a
finite sum. -/
noncomputable def bandJumpSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ) (A : Set ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑' k, pieceSum K X ((Set.Ioc 0 t ×ˢ A).indicator fun p => p.2) k ω

omit [MeasurableSpace Ω] in
/-- The banded jump sum vanishes at time zero: the window `(0, 0] × A` is empty. -/
@[simp] theorem bandJumpSum_zero : bandJumpSum K X A 0 = 0 := by
  funext ω
  have hband : ((Set.Ioc (0 : ℝ) 0 ×ˢ A).indicator fun p : ℝ × ℝ => p.2) = fun _ => 0 := by
    rw [Set.Ioc_self, Set.empty_prod, Set.indicator_empty]
  simp only [bandJumpSum, hband, pieceSum, Finset.sum_const_zero, tsum_zero, Pi.zero_apply]

omit [MeasurableSpace Ω] in
/-- The large-jump sum is the banded jump sum on the mark set `{x | 1 ≤ |x|}`. -/
theorem levyLargeJumpSum_eq_bandJumpSum (t : ℝ) :
    levyLargeJumpSum K X t = bandJumpSum K X {x : ℝ | 1 ≤ |x|} t :=
  rfl

/-- The banded jump sum is a measurable function of the sample point. -/
theorem measurable_bandJumpSum (hK : ∀ k, Measurable (K k)) (hX : ∀ k n, Measurable (X k n))
    (hA : MeasurableSet A) (t : ℝ) : Measurable (bandJumpSum K X A t) :=
  Measurable.tsum fun k =>
    measurable_pieceSum (hK k) (fun n => hX k n) (measurable_bandFun hA 0 t)

/-! ### Sample-path regularity

On a bounded time window `(0, T]` only finitely many pieces carry a realized mark in `A` (when `A`
has finite `ν`-mass), so the banded jump sum agrees on `(-∞, T)` with a finite sum of right-continuous
jump steps. The step sum is càdlàg by `IsCadlag.finsetSum` and `isCadlag_stepIndicator`, and càdlàg
regularity passes to the banded jump sum by locality of the càdlàg property. -/

/-- The finite step-sum path over an active-piece set `S`: for each realized point `(k, n)` with
`k ∈ S`, a right-continuous jump of size `p.2` triggered at the point's time coordinate `p.1`, active
only for points with positive time and mark in `A`. This is the finite càdlàg comparison path for
`bandJumpSum` on a bounded time window. -/
private noncomputable def bandStepFinsetSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ)
    (A : Set ℝ) (ω : Ω) (S : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ S, ∑ n ∈ Finset.range (K k ω),
    (if (X k n ω).1 ≤ t then
      ({p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A}).indicator (fun p : ℝ × ℝ => p.2) (X k n ω) else 0)

omit [MeasurableSpace Ω] in
/-- The finite step-sum path is càdlàg: it is a finite sum of right-continuous jump steps. -/
private lemma isCadlag_bandStepFinsetSum (A : Set ℝ) (ω : Ω) (S : Finset ℕ) :
    IsCadlag (fun t : ℝ => bandStepFinsetSum K X A ω S t) := by
  simp only [bandStepFinsetSum]
  exact IsCadlag.finsetSum _ fun k _ => IsCadlag.finsetSum _ fun n _ => isCadlag_stepIndicator

omit [MeasurableSpace Ω] in
/-- **Path agreement on a window**: whenever only finitely many pieces carry a realized mark in the
window `(0, T] × A`, the banded jump sum agrees on `(-∞, T)` with the finite step-sum path over those
active pieces. -/
private lemma bandJumpSum_eqOn_Iio (A : Set ℝ) (ω : Ω) {T : ℕ}
    (hfin : {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite) :
    Set.EqOn (fun t : ℝ => bandJumpSum K X A t ω)
      (fun t : ℝ => bandStepFinsetSum K X A ω hfin.toFinset t) (Set.Iio (T : ℝ)) := by
  intro t ht
  simp only [Set.mem_Iio] at ht
  have htT : t ≤ (T : ℝ) := le_of_lt ht
  have hvanish : ∀ k ∉ hfin.toFinset,
      pieceSum K X ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) k ω = 0 := by
    intro k hk
    simp only [pieceSum]
    refine Finset.sum_eq_zero fun n hn => ?_
    refine Set.indicator_of_notMem ?_ _
    intro hmem
    exact hk (hfin.mem_toFinset.mpr ⟨n, hn, Set.mem_prod.mpr
      ⟨Set.Ioc_subset_Ioc le_rfl htT (Set.mem_prod.mp hmem).1, (Set.mem_prod.mp hmem).2⟩⟩)
  simp only [bandJumpSum, bandStepFinsetSum]
  rw [tsum_eq_sum hvanish]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [pieceSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hut : (X k n ω).1 ≤ t
  · rw [if_pos hut]
    rcases em (X k n ω ∈ Set.Ioc 0 t ×ˢ A) with hm | hm
    · rw [Set.indicator_of_mem hm,
        Set.indicator_of_mem (show X k n ω ∈ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A} from
          ⟨(Set.mem_Ioc.mp (Set.mem_prod.mp hm).1).1, (Set.mem_prod.mp hm).2⟩)]
    · rw [Set.indicator_of_notMem hm,
        Set.indicator_of_notMem (show X k n ω ∉ {p : ℝ × ℝ | 0 < p.1 ∧ p.2 ∈ A} from
          fun hc => hm (Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨hc.1, hut⟩, hc.2⟩))]
  · rw [if_neg hut,
      Set.indicator_of_notMem (fun hmem => hut (Set.mem_Ioc.mp (Set.mem_prod.mp hmem).1).2)]

/-- For a band `A` of finite `ν`-mass, almost every sample path of the banded jump sum is càdlàg: the
statement is `∀ᵐ ω`, and for every fixed `ω` in the almost-sure event the path `t ↦ bandJumpSum K X A
t ω` is càdlàg at every `t`. Almost surely only finitely many pieces are active in each bounded time
window `(0, T]`, and there the path agrees with a finite sum of jump steps. -/
theorem ae_isCadlag_bandJumpSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAfin : ν A < ⊤) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t : ℝ => bandJumpSum K X A t ω) := by
  have hwin : ∀ T : ℕ, ∀ᵐ ω ∂μ,
      {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite := fun T =>
    ae_finite_pieces_mem hd (measurableSet_Ioc.prod hA)
      (volume_prod_Ioc_prod_lt_top (m := ν) (s := 0) (t := (T : ℝ)) hAfin)
  filter_upwards [ae_all_iff.mpr hwin] with ω hω
  intro t
  obtain ⟨T, hT⟩ := exists_nat_gt t
  refine (isCadlag_bandStepFinsetSum (K := K) (X := X) A ω (hω T).toFinset t).congr ?_
  filter_upwards [Iio_mem_nhds hT] with s hs
  exact (bandJumpSum_eqOn_Iio A ω (hω T) hs).symm

/-- Almost every sample path of the large-jump sum `t ↦ levyLargeJumpSum K X t ω` is càdlàg: the
special case of `ae_isCadlag_bandJumpSum` for the mark set `{x | 1 ≤ |x|}`, which has finite `ν`-mass
for any Lévy measure `ν`. -/
theorem ae_isCadlag_levyLargeJumpSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t : ℝ => levyLargeJumpSum K X t ω) := by
  have h := ae_isCadlag_bandJumpSum hd
    (measurableSet_le measurable_const continuous_abs.measurable)
    (hν.measure_setOf_abs_ge_lt_top one_pos)
  filter_upwards [h] with ω hω
  simpa only [levyLargeJumpSum_eq_bandJumpSum] using hω

end ProbabilityTheory
