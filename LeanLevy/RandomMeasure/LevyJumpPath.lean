/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.RandomMeasure.LevyJumpLaw
import LeanLevy.Processes.Cadlag
import Mathlib.Probability.Martingale.OptionalStopping

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

For a band `A ⊆ (-1, 1)` of finite `ν`-mass, the compensated **banded jump path**
`levyBandPath K X ν A t ω = bandJumpSum K X A t ω - t · ∫_A x dν` subtracts the linear compensator
drift. Almost surely it agrees with the compensated Poisson integral of the band test function
`1_{(0,t] × A}(u, x) · x`, so it lies in `L²(μ)`, is càdlàg, and — through a
`prmFiltration`-adapted representative `levyBandVersion` — is a martingale for the natural filtration.

## Main definitions

* `ProbabilityTheory.bandJumpSum` — the sum of the marks of the realized points in the window
  `(0, t] × A`, as a series of piece sums.
* `ProbabilityTheory.levyBandPath` — the compensated banded jump path
  `bandJumpSum K X A t ω - t · ∫_A x dν`.
* `ProbabilityTheory.levyBandVersion` — a `prmFiltration`-adapted representative of the compensated
  band integral.

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
* `ProbabilityTheory.levyBandPath_ae_eq_compensated` — the compensated band path agrees almost
  everywhere with the compensated Poisson integral of the band test function.
* `ProbabilityTheory.martingale_levyBandVersion` — the adapted representative of the compensated band
  integral is a martingale for the natural filtration `prmFiltration`.
* `ProbabilityTheory.measure_countable_sup_levyBandPath_ge` — the weak-type maximal inequality for the
  compensated band path over a countable time grid: the measure of the event that the path exceeds `ε`
  in absolute value at some grid time is at most `√(T · ∫_A x² dν) / ε`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

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

/-! ### The compensated banded jump path

Subtracting the linear compensator drift `t · ∫_A x dν` from the banded jump sum yields the
**compensated banded jump path** `levyBandPath`. For a band `A ⊆ (-1, 1)` of finite `ν`-mass it agrees
almost everywhere with the compensated Poisson integral of the band test function
`1_{(0,t] × A}(u, x) · x`, hence is square-integrable, càdlàg, and martingale-structured. -/

/-- The **compensated banded jump path**: the banded jump sum with its linear compensator drift
`t · ∫_A x dν` subtracted, so that (for a band of finite `ν`-mass) it has mean zero at each time. -/
noncomputable def levyBandPath (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ) (ν : Measure ℝ)
    (A : Set ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  bandJumpSum K X A t ω - t * ∫ x in A, x ∂ν

omit [MeasurableSpace Ω] [SigmaFinite ν] in
/-- The compensated banded jump path vanishes at time zero: the jump sum vanishes and the drift is
scaled by `0`. -/
@[simp] theorem levyBandPath_zero : levyBandPath K X ν A 0 = 0 := by
  funext ω
  simp [levyBandPath, bandJumpSum_zero]

omit [SigmaFinite ν] in
/-- The compensated banded jump path is a measurable function of the sample point. -/
theorem measurable_levyBandPath (hK : ∀ k, Measurable (K k)) (hX : ∀ k n, Measurable (X k n))
    (hA : MeasurableSet A) (t : ℝ) : Measurable (levyBandPath K X ν A t) :=
  (measurable_bandJumpSum hK hX hA t).sub measurable_const

/-- For a band `A` of finite `ν`-mass, almost every sample path of the compensated banded jump path is
càdlàg: the banded jump sum is càdlàg (a.e.) and the compensator drift `t ↦ -(t · ∫_A x dν)` is
continuous. -/
theorem ae_isCadlag_levyBandPath [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAfin : ν A < ⊤) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t : ℝ => levyBandPath K X ν A t ω) := by
  filter_upwards [ae_isCadlag_bandJumpSum hd hA hAfin] with ω hω
  have hcont : Continuous (fun t : ℝ => -(t * ∫ x in A, x ∂ν)) := by fun_prop
  simpa only [levyBandPath, sub_eq_add_neg] using hω.add hcont.isCadlag

/-- **The `L²` anchor.** For a band `A ⊆ (-1, 1)` of finite `ν`-mass, the compensated banded jump path
agrees almost everywhere with the compensated Poisson integral of the band test function
`1_{(0,t] × A}(u, x) · x`. The banded jump sum matches the uncompensated Poisson sum piecewise, and the
compensator drift `t · ∫_A x dν` equals the summed piece integrals of the band test function. -/
theorem levyBandPath_ae_eq_compensated [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    (fun ω => levyBandPath K X ν A t ω)
      =ᵐ[μ] compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 t).toLp _) := by
  have hfmeas : Measurable ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) :=
    measurable_bandFun hA 0 t
  have hf1 : Integrable ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) (volume.prod ν) :=
    integrable_bandFun hA hAsub hAfin 0 t
  have hbandmeas : MeasurableSet (Set.Ioc 0 t ×ˢ A) := measurableSet_Ioc.prod hA
  -- the compensator drift equals the integral of the band test function
  have hint : (∫ p, ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) p ∂(volume.prod ν))
      = t * ∫ x in A, x ∂ν := by
    rw [integral_indicator hbandmeas,
      setIntegral_prod (fun z : ℝ × ℝ => z.2) ((integrable_indicator_iff hbandmeas).mp hf1)]
    dsimp only
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal ht, smul_eq_mul]
  -- the piece integrals sum to the integral over the whole band
  have hHasSum : HasSum (fun k => ∫ p in prmPiece (volume.prod ν) k,
        ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) p ∂(volume.prod ν))
      (∫ p, ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) p ∂(volume.prod ν)) := by
    have h := hasSum_integral_iUnion (μ := volume.prod ν)
      (f := (Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
      (fun k => measurableSet_prmPiece (m := volume.prod ν))
      (pairwise_disjoint_prmPiece (m := volume.prod ν))
      (by rw [iUnion_prmPiece]; exact hf1.integrableOn)
    rwa [iUnion_prmPiece, setIntegral_univ] at h
  refine EventuallyEq.trans ?_
    (compensatedPoissonIntegral_eq_sum hd hfmeas hf1 (memLp_two_bandFun hA hAsub hAfin 0 t)).symm
  filter_upwards [ae_finite_support_pieceSum hd hbandmeas
    (volume_prod_Ioc_prod_lt_top (m := ν) (s := 0) (t := t) hAfin)
    (fun p hp => Set.indicator_of_notMem hp _)] with ω hfinsupp
  have hsummable_piece : Summable (fun k =>
      pieceSum K X ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) k ω) :=
    summable_of_ne_finset_zero (s := hfinsupp.toFinset) fun k hk => by
      by_contra hne
      exact hk (hfinsupp.mem_toFinset.mpr hne)
  simp only [levyBandPath, bandJumpSum, compensatedPoissonSum, compensatedPieceSum]
  rw [hsummable_piece.tsum_sub hHasSum.summable, hHasSum.tsum_eq, hint]

/-! ### The compensated band martingale

For a band `A ⊆ (-1, 1)` of finite `ν`-mass the compensated band integral (an element of `L²(μ)`) is
a martingale for the natural filtration `prmFiltration`. The increment over a time step `(s, t]` is
the compensated Poisson integral of the band test function `1_{(s,t] × A}(r, x) · x`, supported in the
disjoint band region `(s, t] × ℝ`; hence it is independent of the prefix `(-∞, s] × ℝ` and has mean
zero, so its conditional expectation given the past vanishes. -/

/-- The band test function `1_{(s,t] × A}(r, x) · x`, viewed in `L²`, vanishes almost everywhere
outside any product region `B ×ˢ univ` whose time factor contains `(s, t]`. -/
private lemma bandFun_toLp_ae_zero_off (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hAfin : ν A < ⊤) {s t : ℝ} {B : Set ℝ} (hB : Set.Ioc s t ⊆ B) :
    ∀ᵐ p ∂((volume : Measure ℝ).prod ν), p ∉ B ×ˢ (Set.univ : Set ℝ) →
      (memLp_two_bandFun hA hAsub hAfin s t).toLp
          ((Set.Ioc s t ×ˢ A).indicator fun q : ℝ × ℝ => q.2) p = 0 := by
  filter_upwards [MemLp.coeFn_toLp (memLp_two_bandFun hA hAsub hAfin s t)] with p hp hpB
  rw [hp]
  apply Set.indicator_of_notMem
  intro hmem
  exact hpB ⟨hB hmem.1, Set.mem_univ _⟩

/-- The compensated band integral over `(0, t]` is almost-everywhere strongly measurable with respect
to the evaluation sigma-algebra of the prefix region `(-∞, t] × ℝ`. -/
private lemma aestronglyMeasurable_levyBandPath_prefix [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) :
    AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Iic (t : ℝ) ×ˢ Set.univ)]
      (compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 (t : ℝ)).toLp _)) μ :=
  aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma hd
    (measurableSet_Iic.prod MeasurableSet.univ)
    (bandFun_toLp_ae_zero_off hA hAsub hAfin Set.Ioc_subset_Iic_self)

/-- The compensated band integral over `(s, t]` is almost-everywhere strongly measurable with respect
to the evaluation sigma-algebra of the band region `(s, t] × ℝ`. -/
theorem aestronglyMeasurable_levyBandPath_band [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (s t : ℝ) :
    AEStronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Ioc s t ×ˢ Set.univ)]
      (compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin s t).toLp _)) μ :=
  aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma hd
    (measurableSet_Ioc.prod MeasurableSet.univ)
    (bandFun_toLp_ae_zero_off hA hAsub hAfin (subset_refl _))

/-- The increment of the compensated band integral over a time step `(s, t]` is the compensated
integral of the band test function `1_{(s,t] × A}(r, x) · x`. -/
private lemma compensatedBand_sub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) {s t : ℝ}
    (h0 : 0 ≤ s) (hst : s ≤ t) :
    compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 t).toLp _)
        - compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 s).toLp _)
      = compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin s t).toLp _) := by
  have hdisj : Disjoint (Set.Ioc 0 s ×ˢ A) (Set.Ioc s t ×ˢ A) :=
    Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (le_refl s)) _ _
  have hfun : ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
      = (Set.Ioc 0 s ×ˢ A).indicator (fun p : ℝ × ℝ => p.2)
        + (Set.Ioc s t ×ˢ A).indicator (fun p : ℝ × ℝ => p.2) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc h0 hst, Set.union_prod, Set.indicator_union_of_disjoint hdisj]
    rfl
  have htoLp : (memLp_two_bandFun hA hAsub hAfin 0 t).toLp
        ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
      = (memLp_two_bandFun hA hAsub hAfin 0 s).toLp
          ((Set.Ioc 0 s ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
        + (memLp_two_bandFun hA hAsub hAfin s t).toLp
          ((Set.Ioc s t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq hfun)
  rw [htoLp, compensatedPoissonIntegral_add, add_sub_cancel_left]

/-- A `prmFiltration`-adapted representative of the compensated band integral over `(0, t]`. -/
noncomputable def levyBandVersion [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (_hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) : Ω → ℝ :=
  (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin t).mk _

/-- The adapted representative agrees almost everywhere with the compensated banded jump path. -/
theorem levyBandVersion_ae_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) :
    levyBandVersion hd hν hA hAsub hAfin t =ᵐ[μ] fun ω => levyBandPath K X ν A (t : ℝ) ω := by
  simp only [levyBandVersion]
  refine (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin t).ae_eq_mk.symm.trans ?_
  exact (levyBandPath_ae_eq_compensated hd hA hAsub hAfin (NNReal.coe_nonneg t)).symm

/-- The adapted representative is strongly measurable with respect to the prefix-region evaluation
sigma-algebra. -/
private lemma stronglyMeasurable_levyBandVersion [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) :
    StronglyMeasurable[prmEvalSigma K X (volume.prod ν) (Set.Iic (t : ℝ) ×ˢ Set.univ)]
      (levyBandVersion hd hν hA hAsub hAfin t) :=
  (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin t).stronglyMeasurable_mk

/-- The adapted representative is integrable at each time. -/
private lemma integrable_levyBandVersion [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (t : ℝ≥0) :
    Integrable (levyBandVersion hd hν hA hAsub hAfin t) μ := by
  simp only [levyBandVersion]
  exact ((Lp.memLp (compensatedPoissonIntegral hd
    ((memLp_two_bandFun hA hAsub hAfin 0 (t : ℝ)).toLp _))).integrable one_le_two).congr
    (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin t).ae_eq_mk

/-- **The compensated band integral is a martingale.** For a band `A ⊆ (-1, 1)` of finite `ν`-mass and
the natural filtration `prmFiltration`, the adapted representative of the compensated band integral is
a martingale: the increment over `(s, t]` is the compensated integral of the band test function, which
is independent of the past and has mean zero. -/
theorem martingale_levyBandVersion [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) :
    MeasureTheory.Martingale (levyBandVersion hd hν hA hAsub hAfin)
      (prmFiltration K X ν hd.measurable_count hd.measurable_point) μ := by
  refine ⟨fun u => ?_, fun s t hst => ?_⟩
  · exact stronglyMeasurable_levyBandVersion hd hν hA hAsub hAfin u
  simp only [prmFiltration_apply]
  have hband := aestronglyMeasurable_levyBandPath_band hd hA hAsub hAfin (s : ℝ) (t : ℝ)
  set cb : Ω → ℝ := hband.mk _ with hcbdef
  have hcb_sm : StronglyMeasurable[prmEvalSigma K X (volume.prod ν)
      (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ)] cb := hband.stronglyMeasurable_mk
  have hcb_ae : cb =ᵐ[μ]
      ⇑(compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin (s : ℝ) (t : ℝ)).toLp _)) :=
    hband.ae_eq_mk.symm
  -- the increment identity `Version t = Version s + cb` (a.e.)
  have hincr : levyBandVersion hd hν hA hAsub hAfin t
      =ᵐ[μ] levyBandVersion hd hν hA hAsub hAfin s + cb := by
    have hlpsub :
        ⇑(compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 (t : ℝ)).toLp _))
          - ⇑(compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 (s : ℝ)).toLp _))
        =ᵐ[μ] cb := by
      refine (Lp.coeFn_sub _ _).symm.trans ?_
      rw [compensatedBand_sub hd hA hAsub hAfin (NNReal.coe_nonneg s) (by exact_mod_cast hst)]
      exact hcb_ae.symm
    filter_upwards [(aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin t).ae_eq_mk,
      (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin s).ae_eq_mk, hlpsub]
      with ω hVt hVs hlp
    simp only [levyBandVersion, Pi.add_apply, Pi.sub_apply] at *
    rw [← hVt, ← hVs, ← hlp]
    ring
  -- region sub-sigma-algebras and their finiteness for the conditional expectation
  have hle_s := prmEvalSigma_le (m := volume.prod ν) hd.measurable_count hd.measurable_point
    (Set.Iic (s : ℝ) ×ˢ Set.univ)
  have hle_band := prmEvalSigma_le (m := volume.prod ν) hd.measurable_count hd.measurable_point
    (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ)
  haveI : IsFiniteMeasure (μ.trim hle_s) := isFiniteMeasure_trim hle_s
  -- the band increment is measurable in the disjoint band region, hence independent of the past
  have hindep : Indep (prmEvalSigma K X (volume.prod ν) (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ))
      (prmEvalSigma K X (volume.prod ν) (Set.Iic (s : ℝ) ×ˢ Set.univ)) μ :=
    indep_prmEvalSigma hd
      (Set.Disjoint.set_prod_left (Set.Iic_disjoint_Ioc (le_refl (s : ℝ))).symm Set.univ Set.univ)
  -- the band increment has mean zero
  have hmean : (∫ ω, cb ω ∂μ) = 0 := by
    rw [integral_congr_ae hcb_ae]
    exact integral_compensatedPoissonIntegral hd _
  -- the conditional expectation of the increment collapses to its (zero) mean
  have hcb0 : μ[cb | prmEvalSigma K X (volume.prod ν) (Set.Iic (s : ℝ) ×ˢ Set.univ)] =ᵐ[μ] 0 := by
    have hkey := condExp_indep_eq hle_band hle_s hcb_sm hindep
    simp only [hmean] at hkey
    exact hkey
  -- assemble: `Version t = Version s + increment`, and both pieces resolve
  refine (condExp_congr_ae hincr).trans ?_
  refine (condExp_add (integrable_levyBandVersion hd hν hA hAsub hAfin s)
    (((Lp.memLp _).integrable one_le_two).congr hcb_ae.symm) _).trans ?_
  rw [condExp_of_stronglyMeasurable hle_s
    (stronglyMeasurable_levyBandVersion hd hν hA hAsub hAfin s)
    (integrable_levyBandVersion hd hν hA hAsub hAfin s)]
  calc levyBandVersion hd hν hA hAsub hAfin s
        + μ[cb | prmEvalSigma K X (volume.prod ν) (Set.Iic (s : ℝ) ×ˢ Set.univ)]
      =ᵐ[μ] levyBandVersion hd hν hA hAsub hAfin s + (0 : Ω → ℝ) :=
        EventuallyEq.add EventuallyEq.rfl hcb0
    _ = levyBandVersion hd hν hA hAsub hAfin s := add_zero _

/-! ### Maximal inequality over a countable grid

For a band `A ⊆ (-1, 1)` of finite `ν`-mass the compensated band path satisfies a weak-type maximal
inequality (a Doob-style bound via the elementary maximal inequality `maximal_ineq`): the measure of
the event that the path exceeds a level `ε` in absolute value at some time in a countable subset of
`[0, T]` is bounded by `√(T · ∫_A x² dν) / ε`. The proof restricts the `ℝ≥0`-indexed band martingale
to a monotone `ℕ`-grid, applies the finite maximal inequality to each finite sub-grid, and passes to
the countable limit through continuity of measure from below. -/

omit [SigmaFinite ν] in
/-- The set-lintegral of `x²` over a band `A ⊆ (-1, 1)` against a Lévy measure is finite. -/
private lemma lintegral_setOf_sq_lt_top (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hν : IsLevyMeasure ν) : ∫⁻ x in A, ENNReal.ofReal (x ^ 2) ∂ν < ⊤ := by
  refine lt_of_le_of_lt ?_ hν.2
  rw [← lintegral_indicator hA]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    obtain ⟨h1, h2⟩ := hAsub hx
    exact ENNReal.ofReal_le_ofReal (le_min (by nlinarith) le_rfl)
  · rw [Set.indicator_of_notMem hx]; exact zero_le

omit [SigmaFinite ν] in
/-- The function `x ↦ x²` is `ν`-integrable on a band `A ⊆ (-1, 1)`. -/
private lemma integrableOn_sq (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hν : IsLevyMeasure ν) : IntegrableOn (fun x : ℝ => x ^ 2) A ν := by
  refine ⟨(by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg x)]
  exact lintegral_setOf_sq_lt_top hA hAsub hν

omit [SigmaFinite ν] in
/-- The `ENNReal.ofReal` of the Bochner integral of `x²` over a band equals its lower integral. -/
private lemma ofReal_integral_sq (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1)
    (hν : IsLevyMeasure ν) :
    ENNReal.ofReal (∫ x in A, x ^ 2 ∂ν) = ∫⁻ x in A, ENNReal.ofReal (x ^ 2) ∂ν :=
  ofReal_integral_eq_lintegral_ofReal (integrableOn_sq hA hAsub hν)
    (ae_of_all _ fun x => sq_nonneg x)

/-- The `ℕ`-grid filtration obtained by restricting `prmFiltration` along a monotone reindexing. -/
private noncomputable def gridFiltration
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω› where
  seq k := prmFiltration K X ν hd.measurable_count hd.measurable_point (u k)
  mono' _ _ hij := (prmFiltration K X ν hd.measurable_count hd.measurable_point).mono (hu hij)
  le' k := (prmFiltration K X ν hd.measurable_count hd.measurable_point).le (u k)

/-- The absolute value of the compensated band martingale, sampled along a monotone `ℕ`-grid, is a
nonnegative submartingale for the grid filtration (`|M| = M ⊔ (-M)` of a martingale). -/
private lemma submartingale_abs_levyBandVersion_grid [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {u : ℕ → ℝ≥0} (hu : Monotone u) :
    MeasureTheory.Submartingale
      (fun k ω => |levyBandVersion hd hν hA hAsub hAfin (u k) ω|)
      (gridFiltration hd u hu) μ := by
  have hM := martingale_levyBandVersion hd hν hA hAsub hAfin
  have hMN : MeasureTheory.Martingale
      (fun k => levyBandVersion hd hν hA hAsub hAfin (u k)) (gridFiltration hd u hu) μ :=
    ⟨fun k => hM.1 (u k), fun i j hij => hM.2 (u i) (u j) (hu hij)⟩
  have habs : ∀ a : ℝ, a ⊔ -a = |a| := fun a => by
    rcases le_total 0 a with h | h
    · rw [sup_eq_left.mpr (by linarith), abs_of_nonneg h]
    · rw [sup_eq_right.mpr (by linarith), abs_of_nonpos h]
  have heq : ((fun k => levyBandVersion hd hν hA hAsub hAfin (u k))
        ⊔ -(fun k => levyBandVersion hd hν hA hAsub hAfin (u k)))
      = fun k ω => |levyBandVersion hd hν hA hAsub hAfin (u k) ω| := by
    funext k ω
    show levyBandVersion hd hν hA hAsub hAfin (u k) ω
        ⊔ -(levyBandVersion hd hν hA hAsub hAfin (u k) ω) = _
    exact habs _
  have hsup := hMN.submartingale.sup hMN.neg.submartingale
  rw [heq] at hsup
  exact hsup

/-- The second moment of the compensated band path at time `v` is `v · ∫_A x² dν`. -/
private lemma eLpNorm_two_sq_levyBandVersion [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (v : ℝ≥0) :
    (eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ) ^ 2
      = ENNReal.ofReal ((v : ℝ) * ∫ x in A, x ^ 2 ∂ν) := by
  have hae : levyBandVersion hd hν hA hAsub hAfin v
      =ᵐ[μ] compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 (v : ℝ)).toLp _) :=
    (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin v).ae_eq_mk.symm
  rw [eLpNorm_congr_ae hae, eLpNorm_compensatedPoissonIntegral,
    eLpNorm_congr_ae (MemLp.coeFn_toLp _), eLpNorm_sq_bandFun hA 0 (v : ℝ), sub_zero,
    ← ofReal_integral_sq hA hAsub hν, ← ENNReal.ofReal_mul (NNReal.coe_nonneg v)]

/-- On a probability space, the mean absolute value of the compensated band path at time `v` is
bounded by `√(v · ∫_A x² dν)` (the `L¹ ≤ L²` bound composed with the second-moment isometry). -/
private lemma integral_abs_levyBandVersion_le [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) (v : ℝ≥0) :
    ∫ ω, |levyBandVersion hd hν hA hAsub hAfin v ω| ∂μ
      ≤ Real.sqrt ((v : ℝ) * ∫ x in A, x ^ 2 ∂ν) := by
  have haesm : AEStronglyMeasurable (levyBandVersion hd hν hA hAsub hAfin v) μ :=
    (integrable_levyBandVersion hd hν hA hAsub hAfin v).aestronglyMeasurable
  have hae : levyBandVersion hd hν hA hAsub hAfin v
      =ᵐ[μ] compensatedPoissonIntegral hd ((memLp_two_bandFun hA hAsub hAfin 0 (v : ℝ)).toLp _) :=
    (aestronglyMeasurable_levyBandPath_prefix hd hA hAsub hAfin v).ae_eq_mk.symm
  have h2ne : eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ ≠ ⊤ := by
    rw [eLpNorm_congr_ae hae]; exact Lp.eLpNorm_ne_top _
  have h1 : ∫ ω, |levyBandVersion hd hν hA hAsub hAfin v ω| ∂μ
      = (eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 1 μ).toReal := by
    simp_rw [← Real.norm_eq_abs]
    rw [integral_norm_eq_lintegral_enorm haesm, ← eLpNorm_one_eq_lintegral_enorm]
  have hmono : eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 1 μ
      ≤ eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) haesm
  have hsqrt : (eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ).toReal
      = Real.sqrt ((v : ℝ) * ∫ x in A, x ^ 2 ∂ν) := by
    have hreal : (eLpNorm (levyBandVersion hd hν hA hAsub hAfin v) 2 μ).toReal ^ 2
        = (v : ℝ) * ∫ x in A, x ^ 2 ∂ν := by
      rw [← ENNReal.toReal_pow, eLpNorm_two_sq_levyBandVersion hd hν hA hAsub hAfin v,
        ENNReal.toReal_ofReal (mul_nonneg (NNReal.coe_nonneg v)
          (integral_nonneg fun x => sq_nonneg x))]
    rw [← hreal, Real.sqrt_sq ENNReal.toReal_nonneg]
  rw [h1, ← hsqrt]
  exact ENNReal.toReal_mono h2ne hmono

/-- **Single finite grid.** For a finite set `F ⊆ [0, T]` of times, the measure of the event that the
compensated band path exceeds `ε` at some time in `F` is bounded by `√(T · ∫_A x² dν) / ε`. -/
private lemma measure_finset_sup_levyBandVersion_ge [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {T : ℝ} (_hT : 0 ≤ T) {ε : ℝ≥0} (hε : 0 < ε) (F : Finset ℝ≥0)
    (hFT : ∀ v ∈ F, (v : ℝ) ≤ T) :
    μ {ω | ∃ v ∈ F, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|}
      ≤ ENNReal.ofReal (Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν)) / ε := by
  rcases F.eq_empty_or_nonempty with hFe | hFne
  · subst hFe
    simp only [Finset.notMem_empty, false_and, exists_false, Set.setOf_false, measure_empty]
    exact zero_le
  set N := F.card with hN
  have hmpos : 0 < N := Finset.card_pos.mpr hFne
  have hlt : ∀ k : ℕ, min k (N - 1) < N := fun k => by omega
  let u : ℕ → ℝ≥0 := fun k => F.orderEmbOfFin hN.symm ⟨min k (N - 1), hlt k⟩
  have hmemF : ∀ k, u k ∈ F := fun k => Finset.orderEmbOfFin_mem F hN.symm ⟨min k (N - 1), hlt k⟩
  have hmono : Monotone u := fun i j hij =>
    (F.orderEmbOfFin hN.symm).monotone (by simp only [Fin.mk_le_mk]; omega)
  have hevent_eq :
      {ω | (ε : ℝ) ≤ (Finset.range (N - 1 + 1)).sup' Finset.nonempty_range_add_one
            (fun k => |levyBandVersion hd hν hA hAsub hAfin (u k) ω|)}
        = {ω | ∃ v ∈ F, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.le_sup'_iff, Finset.mem_range]
    constructor
    · rintro ⟨k, _, hle⟩
      exact ⟨u k, hmemF k, hle⟩
    · rintro ⟨v, hv, hle⟩
      have hmem : v ∈ Set.range (F.orderEmbOfFin hN.symm) := by
        rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hv
      obtain ⟨i, hi⟩ := hmem
      refine ⟨(i : ℕ), by have := i.2; omega, ?_⟩
      have hfin : (⟨min (i : ℕ) (N - 1), hlt (i : ℕ)⟩ : Fin N) = i := by
        apply Fin.ext
        show min (i : ℕ) (N - 1) = (i : ℕ)
        have := i.2; omega
      have huv : u (i : ℕ) = v := by
        show F.orderEmbOfFin hN.symm ⟨min (i : ℕ) (N - 1), hlt (i : ℕ)⟩ = v
        rw [hfin]; exact hi
      rw [huv]; exact hle
  have hb : (∫ ω in {ω | ∃ v ∈ F, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|},
        |levyBandVersion hd hν hA hAsub hAfin (u (N - 1)) ω| ∂μ)
      ≤ Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν) :=
    calc (∫ ω in {ω | ∃ v ∈ F, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|},
            |levyBandVersion hd hν hA hAsub hAfin (u (N - 1)) ω| ∂μ)
        ≤ ∫ ω, |levyBandVersion hd hν hA hAsub hAfin (u (N - 1)) ω| ∂μ :=
          setIntegral_le_integral
            (integrable_levyBandVersion hd hν hA hAsub hAfin (u (N - 1))).abs
            (ae_of_all _ fun ω => abs_nonneg _)
      _ ≤ Real.sqrt ((u (N - 1) : ℝ) * ∫ x in A, x ^ 2 ∂ν) :=
          integral_abs_levyBandVersion_le hd hν hA hAsub hAfin (u (N - 1))
      _ ≤ Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (hFT _ (hmemF (N - 1)))
            (integral_nonneg fun x => sq_nonneg x))
  have hmax := maximal_ineq (submartingale_abs_levyBandVersion_grid hd hν hA hAsub hAfin hmono)
    (fun _ _ => abs_nonneg _) (ε := ε) (N - 1)
  rw [hevent_eq] at hmax
  refine (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.mpr hε.ne'))
    (Or.inl ENNReal.coe_ne_top)).mpr ?_
  rw [mul_comm]
  exact hmax.trans (ENNReal.ofReal_le_ofReal hb)

/-- **Maximal inequality over a countable grid.** For a band `A ⊆ (-1, 1)` of finite `ν`-mass and a
countable set of times `D ⊆ [0, T]`, the measure of the event that the compensated band path
`levyBandPath` exceeds a level `ε` in absolute value at some time in `D` is bounded by
`√(T · ∫_A x² dν) / ε`. The event is transferred to the adapted representative `levyBandVersion`
(equal almost everywhere at each of the countably many grid times), then bounded through the finite
maximal inequality on each finite sub-grid and continuity of measure from below. -/
theorem measure_countable_sup_levyBandPath_ge [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    {T : ℝ} (hT : 0 ≤ T) {D : Set ℝ} (hD : D.Countable) (hDT : D ⊆ Set.Icc 0 T)
    {ε : ℝ≥0} (hε : 0 < ε) :
    μ {ω | ∃ t ∈ D, (ε : ℝ) ≤ |levyBandPath K X ν A t ω|}
      ≤ ENNReal.ofReal (Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν)) / ε := by
  rcases Set.eq_empty_or_nonempty D with hDempty | hDne
  · subst hDempty
    simp only [Set.mem_empty_iff_false, false_and, exists_false, Set.setOf_false, measure_empty]
    exact zero_le
  obtain ⟨e, hDe⟩ := hD.exists_eq_range hDne
  -- almost-everywhere transfer between the path and its adapted representative at each grid time
  have htrans : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
        = levyBandPath K X ν A (e n) ω := by
    rw [ae_all_iff]
    intro n
    have hen : e n ∈ D := by rw [hDe]; exact Set.mem_range_self n
    filter_upwards [levyBandVersion_ae_eq hd hν hA hAsub hAfin ((e n).toNNReal)] with ω hω
    rw [hω, Real.coe_toNNReal (e n) (hDT hen).1]
  -- the countable version-event, bounded through finite sub-grids
  have key : μ {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
      ≤ ENNReal.ofReal (Real.sqrt (T * ∫ x in A, x ^ 2 ∂ν)) / ε := by
    have hmono : Monotone (fun N : ℕ =>
        {ω | ∃ n ∈ Finset.range (N + 1),
          (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}) := by
      intro N M hNM ω hω
      obtain ⟨n, hn, hle⟩ := hω
      exact ⟨n, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) (by omega)), hle⟩
    have hunion : {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
        = ⋃ N : ℕ, {ω | ∃ n ∈ Finset.range (N + 1),
            (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨n, hle⟩
        exact ⟨n, n, Finset.self_mem_range_succ n, hle⟩
      · rintro ⟨_, n, _, hle⟩
        exact ⟨n, hle⟩
    rw [hunion, hmono.measure_iUnion]
    refine iSup_le fun N => ?_
    have heq : {ω | ∃ n ∈ Finset.range (N + 1),
          (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
        = {ω | ∃ v ∈ (Finset.range (N + 1)).image (fun n => (e n).toNNReal),
            (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin v ω|} := by
      ext ω
      simp only [Set.mem_setOf_eq, Finset.mem_image]
      constructor
      · rintro ⟨n, hn, hle⟩
        exact ⟨(e n).toNNReal, ⟨n, hn, rfl⟩, hle⟩
      · rintro ⟨v, ⟨n, hn, rfl⟩, hle⟩
        exact ⟨n, hn, hle⟩
    rw [heq]
    refine measure_finset_sup_levyBandVersion_ge hd hν hA hAsub hAfin hT hε _ ?_
    intro v hv
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hv
    have hen : e n ∈ D := by rw [hDe]; exact Set.mem_range_self n
    rw [Real.coe_toNNReal (e n) (hDT hen).1]
    exact (hDT hen).2
  -- transfer the path event to the version event and conclude
  refine le_trans ?_ key
  have hsubset : {ω | ∃ t ∈ D, (ε : ℝ) ≤ |levyBandPath K X ν A t ω|}
      ⊆ {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
        ∪ {ω | ¬ ∀ n : ℕ, levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
            = levyBandPath K X ν A (e n) ω} := by
    intro ω hω
    by_cases hG : ∀ n : ℕ, levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
        = levyBandPath K X ν A (e n) ω
    · left
      obtain ⟨t, htD, hle⟩ := hω
      rw [hDe] at htD
      obtain ⟨n, rfl⟩ := htD
      exact ⟨n, by rw [hG n]; exact hle⟩
    · exact Or.inr hG
  calc μ {ω | ∃ t ∈ D, (ε : ℝ) ≤ |levyBandPath K X ν A t ω|}
      ≤ μ ({ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
          ∪ {ω | ¬ ∀ n : ℕ, levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
              = levyBandPath K X ν A (e n) ω}) := measure_mono hsubset
    _ ≤ μ {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|}
          + μ {ω | ¬ ∀ n : ℕ, levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω
              = levyBandPath K X ν A (e n) ω} := measure_union_le _ _
    _ = μ {ω | ∃ n : ℕ, (ε : ℝ) ≤ |levyBandVersion hd hν hA hAsub hAfin ((e n).toNNReal) ω|} := by
        rw [ae_iff.mp htrans, add_zero]

/-! ### The truncation subsequence

The compensated small-jump path is built as the uniform limit of the compensated banded jump paths
over the growing **annuli** `levyAnnulus n = (-1, 1) ∩ {1/(n+1) ≤ |x|}`, which exhaust the punctured
band `(-1, 1) \ {0}`. Since `∫_{(-1,1)} x² dν < ∞`, the tail second moment over
`(-1, 1) \ levyAnnulus n` vanishes as `n → ∞`; extracting a geometrically-fast subsequence
`levyTruncationSeq` makes the increments between successive annuli summable in `L²`, which (through the
maximal inequality) drives the almost-sure uniform convergence. -/

/-- The **annulus** `(-1, 1) ∩ {1/(n+1) ≤ |x|}`: the small-jump band with a hole of radius `1/(n+1)`
excised around the origin. The annuli grow with `n` and exhaust the punctured band `(-1, 1) \ {0}`. -/
noncomputable def levyAnnulus (n : ℕ) : Set ℝ :=
  Set.Ioo (-1 : ℝ) 1 ∩ {x : ℝ | ((n : ℝ) + 1)⁻¹ ≤ |x|}

/-- The annulus is contained in the small-jump band `(-1, 1)`. -/
lemma levyAnnulus_subset (n : ℕ) : levyAnnulus n ⊆ Set.Ioo (-1 : ℝ) 1 :=
  Set.inter_subset_left

/-- The annulus is measurable. -/
lemma measurableSet_levyAnnulus (n : ℕ) : MeasurableSet (levyAnnulus n) :=
  measurableSet_Ioo.inter (measurableSet_le measurable_const continuous_abs.measurable)

/-- The annuli are monotone increasing: a larger index removes a smaller hole. -/
lemma levyAnnulus_mono : Monotone levyAnnulus := by
  intro m n hmn
  refine Set.inter_subset_inter_right _ fun x hx => ?_
  simp only [Set.mem_setOf_eq] at hx ⊢
  refine le_trans ?_ hx
  have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
  gcongr

omit [SigmaFinite ν] in
/-- The annulus has finite `ν`-mass for any Lévy measure `ν`. -/
lemma levyAnnulus_finite_mass (hν : IsLevyMeasure ν) (n : ℕ) : ν (levyAnnulus n) < ⊤ :=
  (measure_mono Set.inter_subset_right).trans_lt
    (hν.measure_setOf_abs_ge_lt_top (by positivity))

omit [SigmaFinite ν] in
/-- The band complement `(-1, 1) \ levyAnnulus n` is exactly the shrinking central slice
`(-1, 1) ∩ {|x| < 1/(n+1)}`. -/
lemma Ioo_diff_levyAnnulus (n : ℕ) :
    Set.Ioo (-1 : ℝ) 1 \ levyAnnulus n
      = Set.Ioo (-1 : ℝ) 1 ∩ {x : ℝ | |x| < ((n : ℝ) + 1)⁻¹} := by
  ext x
  simp only [levyAnnulus, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq, not_and, not_le]
  constructor
  · rintro ⟨hxIoo, h⟩; exact ⟨hxIoo, h hxIoo⟩
  · rintro ⟨hxIoo, h⟩; exact ⟨hxIoo, fun _ => h⟩

omit [SigmaFinite ν] in
/-- As `n → ∞`, the tail second moment `∫ x² dν` over `(-1, 1) \ levyAnnulus n` vanishes. -/
lemma tendsto_lintegral_Ioo_diff_levyAnnulus (hν : IsLevyMeasure ν) :
    Tendsto (fun n : ℕ => ∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus n,
        ENNReal.ofReal (x ^ 2) ∂ν) atTop (𝓝 0) := by
  simp only [Ioo_diff_levyAnnulus]
  have hslice_meas : ∀ n : ℕ,
      MeasurableSet (Set.Ioo (-1 : ℝ) 1 ∩ {x : ℝ | |x| < ((n : ℝ) + 1)⁻¹}) :=
    fun n => measurableSet_Ioo.inter (measurableSet_lt continuous_abs.measurable measurable_const)
  have hsqmeas : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_id'.pow_const 2)
  have hlim : ∀ x : ℝ, Tendsto (fun n : ℕ =>
      (Set.Ioo (-1 : ℝ) 1 ∩ {y : ℝ | |y| < ((n : ℝ) + 1)⁻¹}).indicator
        (fun y => ENNReal.ofReal (y ^ 2)) x) atTop (𝓝 0) := by
    intro x
    by_cases hx0 : x = 0
    · have hz : (fun n : ℕ => (Set.Ioo (-1 : ℝ) 1 ∩ {y : ℝ | |y| < ((n : ℝ) + 1)⁻¹}).indicator
          (fun y => ENNReal.ofReal (y ^ 2)) x) = fun _ => 0 := by
        funext n; simp [Set.indicator_apply, hx0]
      rw [hz]; exact tendsto_const_nhds
    · have habs : (0 : ℝ) < |x| := abs_pos.mpr hx0
      obtain ⟨N, hN⟩ := exists_nat_gt (|x|⁻¹)
      have hev : ∀ᶠ (n : ℕ) in atTop, (Set.Ioo (-1 : ℝ) 1 ∩ {y : ℝ | |y| < ((n : ℝ) + 1)⁻¹}).indicator
          (fun y => ENNReal.ofReal (y ^ 2)) x = 0 := by
        rw [Filter.eventually_atTop]
        refine ⟨N, fun n hn => Set.indicator_of_notMem (fun hmem => ?_) _⟩
        have hxinv : |x|⁻¹ < (n : ℝ) + 1 := by
          have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          linarith [hN]
        have h1 : (1 : ℝ) < |x| * ((n : ℝ) + 1) := by
          have h2 := mul_lt_mul_of_pos_left hxinv habs
          rwa [mul_inv_cancel₀ (ne_of_gt habs)] at h2
        have hc_lt : ((n : ℝ) + 1)⁻¹ < |x| := by
          rw [inv_eq_one_div, div_lt_iff₀ (Nat.cast_add_one_pos n)]; linarith [h1]
        exact absurd hmem.2 (not_lt.mpr hc_lt.le)
      exact (tendsto_congr' hev).mpr tendsto_const_nhds
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := ν)
    (F := fun n x => (Set.Ioo (-1 : ℝ) 1 ∩ {y : ℝ | |y| < ((n : ℝ) + 1)⁻¹}).indicator
      (fun y => ENNReal.ofReal (y ^ 2)) x)
    (f := fun _ => 0)
    (bound := (Set.Ioo (-1 : ℝ) 1).indicator fun y => ENNReal.ofReal (y ^ 2))
    (fun n => hsqmeas.indicator (hslice_meas n))
    (fun n => Filter.Eventually.of_forall fun x =>
      Set.indicator_le_indicator_apply_of_subset Set.inter_subset_left zero_le)
    (by
      rw [lintegral_indicator measurableSet_Ioo]
      exact (lintegral_setOf_sq_lt_top measurableSet_Ioo (subset_refl _) hν).ne)
    (Filter.Eventually.of_forall hlim)
  have hrw : (fun n : ℕ => ∫⁻ x,
        (Set.Ioo (-1 : ℝ) 1 ∩ {y : ℝ | |y| < ((n : ℝ) + 1)⁻¹}).indicator
          (fun y => ENNReal.ofReal (y ^ 2)) x ∂ν)
      = fun n : ℕ => ∫⁻ x in Set.Ioo (-1 : ℝ) 1 ∩ {x : ℝ | |x| < ((n : ℝ) + 1)⁻¹},
          ENNReal.ofReal (x ^ 2) ∂ν := by
    funext n; rw [lintegral_indicator (hslice_meas n)]
  rw [hrw] at hdct
  simpa using hdct

omit [SigmaFinite ν] in
/-- From the vanishing tail moments, for any starting index `N` and any positive tolerance `16⁻ʲ`,
some later annulus index `n > N` has tail second moment below the tolerance. -/
private lemma exists_gt_lintegral_Ioo_diff_levyAnnulus_le (hν : IsLevyMeasure ν) (N j : ℕ) :
    ∃ n, N < n ∧ (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus n,
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j := by
  have hc : (0 : ℝ≥0∞) < (16 : ℝ≥0∞)⁻¹ ^ j :=
    ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) j
  have hev := ((tendsto_lintegral_Ioo_diff_levyAnnulus hν).eventually
    (Iio_mem_nhds hc)).and (eventually_gt_atTop N)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, hn.2, hn.1.le⟩

/-- The recursively-defined geometric truncation subsequence: each index is chosen strictly larger
than the previous one so that the tail second moment over `(-1, 1) \ levyAnnulus` drops below
`16⁻ʲ`. -/
private noncomputable def levyTruncationAux (hν : IsLevyMeasure ν) : ℕ → ℕ
  | 0 => (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν 0 0).choose
  | (j + 1) =>
      (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν (levyTruncationAux hν j) (j + 1)).choose

omit [SigmaFinite ν] in
private lemma levyTruncationAux_lt_succ (hν : IsLevyMeasure ν) (j : ℕ) :
    levyTruncationAux hν j < levyTruncationAux hν (j + 1) :=
  (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν (levyTruncationAux hν j) (j + 1)).choose_spec.1

omit [SigmaFinite ν] in
private lemma levyTruncationAux_lintegral_le (hν : IsLevyMeasure ν) (j : ℕ) :
    (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (levyTruncationAux hν j),
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j := by
  cases j with
  | zero => exact (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν 0 0).choose_spec.2
  | succ j =>
      exact (exists_gt_lintegral_Ioo_diff_levyAnnulus_le hν
        (levyTruncationAux hν j) (j + 1)).choose_spec.2

omit [SigmaFinite ν] in
private lemma exists_levyTruncationSeq (hν : IsLevyMeasure ν) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ j : ℕ, (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (φ j),
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j :=
  ⟨levyTruncationAux hν, strictMono_nat_of_lt_succ (levyTruncationAux_lt_succ hν),
    levyTruncationAux_lintegral_le hν⟩

/-- The **geometric truncation subsequence**: a strictly increasing sequence of annulus indices along
which the tail second moment over `(-1, 1) \ levyAnnulus` decays at least geometrically at rate
`16⁻ʲ`. -/
noncomputable def levyTruncationSeq (hν : IsLevyMeasure ν) : ℕ → ℕ :=
  (exists_levyTruncationSeq hν).choose

omit [SigmaFinite ν] in
/-- The truncation subsequence is strictly monotone and its tail second moments decay like `16⁻ʲ`. -/
theorem levyTruncationSeq_spec (hν : IsLevyMeasure ν) :
    StrictMono (levyTruncationSeq hν) ∧
    ∀ j : ℕ, (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (levyTruncationSeq hν j),
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j :=
  (exists_levyTruncationSeq hν).choose_spec

/-! ### The consecutive annulus slices

`levySlice hν j` is the annular shell added when passing from `levyAnnulus (levyTruncationSeq hν j)`
to `levyAnnulus (levyTruncationSeq hν (j+1))`. Its `ν`-second moment `∫ x² dν` is bounded by the tail
moment `16⁻ʲ`, which makes the compensated band paths over successive annuli a Cauchy sequence in the
maximal-inequality sense. -/

/-- The consecutive annulus slice added between truncation steps `j` and `j+1`. -/
noncomputable def levySlice (hν : IsLevyMeasure ν) (j : ℕ) : Set ℝ :=
  levyAnnulus (levyTruncationSeq hν (j + 1)) \ levyAnnulus (levyTruncationSeq hν j)

omit [SigmaFinite ν] in
/-- The slice is contained in the small-jump band `(-1, 1)`. -/
lemma levySlice_subset (hν : IsLevyMeasure ν) (j : ℕ) : levySlice hν j ⊆ Set.Ioo (-1 : ℝ) 1 :=
  Set.sdiff_subset.trans (levyAnnulus_subset _)

omit [SigmaFinite ν] in
/-- The slice is measurable. -/
lemma measurableSet_levySlice (hν : IsLevyMeasure ν) (j : ℕ) : MeasurableSet (levySlice hν j) :=
  (measurableSet_levyAnnulus _).diff (measurableSet_levyAnnulus _)

omit [SigmaFinite ν] in
/-- The slice sits inside the central band complement `(-1, 1) \ levyAnnulus (levyTruncationSeq hν j)`,
so its tail second moment is controlled by the truncation spec. -/
lemma levySlice_subset_Ioo_diff (hν : IsLevyMeasure ν) (j : ℕ) :
    levySlice hν j ⊆ Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (levyTruncationSeq hν j) :=
  fun _ hx => ⟨levyAnnulus_subset _ hx.1, hx.2⟩

omit [SigmaFinite ν] in
/-- The slice has finite `ν`-mass. -/
lemma levySlice_finite_mass (hν : IsLevyMeasure ν) (j : ℕ) : ν (levySlice hν j) < ⊤ :=
  (measure_mono Set.sdiff_subset).trans_lt (levyAnnulus_finite_mass hν _)

omit [SigmaFinite ν] in
/-- The annulus at step `j+1` is the disjoint union of the annulus at step `j` and the slice. -/
lemma levyAnnulus_succ_eq (hν : IsLevyMeasure ν) (j : ℕ) :
    levyAnnulus (levyTruncationSeq hν (j + 1))
      = levyAnnulus (levyTruncationSeq hν j) ∪ levySlice hν j :=
  (Set.union_sdiff_cancel
    (levyAnnulus_mono ((levyTruncationSeq_spec hν).1 (Nat.lt_succ_self j)).le)).symm

omit [SigmaFinite ν] in
/-- The annulus at step `j` and the slice are disjoint. -/
lemma disjoint_levyAnnulus_levySlice (hν : IsLevyMeasure ν) (j : ℕ) :
    Disjoint (levyAnnulus (levyTruncationSeq hν j)) (levySlice hν j) :=
  disjoint_sdiff_self_right

omit [SigmaFinite ν] in
/-- The `ν`-second moment of the slice is bounded by the geometric tail rate `16⁻ʲ`. -/
lemma integral_sq_levySlice_le (hν : IsLevyMeasure ν) (j : ℕ) :
    ∫ x in levySlice hν j, x ^ 2 ∂ν ≤ ((16 : ℝ)⁻¹) ^ j := by
  have hlint : (∫⁻ x in levySlice hν j, ENNReal.ofReal (x ^ 2) ∂ν)
      ≤ ∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus (levyTruncationSeq hν j),
          ENNReal.ofReal (x ^ 2) ∂ν :=
    lintegral_mono' (Measure.restrict_mono (levySlice_subset_Ioo_diff hν j) le_rfl) le_rfl
  have hbound : (∫⁻ x in levySlice hν j, ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j :=
    hlint.trans ((levyTruncationSeq_spec hν).2 j)
  have hne : (16 : ℝ≥0∞)⁻¹ ^ j ≠ ⊤ :=
    (ENNReal.pow_lt_top (ENNReal.inv_lt_top.mpr (by norm_num))).ne
  calc ∫ x in levySlice hν j, x ^ 2 ∂ν
      = (ENNReal.ofReal (∫ x in levySlice hν j, x ^ 2 ∂ν)).toReal :=
        (ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg x)).symm
    _ = (∫⁻ x in levySlice hν j, ENNReal.ofReal (x ^ 2) ∂ν).toReal := by
        rw [ofReal_integral_sq (measurableSet_levySlice hν j) (levySlice_subset hν j) hν]
    _ ≤ ((16 : ℝ≥0∞)⁻¹ ^ j).toReal := ENNReal.toReal_mono hne hbound
    _ = ((16 : ℝ)⁻¹) ^ j := by
        rw [ENNReal.toReal_pow, ENNReal.toReal_inv]; norm_num

/-! ### The almost-sure good event

The compensated small-jump path is defined only on a measurable **good set** carved out so that every
sample point in it enjoys the pathwise properties needed for uniform convergence: finitely many active
pieces in each bounded window (for both the annuli and the slices, giving càdlàg approximants), and a
Borel–Cantelli tail control of the slice paths over a countable time grid. The good set is the
complement of a measurable hull of the (measure-zero) bad event, so it is measurable, almost sure, and
contained in the raw event of full pathwise control. -/

/-- The countable rational time grid on `[0, T]`, together with the right endpoint `T`. -/
noncomputable def levyGrid (T : ℕ) : Set ℝ :=
  (Set.range ((↑) : ℚ → ℝ) ∩ Set.Icc 0 (T : ℝ)) ∪ {(T : ℝ)}

lemma levyGrid_countable (T : ℕ) : (levyGrid T).Countable :=
  ((Set.countable_range _).mono Set.inter_subset_left).union (Set.countable_singleton _)

lemma levyGrid_subset_Icc (T : ℕ) : levyGrid T ⊆ Set.Icc 0 (T : ℝ) :=
  Set.union_subset Set.inter_subset_right
    (Set.singleton_subset_iff.mpr ⟨Nat.cast_nonneg T, le_rfl⟩)

/-- The **bad grid event** at slice index `j` over the window `[0, T]`: the compensated slice path
exceeds the geometric level `2⁻ʲ` at some grid time. Borel–Cantelli sums these over `j`. -/
noncomputable def levyBadGrid (_hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) (T j : ℕ) : Set Ω :=
  {ω | ∃ q ∈ levyGrid T, ((2 : ℝ)⁻¹) ^ j ≤ |levyBandPath K X ν (levySlice hν j) q ω|}

/-- Task-4 maximal inequality applied to the slice path: the bad-grid event has measure at most
`√T · 2⁻ʲ`. The `√(T · ∫_slice x²) ≤ √T · 4⁻ʲ` bound, divided by the level `2⁻ʲ`, collapses to
`√T · 2⁻ʲ`. -/
lemma measure_levyBadGrid_le [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (T j : ℕ) :
    μ (levyBadGrid hd hν T j) ≤ ENNReal.ofReal (Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j) := by
  set ε : ℝ≥0 := ((2 : ℝ≥0)⁻¹) ^ j with hεdef
  have hεR : (ε : ℝ) = ((2 : ℝ)⁻¹) ^ j := by rw [hεdef]; push_cast; ring
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hev : levyBadGrid hd hν T j
      = {ω | ∃ t ∈ levyGrid T, (ε : ℝ) ≤ |levyBandPath K X ν (levySlice hν j) t ω|} := by
    simp only [levyBadGrid, hεR]
  rw [hev]
  refine (measure_countable_sup_levyBandPath_ge hd hν (measurableSet_levySlice hν j)
    (levySlice_subset hν j) (levySlice_finite_mass hν j) (Nat.cast_nonneg T)
    (levyGrid_countable T) (levyGrid_subset_Icc T) hεpos).trans ?_
  -- the real-level bound `√(T · ∫_slice x²) / ε ≤ √T · 2⁻ʲ`
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hIle : (∫ x in levySlice hν j, x ^ 2 ∂ν) ≤ ((16 : ℝ)⁻¹) ^ j := integral_sq_levySlice_le hν j
  have hsqrt16 : Real.sqrt (((16 : ℝ)⁻¹) ^ j) = ((4 : ℝ)⁻¹) ^ j := by
    have hthis : (((4 : ℝ)⁻¹) ^ j) ^ 2 = ((16 : ℝ)⁻¹) ^ j := by
      rw [← pow_mul, mul_comm, pow_mul, show ((4 : ℝ)⁻¹) ^ 2 = (16 : ℝ)⁻¹ by norm_num]
    rw [← hthis, Real.sqrt_sq (by positivity)]
  have step1 : Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν)
      ≤ Real.sqrt (T : ℝ) * ((4 : ℝ)⁻¹) ^ j := by
    rw [← hsqrt16, ← Real.sqrt_mul hTnn]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hIle hTnn)
  have step2 : Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j * ((2 : ℝ)⁻¹) ^ j
      = Real.sqrt (T : ℝ) * ((4 : ℝ)⁻¹) ^ j := by
    rw [mul_assoc, ← mul_pow, show (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ = (4 : ℝ)⁻¹ by norm_num]
  have hreal : Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν) / (ε : ℝ)
      ≤ Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j := by
    rw [hεR, div_le_iff₀ (by positivity), step2]
    exact step1
  calc ENNReal.ofReal (Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν)) / (ε : ℝ≥0∞)
      = ENNReal.ofReal (Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν))
          / ENNReal.ofReal (ε : ℝ) := by rw [ENNReal.ofReal_coe_nnreal]
    _ = ENNReal.ofReal (Real.sqrt ((T : ℝ) * ∫ x in levySlice hν j, x ^ 2 ∂ν) / (ε : ℝ)) :=
        (ENNReal.ofReal_div_of_pos (by rw [hεR]; positivity)).symm
    _ ≤ ENNReal.ofReal (Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j) := ENNReal.ofReal_le_ofReal hreal

/-- The bad-grid measures are summable at each `T`: `∑ⱼ √T · 2⁻ʲ = 2√T < ∞`. -/
lemma tsum_measure_levyBadGrid_ne_top [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) (T : ℕ) :
    (∑' j, μ (levyBadGrid hd hν T j)) ≠ ⊤ := by
  have hsummable : Summable (fun j : ℕ => Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : (∑' j, μ (levyBadGrid hd hν T j))
      ≤ ∑' j, ENNReal.ofReal (Real.sqrt (T : ℝ) * ((2 : ℝ)⁻¹) ^ j) :=
    ENNReal.tsum_le_tsum (measure_levyBadGrid_le hd hν T)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsummable] at hle
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- The **raw good event**: full pathwise control at `ω`. Its three clauses are (i) window finiteness
for every annulus, (ii) window finiteness for every slice, (iii) Borel–Cantelli tail control of the
slice paths over each grid. -/
def levySmallJumpRaw (_hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    (hν : IsLevyMeasure ν) (ω : Ω) : Prop :=
  (∀ T j : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ levyAnnulus (levyTruncationSeq hν j)}.Finite) ∧
  (∀ T j : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ levySlice hν j}.Finite) ∧
  (∀ T : ℕ, ∀ᶠ j in atTop, ∀ q ∈ levyGrid T,
      |levyBandPath K X ν (levySlice hν j) q ω| < ((2 : ℝ)⁻¹) ^ j)

/-- The raw good event holds almost surely. -/
lemma ae_levySmallJumpRaw [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    ∀ᵐ ω ∂μ, levySmallJumpRaw hd hν ω := by
  have ha : ∀ᵐ ω ∂μ, ∀ T j : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ levyAnnulus (levyTruncationSeq hν j)}.Finite := by
    rw [ae_all_iff]; intro T; rw [ae_all_iff]; intro j
    exact ae_finite_pieces_mem hd (measurableSet_Ioc.prod (measurableSet_levyAnnulus _))
      (volume_prod_Ioc_prod_lt_top (m := ν) (s := 0) (t := (T : ℝ))
        (levyAnnulus_finite_mass hν (levyTruncationSeq hν j)))
  have hb : ∀ᵐ ω ∂μ, ∀ T j : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ levySlice hν j}.Finite := by
    rw [ae_all_iff]; intro T; rw [ae_all_iff]; intro j
    exact ae_finite_pieces_mem hd (measurableSet_Ioc.prod (measurableSet_levySlice hν j))
      (volume_prod_Ioc_prod_lt_top (m := ν) (s := 0) (t := (T : ℝ)) (levySlice_finite_mass hν j))
  have hc : ∀ᵐ ω ∂μ, ∀ T : ℕ, ∀ᶠ j in atTop, ∀ q ∈ levyGrid T,
      |levyBandPath K X ν (levySlice hν j) q ω| < ((2 : ℝ)⁻¹) ^ j := by
    rw [ae_all_iff]; intro T
    filter_upwards [ae_eventually_notMem (tsum_measure_levyBadGrid_ne_top hd hν T)] with ω hω
    filter_upwards [hω] with j hj
    intro q hq
    by_contra hle
    exact hj ⟨q, hq, not_lt.mp hle⟩
  filter_upwards [ha, hb, hc] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- The **good set** for the compensated small-jump path: the complement of a measurable hull of the
measure-zero bad event. It is measurable, almost sure, and every point in it satisfies the raw
pathwise-control event. -/
noncomputable def levySmallJumpGoodSet
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) : Set Ω :=
  (MeasureTheory.toMeasurable μ {ω | ¬ levySmallJumpRaw hd hν ω})ᶜ

/-- The good set is measurable. -/
theorem measurableSet_levySmallJumpGoodSet
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    MeasurableSet (levySmallJumpGoodSet hd hν) :=
  (measurableSet_toMeasurable _ _).compl

/-- Every sample point in the good set satisfies the raw pathwise-control event. -/
lemma levySmallJumpRaw_of_mem_goodSet
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hω : ω ∈ levySmallJumpGoodSet hd hν) : levySmallJumpRaw hd hν ω := by
  by_contra h
  exact hω (subset_toMeasurable μ {ω | ¬ levySmallJumpRaw hd hν ω} h)

/-- The good set is almost sure. -/
theorem ae_mem_levySmallJumpGoodSet [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    ∀ᵐ ω ∂μ, ω ∈ levySmallJumpGoodSet hd hν := by
  rw [ae_iff]
  have hset : {ω | ω ∉ levySmallJumpGoodSet hd hν}
      = MeasureTheory.toMeasurable μ {ω | ¬ levySmallJumpRaw hd hν ω} := by
    ext ω; simp only [levySmallJumpGoodSet, Set.mem_setOf_eq, Set.mem_compl_iff, not_not]
  rw [hset, measure_toMeasurable]
  exact ae_iff.mp (ae_levySmallJumpRaw hd hν)

end ProbabilityTheory
