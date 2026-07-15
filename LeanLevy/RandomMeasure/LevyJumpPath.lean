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

end ProbabilityTheory
