/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.RandomMeasure.LevyJumpLaw
import LeanLevy.Processes.Cadlag
import LeanLevy.Processes.LevyProcess
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
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
* `ProbabilityTheory.levyAnnulus` — the annulus `(-1, 1) ∩ {1/(n+1) ≤ |x|}`; the annuli exhaust the
  punctured small-jump band.
* `ProbabilityTheory.levyTruncationSeq` — the geometric truncation subsequence of annulus indices
  along which the tail second moments decay like `16⁻ʲ`.
* `ProbabilityTheory.levySmallJumpGoodSet` — the measurable, almost-sure event carrying full pathwise
  control of the annulus paths.
* `ProbabilityTheory.levySmallJumpPath` — the compensated small-jump path, the almost-sure uniform
  limit of the compensated banded jump paths over the growing annuli (gated to the good set).
* `ProbabilityTheory.levyJumpPath` — the càdlàg pure-jump process indexed by `ℝ≥0`: drift plus
  large-jump sum plus the compensated small-jump path. It shares its drift and large-jump summands
  literally with `levyJumpProcess`, differing only in the (a.e.-equal) small-jump summand, and so
  realizes the same law while carrying a.e.-càdlàg sample paths.

## Main results

* `ProbabilityTheory.exists_isLevyProcess_pureJump` — **the headline**: every pure-jump Lévy triple
  `(b, 0, ν)` is realized by a genuine `IsLevyProcess` — a probability space and a process with
  literal zero start, a.e. càdlàg paths, independent and stationary increments, measurable
  time-slices, and marginal characteristic functions `exp (t · ψ_{(b,0,ν)})`.
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
* `ProbabilityTheory.levyTruncationSeq_spec` — the truncation subsequence is strictly monotone with
  geometrically-decaying (`16⁻ʲ`) tail second moments.
* `ProbabilityTheory.measurableSet_levySmallJumpGoodSet`, `ae_mem_levySmallJumpGoodSet` — the good set
  is measurable and almost sure.
* `ProbabilityTheory.tendsto_levyBandPath_levySmallJumpPath` — on the good set and for `t ≥ 0`, the
  annulus paths converge to the compensated small-jump path.
* `ProbabilityTheory.isCadlag_levySmallJumpPath` — for *every* `ω`, the compensated small-jump path is
  càdlàg (unconditional through the off-good-set-zero gating).
* `ProbabilityTheory.measurable_levySmallJumpPath` — the compensated small-jump path is measurable at
  each time.
* `ProbabilityTheory.levySmallJumpPath_ae_eq` — for each fixed `t ≥ 0`, the compensated small-jump
  path agrees `μ`-almost everywhere with the `L²` small-jump element `levyCompensatedSmallJump`
  (a per-time modification statement; the null set may depend on `t`).
* `ProbabilityTheory.levyJumpPath_zero` — the jump path vanishes at time zero (literal function
  equality `= fun _ => 0`).
* `ProbabilityTheory.measurable_levyJumpPath` — the jump path is measurable at each time.
* `ProbabilityTheory.levyJumpPath_ae_eq` — at each fixed time the jump path agrees `μ`-almost
  everywhere with the law-level jump process `levyJumpProcess` (they differ only in the small-jump
  summand, which is a per-time modification of the other).
* `ProbabilityTheory.ae_isCadlag_levyJumpPath` — almost every sample path `t ↦ levyJumpPath t ω` is
  càdlàg (a.e. in `ω`).
* `ProbabilityTheory.isLevyProcess_levyJumpPath` — the jump path is a genuine `IsLevyProcess` for the
  pure-jump triple `(b, 0, ν)`: literal zero start, a.e. càdlàg paths, independent and stationary
  increments.
* `ProbabilityTheory.charFun_map_levyJumpPath` — the fixed-time marginal law of the jump path has
  characteristic function `exp (t · ψ_{(b,0,ν)})`.
* `ProbabilityTheory.charExponent_levyJumpPath` — the characteristic exponent of the jump path is the
  Lévy–Khintchine exponent `ψ_{(b,0,ν)}` of the pure-jump triple.
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
/-- From the vanishing tail moments, for any starting index `N` and any positive tolerance `16⁻ʲ`,
some later annulus index `n > N` has tail second moment below the tolerance. -/
private lemma exists_gt_lintegral_Ioo_diff_levyAnnulus_le (hν : IsLevyMeasure ν) (N j : ℕ) :
    ∃ n, N < n ∧ (∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus n,
        ENNReal.ofReal (x ^ 2) ∂ν) ≤ (16 : ℝ≥0∞)⁻¹ ^ j := by
  have hc : (0 : ℝ≥0∞) < (16 : ℝ≥0∞)⁻¹ ^ j :=
    ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) j
  have htendsto : Tendsto (fun n : ℕ => ∫⁻ x in Set.Ioo (-1 : ℝ) 1 \ levyAnnulus n,
      ENNReal.ofReal (x ^ 2) ∂ν) atTop (𝓝 0) := by
    simpa only [Ioo_diff_levyAnnulus] using tendsto_lintegral_slice_sq hν
  have hev := (htendsto.eventually (Iio_mem_nhds hc)).and (eventually_gt_atTop N)
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

/-! ### Pathwise infrastructure on the good set

The following lemmas reconstruct, for a single sample point `ω` in the raw good event, the pathwise
facts that hold almost surely: window-local càdlàg regularity of the banded jump paths, disjoint-union
additivity of the compensated band paths, and the slice-additivity of successive annulus paths. They
feed the telescoping estimate that establishes uniform Cauchyness. -/

omit [MeasurableSpace Ω] in
/-- Window finiteness at every natural time gives window finiteness at every real time. -/
private lemma finite_pieces_Ioc_of_forall_nat {A : Set ℝ} {ω : Ω}
    (hfin : ∀ T : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite) (t : ℝ) :
    {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 t ×ˢ A}.Finite := by
  obtain ⟨T, hT⟩ := exists_nat_gt t
  refine (hfin T).subset fun k hk => ?_
  obtain ⟨n, hn, hmem⟩ := hk
  exact ⟨n, hn, Set.mem_prod.mpr
    ⟨Set.Ioc_subset_Ioc (le_refl 0) hT.le (Set.mem_prod.mp hmem).1, (Set.mem_prod.mp hmem).2⟩⟩

omit [MeasurableSpace Ω] in
/-- On a window with finitely many active pieces, the band piece sums are summable. -/
private lemma summable_pieceSum_band_of_finite {A : Set ℝ} {ω : Ω} (t : ℝ)
    (hfin : {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 t ×ˢ A}.Finite) :
    Summable (fun k => pieceSum K X ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) k ω) := by
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun k hk => ?_
  simp only [pieceSum]
  refine Finset.sum_eq_zero fun n hn => ?_
  exact Set.indicator_of_notMem (fun hmem => hk (hfin.mem_toFinset.mpr ⟨n, hn, hmem⟩)) _

omit [MeasurableSpace Ω] [SigmaFinite ν] in
/-- The identity function is `ν`-integrable on a finite-mass band `A ⊆ (-1, 1)` (it is bounded). -/
private lemma integrableOn_id_of_subset {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤) :
    IntegrableOn (fun x : ℝ => x) A ν := by
  refine IntegrableOn.of_bound hAfin measurable_id.aestronglyMeasurable 1 ?_
  filter_upwards [ae_restrict_mem hA] with x hx
  have hx' := hAsub hx
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩

omit [MeasurableSpace Ω] [SigmaFinite ν] in
/-- **Disjoint-union additivity** of the compensated band path (on a window with finitely many active
pieces): the compensated band path over `A ∪ B` splits as the sum over `A` and over `B`. -/
private lemma levyBandPath_union_of_finite {A B : Set ℝ} {ω : Ω} (t : ℝ)
    (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1 : ℝ) 1) (hAfin : ν A < ⊤)
    (hB : MeasurableSet B) (hBsub : B ⊆ Set.Ioo (-1 : ℝ) 1) (hBfin : ν B < ⊤)
    (hAB : Disjoint A B)
    (hfinA : {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 t ×ˢ A}.Finite)
    (hfinB : {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ Set.Ioc 0 t ×ˢ B}.Finite) :
    levyBandPath K X ν (A ∪ B) t ω = levyBandPath K X ν A t ω + levyBandPath K X ν B t ω := by
  have hind : ((Set.Ioc 0 t ×ˢ (A ∪ B)).indicator fun p : ℝ × ℝ => p.2)
      = ((Set.Ioc 0 t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
        + ((Set.Ioc 0 t ×ˢ B).indicator fun p : ℝ × ℝ => p.2) := by
    rw [Set.prod_union]
    exact Set.indicator_union_of_disjoint (Set.Disjoint.set_prod_right hAB _ _) _
  have hbjs : bandJumpSum K X (A ∪ B) t ω = bandJumpSum K X A t ω + bandJumpSum K X B t ω := by
    simp only [bandJumpSum]
    rw [← (summable_pieceSum_band_of_finite t hfinA).tsum_add
      (summable_pieceSum_band_of_finite t hfinB)]
    refine tsum_congr fun k => ?_
    simp only [pieceSum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simpa using congrFun hind (X k n ω)
  have hdrift : ∫ x in A ∪ B, x ∂ν = (∫ x in A, x ∂ν) + ∫ x in B, x ∂ν :=
    setIntegral_union hAB hB (integrableOn_id_of_subset hA hAsub hAfin)
      (integrableOn_id_of_subset hB hBsub hBfin)
  simp only [levyBandPath, hbjs, hdrift]; ring

/-- **Slice-additivity**: the compensated band path over the annulus at step `j+1` equals the path
over the annulus at step `j` plus the path over the intervening slice. -/
private lemma levyBandPath_annulus_succ
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hraw : levySmallJumpRaw hd hν ω) (j : ℕ) (t : ℝ) :
    levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν (j + 1))) t ω
      = levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) t ω
        + levyBandPath K X ν (levySlice hν j) t ω := by
  rw [levyAnnulus_succ_eq hν j]
  exact levyBandPath_union_of_finite t
    (measurableSet_levyAnnulus _) (levyAnnulus_subset _)
    (levyAnnulus_finite_mass hν _) (measurableSet_levySlice hν j)
    (levySlice_subset hν j) (levySlice_finite_mass hν j)
    (disjoint_levyAnnulus_levySlice hν j)
    (finite_pieces_Ioc_of_forall_nat (fun T => hraw.1 T j) t)
    (finite_pieces_Ioc_of_forall_nat (fun T => hraw.2.1 T j) t)

omit [MeasurableSpace Ω] in
/-- Window-local finiteness gives a càdlàg banded jump path (pointwise version of
`ae_isCadlag_bandJumpSum`). -/
private lemma isCadlag_bandJumpSum_of_finite {A : Set ℝ} (ω : Ω)
    (hfin : ∀ T : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite) :
    IsCadlag (fun t : ℝ => bandJumpSum K X A t ω) := by
  intro t
  obtain ⟨T, hT⟩ := exists_nat_gt t
  refine (isCadlag_bandStepFinsetSum (K := K) (X := X) A ω (hfin T).toFinset t).congr ?_
  filter_upwards [Iio_mem_nhds hT] with s hs
  exact (bandJumpSum_eqOn_Iio A ω (hfin T) hs).symm

omit [MeasurableSpace Ω] [SigmaFinite ν] in
/-- Window-local finiteness gives a càdlàg compensated band path (pointwise version of
`ae_isCadlag_levyBandPath`). -/
private lemma isCadlag_levyBandPath_of_finite {A : Set ℝ} (ω : Ω)
    (hfin : ∀ T : ℕ, {k | ∃ n ∈ Finset.range (K k ω),
      X k n ω ∈ Set.Ioc 0 (T : ℝ) ×ˢ A}.Finite) :
    IsCadlag (fun t : ℝ => levyBandPath K X ν A t ω) := by
  have hcont : Continuous (fun t : ℝ => -(t * ∫ x in A, x ∂ν)) := by fun_prop
  simpa only [levyBandPath, sub_eq_add_neg] using
    (isCadlag_bandJumpSum_of_finite ω hfin).add hcont.isCadlag

omit [MeasurableSpace Ω] in
/-- A càdlàg function bounded by `c` on the rational grid of `[0, T]` is bounded by `c` on all of
`[0, T]`: rationals descending to `t` from the right transfer the bound via right-continuity. -/
private lemma abs_le_of_isCadlag_of_grid {g : ℝ → ℝ} {T : ℕ} {c : ℝ} (hg : IsCadlag g)
    (hgrid : ∀ q ∈ levyGrid T, |g q| ≤ c) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) (T : ℝ)) :
    |g t| ≤ c := by
  rcases eq_or_lt_of_le ht.2 with htT | htT
  · rw [htT]; exact hgrid (T : ℝ) (Or.inr rfl)
  · set d : ℝ := (T : ℝ) - t with hddef
    have hdpos : 0 < d := by rw [hddef]; linarith
    have hex : ∀ n : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < t + d / ((n : ℝ) + 2) := fun n =>
      exists_rat_btwn (by
        have hpos : (0 : ℝ) < d / ((n : ℝ) + 2) := by positivity
        linarith)
    choose q hq using hex
    have hqT : ∀ n, (q n : ℝ) < (T : ℝ) := fun n => by
      have hle : d / ((n : ℝ) + 2) ≤ d :=
        div_le_self hdpos.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      calc (q n : ℝ) < t + d / ((n : ℝ) + 2) := (hq n).2
        _ ≤ t + d := by linarith
        _ = (T : ℝ) := by rw [hddef]; ring
    have hqmem : ∀ n, (q n : ℝ) ∈ levyGrid T := fun n =>
      Or.inl ⟨⟨q n, rfl⟩, ⟨le_of_lt (lt_of_le_of_lt ht.1 (hq n).1), le_of_lt (hqT n)⟩⟩
    have hd0 : Tendsto (fun n : ℕ => d / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds
        (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
    have hqtend : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 t) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using tendsto_const_nhds.add hd0)
        (Filter.Eventually.of_forall fun n => (hq n).1.le)
        (Filter.Eventually.of_forall fun n => (hq n).2.le)
    have hmem : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[Set.Ici t] t) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hqtend
        (Filter.Eventually.of_forall fun n => (hq n).1.le)
    have hgq : Tendsto (fun n => g (q n : ℝ)) atTop (𝓝 (g t)) :=
      (hg.rightContinuous t).tendsto.comp hmem
    refine le_of_tendsto ((continuous_abs.tendsto _).comp hgq) ?_
    exact Filter.Eventually.of_forall fun n => hgrid _ (hqmem n)

omit [MeasurableSpace Ω] in
/-- A càdlàg function `f` with `f 0 = 0`, composed with `max · 0`, is again càdlàg: it equals `f` on
`(0, ∞)` and is constantly `0` on `(-∞, 0)`, and at `0` right-continuity comes from `f` while the left
limit is `0`. -/
private lemma isCadlag_comp_max_zero {f : ℝ → ℝ} (hf : IsCadlag f) (h0 : f 0 = 0) :
    IsCadlag (fun t : ℝ => f (max t 0)) := by
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · refine (isCadlag_const (c := f 0) t).congr ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    rw [max_eq_right (le_of_lt (Set.mem_Iio.mp hs))]
  · subst ht
    refine ⟨?_, 0, ?_⟩
    · refine (hf.rightContinuous 0).congr (fun y hy => ?_) ?_
      · rw [max_eq_left (Set.mem_Ici.mp hy)]
      · rw [max_eq_left (le_refl (0 : ℝ))]
    · have heq : (fun s => f (max s 0)) =ᶠ[𝓝[Set.Iio 0] 0] fun _ => (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [max_eq_right (le_of_lt (Set.mem_Iio.mp hs)), h0]
      exact tendsto_const_nhds.congr' heq.symm
  · refine (hf t).congr ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    rw [max_eq_left (le_of_lt (Set.mem_Ioi.mp hs))]

/-- **Telescoping estimate.** For `m ≥ N₀` and `m ≤ n`, the gap between the annulus paths at steps `m`
and `n` is bounded by `2 · 2⁻ᵐ` on `[0, T]`, since the successive differences are the slice paths and
each is `≤ 2⁻ʲ` there. -/
private lemma abs_annulusPath_sub_le
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hraw : levySmallJumpRaw hd hν ω) (T : ℕ) {N₀ : ℕ}
    (hbound : ∀ j, N₀ ≤ j → ∀ y ∈ Set.Icc (0 : ℝ) (T : ℝ),
      |levyBandPath K X ν (levySlice hν j) y ω| ≤ ((2 : ℝ)⁻¹) ^ j)
    {m n : ℕ} (hm : N₀ ≤ m) (hmn : m ≤ n) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) (T : ℝ)) :
    |levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) y ω
        - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) y ω| ≤ 2 * ((2 : ℝ)⁻¹) ^ m := by
  set f : ℕ → ℝ := fun i => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν (m + i))) y ω
    with hf
  have htel : levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) y ω
        - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) y ω
      = ∑ i ∈ Finset.range (n - m), levyBandPath K X ν (levySlice hν (m + i)) y ω := by
    have hstep : ∀ i, f (i + 1) - f i = levyBandPath K X ν (levySlice hν (m + i)) y ω := by
      intro i
      simp only [hf, show m + (i + 1) = (m + i) + 1 from by ring]
      rw [levyBandPath_annulus_succ hd hν hraw (m + i) y]; ring
    calc levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) y ω
          - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) y ω
        = f (n - m) - f 0 := by simp only [hf]; rw [Nat.add_sub_cancel' hmn, Nat.add_zero]
      _ = ∑ i ∈ Finset.range (n - m), (f (i + 1) - f i) := (Finset.sum_range_sub f (n - m)).symm
      _ = _ := Finset.sum_congr rfl fun i _ => hstep i
  rw [htel]
  have hgeo : ∑ i ∈ Finset.range (n - m), ((2 : ℝ)⁻¹) ^ i ≤ 2 :=
    (Summable.sum_le_tsum _ (fun i _ => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))).trans tsum_geometric_inv_two.le
  calc |∑ i ∈ Finset.range (n - m), levyBandPath K X ν (levySlice hν (m + i)) y ω|
      ≤ ∑ i ∈ Finset.range (n - m), |levyBandPath K X ν (levySlice hν (m + i)) y ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n - m), ((2 : ℝ)⁻¹) ^ (m + i) :=
        Finset.sum_le_sum fun i _ => hbound (m + i) (hm.trans (Nat.le_add_right m i)) y hy
    _ = ((2 : ℝ)⁻¹) ^ m * ∑ i ∈ Finset.range (n - m), ((2 : ℝ)⁻¹) ^ i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => pow_add _ _ _
    _ ≤ ((2 : ℝ)⁻¹) ^ m * 2 := by
        exact mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 2 * ((2 : ℝ)⁻¹) ^ m := by ring

/-- **Uniform Cauchyness on compacts.** For a raw-good `ω` and each `T`, the annulus paths composed
with `max · 0` form a uniformly Cauchy sequence on `Iic T`. -/
private lemma uniformCauchySeqOn_annulusPath_max
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hraw : levySmallJumpRaw hd hν ω) (T : ℕ) :
    UniformCauchySeqOn
      (fun j (t : ℝ) => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω)
      atTop (Set.Iic (T : ℝ)) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hraw.2.2 T)
  have hbound : ∀ j, N₀ ≤ j → ∀ y ∈ Set.Icc (0 : ℝ) (T : ℝ),
      |levyBandPath K X ν (levySlice hν j) y ω| ≤ ((2 : ℝ)⁻¹) ^ j := fun j hj y hy =>
    abs_le_of_isCadlag_of_grid (isCadlag_levyBandPath_of_finite ω (fun T' => hraw.2.1 T' j))
      (fun q hq => (hN₀ j hj q hq).le) hy
  have hgeo : Tendsto (fun n : ℕ => 2 * ((2 : ℝ)⁻¹) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)).const_mul (2 : ℝ)
    simpa using this
  obtain ⟨N, hNε, hNN₀⟩ :=
    ((hgeo.eventually (Iio_mem_nhds hε)).and (eventually_ge_atTop N₀)).exists
  refine ⟨N, fun m hm n hn x hx => ?_⟩
  have hmax : max x 0 ∈ Set.Icc (0 : ℝ) (T : ℝ) :=
    ⟨le_max_right _ _, max_le (Set.mem_Iic.mp hx) (Nat.cast_nonneg T)⟩
  rw [Real.dist_eq]
  rcases le_total m n with hmn | hnm
  · calc |levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) (max x 0) ω
            - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) (max x 0) ω|
        = |levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) (max x 0) ω
            - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) (max x 0) ω| :=
          abs_sub_comm _ _
      _ ≤ 2 * ((2 : ℝ)⁻¹) ^ m :=
          abs_annulusPath_sub_le hd hν hraw T hbound (hNN₀.trans hm) hmn hmax
      _ ≤ 2 * ((2 : ℝ)⁻¹) ^ N := by
          have : ((2 : ℝ)⁻¹) ^ m ≤ ((2 : ℝ)⁻¹) ^ N :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
          linarith [this, (by positivity : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ N)]
      _ < ε := hNε
  · calc |levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν m)) (max x 0) ω
            - levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν n)) (max x 0) ω|
        ≤ 2 * ((2 : ℝ)⁻¹) ^ n :=
          abs_annulusPath_sub_le hd hν hraw T hbound (hNN₀.trans hn) hnm hmax
      _ ≤ 2 * ((2 : ℝ)⁻¹) ^ N := by
          have : ((2 : ℝ)⁻¹) ^ n ≤ ((2 : ℝ)⁻¹) ^ N :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
          linarith [this, (by positivity : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ N)]
      _ < ε := hNε

/-- For a raw-good `ω` and `s ≥ 0`, the annulus paths converge at `s` (a pointwise consequence of
uniform Cauchyness plus completeness). -/
private lemma exists_tendsto_annulusPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hraw : levySmallJumpRaw hd hν ω) {s : ℝ} (hs : 0 ≤ s) :
    ∃ L, Tendsto (fun j => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) s ω)
      atTop (𝓝 L) := by
  obtain ⟨T, hT⟩ := exists_nat_gt s
  have hcauchy := (uniformCauchySeqOn_annulusPath_max hd hν hraw T).cauchySeq
    (Set.mem_Iic.mpr hT.le)
  rw [max_eq_left hs] at hcauchy
  exact cauchySeq_tendsto_of_complete hcauchy

/-! ### The compensated small-jump path

`levySmallJumpPath hd hν t ω` is the almost-sure uniform limit of the compensated banded jump paths
over the growing annuli, gated to the good set (and to `t ≥ 0` via `max t 0`). Off the good set it is
identically `0`; on the good set it is the genuine limit, càdlàg for every `ω`. -/

open scoped Classical in
/-- The **compensated small-jump path**: the gated `atTop` limit of the annulus paths. The `max t 0`
guarantees the negative-time slice is constantly `0` (there the drift lines need not converge). -/
noncomputable def levySmallJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (t : ℝ) (ω : Ω) : ℝ :=
  Filter.limUnder Filter.atTop (fun j =>
    if ω ∈ levySmallJumpGoodSet hd hν
    then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω else 0)

open scoped Classical in
/-- On the good set, the annulus paths at `max t 0` converge to the compensated small-jump path. -/
private lemma tendsto_annulusPath_max_levySmallJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hω : ω ∈ levySmallJumpGoodSet hd hν) (t : ℝ) :
    Tendsto (fun j => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω)
      atTop (𝓝 (levySmallJumpPath hd hν t ω)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_annulusPath hd hν
    (levySmallJumpRaw_of_mem_goodSet hd hν hω) (le_max_right t 0)
  have hval : levySmallJumpPath hd hν t ω = L := by
    simp only [levySmallJumpPath]
    rw [show (fun j => if ω ∈ levySmallJumpGoodSet hd hν
        then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω else 0)
        = fun j => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω
        from by funext j; rw [if_pos hω]]
    exact hL.limUnder_eq
  rw [hval]; exact hL

/-- On the good set, the annulus paths at `t ≥ 0` converge to the compensated small-jump path. -/
theorem tendsto_levyBandPath_levySmallJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {ω : Ω} (hω : ω ∈ levySmallJumpGoodSet hd hν) {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto (fun j => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) t ω)
      Filter.atTop (nhds (levySmallJumpPath hd hν t ω)) := by
  have h := tendsto_annulusPath_max_levySmallJumpPath hd hν hω t
  rwa [max_eq_left ht] at h

open scoped Classical in
/-- The compensated small-jump path vanishes at time zero: every approximant is `0` there. -/
@[simp] theorem levySmallJumpPath_zero
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    levySmallJumpPath hd hν 0 = 0 := by
  funext ω
  have hconst : (fun j => if ω ∈ levySmallJumpGoodSet hd hν
      then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max (0 : ℝ) 0) ω else 0)
      = fun _ => (0 : ℝ) := by
    funext j
    simp only [max_self]
    split <;> simp [levyBandPath_zero]
  simp only [levySmallJumpPath, Pi.zero_apply]
  rw [hconst]
  exact tendsto_const_nhds.limUnder_eq

open scoped Classical in
/-- The compensated small-jump path is a measurable function of the sample point at each time: the
gated approximants are measurable and converge pointwise for every `ω`. -/
theorem measurable_levySmallJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) (t : ℝ) :
    Measurable (levySmallJumpPath hd hν t) := by
  set g : ℕ → Ω → ℝ := fun j ω =>
    if ω ∈ levySmallJumpGoodSet hd hν
    then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω else 0 with hg
  have hgmeas : ∀ j, Measurable (g j) := fun j =>
    Measurable.ite (measurableSet_levySmallJumpGoodSet hd hν)
      (measurable_levyBandPath hd.measurable_count hd.measurable_point
        (measurableSet_levyAnnulus _) (max t 0)) measurable_const
  have htend : ∀ ω, Tendsto (fun j => g j ω) atTop (𝓝 (levySmallJumpPath hd hν t ω)) := by
    intro ω
    by_cases hω : ω ∈ levySmallJumpGoodSet hd hν
    · simpa only [hg, if_pos hω] using tendsto_annulusPath_max_levySmallJumpPath hd hν hω t
    · have hval : levySmallJumpPath hd hν t ω = 0 := by
        simp only [levySmallJumpPath]
        rw [show (fun j => if ω ∈ levySmallJumpGoodSet hd hν
            then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω else 0)
            = fun _ => (0 : ℝ) from by funext j; rw [if_neg hω]]
        exact tendsto_const_nhds.limUnder_eq
      simp only [hg, if_neg hω, hval]
      exact tendsto_const_nhds
  exact measurable_of_tendsto_metrizable hgmeas (tendsto_pi_nhds.mpr htend)

open scoped Classical in
/-- **The compensated small-jump path is càdlàg for every `ω`.** Off the good set the path is
identically `0` (hence càdlàg by `isCadlag_const`); this unconditional gating is exactly why the
statement holds for *every* `ω`, not merely almost every one. On the good set it is the uniform-on-
compacts limit of the càdlàg annulus paths (composed with `max · 0`), hence càdlàg by
`isCadlag_of_tendstoUniformlyOn`. -/
theorem isCadlag_levySmallJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    ∀ ω, IsCadlag (fun t : ℝ => levySmallJumpPath hd hν t ω) := by
  intro ω
  by_cases hω : ω ∈ levySmallJumpGoodSet hd hν
  · have hraw := levySmallJumpRaw_of_mem_goodSet hd hν hω
    refine isCadlag_of_tendstoUniformlyOn
      (F := fun j t => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω)
      (fun j => ?_) (fun T => ?_)
    · exact isCadlag_comp_max_zero (isCadlag_levyBandPath_of_finite ω (fun T => hraw.1 T j))
        (by simp [levyBandPath_zero])
    · obtain ⟨T', hT'⟩ := exists_nat_ge T
      exact ((uniformCauchySeqOn_annulusPath_max hd hν hraw T').mono
        (Set.Iic_subset_Iic.mpr hT')).tendstoUniformlyOn_of_tendsto
        fun x _ => tendsto_annulusPath_max_levySmallJumpPath hd hν hω x
  · have hzero : (fun t : ℝ => levySmallJumpPath hd hν t ω) = fun _ => (0 : ℝ) := by
      funext t
      simp only [levySmallJumpPath]
      rw [show (fun j => if ω ∈ levySmallJumpGoodSet hd hν
          then levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) (max t 0) ω else 0)
          = fun _ => (0 : ℝ) from by funext j; rw [if_neg hω]]
      exact tendsto_const_nhds.limUnder_eq
    rw [hzero]; exact isCadlag_const

/-! ### The limit path is a modification of the small-jump integral

The truncation elements — the compensated Poisson integrals of the band test functions over
`(0, t] × levyAnnulus (levyTruncationSeq hν j)` — converge in `L²(μ)` to the compensated
small-jump integral `levyCompensatedSmallJump hd hν t`: the distance is the complementary-slice
seminorm (`eLpNorm_smallJumpBand_sub_bandFun`), whose square is at most `t · 16⁻ʲ` by the
truncation spec. `L²` convergence upgrades to convergence in measure and hence to almost-everywhere
convergence along a subsequence; along it the pathwise annulus approximants converge to both the
compensated small-jump path (the pointwise limit on the good set) and the `L²` element, so the two
agree almost everywhere at each fixed time `t ≥ 0`. -/

/-- The **truncation element** at annulus step `j`: the compensated Poisson integral of the band
test function over `(0, t] × levyAnnulus (levyTruncationSeq hν j)`, as an element of `L²(μ)`. -/
private noncomputable def levyAnnulusElement [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (t : ℝ) (j : ℕ) : Lp ℝ 2 μ :=
  compensatedPoissonIntegral hd ((memLp_two_bandFun
    (measurableSet_levyAnnulus (levyTruncationSeq hν j))
    (levyAnnulus_subset (levyTruncationSeq hν j))
    (levyAnnulus_finite_mass hν (levyTruncationSeq hν j)) 0 t).toLp _)

/-- The pathwise annulus approximant agrees almost everywhere with the truncation element (the
Task-3 `L²` anchor at the annulus band). -/
private lemma levyBandPath_ae_eq_levyAnnulusElement [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    (fun ω => levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) t ω)
      =ᵐ[μ] levyAnnulusElement hd hν t j :=
  levyBandPath_ae_eq_compensated hd (measurableSet_levyAnnulus (levyTruncationSeq hν j))
    (levyAnnulus_subset (levyTruncationSeq hν j))
    (levyAnnulus_finite_mass hν (levyTruncationSeq hν j)) ht

/-- **`L²` convergence of the truncation elements.** The `L²(μ)` distance from the truncation
element at step `j` to the compensated small-jump integral is the seminorm of the band indicator
over the complementary slice `(0, t] × ((-1, 1) \ levyAnnulus (levyTruncationSeq hν j))`, whose
square is at most `t · 16⁻ʲ`; hence the distance vanishes as `j → ∞`. -/
private lemma tendsto_eLpNorm_levyAnnulusElement_sub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun j => eLpNorm
        (⇑(levyAnnulusElement hd hν t j) - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ)
      atTop (𝓝 0) := by
  -- the distance flips to the `Lp` difference of the elements
  have hcoe : ∀ j : ℕ,
      eLpNorm (⇑(levyAnnulusElement hd hν t j) - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ
        = eLpNorm (⇑(levyCompensatedSmallJump hd hν t - levyAnnulusElement hd hν t j)) 2 μ := by
    intro j
    rw [← neg_sub (⇑(levyCompensatedSmallJump hd hν t)) (⇑(levyAnnulusElement hd hν t j)),
      eLpNorm_neg]
    exact (eLpNorm_congr_ae (Lp.coeFn_sub _ _)).symm
  -- the `Lp` distance is the complementary-slice seminorm
  have hdist : ∀ j : ℕ,
      eLpNorm (⇑(levyCompensatedSmallJump hd hν t - levyAnnulusElement hd hν t j)) 2 μ
        = eLpNorm ((Set.Ioc 0 t ×ˢ (Set.Ioo (-1 : ℝ) 1
              \ levyAnnulus (levyTruncationSeq hν j))).indicator fun p : ℝ × ℝ => p.2) 2
            (volume.prod ν) := fun j =>
    eLpNorm_smallJumpBand_sub_bandFun hd hν 0 t
      (measurableSet_levyAnnulus (levyTruncationSeq hν j))
      (levyAnnulus_subset (levyTruncationSeq hν j))
      (levyAnnulus_finite_mass hν (levyTruncationSeq hν j))
  -- squared distance bounded by the geometric tail moment
  have hsq_le : ∀ j : ℕ,
      (eLpNorm (⇑(levyAnnulusElement hd hν t j)
          - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ) ^ 2
        ≤ ENNReal.ofReal t * (16 : ℝ≥0∞)⁻¹ ^ j := by
    intro j
    rw [hcoe j, hdist j,
      eLpNorm_sq_bandFun (measurableSet_Ioo.diff (measurableSet_levyAnnulus _)) 0 t, sub_zero]
    exact mul_le_mul_right ((levyTruncationSeq_spec hν).2 j) _
  have hne : ∀ j : ℕ,
      eLpNorm (⇑(levyAnnulusElement hd hν t j) - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ ≠ ⊤ :=
    fun j => by rw [hcoe j]; exact Lp.eLpNorm_ne_top _
  -- the real-valued distances are squeezed by the geometric envelope `√t · 4⁻ʲ`
  have htoReal_le : ∀ j : ℕ,
      (eLpNorm (⇑(levyAnnulusElement hd hν t j)
          - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal
        ≤ Real.sqrt t * ((4 : ℝ)⁻¹) ^ j := by
    intro j
    have hbne : ENNReal.ofReal t * (16 : ℝ≥0∞)⁻¹ ^ j ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.pow_lt_top (ENNReal.inv_lt_top.mpr (by norm_num))).ne
    have hsq' : ((eLpNorm (⇑(levyAnnulusElement hd hν t j)
          - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal) ^ 2
        ≤ t * ((16 : ℝ)⁻¹) ^ j := by
      rw [← ENNReal.toReal_pow]
      calc ((eLpNorm (⇑(levyAnnulusElement hd hν t j)
              - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ) ^ 2).toReal
          ≤ (ENNReal.ofReal t * (16 : ℝ≥0∞)⁻¹ ^ j).toReal :=
            ENNReal.toReal_mono hbne (hsq_le j)
        _ = t * ((16 : ℝ)⁻¹) ^ j := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht, ENNReal.toReal_pow,
              ENNReal.toReal_inv]
            norm_num
    have hsqrt16 : Real.sqrt (((16 : ℝ)⁻¹) ^ j) = ((4 : ℝ)⁻¹) ^ j := by
      have h4 : (((4 : ℝ)⁻¹) ^ j) ^ 2 = ((16 : ℝ)⁻¹) ^ j := by
        rw [← pow_mul, mul_comm, pow_mul, show ((4 : ℝ)⁻¹) ^ 2 = (16 : ℝ)⁻¹ by norm_num]
      rw [← h4, Real.sqrt_sq (by positivity)]
    calc (eLpNorm (⇑(levyAnnulusElement hd hν t j)
            - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal
        = Real.sqrt (((eLpNorm (⇑(levyAnnulusElement hd hν t j)
            - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal) ^ 2) :=
          (Real.sqrt_sq ENNReal.toReal_nonneg).symm
      _ ≤ Real.sqrt (t * ((16 : ℝ)⁻¹) ^ j) := Real.sqrt_le_sqrt hsq'
      _ = Real.sqrt t * ((4 : ℝ)⁻¹) ^ j := by rw [Real.sqrt_mul ht, hsqrt16]
  have hgeo : Tendsto (fun j : ℕ => Real.sqrt t * ((4 : ℝ)⁻¹) ^ j) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹) (by norm_num)).const_mul (Real.sqrt t)
    simpa using h
  have htoReal : Tendsto (fun j => (eLpNorm (⇑(levyAnnulusElement hd hν t j)
      - ⇑(levyCompensatedSmallJump hd hν t)) 2 μ).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun j => ENNReal.toReal_nonneg) htoReal_le hgeo
  exact (ENNReal.tendsto_toReal_iff hne (by simp)).mp (by simpa using htoReal)

/-- **The compensated small-jump path is a modification of the small-jump integral.** For each
fixed time `t ≥ 0`, the compensated small-jump path `levySmallJumpPath hd hν t` agrees
`μ`-almost everywhere with the `L²` small-jump element `levyCompensatedSmallJump hd hν t`.

This is a per-time almost-everywhere identification: the null set may depend on `t`, and no
process-level (uniform-in-`t`) statement is claimed. The truncation elements converge to the
small-jump element in `L²(μ)`, hence in measure, hence almost everywhere along a subsequence
`ns`; on the intersection of the good set with the countably many almost-sure events, the annulus
paths along `ns` converge to both `levySmallJumpPath hd hν t ω` and
`levyCompensatedSmallJump hd hν t ω`, and limits in `ℝ` are unique. -/
theorem levySmallJumpPath_ae_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t) :
    levySmallJumpPath hd hν t =ᵐ[μ] levyCompensatedSmallJump hd hν t := by
  -- `L²` convergence upgrades to convergence in measure, hence a.e. along a subsequence
  have hTIM : TendstoInMeasure μ (fun j => ⇑(levyAnnulusElement hd hν t j)) atTop
      ⇑(levyCompensatedSmallJump hd hν t) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (fun j => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      (tendsto_eLpNorm_levyAnnulusElement_sub hd hν ht)
  obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae
  -- glue the countably many almost-sure events
  have hpath : ∀ᵐ ω ∂μ, ∀ j : ℕ,
      levyBandPath K X ν (levyAnnulus (levyTruncationSeq hν j)) t ω
        = levyAnnulusElement hd hν t j ω := by
    rw [ae_all_iff]
    exact fun j => levyBandPath_ae_eq_levyAnnulusElement hd hν ht j
  filter_upwards [ae_mem_levySmallJumpGoodSet hd hν, hpath, hae] with ω hgood hp hconv
  -- the annulus paths along the subsequence converge to the compensated small-jump path ...
  have h1 : Tendsto (fun i => levyBandPath K X ν
      (levyAnnulus (levyTruncationSeq hν (ns i))) t ω) atTop
      (𝓝 (levySmallJumpPath hd hν t ω)) :=
    (tendsto_levyBandPath_levySmallJumpPath hd hν hgood ht).comp hns.tendsto_atTop
  -- ... and to the small-jump element, through the per-`j` a.e. identifications
  have h2 : Tendsto (fun i => levyBandPath K X ν
      (levyAnnulus (levyTruncationSeq hν (ns i))) t ω) atTop
      (𝓝 (levyCompensatedSmallJump hd hν t ω)) :=
    hconv.congr fun i => (hp (ns i)).symm
  exact tendsto_nhds_unique h1 h2

/-! ### The càdlàg pure-jump process

Assembling the constant drift, the compound-Poisson large-jump sum, and the compensated small-jump
*path* yields a single process `levyJumpPath` indexed by `ℝ≥0`. It shares its drift and large-jump
summands literally with the law-level `levyJumpProcess`, replacing only the `L²` small-jump element
by the pathwise `levySmallJumpPath` — an a.e.-equal per-time modification. The modification carries
over the entire law-level Lévy structure (independent stationary increments, marginal characteristic
function `exp (t · ψ)`) while adding genuine sample-path regularity: almost every path is càdlàg. The
result is a genuine `IsLevyProcess` for the pure-jump triple `(b, 0, ν)`. -/

/-- The **càdlàg pure-jump process**: drift plus large-jump sum plus the compensated small-jump path,
indexed by `ℝ≥0`. Its drift and large-jump summands are literally those of `levyJumpProcess`; the
small-jump summand is the pathwise `levySmallJumpPath`, an a.e. modification of the `L²` element used
there. Unlike `levyJumpProcess`, this process has almost-surely càdlàg sample paths. -/
noncomputable def levyJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  b * (t : ℝ) + levyLargeJumpSum K X (t : ℝ) ω + levySmallJumpPath hd hν (t : ℝ) ω

/-- The jump path starts at zero: at `t = 0` the drift is scaled by `0`, and both the large-jump sum
and the compensated small-jump path vanish, for *every* `ω` (a literal function equality). -/
@[simp] theorem levyJumpPath_zero
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) (b : ℝ) :
    levyJumpPath hd hν b 0 = fun _ => 0 := by
  funext ω
  simp only [levyJumpPath, NNReal.coe_zero, mul_zero, levyLargeJumpSum_zero,
    levySmallJumpPath_zero, Pi.zero_apply, add_zero]

/-- The jump path is a measurable function of the sample point at each time. -/
theorem measurable_levyJumpPath
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) : Measurable (levyJumpPath hd hν b t) :=
  (measurable_const.add
    (measurable_levyLargeJumpSum hd.measurable_count hd.measurable_point)).add
    (measurable_levySmallJumpPath hd hν _)

/-- **The jump path is a modification of the jump process.** At each fixed time `t`, the pathwise
`levyJumpPath` agrees `μ`-almost everywhere with the law-level `levyJumpProcess`: the drift and
large-jump summands are shared syntactically, and the small-jump summands agree a.e. by
`levySmallJumpPath_ae_eq` (the null set may depend on `t`). -/
theorem levyJumpPath_ae_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) :
    levyJumpPath hd hν b t =ᵐ[μ] levyJumpProcess hd hν b t := by
  filter_upwards [levySmallJumpPath_ae_eq hd hν (NNReal.coe_nonneg t)] with ω hω
  show b * (t : ℝ) + levyLargeJumpSum K X (t : ℝ) ω + levySmallJumpPath hd hν (t : ℝ) ω
    = b * (t : ℝ) + levyLargeJumpSum K X (t : ℝ) ω + levyCompensatedSmallJump hd hν (t : ℝ) ω
  rw [hω]

/-- **Almost every sample path of the jump path is càdlàg.** On the almost-sure event where the
large-jump sum is càdlàg, the real-time path `s ↦ b · s + (large-jump sum) + (small-jump path)` is
càdlàg — the drift is continuous, the large-jump sum is càdlàg there, and the small-jump path is
càdlàg for *every* `ω` — and càdlàg regularity is preserved under precomposition with the coercion
`ℝ≥0 → ℝ`. -/
theorem ae_isCadlag_levyJumpPath [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) (b : ℝ) :
    ∀ᵐ ω ∂μ, IsCadlag (fun t : ℝ≥0 => levyJumpPath hd hν b t ω) := by
  filter_upwards [ae_isCadlag_levyLargeJumpSum hd hν] with ω hω
  have hdrift : IsCadlag (fun s : ℝ => b * s) :=
    (by fun_prop : Continuous fun s : ℝ => b * s).isCadlag
  have hcadReal : IsCadlag (fun s : ℝ =>
      b * s + levyLargeJumpSum K X s ω + levySmallJumpPath hd hν s ω) :=
    (hdrift.add hω).add (isCadlag_levySmallJumpPath hd hν ω)
  simpa only [levyJumpPath] using isCadlag_comp_nnrealCoe hcadReal

/-- **The pure-jump process is a genuine Lévy process.** The pathwise `levyJumpPath` realizes the
pure-jump triple `(b, 0, ν)` as a bona fide `IsLevyProcess`: it starts at the origin (literal zero
start), has almost-surely càdlàg sample paths, and — being an a.e. modification of the law-level
`levyJumpProcess` at every time — inherits its independent and stationary increments. Independence
transfers along the a.e.-equal increment families (`iIndepFun_congr`); stationarity transfers because
identical distribution is preserved under a.e. equality (`IdentDistrib.of_ae_eq` and transitivity). -/
theorem isLevyProcess_levyJumpPath [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) : IsLevyProcess (levyJumpPath hd hν b) μ where
  start_zero := levyJumpPath_zero hd hν b
  indep_increments := by
    intro n τ hτmono
    have hae : ∀ k : Fin n,
        increment (levyJumpProcess hd hν b) (τ k.castSucc) (τ k.succ)
          =ᵐ[μ] increment (levyJumpPath hd hν b) (τ k.castSucc) (τ k.succ) := by
      intro k
      filter_upwards [levyJumpPath_ae_eq hd hν b (τ k.castSucc),
        levyJumpPath_ae_eq hd hν b (τ k.succ)] with ω h1 h2
      simp only [increment_apply]
      rw [h1, h2]
    exact (iIndepFun_congr hae).mp
      (hasIndependentIncrements_levyJumpProcess hd hν b n τ hτmono)
  stationary_increments := by
    intro s h
    have hmeas : ∀ u : ℝ≥0, Measurable (levyJumpPath hd hν b u) :=
      fun u => measurable_levyJumpPath hd hν b u
    have haem_incr : ∀ p q : ℝ≥0, AEMeasurable (increment (levyJumpPath hd hν b) p q) μ :=
      fun p q => (measurable_increment (hmeas p) (hmeas q)).aemeasurable
    have hae : ∀ p q : ℝ≥0,
        increment (levyJumpPath hd hν b) p q =ᵐ[μ] increment (levyJumpProcess hd hν b) p q := by
      intro p q
      filter_upwards [levyJumpPath_ae_eq hd hν b p, levyJumpPath_ae_eq hd hν b q] with ω h1 h2
      simp only [increment_apply]
      rw [h1, h2]
    exact ((IdentDistrib.of_ae_eq (haem_incr s (s + h)) (hae s (s + h))).trans
      (hasStationaryIncrements_levyJumpProcess hd hν b s h)).trans
      (IdentDistrib.of_ae_eq (haem_incr 0 h) (hae 0 h)).symm
  cadlag_ae := ae_isCadlag_levyJumpPath hd hν b

/-- The fixed-time marginal law of the jump path has characteristic function
`exp (t · ψ_{(b,0,ν)})` — identical to that of `levyJumpProcess`, since the two agree in law
at each time (`levyJumpPath_ae_eq`). -/
theorem charFun_map_levyJumpPath [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (levyJumpPath hd hν b t)) ξ
      = Complex.exp (((t : ℝ) : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
  rw [Measure.map_congr (levyJumpPath_ae_eq hd hν b t), charFun_map_levyJumpProcess hd hν b t ξ]

/-- **Every pure-jump Lévy triple is realized by a genuine Lévy process.** For every drift `b` and
Lévy measure `ν`, there is a probability space `(Ω, μ)` and a process `X : ℝ≥0 → Ω → ℝ` such that:

* `X` is an `IsLevyProcess` for `μ` — it starts at the origin (literal zero start), has almost-surely
  càdlàg sample paths, and has independent and stationary increments;
* every time-slice `X t` is measurable;
* the fixed-time marginal law of `X t` has characteristic function
  `exp (t · ψ_{(b,0,ν)} ξ)`, the Lévy–Khintchine exponent of the pure-jump triple `(b, 0, ν)` with
  **zero** Gaussian variance.

This is the headline realization theorem for the pure-jump component. It does **not** assert the full
Lévy–Itô decomposition, any uniqueness statement, or anything about a Brownian part. The space is the
canonical Poisson-point family at intensity `volume.prod ν` (σ-finite via `IsLevyMeasure.sigmaFinite`),
and `X` is the pathwise `levyJumpPath`; the four conclusions are the Task-7 theorems
`isLevyProcess_levyJumpPath`, `measurable_levyJumpPath`, and `charFun_map_levyJumpPath`. -/
theorem exists_isLevyProcess_pureJump (b : ℝ) {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure μ ∧ IsLevyProcess X μ ∧ (∀ t, Measurable (X t)) ∧
      ∀ (t : ℝ≥0) (ξ : ℝ), charFun (μ.map (X t)) ξ =
        Complex.exp (((t : ℝ) : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
  haveI := hν.sigmaFinite
  obtain ⟨Ω, mΩ, μ, K, X, hprob, hd⟩ :=
    exists_isPoissonPointFamily ((volume : Measure ℝ).prod ν)
  exact ⟨Ω, mΩ, μ, levyJumpPath hd hν b, hprob,
    isLevyProcess_levyJumpPath hd hν b,
    fun t => measurable_levyJumpPath hd hν b t,
    fun t ξ => charFun_map_levyJumpPath hd hν b t ξ⟩

/-- The characteristic exponent of the jump path is the Lévy–Khintchine exponent of the pure-jump
triple `(b, 0, ν)`. Since each marginal has characteristic function `exp (t · ψ ξ)`, for small
`t > 0` the principal-branch logarithm collapses (`Complex.log_exp`, valid once `|t · Im ψ ξ| < π`,
which holds eventually as `t → 0⁺`), so the defining quotient `log(φ_t ξ) / t` is eventually the
constant `ψ ξ`. -/
theorem charExponent_levyJumpPath [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (ξ : ℝ) :
    (isLevyProcess_levyJumpPath hd hν b).charExponent ξ
      = (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ := by
  set ψ : ℂ := (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ with hψ
  simp only [IsLevyProcess.charExponent]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  have hcont : Filter.Tendsto (fun t : ℝ≥0 => (t : ℝ) * ψ.im) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ≥0 => (t : ℝ) * ψ.im) :=
      NNReal.continuous_coe.mul continuous_const
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    hcont.eventually (Metric.ball_mem_nhds (0 : ℝ) Real.pi_pos)] with t (ht : 0 < t) htim
  have hne : ((t : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast NNReal.coe_ne_zero.mpr (ne_of_gt ht)
  have habs : |(t : ℝ) * ψ.im| < Real.pi := by simpa [Real.dist_eq] using htim
  obtain ⟨h1, h2⟩ := abs_lt.mp habs
  have him : (((t : ℝ) : ℂ) * ψ).im = (t : ℝ) * ψ.im := by simp [Complex.mul_im]
  have hlog : Complex.log (Complex.exp (((t : ℝ) : ℂ) * ψ)) = ((t : ℝ) : ℂ) * ψ :=
    Complex.log_exp (by rw [him]; exact h1) (by rw [him]; exact le_of_lt h2)
  rw [charFun_map_levyJumpPath hd hν b t ξ, hlog, eq_div_iff hne]; ring

end ProbabilityTheory
