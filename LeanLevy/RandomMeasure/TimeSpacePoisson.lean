/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import LeanLevy.RandomMeasure.PoissonRandomMeasure
import LeanLevy.RandomMeasure.PoissonCompensated
import LeanLevy.Levy.LevyMeasure

/-!
# Time-indexed Poisson random measures

Specialize the abstract Poisson random measure to the product space `ℝ × E`, with `ℝ` read as time
and `E` as the mark space, under the product intensity `volume.prod m`. The evaluation on a
space-time band `(s, t] × A` is the number of realized marks in `A` occurring during the time
window `(s, t]`; the running count `poissonTimeCount K X A t` is its value on the initial window
`(0, t]`.

## Main definitions

* `ProbabilityTheory.poissonTimeCount` — the running count of realized points in `(0, t] × A`.
* `ProbabilityTheory.levyCompensatedSmallJump` — the compensated small-jump integral of a Lévy
  measure at time `t`, as an element of `L²(μ)`.

## Main results

* `ProbabilityTheory.measurable_poissonTimeCount` — the running count is a measurable function of the
  sample point.
* `ProbabilityTheory.map_poissonRandomMeasure_band` — the count in a band `(s, t] × A` is Poisson with
  mean `(t - s) · m A`.
* `ProbabilityTheory.map_poissonTimeCount` — the running count `poissonTimeCount K X A t` is Poisson
  with mean `t · m A`.
* `ProbabilityTheory.poissonTimeCount_add` — the running count is pathwise additive over consecutive
  time windows.
* `ProbabilityTheory.iIndepFun_poissonRandomMeasure_bands` — **independent increments**: the counts
  over consecutive disjoint time bands are mutually independent.
* `ProbabilityTheory.memLp_two_smallJumpFun` — the small-jump test function is square-integrable
  against `volume.prod ν` for any Lévy measure `ν`.
* `ProbabilityTheory.memLp_two_smallJumpBandFun` — the same for the band test function supported on a
  time window `(s, t]`.
* `ProbabilityTheory.levyCompensatedSmallJump_sub` — the increment of the compensated small-jump
  integral over `(s, t]` is the compensated integral of the band test function.
* `ProbabilityTheory.integral_levyCompensatedSmallJump` — the compensated small-jump integral has
  mean zero.
* `ProbabilityTheory.eLpNorm_sq_levyCompensatedSmallJump` — **Campbell's isometry**: its second
  moment is `t · ∫_{(-1,1)} x² dν`.
* `ProbabilityTheory.map_levyLargeJumpCount` — the number of large jumps up to time `t` is Poisson
  with mean `t · ν {x | 1 ≤ |x|}`.
* `ProbabilityTheory.levyLargeJumpSum` — the sum of the jump sizes of the realized marks in the band
  `(0, t] × {x | 1 ≤ |x|}`, as a series of piece sums.
* `ProbabilityTheory.measurable_levyLargeJumpSum` — the large-jump sum is a measurable function of the
  sample point.
* `ProbabilityTheory.levyLargeJumpSum_ae_eq_integral` — almost surely the large-jump sum is the
  Bochner integral of the jump size against the random measure over the band.
* `ProbabilityTheory.integral_levyLargeJumpSum` — **Campbell's formula**: under a first moment on the
  large jumps, the mean of the large-jump sum is `t · ∫_{|x|≥1} x dν`.
* `ProbabilityTheory.levyLargeJumpSum_ae_eq_toReal_sub` — the large-jump sum as a difference of
  Lebesgue integrals of the positive and negative jump parts.

Every statement is read off the abstract superposition and disjoint-family independence laws of
`poissonRandomMeasure` on `ℝ × E`; the band mass factorizes as `volume (Ioc s t) * m A` through
`Measure.prod_prod`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × E} {m : Measure E} [SigmaFinite m] {μ : Measure Ω} {A : Set E} {s t : ℝ}

omit [Nonempty E] in
/-- The `volume.prod m`-mass of a space-time band factorizes: `(volume.prod m) ((s, t] ×ˢ A)` is the
time length `t - s` times the mark mass `m A`. -/
theorem volume_prod_Ioc_prod (s t : ℝ) (A : Set E) :
    (volume.prod m) (Set.Ioc s t ×ˢ A) = ENNReal.ofReal (t - s) * m A := by
  rw [Measure.prod_prod, Real.volume_Ioc]

omit [Nonempty E] in
/-- Each space-time band has finite `volume.prod m`-mass whenever the mark set has finite mass. -/
theorem volume_prod_Ioc_prod_lt_top (hfin : m A < ⊤) :
    (volume.prod m) (Set.Ioc s t ×ˢ A) < ⊤ := by
  rw [volume_prod_Ioc_prod]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The running count of points of the time-space random measure: realized points in `(0, t] × A`. -/
noncomputable def poissonTimeCount (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (A : Set E) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  poissonRandomMeasure K X ω (Set.Ioc 0 t ×ˢ A)

omit [Nonempty E] [SigmaFinite m] in
/-- The running count is a measurable function of the sample point. -/
theorem measurable_poissonTimeCount (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) :
    Measurable (poissonTimeCount K X A t) :=
  measurable_poissonRandomMeasure_apply hK hX (measurableSet_Ioc.prod hA)

/-- Band evaluation law: the count in `(s, t] × A` is Poisson with mean `(t - s) · m A`. -/
theorem map_poissonRandomMeasure_band [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A)
    (hfin : m A < ⊤) (_hst : s ≤ t) :
    μ.map (fun ω => poissonRandomMeasure K X ω (Set.Ioc s t ×ˢ A))
      = (poissonMeasure (ENNReal.ofReal (t - s) * m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  rw [map_poissonRandomMeasure_apply hd (measurableSet_Ioc.prod hA)
    (volume_prod_Ioc_prod_lt_top hfin), volume_prod_Ioc_prod]

/-- The running count `poissonTimeCount K X A t` is Poisson with mean `t · m A`. -/
theorem map_poissonTimeCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A)
    (hfin : m A < ⊤) (ht : 0 ≤ t) :
    μ.map (poissonTimeCount K X A t)
      = (poissonMeasure (ENNReal.ofReal t * m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  have h := map_poissonRandomMeasure_band (s := 0) hd hA hfin ht
  rwa [sub_zero] at h

omit [Nonempty E] [SigmaFinite m] [MeasurableSpace Ω] in
/-- Pathwise additivity of the running count over consecutive time bands. -/
theorem poissonTimeCount_add (hA : MeasurableSet A) (h0s : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    poissonTimeCount K X A t ω
      = poissonTimeCount K X A s ω + poissonRandomMeasure K X ω (Set.Ioc s t ×ˢ A) := by
  unfold poissonTimeCount
  rw [← Set.Ioc_union_Ioc_eq_Ioc h0s hst, Set.union_prod,
    measure_union (Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le le_rfl) A A)
      (measurableSet_Ioc.prod hA)]

omit [Nonempty E] [SigmaFinite m] [MeasurableSpace E] in
/-- Two time bands over disjoint windows (ordered `i < j`) evaluate on disjoint space-time sets. -/
private lemma disjoint_band {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t) (A : Set E)
    {i j : Fin n} (hij : i < j) :
    Disjoint (Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A)
      (Set.Ioc (t j.castSucc) (t j.succ) ×ˢ A) := by
  refine Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (ht ?_)) A A
  have hv : (i : ℕ) < (j : ℕ) := hij
  rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
  omega

/-- **Independent increments.** Counts over disjoint consecutive time bands are mutually
independent. -/
theorem iIndepFun_poissonRandomMeasure_bands [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A)
    (hfin : m A < ⊤) {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t) :
    iIndepFun (fun (i : Fin n) ω =>
      poissonRandomMeasure K X ω (Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A)) μ := by
  refine iIndepFun_poissonRandomMeasure_apply hd (fun i => measurableSet_Ioc.prod hA)
    (fun i => volume_prod_Ioc_prod_lt_top hfin) ?_
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact disjoint_band ht A h
  · exact (disjoint_band ht A h).symm

/-! ### The compensated small-jump integral of a Lévy measure

Specializing the mark space to `E = ℝ` and the intensity to `volume.prod ν` for a **Lévy measure**
`ν`, the small-jump test function `1_{(0,t] × (-1,1)}(s, x) · x` is square-integrable, so its
compensated Poisson integral `levyCompensatedSmallJump` is a genuine `L²(μ)` random variable. It
has mean zero and second moment `t · ∫_{(-1,1)} x² dν` (Campbell's isometry). The number of large
jumps up to time `t` is Poisson with mean `t · ν {|x| ≥ 1}`. -/

section LevyIntensity

variable {ν : Measure ℝ} [SigmaFinite ν] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ} {μ : Measure Ω}

/-- Squaring the `L²` seminorm cancels the outer root: `(‖g‖₂)² = ∫⁻ ‖g‖ₑ² `. -/
private lemma eLpNorm_two_sq {α : Type*} {mα : MeasurableSpace α} {τ : Measure α} (g : α → ℝ) :
    (eLpNorm g 2 τ) ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂τ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num,
    ← ENNReal.rpow_natCast (_ ^ (1 / (2 : ℝ))) 2, ← ENNReal.rpow_mul,
    show (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 from by norm_num, ENNReal.rpow_one]

omit [SigmaFinite ν] in
/-- The pointwise square of the small-jump indicator integrates to the set-lintegral of `x²`. -/
private lemma lintegral_enorm_rpow_smallJump (s t : ℝ) :
    ∫⁻ p, ‖(Set.Ioc s t ×ˢ Set.Ioo (-1) 1).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ)
        ∂(volume.prod ν)
      = ∫⁻ p in Set.Ioc s t ×ˢ Set.Ioo (-1) 1, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν) := by
  rw [← lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]

/-- Tonelli for the small-jump band: `∫_{(s,t]×(-1,1)} x² = (t - s) · ∫_{(-1,1)} x²`. -/
private lemma setLIntegral_smallJump_snd_sq (s t : ℝ) :
    ∫⁻ p in Set.Ioc s t ×ˢ Set.Ioo (-1) 1, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν)
      = ENNReal.ofReal (t - s) * ∫⁻ x in Set.Ioo (-1) 1, ENNReal.ofReal (x ^ 2) ∂ν := by
  rw [← Measure.prod_restrict,
    lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ 2))
      (measurable_snd.pow_const 2).ennreal_ofReal.aemeasurable]
  have hinner : ∀ r : ℝ,
      ∫⁻ x, ENNReal.ofReal ((r, x).2 ^ 2) ∂(ν.restrict (Set.Ioo (-1) 1))
        = ∫⁻ x in Set.Ioo (-1) 1, ENNReal.ofReal (x ^ 2) ∂ν := fun _ => rfl
  rw [lintegral_congr hinner, setLIntegral_const, Real.volume_Ioc, mul_comm]

omit [SigmaFinite ν] in
/-- The set-lintegral of `x²` over `(-1,1)` against a Lévy measure is finite. -/
private lemma lintegral_Ioo_sq_lt_top (hν : IsLevyMeasure ν) :
    ∫⁻ x in Set.Ioo (-1) 1, ENNReal.ofReal (x ^ 2) ∂ν < ⊤ := by
  refine lt_of_le_of_lt ?_ hν.2
  rw [← lintegral_indicator measurableSet_Ioo]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    obtain ⟨h1, h2⟩ := hx
    exact ENNReal.ofReal_le_ofReal (le_min (by nlinarith) le_rfl)
  · rw [Set.indicator_of_notMem hx]; exact zero_le

/-- The small-jump band test function `1_{(s,t] × (-1,1)}(u, x) · x` is square-integrable against
`volume.prod ν` for any Lévy measure `ν`. -/
theorem memLp_two_smallJumpBandFun (hν : IsLevyMeasure ν) (s t : ℝ) :
    MemLp ((Set.Ioc s t ×ˢ Set.Ioo (-1) 1).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν) := by
  refine ⟨(measurable_snd.indicator
    (measurableSet_Ioc.prod measurableSet_Ioo)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  rw [lintegral_enorm_rpow_smallJump s t, setLIntegral_smallJump_snd_sq s t]
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_Ioo_sq_lt_top hν)).ne

/-- The small-jump test function `1_{(0,t] × (-1,1)}(u, x) · x` is square-integrable against
`volume.prod ν` for any Lévy measure `ν`. -/
theorem memLp_two_smallJumpFun (hν : IsLevyMeasure ν) (t : ℝ) :
    MemLp ((Set.Ioc 0 t ×ˢ Set.Ioo (-1) 1).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν) :=
  memLp_two_smallJumpBandFun hν 0 t

/-- The compensated small-jump integral of a Lévy measure at time `t`, as an element of `L²(μ)`. -/
noncomputable def levyCompensatedSmallJump [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) (t : ℝ) :
    Lp ℝ 2 μ :=
  compensatedPoissonIntegral hd ((memLp_two_smallJumpFun hν t).toLp _)

/-- The compensated small-jump integral has mean zero. -/
theorem integral_levyCompensatedSmallJump [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) (t : ℝ) :
    ∫ ω, levyCompensatedSmallJump hd hν t ω ∂μ = 0 :=
  integral_compensatedPoissonIntegral hd _

/-- **Isometry:** the second moment of the compensated small-jump integral is
`t · ∫_{(-1,1)} x² dν`. -/
theorem eLpNorm_sq_levyCompensatedSmallJump [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {t : ℝ}
    (_ht : 0 ≤ t) :
    (eLpNorm (levyCompensatedSmallJump hd hν t) 2 μ) ^ 2
      = ENNReal.ofReal t * ∫⁻ x in Set.Ioo (-1) 1, ENNReal.ofReal (x ^ 2) ∂ν := by
  rw [levyCompensatedSmallJump, eLpNorm_compensatedPoissonIntegral,
    eLpNorm_congr_ae (MemLp.coeFn_toLp _), eLpNorm_two_sq,
    lintegral_enorm_rpow_smallJump 0 t, setLIntegral_smallJump_snd_sq 0 t, sub_zero]

/-- The number of large jumps up to time `t` is Poisson with mean `t · ν {x | 1 ≤ |x|}`. -/
theorem map_levyLargeJumpCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.map (poissonTimeCount K X {x | 1 ≤ |x|} t)
      = (poissonMeasure (ENNReal.ofReal t * ν {x | 1 ≤ |x|}).toNNReal).map
          (Nat.cast : ℕ → ℝ≥0∞) :=
  map_poissonTimeCount hd (measurableSet_le measurable_const continuous_abs.measurable)
    (hν.measure_setOf_abs_ge_lt_top one_pos) ht

/-- The increment of the compensated small-jump integral over a time step is the compensated
integral of the band test function `1_{(s,t] × (-1,1)}(r, x) · x`. -/
theorem levyCompensatedSmallJump_sub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {s t : ℝ}
    (h0 : 0 ≤ s) (hst : s ≤ t) :
    levyCompensatedSmallJump hd hν t - levyCompensatedSmallJump hd hν s
      = compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp _) := by
  have hdisj : Disjoint (Set.Ioc 0 s ×ˢ Set.Ioo (-1 : ℝ) 1) (Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (le_refl s)) _ _
  have hfun : ((Set.Ioc 0 t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator fun p : ℝ × ℝ => p.2)
      = (Set.Ioc 0 s ×ˢ Set.Ioo (-1 : ℝ) 1).indicator (fun p : ℝ × ℝ => p.2)
        + (Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator (fun p : ℝ × ℝ => p.2) := by
    rw [← Set.Ioc_union_Ioc_eq_Ioc h0 hst, Set.union_prod, Set.indicator_union_of_disjoint hdisj]
    rfl
  have htoLp : (memLp_two_smallJumpFun hν t).toLp
        ((Set.Ioc 0 t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator fun p : ℝ × ℝ => p.2)
      = (memLp_two_smallJumpFun hν s).toLp
          ((Set.Ioc 0 s ×ˢ Set.Ioo (-1 : ℝ) 1).indicator fun p : ℝ × ℝ => p.2)
        + (memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1 : ℝ) 1).indicator fun p : ℝ × ℝ => p.2) := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq hfun)
  simp only [levyCompensatedSmallJump]
  rw [htoLp, compensatedPoissonIntegral_add, add_sub_cancel_left]

/-! ### The large-jump sum process

The **large-jump sum** `levyLargeJumpSum` is the sum of the jump sizes of the realized marks in the
band `(0, t] × {x | 1 ≤ |x|}`, written as a series of piece sums. Almost surely only finitely many
marks land in the band (their count is a.s. finite), so the defining series is a.s. a finite sum. It
agrees a.s. with the Bochner integral of the jump size against the random measure over the band and
splits into positive and negative Lebesgue parts. Under a first moment on the large jumps its mean is
`t · ∫_{|x|≥1} x dν` (Campbell's formula). -/

/-- The large-jump band `(0, t] × {x | 1 ≤ |x|}` is measurable. -/
private lemma measurableSet_largeBand (t : ℝ) :
    MeasurableSet (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) :=
  measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable)

/-- The band jump-size test function `1_{(0,t] × {|x|≥1}}(u, x) · x` is measurable. -/
private lemma measurable_largeBandFun (t : ℝ) :
    Measurable ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2) :=
  measurable_snd.indicator (measurableSet_largeBand t)

/-- Integral of a measurable function against a per-piece Dirac sum: it collapses to the finite sum
of the function over the realized points of the piece. -/
private lemma integral_pieceMeasure {f : ℝ × ℝ → ℝ} (Y : ℕ → ℝ × ℝ) (N : ℕ) :
    ∫ x, f x ∂(Measure.sum fun n => if n < N then Measure.dirac (Y n) else 0)
      = ∑ n ∈ Finset.range N, f (Y n) := by
  have hInt : Integrable f (Measure.sum fun n => if n < N then Measure.dirac (Y n) else 0) := by
    refine integrable_sum_measure (fun n => ?_) ?_
    · by_cases hn : n < N
      · rw [if_pos hn]; exact integrable_dirac (by simp)
      · rw [if_neg hn]; exact integrable_zero_measure
    · refine summable_of_ne_finset_zero (s := Finset.range N) fun n hn => ?_
      rw [if_neg (by simpa using hn), integral_zero_measure]
  rw [integral_sum_measure hInt,
    tsum_eq_sum (s := Finset.range N) fun n hn => by
      rw [if_neg (by simpa using hn), integral_zero_measure]]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (by simpa using hn), integral_dirac]

/-- The `ℝ≥0∞`-valued piece sum of a measurable function is a measurable function of the sample
point. -/
private lemma measurable_lintegralPieceSum (hd : IsPoissonPointFamily K X (volume.prod ν) μ)
    {g : ℝ × ℝ → ℝ≥0∞} (hg : Measurable g) (k : ℕ) :
    Measurable fun ω => ∑ n ∈ Finset.range (K k ω), g (X k n ω) := by
  have h : Measurable fun p : Ω × ℕ => ∑ n ∈ Finset.range p.2, g (X k n p.1) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n _ => hg.comp (hd.measurable_point k n)
  exact h.comp (measurable_id.prodMk (hd.measurable_count k))

/-- Almost surely, the jump size is Lebesgue-integrable against the random measure over the band: the
band count is a.s. finite, so only finitely many pieces contribute a finite sum. -/
private lemma ae_lintegral_enorm_largeBand_lt_top [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {t : ℝ} :
    ∀ᵐ ω ∂μ, ∫⁻ p, ‖(Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ
        ∂(poissonRandomMeasure K X ω) < ⊤ := by
  have hbandmeas : MeasurableSet (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) := measurableSet_largeBand t
  have hbandfin : (volume.prod ν) (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := 0) (t := t)
      (hν.measure_setOf_abs_ge_lt_top one_pos)
  have hg1 : Measurable ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
      (fun _ : ℝ × ℝ => (1 : ℝ≥0∞))) := measurable_const.indicator hbandmeas
  filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hbandmeas hbandfin] with ω hω
  rw [lintegral_poissonRandomMeasure (measurable_largeBandFun t).enorm ω]
  have hcount : ∑' k, ∑ n ∈ Finset.range (K k ω),
        (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)
      = poissonRandomMeasure K X ω (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) := by
    rw [← lintegral_poissonRandomMeasure hg1 ω, lintegral_indicator hbandmeas, setLIntegral_one]
  have hCfin : {k | (1 : ℝ≥0∞) ≤ ∑ n ∈ Finset.range (K k ω),
        (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
          (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top (by rw [hcount]; exact hω.ne) one_ne_zero
  rw [tsum_eq_sum (s := hCfin.toFinset) ?_]
  · exact ENNReal.sum_lt_top.mpr fun k _ => ENNReal.sum_lt_top.mpr fun n _ => enorm_lt_top
  · intro k hk
    by_contra hne
    refine hk (hCfin.mem_toFinset.mpr ?_)
    obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hmem : X k n ω ∈ Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|} := by
      by_contra hnm
      exact hterm (by rw [Set.indicator_of_notMem hnm, enorm_zero])
    show (1 : ℝ≥0∞) ≤ ∑ n ∈ Finset.range (K k ω),
      (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)
    calc (1 : ℝ≥0∞)
        = (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
            (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω) := by rw [Set.indicator_of_mem hmem]
      _ ≤ _ := Finset.single_le_sum
          (f := fun n => (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
            (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)) (fun _ _ => zero_le) hn

/-- The **large-jump sum**: the sum of the jump sizes of the realized marks in
`(0, t] × {x | 1 ≤ |x|}`, as a series of piece sums. Almost surely this is a finite sum. -/
noncomputable def levyLargeJumpSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑' k, pieceSum K X
    ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω

/-- The large-jump sum is a measurable function of the sample point. -/
theorem measurable_levyLargeJumpSum (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) : Measurable (levyLargeJumpSum K X t) :=
  Measurable.tsum fun k =>
    measurable_pieceSum (hK k) (fun n => hX k n) (measurable_largeBandFun t)

/-- Almost surely, the large-jump sum is the Bochner integral of the jump size against the random
measure over the band. -/
theorem levyLargeJumpSum_ae_eq_integral [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (_ht : 0 ≤ t) :
    levyLargeJumpSum K X t =ᵐ[μ] fun ω =>
      ∫ p in Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}, p.2 ∂(poissonRandomMeasure K X ω) := by
  have hbandmeas : MeasurableSet (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) := measurableSet_largeBand t
  filter_upwards [ae_lintegral_enorm_largeBand_lt_top hd hν (t := t)] with ω hω_fin
  have hInt : Integrable
      ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2)
      (poissonRandomMeasure K X ω) :=
    ⟨(measurable_largeBandFun t).aestronglyMeasurable, hω_fin⟩
  have hval : ∫ p, (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun p : ℝ × ℝ => p.2) p
        ∂(poissonRandomMeasure K X ω)
      = ∑' k, pieceSum K X
          ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω := by
    unfold poissonRandomMeasure at hInt ⊢
    rw [integral_sum_measure hInt]
    refine tsum_congr fun k => ?_
    exact integral_pieceMeasure (fun n => X k n ω) (K k ω)
  show ∑' k, pieceSum K X ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω
      = ∫ p in Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}, p.2 ∂(poissonRandomMeasure K X ω)
  rw [← hval, integral_indicator hbandmeas]

/-- The large-jump sum as a difference of Lebesgue integrals of the positive and negative jump
parts — the cross-file interface consumed by the independence argument. -/
theorem levyLargeJumpSum_ae_eq_toReal_sub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t) :
    levyLargeJumpSum K X t =ᵐ[μ] fun ω =>
      (∫⁻ p, (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun q => ENNReal.ofReal q.2) p ∂(poissonRandomMeasure K X ω)).toReal
      - (∫⁻ p, (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun q => ENNReal.ofReal (-q.2)) p ∂(poissonRandomMeasure K X ω)).toReal := by
  have hbandmeas : MeasurableSet (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) := measurableSet_largeBand t
  filter_upwards [levyLargeJumpSum_ae_eq_integral hd hν ht,
    ae_lintegral_enorm_largeBand_lt_top hd hν (t := t)] with ω hω_int hω_fin
  have hInt : Integrable
      ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2)
      (poissonRandomMeasure K X ω) :=
    ⟨(measurable_largeBandFun t).aestronglyMeasurable, hω_fin⟩
  have hpos : ∀ p : ℝ × ℝ,
      ENNReal.ofReal ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => q.2) p)
        = (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.2) p := by
    intro p
    by_cases hp : p ∈ Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, ENNReal.ofReal_zero]
  have hneg : ∀ p : ℝ × ℝ,
      ENNReal.ofReal (-(Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => q.2) p)
        = (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
            (fun q : ℝ × ℝ => ENNReal.ofReal (-q.2)) p := by
    intro p
    by_cases hp : p ∈ Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, neg_zero, ENNReal.ofReal_zero]
  rw [hω_int, ← integral_indicator hbandmeas,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt,
    lintegral_congr hpos, lintegral_congr hneg]

/-- **Campbell's formula for the large-jump sum**: under a first moment on the large jumps, the mean
is `t · ∫_{|x|≥1} x dν`. -/
theorem integral_levyLargeJumpSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (_hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t)
    (hx : Integrable (fun x => x) (ν.restrict {x : ℝ | 1 ≤ |x|})) :
    ∫ ω, levyLargeJumpSum K X t ω ∂μ = t * ∫ x in {x : ℝ | 1 ≤ |x|}, x ∂ν := by
  have hbandmeas : MeasurableSet (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) := measurableSet_largeBand t
  set f := (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2 with hf_def
  have hfmeas : Measurable f := measurable_largeBandFun t
  have hband_enorm : ∫⁻ p, ‖f p‖ₑ ∂(volume.prod ν)
      = ENNReal.ofReal t * ∫⁻ x in {x : ℝ | 1 ≤ |x|}, ‖x‖ₑ ∂ν := by
    have hcongr : (fun p : ℝ × ℝ => ‖f p‖ₑ)
        = (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun q : ℝ × ℝ => ‖q.2‖ₑ := by
      funext p
      by_cases hp : p ∈ Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}
      · rw [hf_def, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      · rw [hf_def, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, enorm_zero]
    rw [hcongr, lintegral_indicator hbandmeas, ← Measure.prod_restrict,
      lintegral_prod _ (measurable_snd.enorm.aemeasurable)]
    have hinner : ∀ u : ℝ, ∫⁻ x, ‖((u, x) : ℝ × ℝ).2‖ₑ ∂(ν.restrict {x : ℝ | 1 ≤ |x|})
        = ∫⁻ x in {x : ℝ | 1 ≤ |x|}, ‖x‖ₑ ∂ν := fun _ => rfl
    rw [lintegral_congr hinner, setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]
  have hfint_fin : ∫⁻ p, ‖f p‖ₑ ∂(volume.prod ν) < ⊤ := by
    rw [hband_enorm]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have hxfin : ∫⁻ x, ‖x‖ₑ ∂(ν.restrict {x : ℝ | 1 ≤ |x|}) < ⊤ := hx.2
    exact hxfin
  have hfL1 : Integrable f (volume.prod ν) := ⟨hfmeas.aestronglyMeasurable, hfint_fin⟩
  have hswapfin : ∑' k, ∫⁻ ω, ‖pieceSum K X f k ω‖ₑ ∂μ ≠ ⊤ := by
    have hmeas_inner : ∀ k, Measurable fun ω =>
        ∑ n ∈ Finset.range (K k ω), ‖f (X k n ω)‖ₑ :=
      fun k => measurable_lintegralPieceSum hd hfmeas.enorm k
    have hbound : ∀ k, ∫⁻ ω, ‖pieceSum K X f k ω‖ₑ ∂μ
        ≤ ∫⁻ ω, ∑ n ∈ Finset.range (K k ω), ‖f (X k n ω)‖ₑ ∂μ :=
      fun k => lintegral_mono fun ω => enorm_sum_le _ _
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← lintegral_tsum fun k => (hmeas_inner k).aemeasurable]
    have hcongr : (fun ω => ∑' k, ∑ n ∈ Finset.range (K k ω), ‖f (X k n ω)‖ₑ)
        = fun ω => ∫⁻ p, ‖f p‖ₑ ∂(poissonRandomMeasure K X ω) :=
      funext fun ω => (lintegral_poissonRandomMeasure hfmeas.enorm ω).symm
    rw [hcongr, lintegral_lintegral_poissonRandomMeasure hd hfmeas.enorm]
    exact hfint_fin.ne
  have hHasSum : HasSum (fun k => ∫ p in prmPiece (volume.prod ν) k, f p ∂(volume.prod ν))
      (∫ p, f p ∂(volume.prod ν)) := by
    have h := hasSum_integral_iUnion (μ := volume.prod ν) (f := f)
      (fun k => measurableSet_prmPiece (m := volume.prod ν))
      (pairwise_disjoint_prmPiece (m := volume.prod ν))
      (by rw [iUnion_prmPiece]; exact hfL1.integrableOn)
    rwa [iUnion_prmPiece, setIntegral_univ] at h
  calc ∫ ω, levyLargeJumpSum K X t ω ∂μ
      = ∫ ω, ∑' k, pieceSum K X f k ω ∂μ := rfl
    _ = ∑' k, ∫ ω, pieceSum K X f k ω ∂μ :=
        integral_tsum (fun k => (measurable_pieceSum (hd.measurable_count k)
          (hd.measurable_point k) hfmeas).aestronglyMeasurable) hswapfin
    _ = ∑' k, ∫ p in prmPiece (volume.prod ν) k, f p ∂(volume.prod ν) :=
        tsum_congr fun k => integral_pieceSum hd hfmeas hfL1.integrableOn
    _ = ∫ p, f p ∂(volume.prod ν) := hHasSum.tsum_eq
    _ = ∫ p in Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}, p.2 ∂(volume.prod ν) := by
        rw [hf_def, integral_indicator hbandmeas]
    _ = t * ∫ x in {x : ℝ | 1 ≤ |x|}, x ∂ν := by
        rw [setIntegral_prod (fun z : ℝ × ℝ => z.2)
          ((integrable_indicator_iff hbandmeas).mp (hf_def ▸ hfL1))]
        dsimp only
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal ht, smul_eq_mul]

end LevyIntensity

end ProbabilityTheory
