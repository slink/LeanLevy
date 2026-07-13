/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
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
* `ProbabilityTheory.integral_levyCompensatedSmallJump` — the compensated small-jump integral has
  mean zero.
* `ProbabilityTheory.eLpNorm_sq_levyCompensatedSmallJump` — **Campbell's isometry**: its second
  moment is `t · ∫_{(-1,1)} x² dν`.
* `ProbabilityTheory.map_levyLargeJumpCount` — the number of large jumps up to time `t` is Poisson
  with mean `t · ν {x | 1 ≤ |x|}`.

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
private lemma volume_prod_Ioc_prod (s t : ℝ) (A : Set E) :
    (volume.prod m) (Set.Ioc s t ×ˢ A) = ENNReal.ofReal (t - s) * m A := by
  rw [Measure.prod_prod, Real.volume_Ioc]

omit [Nonempty E] in
/-- Each space-time band has finite `volume.prod m`-mass whenever the mark set has finite mass. -/
private lemma volume_prod_Ioc_prod_lt_top (hfin : m A < ⊤) :
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
private lemma lintegral_enorm_rpow_smallJump (t : ℝ) :
    ∫⁻ p, ‖(Set.Ioc 0 t ×ˢ Set.Ioo (-1) 1).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ)
        ∂(volume.prod ν)
      = ∫⁻ p in Set.Ioc 0 t ×ˢ Set.Ioo (-1) 1, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν) := by
  rw [← lintegral_indicator (measurableSet_Ioc.prod measurableSet_Ioo)]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ Set.Ioc 0 t ×ˢ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]

/-- Tonelli for the small-jump band: `∫_{(0,t]×(-1,1)} x² = t · ∫_{(-1,1)} x²`. -/
private lemma setLIntegral_smallJump_snd_sq (t : ℝ) :
    ∫⁻ p in Set.Ioc 0 t ×ˢ Set.Ioo (-1) 1, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν)
      = ENNReal.ofReal t * ∫⁻ x in Set.Ioo (-1) 1, ENNReal.ofReal (x ^ 2) ∂ν := by
  rw [← Measure.prod_restrict,
    lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ 2))
      (measurable_snd.pow_const 2).ennreal_ofReal.aemeasurable]
  have hinner : ∀ s : ℝ,
      ∫⁻ x, ENNReal.ofReal ((s, x).2 ^ 2) ∂(ν.restrict (Set.Ioo (-1) 1))
        = ∫⁻ x in Set.Ioo (-1) 1, ENNReal.ofReal (x ^ 2) ∂ν := fun _ => rfl
  rw [lintegral_congr hinner, setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]

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
  · rw [Set.indicator_of_notMem hx]; exact zero_le _

/-- The small-jump test function `1_{(0,t] × (-1,1)}(s, x) · x` is square-integrable against
`volume.prod ν` for any Lévy measure `ν`. -/
theorem memLp_two_smallJumpFun (hν : IsLevyMeasure ν) (t : ℝ) :
    MemLp ((Set.Ioc 0 t ×ˢ Set.Ioo (-1) 1).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν) := by
  refine ⟨(measurable_snd.indicator
    (measurableSet_Ioc.prod measurableSet_Ioo)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  rw [lintegral_enorm_rpow_smallJump t, setLIntegral_smallJump_snd_sq t]
  exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_Ioo_sq_lt_top hν)).ne

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
    lintegral_enorm_rpow_smallJump t, setLIntegral_smallJump_snd_sq t]

/-- The number of large jumps up to time `t` is Poisson with mean `t · ν {x | 1 ≤ |x|}`. -/
theorem map_levyLargeJumpCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.map (poissonTimeCount K X {x | 1 ≤ |x|} t)
      = (poissonMeasure (ENNReal.ofReal t * ν {x | 1 ≤ |x|}).toNNReal).map
          (Nat.cast : ℕ → ℝ≥0∞) :=
  map_poissonTimeCount hd (measurableSet_le measurable_const continuous_abs.measurable)
    (hν.measure_setOf_abs_ge_lt_top one_pos) ht

end LevyIntensity

end ProbabilityTheory
