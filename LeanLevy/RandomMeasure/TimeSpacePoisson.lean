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
import LeanLevy.Levy.CompensatedIntegral

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
* `ProbabilityTheory.charFun_map_levyLargeJumpSum` — **the large-jump sum is compound Poisson**: its
  characteristic function is `exp (t · ∫_{|x|≥1} (e^{iξx} − 1) dν)`.
* `ProbabilityTheory.charFun_map_compensatedBandSum` — the compensated Poisson sum of the band test
  function on a mark set `A ⊆ (-1, 1)` of finite `ν`-mass has characteristic function
  `exp (t · ∫_A (e^{ixξ} − 1 − ixξ) dν)`.
* `ProbabilityTheory.charFun_map_levyCompensatedSmallJump` — **the law of the compensated small-jump
  integral**: its characteristic function is `exp (t · ∫_{(-1,1)} (e^{ixξ} − 1 − ixξ) dν)`, the
  small-jump factor of the Lévy–Khintchine exponent.
* `ProbabilityTheory.charFun_map_levyLargeJumpSum_sub`,
  `ProbabilityTheory.charFun_map_levyCompensatedSmallJump_sub` — **the increment laws over a time band
  `(s, t]`**: the large-jump increment is compound Poisson and the compensated small-jump increment
  carries the small-jump factor, both at rate `(t − s)`.

Every statement is read off the abstract superposition and disjoint-family independence laws of
`poissonRandomMeasure` on `ℝ × E`; the band mass factorizes as `volume (Ioc s t) * m A` through
`Measure.prod_prod`.
-/

open MeasureTheory Filter Topology
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
/-- The pointwise square of a band indicator over a measurable mark set integrates to the set
lintegral of `x²`. -/
private lemma lintegral_enorm_rpow_band {B : Set ℝ} (hB : MeasurableSet B) (s t : ℝ) :
    ∫⁻ p, ‖(Set.Ioc s t ×ˢ B).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ)
        ∂(volume.prod ν)
      = ∫⁻ p in Set.Ioc s t ×ˢ B, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν) := by
  rw [← lintegral_indicator (measurableSet_Ioc.prod hB)]
  refine lintegral_congr fun p => ?_
  by_cases hp : p ∈ Set.Ioc s t ×ˢ B
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]

/-- Tonelli for a band over a measurable mark set: `∫_{(s,t]×B} x² = (t - s) · ∫_B x²`. -/
private lemma setLIntegral_band_snd_sq {B : Set ℝ} (_hB : MeasurableSet B) (s t : ℝ) :
    ∫⁻ p in Set.Ioc s t ×ˢ B, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν)
      = ENNReal.ofReal (t - s) * ∫⁻ x in B, ENNReal.ofReal (x ^ 2) ∂ν := by
  rw [← Measure.prod_restrict,
    lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ 2))
      (measurable_snd.pow_const 2).ennreal_ofReal.aemeasurable]
  have hinner : ∀ r : ℝ,
      ∫⁻ x, ENNReal.ofReal ((r, x).2 ^ 2) ∂(ν.restrict B)
        = ∫⁻ x in B, ENNReal.ofReal (x ^ 2) ∂ν := fun _ => rfl
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
  rw [lintegral_enorm_rpow_band measurableSet_Ioo s t, setLIntegral_band_snd_sq measurableSet_Ioo s t]
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
    lintegral_enorm_rpow_band measurableSet_Ioo 0 t, setLIntegral_band_snd_sq measurableSet_Ioo 0 t,
    sub_zero]

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

/-- The compensated small-jump integral vanishes a.e. at time zero: its `(0, 0]` band is empty. -/
theorem levyCompensatedSmallJump_zero_ae_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν) :
    (fun ω => levyCompensatedSmallJump hd hν 0 ω) =ᵐ[μ] fun _ => 0 := by
  have hz : levyCompensatedSmallJump hd hν 0 = 0 := by
    rw [← norm_eq_zero, Lp.norm_def, levyCompensatedSmallJump,
      eLpNorm_compensatedPoissonIntegral, eLpNorm_congr_ae (MemLp.coeFn_toLp _),
      Set.Ioc_self, Set.empty_prod, Set.indicator_empty]
    simp
  rw [hz]
  exact Lp.coeFn_zero ℝ 2 μ

/-! ### The large-jump sum process

The **large-jump sum** `levyLargeJumpSum` is the sum of the jump sizes of the realized marks in the
band `(0, t] × {x | 1 ≤ |x|}`, written as a series of piece sums. Almost surely only finitely many
marks land in the band (their count is a.s. finite), so the defining series is a.s. a finite sum. It
agrees a.s. with the Bochner integral of the jump size against the random measure over the band and
splits into positive and negative Lebesgue parts. Under a first moment on the large jumps its mean is
`t · ∫_{|x|≥1} x dν` (Campbell's formula). -/

/-- The large-jump band `(s, t] × {x | 1 ≤ |x|}` is measurable. -/
private lemma measurableSet_largeBand (s t : ℝ) :
    MeasurableSet (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) :=
  measurableSet_Ioc.prod (measurableSet_le measurable_const continuous_abs.measurable)

/-- The band jump-size test function `1_{(s,t] × {|x|≥1}}(u, x) · x` is measurable. -/
private lemma measurable_largeBandFun (s t : ℝ) :
    Measurable ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2) :=
  measurable_snd.indicator (measurableSet_largeBand s t)

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

/-- A.e., only finitely many pieces carry a realized point in a finite-mass region. -/
lemma ae_finite_pieces_mem [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
    (hRfin : ((volume : Measure ℝ).prod ν) R < ⊤) :
    ∀ᵐ ω ∂μ, {k | ∃ n ∈ Finset.range (K k ω), X k n ω ∈ R}.Finite := by
  have hg1 : Measurable (R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hR
  filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hR hRfin] with ω hω
  have hcount : ∑' k, ∑ n ∈ Finset.range (K k ω),
        R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)
      = poissonRandomMeasure K X ω R := by
    rw [← lintegral_poissonRandomMeasure hg1 ω, lintegral_indicator hR, setLIntegral_one]
  have hCfin : {k | (1 : ℝ≥0∞) ≤ ∑ n ∈ Finset.range (K k ω),
        R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω)}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top (by rw [hcount]; exact hω.ne) one_ne_zero
  refine hCfin.subset fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk ⊢
  obtain ⟨n, hn, hmem⟩ := hk
  calc (1 : ℝ≥0∞)
      = R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω) := by rw [Set.indicator_of_mem hmem]
    _ ≤ _ := Finset.single_le_sum
        (f := fun n => R.indicator (fun _ : ℝ × ℝ => (1 : ℝ≥0∞)) (X k n ω))
        (fun _ _ => zero_le) hn

/-- A.e., the piece sums of a function vanishing off a finite-mass region have finite support. -/
lemma ae_finite_support_pieceSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    {R : Set (ℝ × ℝ)} (hR : MeasurableSet R)
    (hRfin : ((volume : Measure ℝ).prod ν) R < ⊤)
    {g : ℝ × ℝ → ℝ} (hg : ∀ p ∉ R, g p = 0) :
    ∀ᵐ ω ∂μ, {k | pieceSum K X g k ω ≠ 0}.Finite := by
  filter_upwards [ae_finite_pieces_mem hd hR hRfin] with ω hω
  refine hω.subset fun k hk => ?_
  simp only [Set.mem_setOf_eq] at hk ⊢
  have hk' : (∑ n ∈ Finset.range (K k ω), g (X k n ω)) ≠ 0 := hk
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk'
  refine ⟨n, hn, ?_⟩
  by_contra hnm
  exact hterm (hg _ hnm)

/-- Almost surely, the jump size is Lebesgue-integrable against the random measure over the band: the
band count is a.s. finite, so only finitely many pieces contribute a finite sum. -/
private lemma ae_lintegral_enorm_largeBand_lt_top [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {t : ℝ} :
    ∀ᵐ ω ∂μ, ∫⁻ p, ‖(Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ
        ∂(poissonRandomMeasure K X ω) < ⊤ := by
  have hbandfin : (volume.prod ν) (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := 0) (t := t)
      (hν.measure_setOf_abs_ge_lt_top one_pos)
  filter_upwards [ae_finite_pieces_mem hd (measurableSet_largeBand 0 t) hbandfin] with ω hω
  rw [lintegral_poissonRandomMeasure (measurable_largeBandFun 0 t).enorm ω,
    tsum_eq_sum (s := hω.toFinset) ?_]
  · exact ENNReal.sum_lt_top.mpr fun k _ => ENNReal.sum_lt_top.mpr fun n _ => enorm_lt_top
  · intro k hk
    refine Finset.sum_eq_zero fun n hn => ?_
    have hnm : X k n ω ∉ Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|} := fun hmem =>
      hk (hω.mem_toFinset.mpr ⟨n, hn, hmem⟩)
    rw [Set.indicator_of_notMem hnm, enorm_zero]

/-- The **large-jump sum**: the sum of the jump sizes of the realized marks in
`(0, t] × {x | 1 ≤ |x|}`, as a series of piece sums. Almost surely this is a finite sum. -/
noncomputable def levyLargeJumpSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑' k, pieceSum K X
    ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω

/-- The large-jump sum is a measurable function of the sample point. -/
theorem measurable_levyLargeJumpSum (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) : Measurable (levyLargeJumpSum K X t) :=
  Measurable.tsum fun k =>
    measurable_pieceSum (hK k) (fun n => hX k n) (measurable_largeBandFun 0 t)

omit [MeasurableSpace Ω] in
/-- The large-jump sum vanishes at time zero: the band `(0, 0] × {x | 1 ≤ |x|}` is empty. -/
@[simp] theorem levyLargeJumpSum_zero (ω : Ω) : levyLargeJumpSum K X 0 ω = 0 := by
  have hband : ((Set.Ioc (0 : ℝ) 0 ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2)
      = fun _ => 0 := by
    rw [Set.Ioc_self, Set.empty_prod, Set.indicator_empty]
  simp only [levyLargeJumpSum, hband, pieceSum, Finset.sum_const_zero, tsum_zero]

/-- Almost surely, the large-jump sum is the Bochner integral of the jump size against the random
measure over the band. -/
theorem levyLargeJumpSum_ae_eq_integral [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (_ht : 0 ≤ t) :
    levyLargeJumpSum K X t =ᵐ[μ] fun ω =>
      ∫ p in Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}, p.2 ∂(poissonRandomMeasure K X ω) := by
  have hbandmeas : MeasurableSet (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) := measurableSet_largeBand 0 t
  filter_upwards [ae_lintegral_enorm_largeBand_lt_top hd hν (t := t)] with ω hω_fin
  have hInt : Integrable
      ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2)
      (poissonRandomMeasure K X ω) :=
    ⟨(measurable_largeBandFun 0 t).aestronglyMeasurable, hω_fin⟩
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
  have hbandmeas : MeasurableSet (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) := measurableSet_largeBand 0 t
  filter_upwards [levyLargeJumpSum_ae_eq_integral hd hν ht,
    ae_lintegral_enorm_largeBand_lt_top hd hν (t := t)] with ω hω_int hω_fin
  have hInt : Integrable
      ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2)
      (poissonRandomMeasure K X ω) :=
    ⟨(measurable_largeBandFun 0 t).aestronglyMeasurable, hω_fin⟩
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
  have hbandmeas : MeasurableSet (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}) := measurableSet_largeBand 0 t
  set f := (Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2 with hf_def
  have hfmeas : Measurable f := measurable_largeBandFun 0 t
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

/-! ### The compound-Poisson characteristic function of the large-jump sum

The characteristic function of the large-jump sum is the compound-Poisson exponential
`exp (t · ∫_{|x|≥1} (e^{iξx} − 1) dν)`. The proof runs through the piece decomposition: each piece
contributes a probability-generating factor `exp (∫_{piece} (e^{iξx} − 1) d(volume.prod ν))`
(`integral_exp_pieceSum`), the finitely-many-piece partial products factorize by prefix-versus-block
independence (`charFun_partial_largeJumpSum`), and dominated convergence together with the
piece-partition sum of the band integral pass to the limit. -/

/-- Measurability skeleton for a piece sum read off an abstract coordinate space `D` supplying the
count `cnt` and the points `pt`. Used to extract the partial large-jump sum from a block process. -/
private lemma measurable_pieceSumExtract {D : Type*} [MeasurableSpace D] {f : ℝ × ℝ → ℝ}
    (hf : Measurable f) (cnt : D → ℕ) (pt : ℕ → D → ℝ × ℝ) (hcnt : Measurable cnt)
    (hpt : ∀ n, Measurable (pt n)) :
    Measurable fun g => ∑ n ∈ Finset.range (cnt g), f (pt n g) := by
  have hP : Measurable fun p : D × ℕ => ∑ n ∈ Finset.range p.2, f (pt n p.1) :=
    measurable_from_prod_countable_left fun j =>
      Finset.measurable_sum (Finset.range j) fun n _ => hf.comp (hpt n)
  exact hP.comp (measurable_id.prodMk hcnt)

/-- Complex scaling bridge: the `volume.prod ν`-mass of a piece times the Bochner integral against
the normalized piece law recovers the set integral against `volume.prod ν`, for complex integrands.
Re-derived from the public `prmPieceLaw` definition (the real-valued wrappers are not exported). -/
private lemma toReal_smul_integral_prmPieceLaw_complex {F : Type*} [MeasurableSpace F] [Nonempty F]
    (m : Measure F) [SigmaFinite m] (g : F → ℂ) (k : ℕ) :
    (m (prmPiece m k)).toReal • ∫ x, g x ∂(prmPieceLaw m k)
      = ∫ x in prmPiece m k, g x ∂m := by
  by_cases h : m (prmPiece m k) = 0
  · rw [h, ENNReal.toReal_zero, zero_smul,
      show (∫ x in prmPiece m k, g x ∂m) = ∫ x, g x ∂(m.restrict (prmPiece m k)) from rfl,
      Measure.restrict_eq_zero.mpr h, integral_zero_measure]
  · have hpl : prmPieceLaw m k = (m (prmPiece m k))⁻¹ • m.restrict (prmPiece m k) := by
      unfold prmPieceLaw; rw [if_neg h]
    rw [hpl, integral_smul_measure, smul_smul, ENNReal.toReal_inv,
      mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨h, measure_prmPiece_lt_top.ne⟩), one_smul]

/-- **Per-piece probability-generating factor.** For a measurable real test function `f`, the mean of
`exp (i ξ · pieceSum f k)` is `exp (∫_{piece k} (e^{iξ f} − 1) d(volume.prod ν))`. This is the piece
pgf identity `integral_pieceProd_eq_exp` at the purely-imaginary weight `w x = e^{iξ f x}`. -/
private lemma integral_exp_pieceSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) (ξ : ℝ)
    (k : ℕ) :
    ∫ ω, Complex.exp (↑ξ * ↑(pieceSum K X f k ω) * Complex.I) ∂μ
      = Complex.exp (∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)) := by
  have hwmeas : Measurable fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑(f x) * Complex.I) :=
    Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp hf).const_mul (↑ξ)).mul_const Complex.I)
  have hwbdd : ∀ x : ℝ × ℝ, ‖Complex.exp (↑ξ * ↑(f x) * Complex.I)‖ ≤ 1 := fun x => by
    rw [show (↑ξ * ↑(f x) * Complex.I : ℂ) = ↑(ξ * f x) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hw_int : Integrable (fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑(f x) * Complex.I))
      (prmPieceLaw (volume.prod ν) k) :=
    Integrable.of_bound hwmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hwbdd)
  have hprod : ∀ ω, ∏ n ∈ Finset.range (K k ω),
        Complex.exp (↑ξ * ↑(f (X k n ω)) * Complex.I)
      = Complex.exp (↑ξ * ↑(pieceSum K X f k ω) * Complex.I) := by
    intro ω
    rw [← Complex.exp_sum]
    congr 1
    simp only [pieceSum, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  have hone : ∫ _x : ℝ × ℝ, (1 : ℂ) ∂(prmPieceLaw (volume.prod ν) k) = 1 := by
    simp
  have hint : ∫ ω, Complex.exp (↑ξ * ↑(pieceSum K X f k ω) * Complex.I) ∂μ
      = ∫ ω, ∏ n ∈ Finset.range (K k ω), Complex.exp (↑ξ * ↑(f (X k n ω)) * Complex.I) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => (hprod ω).symm)
  rw [hint, integral_pieceProd_eq_exp hd hwmeas hwbdd]
  congr 1
  rw [show (∫ x, Complex.exp (↑ξ * ↑(f x) * Complex.I) ∂(prmPieceLaw (volume.prod ν) k)) - 1
        = ∫ x, (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(prmPieceLaw (volume.prod ν) k) from by
      rw [integral_sub hw_int (integrable_const 1), hone],
    ← Complex.real_smul]
  exact toReal_smul_integral_prmPieceLaw_complex _ _ k

/-- **Prefix-versus-next-piece independence of the piece sums.** The partial large-jump sum over the
first `n + 1` pieces is independent of the piece sum of piece `n + 1`, since they read disjoint blocks
of the point family. -/
private lemma indepFun_partialPieceSum_pieceSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) (n : ℕ) :
    IndepFun (fun ω => ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω)
      (pieceSum K X f (n + 1)) μ := by
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
  set G : (∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ, pointFamilyIndexType (ℝ × ℝ) (φ i)) → ℝ :=
    fun g => ∑ k : Fin (n + 1),
      ∑ n' ∈ Finset.range (g (Sum.inl k)), f (g (Sum.inr (k, n'))) with hG_def
  set H : (∀ j : Unit ⊕ ℕ, pointFamilyIndexType (ℝ × ℝ) (ψ j)) → ℝ :=
    fun g => ∑ n' ∈ Finset.range (g (Sum.inl ())), f (g (Sum.inr n')) with hH_def
  have hG : Measurable G := by
    rw [hG_def]
    exact Finset.measurable_sum _ fun k _ =>
      measurable_pieceSumExtract (D := ∀ i : Fin (n + 1) ⊕ Fin (n + 1) × ℕ,
          pointFamilyIndexType (ℝ × ℝ) (φ i))
        hf (fun g => g (Sum.inl k)) (fun n' g => g (Sum.inr (k, n')))
        (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hH : Measurable H :=
    measurable_pieceSumExtract (D := ∀ j : Unit ⊕ ℕ, pointFamilyIndexType (ℝ × ℝ) (ψ j))
      hf (fun g => g (Sum.inl ())) (fun n' g => g (Sum.inr n'))
      (measurable_pi_apply _) fun n' => measurable_pi_apply _
  have hGeq : (fun ω => G fun i => pointFamilyCombined K X (φ i) ω)
      = fun ω => ∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω := by
    funext ω
    simp only [hG_def]
    rw [← Fin.sum_univ_eq_sum_range (fun j => pieceSum K X f j ω) (n + 1)]
    rfl
  have hHeq : (fun ω => H fun j => pointFamilyCombined K X (ψ j) ω) = pieceSum K X f (n + 1) := by
    funext ω; rfl
  have key := hsplit.comp hG hH
  simp only [Function.comp_def] at key
  rwa [hGeq, hHeq] at key

/-- **The partial-product identity.** The mean of `exp (i ξ · (partial large-jump sum over pieces
`0, …, n`))` is the product of the per-piece factors, by prefix-versus-block independence. -/
private lemma charFun_partial_largeJumpSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f) (ξ : ℝ)
    (n : ℕ) :
    ∫ ω, Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I) ∂μ
      = ∏ k ∈ Finset.range (n + 1),
          Complex.exp (∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)) := by
  have hgmeas : Measurable fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.const_mul (↑ξ)).mul_const Complex.I)
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, Finset.prod_range_one]
    exact integral_exp_pieceSum hd hf ξ 0
  | succ n ih =>
    have hexp : ∀ ω,
        Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 2), pieceSum K X f k ω) * Complex.I)
          = Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I)
            * Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I) := by
      intro ω
      rw [← Complex.exp_add]
      congr 1
      rw [Finset.sum_range_succ]
      push_cast
      ring
    have hmL : Measurable fun ω =>
        Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I) :=
      hgmeas.comp (Finset.measurable_sum _ fun k _ =>
        measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf)
    have hmR : Measurable fun ω =>
        Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I) :=
      hgmeas.comp (measurable_pieceSum (hd.measurable_count _) (hd.measurable_point _) hf)
    have hind : IndepFun
        (fun ω => Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I))
        (fun ω => Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I)) μ :=
      (indepFun_partialPieceSum_pieceSum hd hf n).comp hgmeas hgmeas
    calc ∫ ω, Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 2), pieceSum K X f k ω) * Complex.I) ∂μ
        = ∫ ω,
            Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I)
              * Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hexp)
      _ = (∫ ω,
              Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω) * Complex.I) ∂μ)
            * ∫ ω, Complex.exp (↑ξ * ↑(pieceSum K X f (n + 1) ω) * Complex.I) ∂μ :=
          hind.integral_fun_mul_eq_mul_integral hmL.aestronglyMeasurable hmR.aestronglyMeasurable
      _ = (∏ k ∈ Finset.range (n + 1),
              Complex.exp (∫ x in prmPiece (volume.prod ν) k,
                (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)))
            * Complex.exp (∫ x in prmPiece (volume.prod ν) (n + 1),
                (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)) := by
          rw [ih, integral_exp_pieceSum hd hf ξ (n + 1)]
      _ = ∏ k ∈ Finset.range (n + 2),
            Complex.exp (∫ x in prmPiece (volume.prod ν) k,
              (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν)) :=
          (Finset.prod_range_succ _ _).symm

/-- Almost surely only finitely many pieces carry a realized point in the large-jump band, so the
piece sums of the band test function have finite support. -/
private lemma ae_finite_support_pieceSum_largeBand [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) (hν : IsLevyMeasure ν) {s t : ℝ} :
    ∀ᵐ ω ∂μ, {k | pieceSum K X
        ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω ≠ 0}.Finite := by
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t)
      (hν.measure_setOf_abs_ge_lt_top one_pos)
  exact ae_finite_support_pieceSum hd (measurableSet_largeBand s t) hbandfin
    fun p hp => Set.indicator_of_notMem hp _

/-- **The band large-jump sum is compound Poisson over `(s, t]`:** the characteristic function of the
piece-sum series on the band `(s, t] × {x | 1 ≤ |x|}` is `exp ((t − s) · ∫_{|x|≥1} (e^{iξx} − 1) dν)`.
This is the band-generic engine behind the running large-jump sum and its increments. -/
private lemma charFun_map_bandJumpSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => ∑' k,
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) *
          ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν) := by
  have hbandmeas : MeasurableSet (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) := measurableSet_largeBand s t
  have hbandFnmeas : Measurable ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2) :=
    measurable_largeBandFun s t
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t)
      (hν.measure_setOf_abs_ge_lt_top one_pos)
  have hgmeas : Measurable fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.const_mul (↑ξ)).mul_const Complex.I)
  have hgcont : Continuous fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) := by fun_prop
  -- The band exponential integrand, in indicator form and its norm bound.
  have hf'eq : (fun x : ℝ × ℝ =>
        Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
          (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1)
      = (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
          fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 := by
    funext x
    by_cases hx : x ∈ Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.ofReal_zero,
        mul_zero, zero_mul, Complex.exp_zero, sub_self]
  have hbound2 : ∀ x : ℝ × ℝ, ‖Complex.exp (↑ξ * ↑x.2 * Complex.I) - 1‖ ≤ 2 := fun x => by
    calc ‖Complex.exp (↑ξ * ↑x.2 * Complex.I) - 1‖
        ≤ ‖Complex.exp (↑ξ * ↑x.2 * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show (↑ξ * ↑x.2 * Complex.I : ℂ) = ↑(ξ * x.2) * Complex.I from by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hintegrand_meas : Measurable
      fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 :=
    (Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp measurable_snd).const_mul (↑ξ)).mul_const
        Complex.I)).sub measurable_const
  have hband_intOn : IntegrableOn
      (fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1)
      (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) (volume.prod ν) :=
    IntegrableOn.of_bound hbandfin hintegrand_meas.aestronglyMeasurable 2
      (Filter.Eventually.of_forall hbound2)
  have hf'_int : Integrable (fun x : ℝ × ℝ =>
      Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) (volume.prod ν) := by
    rw [hf'eq]; exact (integrable_indicator_iff hbandmeas).mpr hband_intOn
  -- The piece-partition sum of the band-integral factors (HasSum of the per-piece exponents).
  have hFpiece_hassum : HasSum
      (fun k => ∫ x in prmPiece (volume.prod ν) k,
        (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
          (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν))
      (∫ x, (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν)) := by
    have h := hasSum_integral_iUnion (μ := volume.prod ν)
      (f := fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1)
      (fun k => measurableSet_prmPiece (m := volume.prod ν))
      (pairwise_disjoint_prmPiece (m := volume.prod ν))
      (by rw [iUnion_prmPiece]; exact hf'_int.integrableOn)
    rwa [iUnion_prmPiece, setIntegral_univ] at h
  -- The band-integral equals the compound-Poisson exponent.
  have hfinal : (∫ x, (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν))
      = ((t - s : ℝ) : ℂ) * ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν := by
    rw [hf'eq, integral_indicator hbandmeas,
      setIntegral_prod (fun z : ℝ × ℝ => Complex.exp (↑ξ * ↑z.2 * Complex.I) - 1) hband_intOn]
    dsimp only
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst), Complex.real_smul]
    refine congrArg (fun z => ((↑(t - s) : ℂ)) * z) ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [mul_comm (↑ξ : ℂ) (↑y : ℂ)]
  -- Dominated convergence: partial sums of piece sums converge a.e. to the band large-jump sum.
  have hmeas_sum : Measurable fun ω =>
      ∑' k, pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω :=
    Measurable.tsum fun k =>
      measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hbandFnmeas
  have hFmeas : ∀ n, Measurable fun ω =>
      Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
        * Complex.I) := fun n =>
    hgmeas.comp (Finset.measurable_sum _ fun k _ =>
      measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hbandFnmeas)
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
        * Complex.I)‖ ≤ (fun _ : Ω => (1 : ℝ)) ω := fun n => by
    filter_upwards with ω
    rw [show (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
          pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
          * Complex.I : ℂ)
        = ↑(ξ * ∑ k ∈ Finset.range (n + 1),
          pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
          * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n =>
      Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
        * Complex.I)) atTop
      (𝓝 (Complex.exp (↑ξ * ↑(∑' k,
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)
        * Complex.I))) := by
    filter_upwards [ae_finite_support_pieceSum_largeBand hd hν (s := s) (t := t)] with ω hωfin
    have hsummable : Summable (fun k =>
        pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω) :=
      summable_of_ne_finset_zero (s := hωfin.toFinset) fun k hk => by
        by_contra hne
        exact hk (hωfin.mem_toFinset.mpr hne)
    have htends : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1),
          pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω) atTop
        (𝓝 (∑' k,
          pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω)) :=
      hsummable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact (hgcont.tendsto _).comp htends
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  simp_rw [charFun_partial_largeJumpSum hd hbandFnmeas ξ] at hdct
  -- The product side converges to the compound-Poisson exponential.
  have hprodexp : ∀ n, ∏ k ∈ Finset.range (n + 1),
        Complex.exp (∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
            (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν))
      = Complex.exp (∑ k ∈ Finset.range (n + 1),
          ∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
              (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν)) :=
    fun n => (Complex.exp_sum _ _).symm
  simp_rw [hprodexp] at hdct
  have hprodlim : Tendsto (fun n => Complex.exp (∑ k ∈ Finset.range (n + 1),
        ∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
            (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν))) atTop
      (𝓝 (Complex.exp (∫ x, (Complex.exp (↑ξ * ↑((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator
        (fun p : ℝ × ℝ => p.2) x) * Complex.I) - 1) ∂(volume.prod ν)))) :=
    (Complex.continuous_exp.tendsto _).comp
      (hFpiece_hassum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  have hval := tendsto_nhds_unique hdct hprodlim
  rw [charFun_apply_real, integral_map hmeas_sum.aemeasurable (by fun_prop), hval, hfinal]

/-- **The large-jump sum is compound Poisson:** its characteristic function is
`exp (t · ∫_{|x|≥1} (e^{iξx} − 1) dν)`. -/
theorem charFun_map_levyLargeJumpSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    charFun (μ.map (levyLargeJumpSum K X t)) ξ
      = Complex.exp ((t : ℂ) *
          ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν) := by
  have h := charFun_map_bandJumpSum hd hν (s := 0) ht ξ
  rw [sub_zero] at h
  exact h

/-- The large-jump increment over `(s, t]` is a.e. the banded piece-sum series on
`(s, t] × {x | 1 ≤ |x|}`. -/
theorem levyLargeJumpSum_sub_ae_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) :
    (fun ω => levyLargeJumpSum K X t ω - levyLargeJumpSum K X s ω) =ᵐ[μ] fun ω =>
      ∑' k, pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω := by
  filter_upwards [ae_finite_support_pieceSum_largeBand hd hν (s := 0) (t := s),
    ae_finite_support_pieceSum_largeBand hd hν (s := s) (t := t)] with ω hω_s hω_st
  have hsplit : ∀ k,
      pieceSum K X ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω
        = pieceSum K X ((Set.Ioc 0 s ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω
          + pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω := by
    intro k
    have hdisj : Disjoint (Set.Ioc 0 s ×ˢ {x : ℝ | 1 ≤ |x|})
        (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}) :=
      Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (le_refl s)) _ _
    have hfun : ((Set.Ioc 0 t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p : ℝ × ℝ => p.2)
        = (Set.Ioc 0 s ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun p : ℝ × ℝ => p.2)
          + (Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator (fun p : ℝ × ℝ => p.2) := by
      rw [← Set.Ioc_union_Ioc_eq_Ioc h0 hst, Set.union_prod,
        Set.indicator_union_of_disjoint hdisj]
      rfl
    simp only [pieceSum, hfun, Pi.add_apply, Finset.sum_add_distrib]
  have hsum_s : Summable (fun k =>
      pieceSum K X ((Set.Ioc 0 s ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω) :=
    summable_of_ne_finset_zero (s := hω_s.toFinset) fun k hk => by
      by_contra hne; exact hk (hω_s.mem_toFinset.mpr hne)
  have hsum_st : Summable (fun k =>
      pieceSum K X ((Set.Ioc s t ×ˢ {x : ℝ | 1 ≤ |x|}).indicator fun p => p.2) k ω) :=
    summable_of_ne_finset_zero (s := hω_st.toFinset) fun k hk => by
      by_contra hne; exact hk (hω_st.mem_toFinset.mpr hne)
  simp only [levyLargeJumpSum]
  rw [tsum_congr hsplit, hsum_s.tsum_add hsum_st]
  ring

/-- The large-jump increment over `(s, t]` is compound Poisson with rate `(t − s)`. -/
theorem charFun_map_levyLargeJumpSum_sub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => levyLargeJumpSum K X t ω - levyLargeJumpSum K X s ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) *
          ∫ x in {x : ℝ | 1 ≤ |x|}, (Complex.exp (x * ξ * Complex.I) - 1) ∂ν) := by
  rw [Measure.map_congr (levyLargeJumpSum_sub_ae_eq hd hν h0 hst)]
  exact charFun_map_bandJumpSum hd hν hst ξ

/-! ### The characteristic function of compensated band sums

For a mark set `A ⊆ (-1, 1)` with finite `ν`-mass, the compensated Poisson sum of the band test
function `1_{(0,t] × A}(u, x) · x` has characteristic function
`exp (t · ∫_A (e^{ixξ} − 1 − ixξ) dν)`. The proof is the sibling of `charFun_map_levyLargeJumpSum`
with the per-piece compensator riding along: the compensated partial sums factor into per-piece
factors carrying the extra `−iξ ∫ f` drift, and dominated convergence together with the
piece-partition sum of the band integral pass to the limit. -/

/-- The band test function `1_{(s,t] × A}(u, x) · x` is measurable. -/
lemma measurable_bandFun {A : Set ℝ} (hA : MeasurableSet A) (s t : ℝ) :
    Measurable ((Set.Ioc s t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) :=
  measurable_snd.indicator (measurableSet_Ioc.prod hA)

/-- The band test function is integrable against `volume.prod ν` when `A ⊆ (-1, 1)` has finite mass:
its support has finite `volume.prod ν`-mass and `|x| ≤ 1` there. -/
lemma integrable_bandFun {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Ioo (-1) 1) (hAfin : ν A < ⊤) (s t : ℝ) :
    Integrable ((Set.Ioc s t ×ˢ A).indicator fun p : ℝ × ℝ => p.2)
      ((volume : Measure ℝ).prod ν) := by
  have hbandmeas : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ A) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t) hAfin
  rw [integrable_indicator_iff hbandmeas]
  refine IntegrableOn.of_bound hbandfin measurable_snd.aestronglyMeasurable 1 ?_
  refine (ae_restrict_mem hbandmeas).mono fun p hp => ?_
  obtain ⟨h1, h2⟩ := hAsub hp.2
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨le_of_lt h1, le_of_lt h2⟩

/-- The band test function lies in `L²(volume.prod ν)` when `A ⊆ (-1, 1)` has finite mass: its
square is bounded by `1` on the finite-mass support. -/
lemma memLp_two_bandFun {A : Set ℝ} (hA : MeasurableSet A)
    (hAsub : A ⊆ Set.Ioo (-1) 1) (hAfin : ν A < ⊤) (s t : ℝ) :
    MemLp ((Set.Ioc s t ×ˢ A).indicator fun p : ℝ × ℝ => p.2) 2
      ((volume : Measure ℝ).prod ν) := by
  have hbandmeas : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ A) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t) hAfin
  refine ⟨(measurable_snd.indicator hbandmeas).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hle : (fun p : ℝ × ℝ =>
        ‖(Set.Ioc s t ×ˢ A).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ))
      ≤ (Set.Ioc s t ×ˢ A).indicator fun _ : ℝ × ℝ => (1 : ℝ≥0∞) := by
    intro p
    dsimp only
    by_cases hp : p ∈ Set.Ioc s t ×ˢ A
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      obtain ⟨h1, h2⟩ := hAsub hp.2
      have habs : |p.2| ≤ 1 := abs_le.mpr ⟨le_of_lt h1, le_of_lt h2⟩
      calc ‖p.2‖ₑ ^ (2 : ℝ) ≤ (1 : ℝ≥0∞) ^ (2 : ℝ) := by
            refine ENNReal.rpow_le_rpow ?_ (by norm_num)
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_one.mpr habs
        _ = 1 := ENNReal.one_rpow _
    · rw [Set.indicator_of_notMem hp, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num)]
      exact bot_le
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono hle) ?_)
  rw [lintegral_indicator hbandmeas, setLIntegral_const, one_mul]
  exact hbandfin

/-- **The partial-product identity for compensated band sums.** The mean of
`exp (i ξ · (partial compensated sum over pieces `0, …, n`))` factors into the per-piece
compensated factors, each carrying the drift `−iξ ∫ f`. Obtained from the uncompensated
`charFun_partial_largeJumpSum` by pulling out the constant `exp (−iξ ∑ ∫ f)`. -/
private lemma charFun_partial_compensatedBandSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod ν) μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hf1 : Integrable f (volume.prod ν)) (ξ : ℝ) (n : ℕ) :
    ∫ ω, Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I) ∂μ
      = ∏ k ∈ Finset.range (n + 1),
          Complex.exp (∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
              ∂(volume.prod ν)) := by
  have hmeasE1 : Measurable fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 :=
    (Complex.measurable_exp.comp
      (((Complex.measurable_ofReal.comp hf).const_mul (↑ξ)).mul_const Complex.I)).sub
      measurable_const
  have hboundE1 : ∀ x : ℝ × ℝ, ‖Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1‖ ≤ 2 := fun x => by
    calc ‖Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1‖
        ≤ ‖Complex.exp (↑ξ * ↑(f x) * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show (↑ξ * ↑(f x) * Complex.I : ℂ) = ↑(ξ * f x) * Complex.I from by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hE1int : ∀ k, IntegrableOn (fun x : ℝ × ℝ => Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1)
      (prmPiece (volume.prod ν) k) (volume.prod ν) := fun k =>
    IntegrableOn.of_bound measure_prmPiece_lt_top hmeasE1.aestronglyMeasurable 2
      (Filter.Eventually.of_forall hboundE1)
  have hLint : ∀ k, IntegrableOn (fun x : ℝ × ℝ => (↑ξ * ↑(f x) * Complex.I : ℂ))
      (prmPiece (volume.prod ν) k) (volume.prod ν) := by
    intro k
    have h0 : IntegrableOn (fun x : ℝ × ℝ => (↑(f x) : ℂ))
        (prmPiece (volume.prod ν) k) (volume.prod ν) := hf1.integrableOn.ofReal
    exact (h0.const_mul (↑ξ : ℂ)).mul_const Complex.I
  have halg :
      Complex.exp (-(↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
          ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I))
        * ∏ k ∈ Finset.range (n + 1),
            Complex.exp (∫ x in prmPiece (volume.prod ν) k,
              (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν))
      = ∏ k ∈ Finset.range (n + 1),
          Complex.exp (∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
              ∂(volume.prod ν)) := by
    have hper : ∀ k ∈ Finset.range (n + 1),
        ∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
              ∂(volume.prod ν)
          = (∫ x in prmPiece (volume.prod ν) k,
              (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1) ∂(volume.prod ν))
            - ↑ξ * ↑(∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I := by
      intro k _
      rw [integral_sub (hE1int k) (hLint k)]
      congr 1
      rw [integral_mul_const, integral_const_mul, integral_complex_ofReal]
    simp only [← Complex.exp_sum]
    rw [← Complex.exp_add]
    congr 1
    rw [Finset.sum_congr rfl hper, Finset.sum_sub_distrib]
    have hCeq : (∑ k ∈ Finset.range (n + 1),
          ↑ξ * ↑(∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I)
        = ↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
            ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I := by
      rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    rw [hCeq]
    ring
  have hexp : ∀ ω, Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I)
      = Complex.exp (-(↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
          ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) * Complex.I))
        * Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
            pieceSum K X f k ω) * Complex.I) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    rw [show (∑ k ∈ Finset.range (n + 1), compensatedPieceSum K X f (volume.prod ν) k ω)
          = (∑ k ∈ Finset.range (n + 1), pieceSum K X f k ω)
            - ∑ k ∈ Finset.range (n + 1),
                ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν) from by
        rw [← Finset.sum_sub_distrib]; rfl]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_const_mul,
    charFun_partial_largeJumpSum hd hf ξ n]
  exact halg

/-- **Characteristic function of a compensated band sum over `(s, t]`.** For a mark set `A` inside the
unit interval with finite `ν`-mass, the compensated Poisson sum of the band test function
`1_{(s,t] × A}(u, x) · x` has characteristic function `exp ((t − s) · ∫_A (e^{ixξ} − 1 − ixξ) dν)`. -/
theorem charFun_map_compensatedTimeBandSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1) 1) (hAfin : ν A < ⊤)
    {s t : ℝ} (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (compensatedPoissonSum K X
        ((Set.Ioc s t ×ˢ A).indicator fun p => p.2) ((volume : Measure ℝ).prod ν))) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in A,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) := by
  have hbandmeas : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
  set f : ℝ × ℝ → ℝ := (Set.Ioc s t ×ˢ A).indicator fun p : ℝ × ℝ => p.2 with hf_def
  have hbandFnmeas : Measurable f := measurable_bandFun hA s t
  have hbandfin : (volume.prod ν) (Set.Ioc s t ×ˢ A) < ⊤ :=
    volume_prod_Ioc_prod_lt_top (m := ν) (s := s) (t := t) hAfin
  have hf1 : Integrable f (volume.prod ν) := integrable_bandFun hA hAsub hAfin s t
  have hf2 : MemLp f 2 (volume.prod ν) := memLp_two_bandFun hA hAsub hAfin s t
  have hgmeas : Measurable fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.const_mul (↑ξ)).mul_const Complex.I)
  have hgcont : Continuous fun r : ℝ => Complex.exp (↑ξ * ↑r * Complex.I) := by fun_prop
  -- The band integrand `e^{iξf} − 1 − iξf` in indicator form.
  have hg'eq : (fun x : ℝ × ℝ =>
        Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
      = (Set.Ioc s t ×ˢ A).indicator
          fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 - ↑ξ * ↑q.2 * Complex.I := by
    funext x
    by_cases hx : x ∈ Set.Ioc s t ×ˢ A
    · rw [hf_def]; simp only [Set.indicator_of_mem hx]
    · rw [hf_def]; simp [Set.indicator_of_notMem hx]
  have hbound2 : ∀ x : ℝ × ℝ, ‖Complex.exp (↑ξ * ↑x.2 * Complex.I) - 1‖ ≤ 2 := fun x => by
    calc ‖Complex.exp (↑ξ * ↑x.2 * Complex.I) - 1‖
        ≤ ‖Complex.exp (↑ξ * ↑x.2 * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by
        rw [show (↑ξ * ↑x.2 * Complex.I : ℂ) = ↑(ξ * x.2) * Complex.I from by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, norm_one]; norm_num
  have hintegrand_meas : Measurable
      fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 - ↑ξ * ↑q.2 * Complex.I := by
    have h1 : Measurable fun q : ℝ × ℝ => (↑ξ * ↑q.2 * Complex.I : ℂ) :=
      ((Complex.measurable_ofReal.comp measurable_snd).const_mul (↑ξ)).mul_const Complex.I
    exact ((Complex.measurable_exp.comp h1).sub measurable_const).sub h1
  have hband_intOn : IntegrableOn
      (fun q : ℝ × ℝ => Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 - ↑ξ * ↑q.2 * Complex.I)
      (Set.Ioc s t ×ˢ A) (volume.prod ν) := by
    refine IntegrableOn.of_bound hbandfin hintegrand_meas.aestronglyMeasurable (2 + |ξ|) ?_
    refine (ae_restrict_mem hbandmeas).mono fun q hq => ?_
    obtain ⟨h1, h2⟩ := hAsub hq.2
    have habs : |q.2| ≤ 1 := abs_le.mpr ⟨le_of_lt h1, le_of_lt h2⟩
    have hlin : ‖(↑ξ * ↑q.2 * Complex.I : ℂ)‖ ≤ |ξ| := by
      rw [show (↑ξ * ↑q.2 * Complex.I : ℂ) = ↑(ξ * q.2) * Complex.I from by push_cast; ring,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      calc |ξ| * |q.2| ≤ |ξ| * 1 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
        _ = |ξ| := mul_one _
    calc ‖Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1 - ↑ξ * ↑q.2 * Complex.I‖
        ≤ ‖Complex.exp (↑ξ * ↑q.2 * Complex.I) - 1‖ + ‖(↑ξ * ↑q.2 * Complex.I : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ 2 + |ξ| := add_le_add (hbound2 q) hlin
  have hg_int : Integrable (fun x : ℝ × ℝ =>
      Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I) (volume.prod ν) := by
    rw [hg'eq]; exact (integrable_indicator_iff hbandmeas).mpr hband_intOn
  -- The piece-partition sum of the per-piece exponents.
  have hGHasSum : HasSum
      (fun k => ∫ x in prmPiece (volume.prod ν) k,
        (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I) ∂(volume.prod ν))
      (∫ x, (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
        ∂(volume.prod ν)) := by
    have h := hasSum_integral_iUnion (μ := volume.prod ν)
      (f := fun x : ℝ × ℝ =>
        Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
      (fun k => measurableSet_prmPiece (m := volume.prod ν))
      (pairwise_disjoint_prmPiece (m := volume.prod ν))
      (by rw [iUnion_prmPiece]; exact hg_int.integrableOn)
    rwa [iUnion_prmPiece, setIntegral_univ] at h
  -- The band integral equals the compensated-Poisson exponent.
  have hfinal : (∫ x, (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
        ∂(volume.prod ν))
      = ((t - s : ℝ) : ℂ)
          * ∫ x in A, (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν := by
    rw [hg'eq, integral_indicator hbandmeas, setIntegral_prod _ hband_intOn]
    dsimp only
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hst), Complex.real_smul]
    refine congrArg (fun z => ((↑(t - s) : ℂ)) * z) ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    simp only [mul_comm (↑ξ : ℂ) (↑y : ℂ)]
  -- Dominated convergence: partial compensated sums converge a.e. to the compensated Poisson sum.
  have hmeas_sum : AEStronglyMeasurable (compensatedPoissonSum K X f (volume.prod ν)) μ :=
    (memLp_two_compensatedPoissonSum hd hbandFnmeas hf1 hf2).aestronglyMeasurable
  have hFmeas : ∀ n, Measurable fun ω =>
      Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I) := fun n =>
    hgmeas.comp (Finset.measurable_sum _ fun k _ =>
      measurable_compensatedPieceSum hd hbandFnmeas)
  have hbound : ∀ n, ∀ᵐ ω ∂μ, ‖Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I)‖
        ≤ (fun _ : Ω => (1 : ℝ)) ω := fun n => by
    filter_upwards with ω
    rw [show (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
          compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I : ℂ)
        = ↑(ξ * ∑ k ∈ Finset.range (n + 1),
          compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n =>
      Complex.exp (↑ξ * ↑(∑ k ∈ Finset.range (n + 1),
        compensatedPieceSum K X f (volume.prod ν) k ω) * Complex.I)) atTop
      (𝓝 (Complex.exp (↑ξ * ↑(compensatedPoissonSum K X f (volume.prod ν) ω) * Complex.I))) := by
    filter_upwards [ae_finite_support_pieceSum hd hbandmeas hbandfin (g := f)
      (fun p hp => by rw [hf_def]; exact Set.indicator_of_notMem hp _)] with ω hωfin
    have hsummablePiece : Summable (fun k => pieceSum K X f k ω) :=
      summable_of_ne_finset_zero (s := hωfin.toFinset) fun k hk => by
        by_contra hne
        exact hk (hωfin.mem_toFinset.mpr hne)
    have hsummableC : Summable (fun k =>
        ∫ x in prmPiece (volume.prod ν) k, f x ∂(volume.prod ν)) := by
      have h := hasSum_integral_iUnion (μ := volume.prod ν) (f := f)
        (fun k => measurableSet_prmPiece (m := volume.prod ν))
        (pairwise_disjoint_prmPiece (m := volume.prod ν))
        (by rw [iUnion_prmPiece]; exact hf1.integrableOn)
      exact h.summable
    have hsummableComp : Summable (fun k => compensatedPieceSum K X f (volume.prod ν) k ω) :=
      (hsummablePiece.hasSum.sub hsummableC.hasSum).summable
    have htends : Tendsto (fun n => ∑ k ∈ Finset.range (n + 1),
          compensatedPieceSum K X f (volume.prod ν) k ω)
        atTop (𝓝 (compensatedPoissonSum K X f (volume.prod ν) ω)) :=
      hsummableComp.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    exact (hgcont.tendsto _).comp htends
  have hdct := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun n => (hFmeas n).aestronglyMeasurable) (integrable_const 1) hbound hlim
  simp_rw [charFun_partial_compensatedBandSum hd hbandFnmeas hf1 ξ] at hdct
  -- The product side converges to the compensated-Poisson exponential.
  have hprodexp : ∀ n, ∏ k ∈ Finset.range (n + 1),
        Complex.exp (∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I) ∂(volume.prod ν))
      = Complex.exp (∑ k ∈ Finset.range (n + 1),
          ∫ x in prmPiece (volume.prod ν) k,
            (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
              ∂(volume.prod ν)) :=
    fun n => (Complex.exp_sum _ _).symm
  simp_rw [hprodexp] at hdct
  have hprodlim : Tendsto (fun n => Complex.exp (∑ k ∈ Finset.range (n + 1),
        ∫ x in prmPiece (volume.prod ν) k,
          (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
            ∂(volume.prod ν))) atTop
      (𝓝 (Complex.exp (∫ x,
        (Complex.exp (↑ξ * ↑(f x) * Complex.I) - 1 - ↑ξ * ↑(f x) * Complex.I)
          ∂(volume.prod ν)))) :=
    (Complex.continuous_exp.tendsto _).comp
      (hGHasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))
  have hval := tendsto_nhds_unique hdct hprodlim
  rw [charFun_apply_real, integral_map hmeas_sum.aemeasurable (by fun_prop), hval, hfinal]

/-- **Characteristic function of a compensated band sum.** For a mark set `A` inside the unit
interval with finite `ν`-mass, the compensated Poisson sum of the band test function
`1_{(0,t] × A}(u, x) · x` has characteristic function `exp (t · ∫_A (e^{ixξ} − 1 − ixξ) dν)`. -/
theorem charFun_map_compensatedBandSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ)
    {A : Set ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Set.Ioo (-1) 1) (hAfin : ν A < ⊤)
    {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    charFun (μ.map (compensatedPoissonSum K X
        ((Set.Ioc 0 t ×ˢ A).indicator fun p => p.2) ((volume : Measure ℝ).prod ν))) ξ
      = Complex.exp ((t : ℂ) * ∫ x in A,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) := by
  have h := charFun_map_compensatedTimeBandSum hd hA hAsub hAfin (s := 0) ht ξ
  rwa [sub_zero] at h

/-! ### The law of the compensated small-jump integral

The compensated small-jump integral `levyCompensatedSmallJump` has characteristic function
`exp (t · ∫_{(-1,1)} (e^{ixξ} − 1 − ixξ) dν)` — the small-jump factor of the Lévy–Khintchine
exponent. The proof truncates the mark set to the annuli `A n := (-1, 1) ∩ {x | 1/(n+1) ≤ |x|}`,
each of finite `ν`-mass, so that `charFun_map_compensatedBandSum` applies to the truncated integral;
the truncated integral converges to `levyCompensatedSmallJump` in `L²(μ)`, hence its characteristic
function converges, and the exponent converges by dominated convergence. -/

/-- The charFun distance of two real random variables is controlled by their L¹ distance. -/
private lemma norm_charFun_map_sub_le [IsProbabilityMeasure μ] {V W : Ω → ℝ}
    (hV : AEMeasurable V μ) (hW : AEMeasurable W μ)
    (hVW : Integrable (fun ω => V ω - W ω) μ) (ξ : ℝ) :
    ‖charFun (μ.map V) ξ - charFun (μ.map W) ξ‖ ≤ |ξ| * ∫ ω, |V ω - W ω| ∂μ := by
  have hgV : AEMeasurable (fun ω => Complex.exp (↑ξ * ↑(V ω) * Complex.I)) μ :=
    Complex.measurable_exp.comp_aemeasurable
      (((Complex.measurable_ofReal.comp_aemeasurable hV).const_mul (↑ξ)).mul_const Complex.I)
  have hgW : AEMeasurable (fun ω => Complex.exp (↑ξ * ↑(W ω) * Complex.I)) μ :=
    Complex.measurable_exp.comp_aemeasurable
      (((Complex.measurable_ofReal.comp_aemeasurable hW).const_mul (↑ξ)).mul_const Complex.I)
  have hbV : ∀ ω, ‖Complex.exp (↑ξ * ↑(V ω) * Complex.I)‖ ≤ 1 := fun ω => by
    rw [show (↑ξ * ↑(V ω) * Complex.I : ℂ) = ↑(ξ * V ω) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hbW : ∀ ω, ‖Complex.exp (↑ξ * ↑(W ω) * Complex.I)‖ ≤ 1 := fun ω => by
    rw [show (↑ξ * ↑(W ω) * Complex.I : ℂ) = ↑(ξ * W ω) * Complex.I from by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hIV : Integrable (fun ω => Complex.exp (↑ξ * ↑(V ω) * Complex.I)) μ :=
    Integrable.of_bound hgV.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbV)
  have hIW : Integrable (fun ω => Complex.exp (↑ξ * ↑(W ω) * Complex.I)) μ :=
    Integrable.of_bound hgW.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbW)
  rw [charFun_apply_real, charFun_apply_real,
    integral_map hV (by fun_prop), integral_map hW (by fun_prop),
    ← integral_sub hIV hIW]
  calc ‖∫ ω, (Complex.exp (↑ξ * ↑(V ω) * Complex.I)
            - Complex.exp (↑ξ * ↑(W ω) * Complex.I)) ∂μ‖
      ≤ ∫ ω, ‖Complex.exp (↑ξ * ↑(V ω) * Complex.I)
            - Complex.exp (↑ξ * ↑(W ω) * Complex.I)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |ξ| * |V ω - W ω| ∂μ := by
        refine integral_mono ((hIV.sub hIW).norm) (hVW.abs.const_mul |ξ|) fun ω => ?_
        have hfactor : Complex.exp (↑ξ * ↑(V ω) * Complex.I)
              - Complex.exp (↑ξ * ↑(W ω) * Complex.I)
            = Complex.exp (↑ξ * ↑(W ω) * Complex.I)
              * (Complex.exp (Complex.I * ↑(ξ * (V ω - W ω))) - 1) := by
          rw [mul_sub, mul_one, ← Complex.exp_add]
          congr 2
          push_cast; ring
        rw [hfactor, norm_mul,
          show (↑ξ * ↑(W ω) * Complex.I : ℂ) = ↑(ξ * W ω) * Complex.I from by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        calc ‖Complex.exp (Complex.I * ↑(ξ * (V ω - W ω))) - 1‖
            ≤ ‖ξ * (V ω - W ω)‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
          _ = |ξ| * |V ω - W ω| := by rw [Real.norm_eq_abs, abs_mul]
    _ = |ξ| * ∫ ω, |V ω - W ω| ∂μ := integral_const_mul _ _

/-- The squared `L²` seminorm of a band indicator over a measurable mark set `C`. -/
lemma eLpNorm_sq_bandFun {C : Set ℝ} (hC : MeasurableSet C) (s t : ℝ) :
    (eLpNorm ((Set.Ioc s t ×ˢ C).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν)) ^ 2
      = ENNReal.ofReal (t - s) * ∫⁻ x in C, ENNReal.ofReal (x ^ 2) ∂ν := by
  rw [eLpNorm_two_sq, lintegral_enorm_rpow_band hC, setLIntegral_band_snd_sq hC]

/-- The `L²(μ)` distance between the compensated small-jump band integral over `(s, t]` and its
truncation to a mark set `B ⊆ (-1, 1)` of finite mass equals the `L²(volume.prod ν)` seminorm of the
band indicator over the complementary slice `(s, t] × ((-1, 1) \ B)`. -/
private lemma eLpNorm_smallJumpBand_sub_bandFun [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (s t : ℝ) {B : Set ℝ} (hB : MeasurableSet B) (hBsub : B ⊆ Set.Ioo (-1) 1) (hBfin : ν B < ⊤) :
    eLpNorm (compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))
        - compensatedPoissonIntegral hd ((memLp_two_bandFun hB hBsub hBfin s t).toLp
            ((Set.Ioc s t ×ˢ B).indicator fun p => p.2))) 2 μ
      = eLpNorm ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \ B)).indicator fun p : ℝ × ℝ => p.2) 2
          (volume.prod ν) := by
  have hunion_prod : Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1
      = (Set.Ioc s t ×ˢ B) ∪ (Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \ B)) := by
    rw [← Set.prod_union, Set.union_sdiff_cancel hBsub]
  have hdisj_prod : Disjoint (Set.Ioc s t ×ˢ B) (Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \ B)) :=
    Set.Disjoint.set_prod_right disjoint_sdiff_self_right _ _
  have hsplit_fun : ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p : ℝ × ℝ => p.2)
        - ((Set.Ioc s t ×ˢ B).indicator fun p : ℝ × ℝ => p.2)
      = (Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \ B)).indicator fun p : ℝ × ℝ => p.2 := by
    rw [hunion_prod, Set.indicator_union_of_disjoint hdisj_prod]
    ext p
    simp only [Pi.sub_apply]
    ring
  have hsub : compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))
        - compensatedPoissonIntegral hd ((memLp_two_bandFun hB hBsub hBfin s t).toLp
            ((Set.Ioc s t ×ˢ B).indicator fun p => p.2))
      = compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
            ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2)
          - (memLp_two_bandFun hB hBsub hBfin s t).toLp
            ((Set.Ioc s t ×ˢ B).indicator fun p => p.2)) :=
    (compensatedPoissonIntegral_sub _ _ _).symm
  rw [hsub, eLpNorm_compensatedPoissonIntegral]
  refine eLpNorm_congr_ae ?_
  filter_upwards [Lp.coeFn_sub ((memLp_two_smallJumpBandFun hν s t).toLp
      ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))
      ((memLp_two_bandFun hB hBsub hBfin s t).toLp
      ((Set.Ioc s t ×ˢ B).indicator fun p => p.2)),
    (memLp_two_smallJumpBandFun hν s t).coeFn_toLp,
    (memLp_two_bandFun hB hBsub hBfin s t).coeFn_toLp] with p h0 h2 h3
  rw [h0]
  simp only [Pi.sub_apply]
  rw [h2, h3]
  exact congrFun hsplit_fun p

omit [SigmaFinite ν] in
/-- As `n → ∞`, the shrinking-ball tail of `∫ x² dν` over `(-1, 1)` vanishes. -/
lemma tendsto_lintegral_slice_sq (hν : IsLevyMeasure ν) :
    Tendsto (fun n : ℕ => ∫⁻ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹},
        ENNReal.ofReal (x ^ 2) ∂ν) atTop (𝓝 0) := by
  have hslice_meas : ∀ n : ℕ,
      MeasurableSet (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹}) :=
    fun n => measurableSet_Ioo.inter (measurableSet_lt continuous_abs.measurable measurable_const)
  have hsqmeas : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_id'.pow_const 2)
  have hlim : ∀ x : ℝ, Tendsto (fun n : ℕ =>
      (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
        (fun y => ENNReal.ofReal (y ^ 2)) x) atTop (𝓝 0) := by
    intro x
    by_cases hx0 : x = 0
    · have hz : (fun n : ℕ => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
          (fun y => ENNReal.ofReal (y ^ 2)) x) = fun _ => 0 := by
        funext n; simp [Set.indicator_apply, hx0]
      rw [hz]; exact tendsto_const_nhds
    · have habs : (0:ℝ) < |x| := abs_pos.mpr hx0
      obtain ⟨N, hN⟩ := exists_nat_gt (|x|⁻¹)
      have hev : ∀ᶠ (n : ℕ) in atTop, (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
          (fun y => ENNReal.ofReal (y ^ 2)) x = 0 := by
        rw [Filter.eventually_atTop]
        refine ⟨N, fun n hn => Set.indicator_of_notMem (fun hmem => ?_) _⟩
        have hxinv : |x|⁻¹ < (n:ℝ) + 1 := by
          have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
          linarith [hN]
        have h1 : (1:ℝ) < |x| * ((n:ℝ) + 1) := by
          have h2 := mul_lt_mul_of_pos_left hxinv habs
          rwa [mul_inv_cancel₀ (ne_of_gt habs)] at h2
        have hc_lt : ((n:ℝ) + 1)⁻¹ < |x| := by
          rw [inv_eq_one_div, div_lt_iff₀ (Nat.cast_add_one_pos n)]; linarith [h1]
        exact absurd hmem.2 (not_lt.mpr hc_lt.le)
      exact (tendsto_congr' hev).mpr tendsto_const_nhds
  have hdct := tendsto_lintegral_of_dominated_convergence (μ := ν)
    (F := fun n x => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
      (fun y => ENNReal.ofReal (y ^ 2)) x)
    (f := fun _ => 0)
    (bound := (Set.Ioo (-1:ℝ) 1).indicator fun y => ENNReal.ofReal (y ^ 2))
    (fun n => hsqmeas.indicator (hslice_meas n))
    (fun n => Filter.Eventually.of_forall fun x =>
      Set.indicator_le_indicator_apply_of_subset Set.inter_subset_left zero_le)
    (by rw [lintegral_indicator measurableSet_Ioo]; exact (lintegral_Ioo_sq_lt_top hν).ne)
    (Filter.Eventually.of_forall hlim)
  have hrw : (fun n : ℕ => ∫⁻ x,
        (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | |y| < ((n:ℝ) + 1)⁻¹}).indicator
          (fun y => ENNReal.ofReal (y ^ 2)) x ∂ν)
      = fun n : ℕ => ∫⁻ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹},
          ENNReal.ofReal (x ^ 2) ∂ν := by
    funext n; rw [lintegral_indicator (hslice_meas n)]
  rw [hrw] at hdct
  simpa using hdct

omit [SigmaFinite ν] in
/-- As `n → ∞`, the integral of the compensated small-jump integrand over the annulus
`(-1, 1) ∩ {1/(n+1) ≤ |x|}` converges to its integral over all of `(-1, 1)`. -/
private lemma tendsto_setIntegral_annulus (hν : IsLevyMeasure ν) (ξ : ℝ) :
    Tendsto (fun n : ℕ => ∫ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|},
        (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν) atTop
      (𝓝 (∫ x in Set.Ioo (-1:ℝ) 1,
        (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν)) := by
  have hA_meas : ∀ n : ℕ,
      MeasurableSet (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|}) :=
    fun n => measurableSet_Ioo.inter (measurableSet_le measurable_const continuous_abs.measurable)
  have hgmeas : Measurable fun x : ℝ =>
      Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I := by
    have h1 : Measurable fun x : ℝ => (↑x * ↑ξ * Complex.I : ℂ) :=
      ((Complex.measurable_ofReal.mul measurable_const).mul measurable_const)
    exact ((Complex.measurable_exp.comp h1).sub measurable_const).sub h1
  -- On `(-1,1)` the integrand equals the compensated Lévy integrand.
  have hg_eq : ∀ x ∈ Set.Ioo (-1:ℝ) 1,
      Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I = levyCompensatedIntegrand ξ x := by
    intro x hx
    have hlt : |x| < 1 := abs_lt.mpr hx
    simp [levyCompensatedIntegrand, hlt]
  have hbound_int : Integrable (fun x : ℝ => (2 + 3 * ξ ^ 2) * min 1 (x ^ 2)) ν := by
    refine ⟨((measurable_const.min (measurable_id'.pow_const 2)).const_mul _).aestronglyMeasurable,
      ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hC : (0:ℝ) ≤ 2 + 3 * ξ ^ 2 := by positivity
    have henorm : ∀ x : ℝ, ‖(2 + 3 * ξ ^ 2) * min 1 (x ^ 2)‖ₑ
        = ENNReal.ofReal (2 + 3 * ξ ^ 2) * ENNReal.ofReal (min 1 (x ^ 2)) := fun x => by
      rw [Real.enorm_eq_ofReal (mul_nonneg hC (le_min zero_le_one (sq_nonneg x))),
        ENNReal.ofReal_mul hC]
    simp_rw [henorm]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hν.lintegral_min_one_sq_lt_top
  have hlim : ∀ x : ℝ, Tendsto (fun n : ℕ =>
      (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
        (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x) atTop
      (𝓝 ((Set.Ioo (-1:ℝ) 1).indicator
        (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x)) := by
    intro x
    by_cases hxo : x ∈ Set.Ioo (-1:ℝ) 1
    · rw [Set.indicator_of_mem hxo]
      by_cases hx0 : x = 0
      · have hz : (fun n : ℕ => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
            (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x)
            = fun _ => Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I := by
          funext n; rw [hx0]; simp [Set.indicator_apply]
        rw [hz]; exact tendsto_const_nhds
      · have habs : (0:ℝ) < |x| := abs_pos.mpr hx0
        obtain ⟨N, hN⟩ := exists_nat_gt (|x|⁻¹)
        have hev : ∀ᶠ (n : ℕ) in atTop, (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
            (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x
            = Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I := by
          rw [Filter.eventually_atTop]
          refine ⟨N, fun n hn => ?_⟩
          have hxinv : |x|⁻¹ < (n:ℝ) + 1 := by
            have hNn : (N:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
            linarith [hN]
          have h1 : (1:ℝ) < |x| * ((n:ℝ) + 1) := by
            have h2 := mul_lt_mul_of_pos_left hxinv habs
            rwa [mul_inv_cancel₀ (ne_of_gt habs)] at h2
          have hmem : x ∈ Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|} := by
            refine ⟨hxo, ?_⟩
            show ((n:ℝ) + 1)⁻¹ ≤ |x|
            rw [inv_eq_one_div, div_le_iff₀ (Nat.cast_add_one_pos n)]; linarith [h1]
          exact Set.indicator_of_mem hmem _
        exact (tendsto_congr' hev).mpr tendsto_const_nhds
    · rw [Set.indicator_of_notMem hxo]
      have hz : (fun n : ℕ => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
          (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x)
          = fun _ => 0 := by
        funext n; exact Set.indicator_of_notMem (fun hmem => hxo hmem.1) _
      rw [hz]; exact tendsto_const_nhds
  have hdct := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun n x => (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
      (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x)
    (f := (Set.Ioo (-1:ℝ) 1).indicator
      fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I)
    (bound := fun x => (2 + 3 * ξ ^ 2) * min 1 (x ^ 2))
    (fun n => (hgmeas.indicator (hA_meas n)).aestronglyMeasurable) hbound_int
    (fun n => Filter.Eventually.of_forall fun x => ?_) (Filter.Eventually.of_forall hlim)
  · rw [integral_indicator measurableSet_Ioo] at hdct
    have hrw : (fun n : ℕ => ∫ x,
          (Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}).indicator
            (fun y => Complex.exp (↑y * ↑ξ * Complex.I) - 1 - ↑y * ↑ξ * Complex.I) x ∂ν)
        = fun n : ℕ => ∫ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|},
            (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν := by
      funext n; rw [integral_indicator (hA_meas n)]
    rw [hrw] at hdct
    exact hdct
  · -- pointwise bound
    by_cases hxa : x ∈ Set.Ioo (-1:ℝ) 1 ∩ {y : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |y|}
    · rw [Set.indicator_of_mem hxa, hg_eq x hxa.1]
      exact norm_levyCompensatedIntegrand_le ξ x
    · rw [Set.indicator_of_notMem hxa, norm_zero]
      exact mul_nonneg (by positivity) (le_min zero_le_one (sq_nonneg x))

/-- **The law of the compensated small-jump band integral over `(s, t]`:** the compensated Poisson
integral of the band test function on `(s, t] × (-1, 1)` has characteristic function
`exp ((t − s) · ∫_{(-1,1)} (e^{ixξ} − 1 − ixξ) dν)` — the band-generic small-jump engine. -/
private lemma charFun_map_smallJumpBandIntegral [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => (compensatedPoissonIntegral hd
        ((memLp_two_smallJumpBandFun hν s t).toLp
          ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))) ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in Set.Ioo (-1) 1,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) := by
  set V : Lp ℝ 2 μ := compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
      ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2)) with hV
  have hA_meas : ∀ n : ℕ,
      MeasurableSet (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|}) :=
    fun n => measurableSet_Ioo.inter (measurableSet_le measurable_const continuous_abs.measurable)
  have hA_sub : ∀ n : ℕ,
      Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|} ⊆ Set.Ioo (-1) 1 :=
    fun n => Set.inter_subset_left
  have hA_fin : ∀ n : ℕ, ν (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|}) < ⊤ := fun n =>
    (measure_mono Set.inter_subset_right).trans_lt
      (hν.measure_setOf_abs_ge_lt_top (by positivity))
  have hslice_eq : ∀ n : ℕ,
      Set.Ioo (-1:ℝ) 1 \ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})
        = Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹} := by
    intro n
    ext x
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq, not_and, not_le]
    exact ⟨fun ⟨hxo, h⟩ => ⟨hxo, h hxo⟩, fun ⟨hxo, h⟩ => ⟨hxo, fun _ => h⟩⟩
  -- The truncated compensated integral agrees a.e. with the compensated band sum.
  have hTrunc_ae : ∀ n : ℕ, (fun ω => (compensatedPoissonIntegral hd
        ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2))) ω)
      =ᵐ[μ] compensatedPoissonSum K X
        ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator fun p => p.2)
        ((volume : Measure ℝ).prod ν) := fun n =>
    compensatedPoissonIntegral_eq_sum hd (measurable_bandFun (hA_meas n) s t)
      (integrable_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t)
      (memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t)
  -- The charFun of the truncated integral is the annulus exponential.
  have hcharTrunc : ∀ n : ℕ, charFun (μ.map (fun ω => (compensatedPoissonIntegral hd
        ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2))) ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ)
          * ∫ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|},
          (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν) := by
    intro n
    rw [Measure.map_congr (hTrunc_ae n),
      charFun_map_compensatedTimeBandSum hd (hA_meas n) (hA_sub n) (hA_fin n) hst ξ]
  -- The annulus exponentials converge to the small-jump exponential.
  have hRHS : Tendsto (fun n : ℕ => Complex.exp (((t - s : ℝ) : ℂ) *
        ∫ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|},
          (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν)) atTop
      (𝓝 (Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in Set.Ioo (-1:ℝ) 1,
        (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I) ∂ν))) :=
    (Complex.continuous_exp.tendsto _).comp
      ((tendsto_setIntegral_annulus hν ξ).const_mul ((t - s : ℝ) : ℂ))
  -- The band distance rewrites through the increment sub-lemma.
  have hdist : ∀ n : ℕ, eLpNorm (V - compensatedPoissonIntegral hd
        ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2))) 2 μ
      = eLpNorm ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 \
          (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|}))).indicator fun p : ℝ × ℝ => p.2) 2
          (volume.prod ν) := by
    intro n
    rw [hV]
    exact eLpNorm_smallJumpBand_sub_bandFun hd hν s t (hA_meas n) (hA_sub n) (hA_fin n)
  -- The `L²(μ)` distance to the band integral vanishes.
  have htend_r : Tendsto (fun n : ℕ => (eLpNorm (V
        - compensatedPoissonIntegral hd
          ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
            ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
              fun p => p.2))) 2 μ).toReal) atTop (𝓝 0) := by
    have hsq : ∀ n : ℕ, ((eLpNorm (V
          - compensatedPoissonIntegral hd
            ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
              ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                fun p => p.2))) 2 μ).toReal) ^ 2
        = (t - s) * (∫⁻ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹},
            ENNReal.ofReal (x ^ 2) ∂ν).toReal := by
      intro n
      rw [← ENNReal.toReal_pow, hdist n,
        eLpNorm_sq_bandFun (measurableSet_Ioo.diff (hA_meas n)) s t, hslice_eq n,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
    have hJ : Tendsto (fun n : ℕ => (∫⁻ x in Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | |x| < ((n:ℝ) + 1)⁻¹},
          ENNReal.ofReal (x ^ 2) ∂ν).toReal) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (ENNReal.tendsto_toReal (by simp)).comp (tendsto_lintegral_slice_sq hν)
    have hr2 : Tendsto (fun n : ℕ => ((eLpNorm (V
          - compensatedPoissonIntegral hd
            ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
              ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                fun p => p.2))) 2 μ).toReal) ^ 2) atTop (𝓝 0) := by
      simp_rw [hsq]; simpa using hJ.const_mul (t - s)
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hr2
    rw [Real.sqrt_zero] at hsqrt
    exact hsqrt.congr fun n => Real.sqrt_sq ENNReal.toReal_nonneg
  -- The L¹ distance is dominated by the L² distance.
  have hbnd : ∀ n : ℕ, ∫ ω, |V ω
        - (compensatedPoissonIntegral hd
          ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
            ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
              fun p => p.2))) ω| ∂μ
      ≤ (eLpNorm (V
          - compensatedPoissonIntegral hd
            ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
              ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                fun p => p.2))) 2 μ).toReal := by
    intro n
    set Hn := V
      - compensatedPoissonIntegral hd
        ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2)) with hHn
    calc ∫ ω, |V ω
            - (compensatedPoissonIntegral hd
              ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
                ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                  fun p => p.2))) ω| ∂μ
        = ∫ ω, ‖Hn ω‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hHn ▸ Lp.coeFn_sub V
            (compensatedPoissonIntegral hd
              ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
                ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
                  fun p => p.2)))] with ω hω
          rw [Real.norm_eq_abs, hω]; rfl
      _ = (eLpNorm Hn 1 μ).toReal := by
          rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable Hn),
            ← eLpNorm_one_eq_lintegral_enorm]
      _ ≤ (eLpNorm Hn 2 μ).toReal :=
          ENNReal.toReal_mono (Lp.eLpNorm_ne_top Hn)
            (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable Hn))
  -- The characteristic function of the truncated integral converges to that of the band one.
  have hint0 : Tendsto (fun n : ℕ => ∫ ω, |V ω
        - (compensatedPoissonIntegral hd
          ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
            ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
              fun p => p.2))) ω| ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) hbnd htend_r
  have hLHS : Tendsto (fun n : ℕ => charFun (μ.map (fun ω => (compensatedPoissonIntegral hd
        ((memLp_two_bandFun (hA_meas n) (hA_sub n) (hA_fin n) s t).toLp
          ((Set.Ioc s t ×ˢ (Set.Ioo (-1:ℝ) 1 ∩ {x : ℝ | ((n:ℝ) + 1)⁻¹ ≤ |x|})).indicator
            fun p => p.2))) ω)) ξ) atTop
      (𝓝 (charFun (μ.map (fun ω => V ω)) ξ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hint0.const_mul |ξ|)
    rw [norm_sub_rev]
    exact norm_charFun_map_sub_le
      (Lp.aestronglyMeasurable V).aemeasurable
      (Lp.aestronglyMeasurable _).aemeasurable
      (((Lp.memLp V).integrable (by norm_num)).sub
        ((Lp.memLp _).integrable (by norm_num))) ξ
  exact tendsto_nhds_unique (hLHS.congr fun n => hcharTrunc n) hRHS

/-- **The law of the compensated small-jump integral:** its characteristic function is
`exp (t · ∫_{(-1,1)} (e^{ixξ} − 1 − ixξ) dν)` — the small-jump factor of the
Lévy–Khintchine exponent. -/
theorem charFun_map_levyCompensatedSmallJump [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => levyCompensatedSmallJump hd hν t ω)) ξ
      = Complex.exp ((t : ℂ) * ∫ x in Set.Ioo (-1) 1,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) := by
  have h := charFun_map_smallJumpBandIntegral hd hν (s := 0) ht ξ
  rw [sub_zero] at h
  exact h

/-- The compensated small-jump increment over `(s, t]` has the small-jump law at rate `(t − s)`. -/
theorem charFun_map_levyCompensatedSmallJump_sub [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    {s t : ℝ} (h0 : 0 ≤ s) (hst : s ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => levyCompensatedSmallJump hd hν t ω
        - levyCompensatedSmallJump hd hν s ω)) ξ
      = Complex.exp (((t - s : ℝ) : ℂ) * ∫ x in Set.Ioo (-1) 1,
          (Complex.exp (x * ξ * Complex.I) - 1 - x * ξ * Complex.I) ∂ν) := by
  have hmap : (fun ω => levyCompensatedSmallJump hd hν t ω - levyCompensatedSmallJump hd hν s ω)
      =ᵐ[μ] fun ω => (compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
        ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2))) ω := by
    have hsub : levyCompensatedSmallJump hd hν t - levyCompensatedSmallJump hd hν s
        = compensatedPoissonIntegral hd ((memLp_two_smallJumpBandFun hν s t).toLp
            ((Set.Ioc s t ×ˢ Set.Ioo (-1:ℝ) 1).indicator fun p => p.2)) :=
      levyCompensatedSmallJump_sub hd hν h0 hst
    filter_upwards [Lp.coeFn_sub (levyCompensatedSmallJump hd hν t)
      (levyCompensatedSmallJump hd hν s)] with ω hω
    rw [Pi.sub_apply] at hω
    rw [← hω, hsub]
  rw [Measure.map_congr hmap]
  exact charFun_map_smallJumpBandIntegral hd hν hst ξ

end LevyIntensity

end ProbabilityTheory
