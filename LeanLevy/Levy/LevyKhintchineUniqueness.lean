/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Levy.LevyKhintchineProof

/-!
# Uniqueness of the Lévy–Khintchine triple: the smeared canonical measure

This file begins Part B of the Lévy–Khintchine programme: the triple `(b, σ², ν)` is
determined by the characteristic exponent. The route follows Sato (Theorem 8.1): the
*smeared exponent*
`g(ξ) := ψ(ξ) − ½ ∫_{[-1,1]} ψ(ξ + u) du`
is the characteristic function of a **finite** measure `ρ` on `ℝ`, from which `σ²` is read
off as an atom and `ν` by untilting on `{0}ᶜ`.

## The smeared measure

We construct `ρ = smearedMeasure σ² ν` and prove it is finite and computes its atom at `0`.
Later tasks identify `charFun ρ` with the smeared exponent (giving `ρ` from the exponent alone)
and invert `ρ` back to `(σ², ν)`.

### Pinning the Gaussian coefficient (worked by hand)

The Gaussian piece of the LK exponent is `ψ_G(ξ) = −σ²ξ²/2`. Its smear is
```
g_G(ξ) = ψ_G(ξ) − ½ ∫_{-1}^{1} ψ_G(ξ + u) du
       = −σ²ξ²/2 + (σ²/4) ∫_{-1}^{1} (ξ + u)² du.
```
Since `∫_{-1}^{1} (ξ + u)² du = ∫_{-1}^{1} (ξ² + 2ξu + u²) du = 2ξ² + 0 + 2/3`, we get
```
g_G(ξ) = −σ²ξ²/2 + (σ²/4)(2ξ² + 2/3) = −σ²ξ²/2 + σ²ξ²/2 + σ²/6 = σ²/6.
```
The Gaussian smear is the **constant** `σ²/6`; a constant is the characteristic function of a
point mass at `0`, so `ρ` carries a Dirac atom of weight `σ²/6` (NOT `σ²`). Hence the
recovery formula `σ² = 6 · ρ{0}` (`smearedMeasure_singleton_zero`).

### The jump piece

The smear of the jump piece produces, via the Fourier identity
`½ ∫_{-1}^{1} e^{iux} du = Real.sinc x` (`intervalIntegral_exp_I_symm`), a density
`1 − Real.sinc x` against `ν`. We use the mathlib spelling `Real.sinc x` throughout — for a
Lévy measure `ν` with `ν{0} = 0` this agrees `ν`-a.e. with the classical `1 − sin x / x`, and
`Real.sinc` makes the sinc bounds from `LevyKhintchineProof` (`one_sub_sinc_le_mul_min`,
`mul_min_le_one_sub_sinc`) apply syntactically.

## Main definitions

* `ProbabilityTheory.smearedMeasure` — the finite measure `ρ = (σ²/6)•δ₀ + ν.withDensity(1 − sinc)`.

## Main results

* `ProbabilityTheory.lintegral_one_sub_sinc_lt_top` — the withDensity mass is finite.
* `ProbabilityTheory.smearedMeasure_isFiniteMeasure` — `ρ` is a finite measure.
* `ProbabilityTheory.smearedMeasure_singleton_zero` — `ρ{0} = σ²/6`, so `σ² = 6·ρ{0}`.
-/

open MeasureTheory ENNReal Set
open scoped NNReal ENNReal Real

namespace ProbabilityTheory

variable (σ_sq : ℝ≥0) (ν : Measure ℝ)

/-- The **smeared canonical measure** `ρ` from Sato's uniqueness route. It is the finite
measure whose characteristic function is the smeared Lévy–Khintchine exponent
`g(ξ) = ψ(ξ) − ½ ∫_{[-1,1]} ψ(ξ + u) du`.

Its two pieces are pinned by the smear algebra:
* a Dirac atom at `0` of weight `σ²/6` (the smear of the Gaussian piece `−σ²ξ²/2` is the
  constant `σ²/6`; see the module docstring for the hand computation), and
* a density `1 − Real.sinc x` against the Lévy measure `ν` (the smear of the jump piece).

The `Real.sinc` spelling is chosen deliberately over the classical `1 − sin x / x`: the two
agree `ν`-a.e. when `ν{0} = 0`, and `Real.sinc` matches the sinc bounds proved in
`LevyKhintchineProof`. -/
noncomputable def smearedMeasure : Measure ℝ :=
  ((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)
    + ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))

/-- The density defining the jump piece of `smearedMeasure` is measurable. -/
theorem measurable_one_sub_sinc :
    Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.sinc x) :=
  ENNReal.measurable_ofReal.comp (measurable_const.sub Real.measurable_sinc)

/-- The mass of the jump (withDensity) piece of `smearedMeasure` is finite: it is dominated by
`2 · ∫⁻ min(1, x²) dν`, which is finite for a Lévy measure via `one_sub_sinc_le_mul_min`. -/
theorem lintegral_one_sub_sinc_lt_top {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤ := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.min (measurable_id'.pow_const 2))
  calc ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν
      ≤ ∫⁻ x, 2 * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (one_sub_sinc_le_mul_min x)
    _ = 2 * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := lintegral_const_mul 2 hmeas
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hν.lintegral_min_one_sq_lt_top

/-- `smearedMeasure σ² ν` is a finite measure when `ν` is a Lévy measure: the Dirac piece has
finite mass `σ²/6` and the withDensity piece has finite mass by
`lintegral_one_sub_sinc_lt_top`. -/
theorem smearedMeasure_isFiniteMeasure {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    IsFiniteMeasure (smearedMeasure σ_sq ν) := by
  refine ⟨?_⟩
  rw [smearedMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine ENNReal.add_lt_top.mpr ⟨?_, lintegral_one_sub_sinc_lt_top hν⟩
  exact ENNReal.mul_lt_top (by simp [ENNReal.div_lt_top]) (measure_lt_top _ _)

/-- The atom of the smeared measure at the origin is `σ²/6`: the withDensity piece vanishes on
`{0}` because a Lévy measure gives no mass to the origin. This pins the σ²-recovery
`σ² = 6 · (smearedMeasure σ² ν){0}` as a pure rewrite. -/
theorem smearedMeasure_singleton_zero {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    smearedMeasure σ_sq ν {0} = (σ_sq : ℝ≥0∞) / 6 := by
  have hd : (Measure.dirac (0 : ℝ)) {0} = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton 0)
  rw [smearedMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hd, mul_one,
    withDensity_apply _ (measurableSet_singleton 0),
    setLIntegral_measure_zero _ _ hν.zero_singleton, add_zero]

/-!
## The smear identity

We identify the *smeared exponent* `g(ξ) = ψ_T(ξ) − ½ ∫_{[-1,1]} ψ_T(ξ+u) du` with
`charFun (smearedMeasure σ² ν) ξ`. The drift piece cancels (its `u`-average is symmetric),
the Gaussian piece contributes the constant `σ²/6`, and the jump piece contributes
`∫ e^{ixξ}(1 − sinc x) dν`.
-/

section SmearIdentity

variable {ν : Measure ℝ}

/-- `1 − Real.sinc x` is non-negative everywhere (via the sinc lower bound). -/
private lemma one_sub_sinc_nonneg (x : ℝ) : 0 ≤ 1 - Real.sinc x :=
  le_trans (mul_nonneg (by positivity) (le_min zero_le_one (sq_nonneg x)))
    (mul_min_le_one_sub_sinc x)

/-- `∫_{-1}^{1} (ξ + u) du = 2ξ`. -/
private lemma intInt_linear (ξ : ℝ) : ∫ u in (-1 : ℝ)..1, (ξ + u) = 2 * ξ := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v) ξ, integral_id]
  ring

/-- `∫_{-1}^{1} (ξ + u)² du = 2ξ² + 2/3`. -/
private lemma intInt_quadratic (ξ : ℝ) : ∫ u in (-1 : ℝ)..1, (ξ + u) ^ 2 = 2 * ξ ^ 2 + 2 / 3 := by
  rw [intervalIntegral.integral_comp_add_left (fun v => v ^ 2) ξ, integral_pow]
  ring

/-- The symmetric exponential average, shifted: `∫_{-1}^{1} e^{ix(ξ+u)} du = e^{ixξ}·2·sinc x`. -/
private lemma intInt_exp_shift (ξ x : ℝ) :
    ∫ u in (-1 : ℝ)..1, Complex.exp (↑x * ↑(ξ + u) * Complex.I)
      = Complex.exp (↑x * ↑ξ * Complex.I) * (2 * (Real.sinc x : ℂ)) := by
  have hcongr : (fun u : ℝ => Complex.exp (↑x * ↑(ξ + u) * Complex.I))
      = fun u : ℝ => Complex.exp (↑x * ↑ξ * Complex.I) * Complex.exp (↑u * ↑x * Complex.I) := by
    funext u
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [hcongr, show (∫ u in (-1 : ℝ)..1,
        Complex.exp (↑x * ↑ξ * Complex.I) * Complex.exp (↑u * ↑x * Complex.I))
      = Complex.exp (↑x * ↑ξ * Complex.I) * ∫ u in (-1 : ℝ)..1, Complex.exp (↑u * ↑x * Complex.I)
    from intervalIntegral.integral_const_mul _ _]
  congr 1
  have h := intervalIntegral_exp_I_symm x
  rw [← h]; ring

/-- **Pointwise smear of the compensated integrand.** The compensator (linear in the
frequency) and the constant `−1` both cancel in the `u`-average, leaving `e^{ixξ}(1 − sinc x)`. -/
private lemma levyCompensatedIntegrand_smear (ξ x : ℝ) :
    levyCompensatedIntegrand ξ x
        - (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, levyCompensatedIntegrand (ξ + u) x
      = Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) := by
  -- Interval integrability of the two `u`-dependent pieces.
  have hexp_int : IntervalIntegrable
      (fun u => Complex.exp (↑x * ↑(ξ + u) * Complex.I)) volume (-1) 1 :=
    (Complex.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _
  have hlin_int : IntervalIntegrable
      (fun u => (↑x * ↑(ξ + u) * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0)))
      volume (-1) 1 :=
    (by fun_prop : Continuous fun u : ℝ =>
      (↑x * ↑(ξ + u) * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0))).intervalIntegrable _ _
  -- The linear (compensator) integral.
  have hlin : (∫ u in (-1 : ℝ)..1,
      (↑x * ↑(ξ + u) * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0)))
      = (↑x * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0)) * (2 * (ξ : ℂ)) := by
    have hc : (fun u : ℝ => (↑x * ↑(ξ + u) * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0)))
        = fun u : ℝ =>
          (↑x * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0)) * (↑(ξ + u) : ℂ) := by
      funext u; ring
    rw [hc, show (∫ u in (-1 : ℝ)..1,
          (↑x * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0)) * (↑(ξ + u) : ℂ))
        = (↑x * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0))
            * ∫ u in (-1 : ℝ)..1, (↑(ξ + u) : ℂ)
      from intervalIntegral.integral_const_mul _ _,
      intervalIntegral.integral_ofReal, intInt_linear]
    push_cast; ring
  -- `∫_{-1}^{1} 1 du = 2`.
  have h1c : (∫ _u in (-1 : ℝ)..1, (1 : ℂ)) = 2 := by
    rw [intervalIntegral.integral_const]
    show (1 - -1 : ℝ) • (1 : ℂ) = 2
    rw [Complex.real_smul]; push_cast; ring
  -- Closed form of the full shifted interval integral.
  have hval : (∫ u in (-1 : ℝ)..1, levyCompensatedIntegrand (ξ + u) x)
      = Complex.exp (↑x * ↑ξ * Complex.I) * (2 * (Real.sinc x : ℂ)) - 2
        - (↑x * Complex.I * (if |x| < (1 : ℝ) then (1 : ℂ) else 0)) * (2 * (ξ : ℂ)) := by
    simp only [levyCompensatedIntegrand_def]
    rw [intervalIntegral.integral_sub (hexp_int.sub intervalIntegrable_const) hlin_int,
        intervalIntegral.integral_sub hexp_int intervalIntegrable_const,
        intInt_exp_shift, hlin, h1c]
  rw [hval]
  simp only [levyCompensatedIntegrand_def]
  push_cast
  ring

/-- The `u`-average of the shifted compensated integrand as a difference. -/
private lemma intInt_levyCompensatedIntegrand_eq (ξ x : ℝ) :
    (∫ u in (-1 : ℝ)..1, levyCompensatedIntegrand (ξ + u) x)
      = 2 * (levyCompensatedIntegrand ξ x
          - Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)) := by
  have h := levyCompensatedIntegrand_smear ξ x
  linear_combination (-2 : ℂ) * h

/-- The smeared density `e^{ixξ}(1 − sinc x)` is integrable against a Lévy measure. -/
private lemma integrable_exp_mul_one_sub_sinc (hν : IsLevyMeasure ν) (ξ : ℝ) :
    Integrable (fun x => Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)) ν := by
  apply Integrable.mono' (g := fun x => 2 * min 1 (x ^ 2)) (hν.integrable_min_one_sq.const_mul 2)
  · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
    · exact (((Complex.measurable_ofReal.mul measurable_const).mul measurable_const).cexp)
    · exact Complex.measurable_ofReal.comp (measurable_const.sub Real.measurable_sinc)
  · refine ae_of_all _ fun x => ?_
    rw [norm_mul]
    have hnorm_exp : ‖Complex.exp (↑x * ↑ξ * Complex.I)‖ = 1 := by
      rw [show (↑x : ℂ) * ↑ξ * Complex.I = ↑(x * ξ) * Complex.I from by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hnorm_exp, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (one_sub_sinc_nonneg x)]
    exact one_sub_sinc_le_mul_min x

/-- **Smear of the jump integral.** Fubini swaps the `u`-average with the `ν`-integral; the
pointwise smear identity then collapses the inner average. -/
private lemma intInt_exponent_jump (hν : IsLevyMeasure ν) (ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, (∫ x, levyCompensatedIntegrand (ξ + u) x ∂ν)
      = 2 * ((∫ x, levyCompensatedIntegrand ξ x ∂ν)
          - ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) ∂ν) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]; infer_instance
  haveI : SigmaFinite ν := hν.sigmaFinite
  -- Joint measurability of `(u, x) ↦ f(ξ+u, x)`.
  have hmeas_joint : Measurable
      (fun p : ℝ × ℝ => levyCompensatedIntegrand (ξ + p.1) p.2) := by
    simp only [levyCompensatedIntegrand_def]
    refine (Measurable.sub (Measurable.sub ?_ measurable_const) ?_)
    · exact (((Complex.measurable_ofReal.comp measurable_snd).mul
        (Complex.measurable_ofReal.comp (measurable_const.add measurable_fst))).mul
        measurable_const).cexp
    · refine Measurable.mul ?_ ?_
      · exact ((Complex.measurable_ofReal.comp measurable_snd).mul
          (Complex.measurable_ofReal.comp (measurable_const.add measurable_fst))).mul
          measurable_const
      · exact measurable_const.ite
          ((isOpen_Iio.preimage (continuous_abs.comp continuous_snd)).measurableSet)
          measurable_const
  -- Joint integrability, dominated by `(2 + 3(|ξ|+1)²)·min(1, x²)`.
  have h_int : Integrable (Function.uncurry (fun u x => levyCompensatedIntegrand (ξ + u) x))
      ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν) := by
    apply Integrable.mono' (g := fun p : ℝ × ℝ => (2 + 3 * (|ξ| + 1) ^ 2) * min 1 (p.2 ^ 2))
      ((hν.integrable_min_one_sq.const_mul (2 + 3 * (|ξ| + 1) ^ 2)).comp_snd _)
      hmeas_joint.aestronglyMeasurable
    have hfst : ∀ᵐ p ∂((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν),
        p.1 ∈ Set.uIoc (-1 : ℝ) 1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_uIoc)
    filter_upwards [hfst] with p hp
    have hp1 : |p.1| ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hp
      rw [abs_le]; exact ⟨hp.1.le, hp.2⟩
    calc ‖Function.uncurry (fun u x => levyCompensatedIntegrand (ξ + u) x) p‖
        = ‖levyCompensatedIntegrand (ξ + p.1) p.2‖ := rfl
      _ ≤ (2 + 3 * (ξ + p.1) ^ 2) * min 1 (p.2 ^ 2) := norm_levyCompensatedIntegrand_le _ _
      _ ≤ (2 + 3 * (|ξ| + 1) ^ 2) * min 1 (p.2 ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (le_min zero_le_one (sq_nonneg _))
          have hsq : (ξ + p.1) ^ 2 ≤ (|ξ| + 1) ^ 2 := by
            apply sq_le_sq'
            · nlinarith [abs_le.mp hp1, neg_abs_le ξ, le_abs_self ξ]
            · nlinarith [abs_le.mp hp1, neg_abs_le ξ, le_abs_self ξ]
          nlinarith [hsq]
  rw [intervalIntegral_integral_swap h_int]
  simp only [intInt_levyCompensatedIntegrand_eq]
  rw [show (∫ y, 2 * (levyCompensatedIntegrand ξ y
          - Complex.exp (↑y * ↑ξ * Complex.I) * ((1 - Real.sinc y : ℝ) : ℂ)) ∂ν)
        = 2 * ∫ y, (levyCompensatedIntegrand ξ y
            - Complex.exp (↑y * ↑ξ * Complex.I) * ((1 - Real.sinc y : ℝ) : ℂ)) ∂ν
      from integral_const_mul _ _,
      integral_sub (integrable_levyCompensatedIntegrand hν ξ)
        (integrable_exp_mul_one_sub_sinc hν ξ)]

/-- `∫_{-1}^{1} ↑b(ξ+u)I du = 2b·ξ·I` — the drift term of the smeared exponent. -/
private lemma intInt_exponent_drift (b ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, ((b : ℂ) * ↑(ξ + u) * Complex.I)
      = 2 * (b : ℂ) * ↑ξ * Complex.I := by
  have hc : (fun u : ℝ => ((b : ℂ) * ↑(ξ + u) * Complex.I))
      = fun u : ℝ => ((b : ℂ) * Complex.I) * (↑(ξ + u) : ℂ) := by
    funext u; ring
  rw [hc, show (∫ u in (-1 : ℝ)..1, ((b : ℂ) * Complex.I) * (↑(ξ + u) : ℂ))
        = ((b : ℂ) * Complex.I) * ∫ u in (-1 : ℝ)..1, (↑(ξ + u) : ℂ)
      from intervalIntegral.integral_const_mul _ _,
      intervalIntegral.integral_ofReal, intInt_linear]
  push_cast; ring

/-- `∫_{-1}^{1} ↑s(ξ+u)²/2 du = s·ξ² + s/3` — the Gaussian term of the smeared exponent. -/
private lemma intInt_exponent_gauss (s ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2)
      = (s : ℂ) * (ξ : ℂ) ^ 2 + (s : ℂ) / 3 := by
  have hc : (fun u : ℝ => ((s : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2))
      = fun u : ℝ => ((s : ℂ) / 2) * (↑((ξ + u) ^ 2 : ℝ) : ℂ) := by
    funext u; push_cast; ring
  rw [hc, show (∫ u in (-1 : ℝ)..1, ((s : ℂ) / 2) * (↑((ξ + u) ^ 2 : ℝ) : ℂ))
        = ((s : ℂ) / 2) * ∫ u in (-1 : ℝ)..1, (↑((ξ + u) ^ 2 : ℝ) : ℂ)
      from intervalIntegral.integral_const_mul _ _,
      intervalIntegral.integral_ofReal, intInt_quadratic]
  push_cast; ring

/-- The characteristic function of the smeared measure splits into the Gaussian atom `σ²/6`
and the jump density integral `∫ e^{ixξ}(1 − sinc x) dν`. -/
theorem charFun_smearedMeasure (hν : IsLevyMeasure ν) (σ_sq : ℝ≥0) (ξ : ℝ) :
    charFun (smearedMeasure σ_sq ν) ξ
      = (((σ_sq : ℝ) / 6 : ℝ) : ℂ)
        + ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) ∂ν := by
  -- The two pieces of `smearedMeasure` are finite measures.
  haveI hAfin : IsFiniteMeasure (((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ 0), mul_one]
    exact ENNReal.div_lt_top (by simp) (by simp)
  haveI hBfin : IsFiniteMeasure (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact lintegral_one_sub_sinc_lt_top hν
  -- Integrability of the charFun integrand against each piece.
  have hIntA : Integrable (fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I))
      (((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)) :=
    Integrable.of_bound (by fun_prop)
      1 (ae_of_all _ fun x => le_of_eq (by
        rw [show (↑ξ : ℂ) * ↑x * Complex.I = ↑(ξ * x) * Complex.I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _))
  have hIntB : Integrable (fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I))
      (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) :=
    Integrable.of_bound (by fun_prop)
      1 (ae_of_all _ fun x => le_of_eq (by
        rw [show (↑ξ : ℂ) * ↑x * Complex.I = ↑(ξ * x) * Complex.I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _))
  rw [charFun_apply_real, smearedMeasure, integral_add_measure hIntA hIntB]
  congr 1
  · -- Gaussian atom.
    rw [integral_smul_measure, integral_dirac,
        show (↑ξ : ℂ) * ↑(0 : ℝ) * Complex.I = 0 from by simp, Complex.exp_zero]
    show ((↑σ_sq / 6 : ℝ≥0∞).toReal) • (1 : ℂ) = ↑((σ_sq : ℝ) / 6)
    rw [Complex.real_smul, mul_one]
    congr 1
    rw [ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.toReal_ofNat]
  · -- Jump density.
    rw [integral_withDensity_eq_integral_toReal_smul measurable_one_sub_sinc
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [ENNReal.toReal_ofReal (one_sub_sinc_nonneg x)]
    show (1 - Real.sinc x : ℝ) • Complex.exp (↑ξ * ↑x * Complex.I)
      = Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)
    rw [Complex.real_smul, show (↑ξ : ℂ) * ↑x * Complex.I = ↑x * ↑ξ * Complex.I from by ring]
    ring

/-- **The smear identity** (Sato, Theorem 8.1). The smeared Lévy–Khintchine exponent of a
triple equals the characteristic function of the smeared canonical measure `ρ`. The drift
cancels, the Gaussian piece produces the constant `σ²/6` (the atom of `ρ`), and the jump
integral produces the density `1 − sinc` against `ν`. Chained with `Measure.ext_of_charFun`
(both `smearedMeasure`s are finite) this pins the triple from the exponent alone. -/
theorem smeared_exponent_eq_charFun (T : LevyKhintchineTriple) (ξ : ℝ) :
    T.exponent ξ - (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, T.exponent (ξ + u)
      = charFun (smearedMeasure T.gaussianVariance T.levyMeasure) ξ := by
  have hν := T.levyMeasure_isLevyMeasure
  -- Interval integrability of the three exponent pieces.
  have hdrift_int : IntervalIntegrable
      (fun u => ((T.drift : ℂ) * ↑(ξ + u) * Complex.I)) volume (-1) 1 :=
    (by fun_prop : Continuous fun u : ℝ =>
      ((T.drift : ℂ) * ↑(ξ + u) * Complex.I)).intervalIntegrable _ _
  have hgauss_int : IntervalIntegrable
      (fun u => ((T.gaussianVariance : ℝ) : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2) volume (-1) 1 :=
    (by fun_prop : Continuous fun u : ℝ =>
      ((T.gaussianVariance : ℝ) : ℂ) * (↑(ξ + u) : ℂ) ^ 2 / 2).intervalIntegrable _ _
  have hjump_int : IntervalIntegrable
      (fun u => ∫ x, levyCompensatedIntegrand (ξ + u) x ∂T.levyMeasure) volume (-1) 1 :=
    ((continuous_integral_levyCompensatedIntegrand hν).comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  -- Closed form of `∫_{-1}^{1} ψ_T(ξ+u) du`.
  have hval : (∫ u in (-1 : ℝ)..1, T.exponent (ξ + u))
      = 2 * (T.drift : ℂ) * ↑ξ * Complex.I
        - (((T.gaussianVariance : ℝ) : ℂ) * (ξ : ℂ) ^ 2 + ((T.gaussianVariance : ℝ) : ℂ) / 3)
        + 2 * ((∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure)
            - ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)
                ∂T.levyMeasure) := by
    simp only [LevyKhintchineTriple.exponent_def]
    rw [intervalIntegral.integral_add (hdrift_int.sub hgauss_int) hjump_int,
        intervalIntegral.integral_sub hdrift_int hgauss_int,
        intInt_exponent_drift, intInt_exponent_gauss, intInt_exponent_jump hν]
  rw [LevyKhintchineTriple.exponent_def, hval,
      charFun_smearedMeasure hν T.gaussianVariance ξ]
  push_cast
  ring

end SmearIdentity

/-!
## Recovery of the triple from the smeared measure

The smearing is injective: from `ρ = smearedMeasure σ² ν` (with `ν` a Lévy measure) both `σ²`
and `ν` are recovered. The Gaussian coefficient is read off the atom at `0`
(`smearedMeasure_singleton_zero`); the Lévy measure is recovered by restricting to `{0}ᶜ` — which
discards the Dirac atom and leaves the jump density untouched — and untilting the density
`1 − Real.sinc x`, which is strictly positive `ν`-a.e. (`one_sub_sinc_pos`, using `ν{0} = 0`).
-/

section Recovery

variable {ν : Measure ℝ}

/-- The jump (withDensity) piece of the smeared measure gives no mass to the origin, because a
Lévy measure gives none. -/
private lemma withDensity_one_sub_sinc_singleton_zero (hν : IsLevyMeasure ν) :
    (ν.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x)) {(0 : ℝ)} = 0 := by
  rw [withDensity_apply _ (measurableSet_singleton 0),
    setLIntegral_measure_zero _ _ hν.zero_singleton]

/-- **Restriction to `{0}ᶜ` isolates the jump piece.** The Dirac atom lives on `{0}` and so
restricts to `0`, while the density piece charges nothing at `0`, so it is unchanged. -/
private lemma smearedMeasure_restrict_compl (hν : IsLevyMeasure ν) :
    (smearedMeasure σ_sq ν).restrict {(0 : ℝ)}ᶜ
      = ν.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x) := by
  classical
  rw [smearedMeasure, Measure.restrict_add, Measure.restrict_smul, restrict_dirac,
    if_neg (by simp), smul_zero, zero_add]
  refine Measure.restrict_eq_self_of_ae_mem ?_
  rw [ae_iff, show {a : ℝ | a ∉ {(0 : ℝ)}ᶜ} = {(0 : ℝ)} from by ext a; simp]
  exact withDensity_one_sub_sinc_singleton_zero hν

/-- **Untilt.** The density `1 − Real.sinc x` is strictly positive `ν`-a.e. (it vanishes only at
`0`, which is `ν`-null) and finite everywhere, so multiplying by its pointwise inverse recovers
`ν` from `ν.withDensity (1 − Real.sinc)`. -/
private lemma withDensity_one_sub_sinc_untilt (hν : IsLevyMeasure ν) :
    (ν.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x)).withDensity
      (fun x => (ENNReal.ofReal (1 - Real.sinc x))⁻¹) = ν := by
  have hne0 : ∀ᵐ x ∂ν, x ≠ 0 := by
    rw [ae_iff]; simpa using hν.zero_singleton
  refine withDensity_inv_same measurable_one_sub_sinc ?_ ?_
  · filter_upwards [hne0] with x hx
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact one_sub_sinc_pos hx
  · filter_upwards with x using ENNReal.ofReal_ne_top

/-- **Recovery of the Gaussian coefficient.** If two smeared measures agree, the Gaussian
variances agree: both equal `6 ·` the atom at `0`. -/
theorem smearedMeasure_gaussianVariance_inj {ν₁ ν₂ : Measure ℝ}
    (hν₁ : IsLevyMeasure ν₁) (hν₂ : IsLevyMeasure ν₂) {σ₁ σ₂ : ℝ≥0}
    (h : smearedMeasure σ₁ ν₁ = smearedMeasure σ₂ ν₂) : σ₁ = σ₂ := by
  have h0 : (σ₁ : ℝ≥0∞) / 6 = (σ₂ : ℝ≥0∞) / 6 := by
    have hpt : (smearedMeasure σ₁ ν₁) {(0 : ℝ)} = (smearedMeasure σ₂ ν₂) {(0 : ℝ)} := by rw [h]
    rwa [smearedMeasure_singleton_zero σ₁ hν₁, smearedMeasure_singleton_zero σ₂ hν₂] at hpt
  have h6 : (σ₁ : ℝ≥0∞) / 6 * 6 = (σ₂ : ℝ≥0∞) / 6 * 6 := by rw [h0]
  rw [ENNReal.div_mul_cancel (by norm_num) (by norm_num),
    ENNReal.div_mul_cancel (by norm_num) (by norm_num)] at h6
  exact ENNReal.coe_inj.mp h6

/-- **Recovery of the Lévy measure.** If two smeared measures agree, the Lévy measures agree:
restrict to `{0}ᶜ` to strip the Gaussian atom, then untilt the shared density `1 − Real.sinc x`. -/
theorem smearedMeasure_levyMeasure_inj {ν₁ ν₂ : Measure ℝ}
    (hν₁ : IsLevyMeasure ν₁) (hν₂ : IsLevyMeasure ν₂) {σ₁ σ₂ : ℝ≥0}
    (h : smearedMeasure σ₁ ν₁ = smearedMeasure σ₂ ν₂) : ν₁ = ν₂ := by
  have hr : (ν₁.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x))
      = ν₂.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x) := by
    have hpt : (smearedMeasure σ₁ ν₁).restrict {(0 : ℝ)}ᶜ
        = (smearedMeasure σ₂ ν₂).restrict {(0 : ℝ)}ᶜ := by rw [h]
    rwa [smearedMeasure_restrict_compl σ₁ hν₁, smearedMeasure_restrict_compl σ₂ hν₂] at hpt
  calc ν₁ = (ν₁.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x)).withDensity
              (fun x => (ENNReal.ofReal (1 - Real.sinc x))⁻¹) :=
        (withDensity_one_sub_sinc_untilt hν₁).symm
    _ = (ν₂.withDensity fun x => ENNReal.ofReal (1 - Real.sinc x)).withDensity
              (fun x => (ENNReal.ofReal (1 - Real.sinc x))⁻¹) := by rw [hr]
    _ = ν₂ := withDensity_one_sub_sinc_untilt hν₂

/-- **Injectivity of the smearing.** A smeared measure determines its Lévy triple `(σ², ν)`:
equal smeared measures have equal Gaussian variances and equal Lévy measures. This is the
inversion step of Sato's uniqueness route; chained with `smeared_exponent_eq_charFun` and
`Measure.ext_of_charFun` it pins the triple from the characteristic exponent. -/
theorem smearedMeasure_inj {ν₁ ν₂ : Measure ℝ}
    (hν₁ : IsLevyMeasure ν₁) (hν₂ : IsLevyMeasure ν₂) {σ₁ σ₂ : ℝ≥0}
    (h : smearedMeasure σ₁ ν₁ = smearedMeasure σ₂ ν₂) : σ₁ = σ₂ ∧ ν₁ = ν₂ :=
  ⟨smearedMeasure_gaussianVariance_inj hν₁ hν₂ h, smearedMeasure_levyMeasure_inj hν₁ hν₂ h⟩

end Recovery

/-!
## Uniqueness of the triple

Chaining the smear identity with `Measure.ext_of_charFun` and the smearing inversion pins the
whole triple `(b, σ², ν)` from the exponent alone.
-/

section Uniqueness

/-- If two triples with equal Gaussian variance and equal Lévy measure share the exponent value
at `ξ = 1`, their drifts coincide: the Gaussian and jump pieces cancel, leaving `b·I = b'·I`. -/
private lemma drift_eq_of_exponent_one {T T' : LevyKhintchineTriple}
    (hσ : T.gaussianVariance = T'.gaussianVariance) (hν : T.levyMeasure = T'.levyMeasure)
    (h : T.exponent 1 = T'.exponent 1) : T.drift = T'.drift := by
  rw [LevyKhintchineTriple.exponent_def, LevyKhintchineTriple.exponent_def, hσ, hν] at h
  have hI : (T.drift : ℂ) * Complex.I = (T'.drift : ℂ) * Complex.I := by
    have hcancel : (T.drift : ℂ) * ↑(1 : ℝ) * Complex.I
        = (T'.drift : ℂ) * ↑(1 : ℝ) * Complex.I := by linear_combination h
    simpa using hcancel
  exact Complex.ofReal_inj.mp (mul_right_cancel₀ Complex.I_ne_zero hI)

/-- **Uniqueness of the Lévy–Khintchine triple.** A triple `(b, σ², ν)` is determined by its
characteristic exponent: if two triples have the same exponent at every frequency, they are
equal. The proof smears the exponent (`smeared_exponent_eq_charFun`) to obtain equal
characteristic functions of the two finite smeared measures, applies `Measure.ext_of_charFun`
to equate the smeared measures, inverts the smearing (`smearedMeasure_inj`) to recover `σ²` and
`ν`, and reads the drift off the exponent at `ξ = 1`. -/
theorem LevyKhintchineTriple.ext_of_exponent_eq {T T' : LevyKhintchineTriple}
    (h : ∀ ξ : ℝ, T.exponent ξ = T'.exponent ξ) : T = T' := by
  -- Smearing turns the exponent agreement into charFun agreement of the smeared measures.
  have hcf : charFun (smearedMeasure T.gaussianVariance T.levyMeasure)
      = charFun (smearedMeasure T'.gaussianVariance T'.levyMeasure) := by
    funext ξ
    rw [← smeared_exponent_eq_charFun T ξ, ← smeared_exponent_eq_charFun T' ξ, h ξ,
      intervalIntegral.integral_congr (fun u _ => h (ξ + u))]
  -- The two smeared measures are finite, so charFun agreement forces measure equality.
  haveI := smearedMeasure_isFiniteMeasure T.gaussianVariance T.levyMeasure_isLevyMeasure
  haveI := smearedMeasure_isFiniteMeasure T'.gaussianVariance T'.levyMeasure_isLevyMeasure
  have hmeas := Measure.ext_of_charFun hcf
  -- Invert the smearing to recover the Gaussian variance and the Lévy measure.
  obtain ⟨hσ, hν⟩ :=
    smearedMeasure_inj T.levyMeasure_isLevyMeasure T'.levyMeasure_isLevyMeasure hmeas
  -- The drift is read off the exponent at `ξ = 1` once the other pieces agree.
  have hdrift := drift_eq_of_exponent_one hσ hν (h 1)
  -- All three data fields agree; conclude by structure eta and proof irrelevance.
  obtain ⟨b, σ, ν, hνfact⟩ := T
  obtain ⟨b', σ', ν', hνfact'⟩ := T'
  subst hσ; subst hν; subst hdrift; rfl

end Uniqueness

/-!
## Characterization of infinite divisibility

The three pieces of the Lévy–Khintchine programme compose into the classical characterization:
a probability measure on `ℝ` is infinitely divisible **iff** its characteristic function is
`exp ∘ ψ_T` for some Lévy–Khintchine triple `T`, and that triple is then **unique**.

* forward direction: `levyKhintchine_representation` (needs only infinite divisibility);
* backward direction: `levyKhintchine_converse` + `Measure.ext_of_charFun` (a triple's law is
  pinned by its characteristic function, so it must equal `μ`);
* uniqueness: `LevyKhintchineTriple.ext_of_exponent_eq`, once exponents are identified from
  equal exponentials by the continuous-log argument below.
-/

section Characterization

/-- **Uniqueness of a continuous logarithm on the line.** If two continuous functions
`f, g : ℝ → ℂ` agree at `0` and have equal exponentials everywhere, they are equal. The
difference `f − g` is continuous with `exp (f ξ − g ξ) = 1`, hence lands in the discrete lattice
`2πiℤ`; writing `f ξ − g ξ = (m ξ)·2πi` with `m ξ : ℤ`, the integer `m` is a continuous map into
the discrete space `ℤ` (via `Int.isClosedEmbedding_coe_real`), hence constant on the connected
line, so `f − g ≡ f 0 − g 0 = 0`. -/
private lemma eq_of_cexp_eq_of_continuous {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (h0 : f 0 = g 0)
    (h : ∀ ξ, Complex.exp (f ξ) = Complex.exp (g ξ)) : f = g := by
  -- The difference has exponential `1`, so it lies in `2πiℤ` pointwise.
  have hone : ∀ ξ, Complex.exp (f ξ - g ξ) = 1 := fun ξ => by
    rw [Complex.exp_sub, h ξ, div_self (Complex.exp_ne_zero _)]
  have hex : ∀ ξ, ∃ n : ℤ, f ξ - g ξ = n * (2 * ↑π * Complex.I) :=
    fun ξ => Complex.exp_eq_one_iff.mp (hone ξ)
  choose m hm using hex
  -- The integer multiplier equals a continuous real function, so `m` is continuous into `ℤ`.
  have hcast : ∀ ξ, ((m ξ : ℤ) : ℝ) = ((f ξ - g ξ) / (2 * ↑π * Complex.I)).re := by
    intro ξ
    have hquot : (f ξ - g ξ) / (2 * ↑π * Complex.I) = (m ξ : ℂ) := by
      rw [hm ξ, mul_div_assoc, div_self Complex.two_pi_I_ne_zero, mul_one]
    rw [hquot, Complex.intCast_re]
  have hcont_cast : Continuous fun ξ => ((m ξ : ℤ) : ℝ) := by
    simp only [hcast]
    exact Complex.continuous_re.comp ((hf.sub hg).div_const _)
  have hcont_m : Continuous m :=
    Int.isClosedEmbedding_coe_real.isEmbedding.continuous_iff.mpr hcont_cast
  -- A continuous map from the connected line into the discrete `ℤ` is constant.
  funext ξ
  have hval : f ξ - g ξ = 0 := by
    rw [hm ξ, PreconnectedSpace.constant (α := ℝ) inferInstance hcont_m (x := ξ) (y := 0),
      ← hm 0, h0, sub_self]
  exact sub_eq_zero.mp hval

/-- **Characterization of infinite divisibility (Lévy–Khintchine).** A probability measure `μ`
on `ℝ` is infinitely divisible **iff** its characteristic function is `exp (ψ_T)` for some
Lévy–Khintchine triple `T = (b, σ², ν)`.

The forward implication is `levyKhintchine_representation`; the converse follows from
`levyKhintchine_converse` — its measure has the same characteristic function `exp (ψ_T)` as `μ`,
so `Measure.ext_of_charFun` identifies the two and transports infinite divisibility back to
`μ`. -/
theorem isInfinitelyDivisible_iff_exists_levyKhintchineTriple
    {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    IsInfinitelyDivisible μ ↔
      ∃ T : LevyKhintchineTriple, ∀ ξ, charFun μ ξ = Complex.exp (T.exponent ξ) := by
  constructor
  · intro h
    obtain ⟨T, hψ⟩ := levyKhintchine_representation h
    exact ⟨T, hψ⟩
  · rintro ⟨T, hT⟩
    obtain ⟨μ', hμ'P, hμ'ID, hcf'⟩ := levyKhintchine_converse T
    haveI := hμ'P
    have hμeq : μ = μ' := by
      apply Measure.ext_of_charFun
      funext ξ
      rw [hT ξ, hcf' ξ]
    rwa [hμeq]

/-- **Uniqueness of the Lévy–Khintchine triple of an infinitely divisible law.** Combining the
representation with triple uniqueness: an infinitely divisible `μ` has a *unique*
Lévy–Khintchine triple `T` with `charFun μ = exp (ψ_T)`. Two such triples have equal
exponentials of their (continuous, `0`-vanishing) exponents, hence equal exponents
(`eq_of_cexp_eq_of_continuous`), hence are equal (`LevyKhintchineTriple.ext_of_exponent_eq`). -/
theorem existsUnique_levyKhintchineTriple
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : IsInfinitelyDivisible μ) :
    ∃! T : LevyKhintchineTriple, ∀ ξ, charFun μ ξ = Complex.exp (T.exponent ξ) := by
  obtain ⟨T, hT⟩ := isInfinitelyDivisible_iff_exists_levyKhintchineTriple.mp hμ
  refine ⟨T, hT, fun T' hT' => ?_⟩
  apply LevyKhintchineTriple.ext_of_exponent_eq
  have hfe : T'.exponent = T.exponent :=
    eq_of_cexp_eq_of_continuous T'.exponent_continuous T.exponent_continuous
      (by rw [T'.exponent_zero, T.exponent_zero])
      (fun ξ => by rw [← hT' ξ, ← hT ξ])
  exact fun ξ => congrFun hfe ξ

end Characterization

end ProbabilityTheory
