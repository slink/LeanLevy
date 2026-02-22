/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Levy.LevyMeasure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Compensated Integrand for the Lévy-Khintchine Formula

The **compensated integrand** is the function
`f(ξ, x) = exp(ixξ) - 1 - ixξ · 1_{|x| < 1}`
which appears in the Lévy-Khintchine representation of infinitely divisible distributions.

## Main definitions

* `ProbabilityTheory.levyCompensatedIntegrand` — the compensated integrand as a function `ℝ → ℝ → ℂ`.

## Main results

* `ProbabilityTheory.norm_levyCompensatedIntegrand_le` — pointwise norm bound in terms of `min(1, x²)`.
* `ProbabilityTheory.measurable_levyCompensatedIntegrand` — measurability in `x` for fixed `ξ`.
* `ProbabilityTheory.integrable_levyCompensatedIntegrand` — Bochner integrability under a Lévy measure.
-/

open MeasureTheory Complex ENNReal Set
open scoped NNReal ENNReal ComplexConjugate

namespace ProbabilityTheory

/-- The **compensated integrand** for the Lévy-Khintchine formula:
`f(ξ, x) = exp(ixξ) - 1 - ixξ · 1_{|x| < 1}`. -/
noncomputable def levyCompensatedIntegrand (ξ x : ℝ) : ℂ :=
  exp (↑x * ↑ξ * I) - 1 - ↑x * ↑ξ * I * if |x| < 1 then 1 else 0

@[simp]
theorem levyCompensatedIntegrand_def (ξ x : ℝ) :
    levyCompensatedIntegrand ξ x =
      exp (↑x * ↑ξ * I) - 1 - ↑x * ↑ξ * I * if |x| < 1 then 1 else 0 :=
  rfl

/-- The compensated integrand vanishes at `x = 0`. -/
@[simp]
theorem levyCompensatedIntegrand_zero_right (ξ : ℝ) :
    levyCompensatedIntegrand ξ 0 = 0 := by
  simp [levyCompensatedIntegrand]

/-- The compensated integrand is measurable in `x` for fixed `ξ`. -/
@[fun_prop]
theorem measurable_levyCompensatedIntegrand (ξ : ℝ) :
    Measurable (levyCompensatedIntegrand ξ) := by
  unfold levyCompensatedIntegrand
  apply Measurable.sub
  · apply Measurable.sub
    · exact (((Complex.measurable_ofReal).mul measurable_const).mul measurable_const).cexp
    · exact measurable_const
  · apply Measurable.mul
    · exact (Complex.measurable_ofReal.mul measurable_const).mul measurable_const
    · exact measurable_const.ite
        (isOpen_Iio.preimage continuous_abs |>.measurableSet) measurable_const

/-- For `|x| ≥ 1`, `‖f(ξ,x)‖ ≤ 2`. -/
theorem norm_levyCompensatedIntegrand_le_two {ξ x : ℝ} (hx : 1 ≤ |x|) :
    ‖levyCompensatedIntegrand ξ x‖ ≤ 2 := by
  simp only [levyCompensatedIntegrand, not_lt.mpr hx, if_false, mul_zero, sub_zero]
  calc ‖exp (↑x * ↑ξ * I) - 1‖
      ≤ ‖exp (↑x * ↑ξ * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 1 + 1 := by
        rw [show (↑x : ℂ) * ↑ξ * I = ↑(x * ξ) * I from by push_cast; ring,
          norm_exp_ofReal_mul_I, norm_one]
    _ = 2 := by ring

/-- The compensated integrand norm is bounded by `(2 + 3 * ξ²) · min(1, x²)`. -/
theorem norm_levyCompensatedIntegrand_le (ξ x : ℝ) :
    ‖levyCompensatedIntegrand ξ x‖ ≤ (2 + 3 * ξ ^ 2) * min 1 (x ^ 2) := by
  by_cases hx : |x| < 1
  · -- Case |x| < 1: indicator is 1, f(ξ,x) = exp(ixξ) - 1 - ixξ
    have hx2 : x ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one x).mpr hx
    have hmin : min (1 : ℝ) (x ^ 2) = x ^ 2 := min_eq_right (le_of_lt hx2)
    rw [hmin]
    simp only [levyCompensatedIntegrand, hx, ite_true, mul_one]
    -- Now goal: ‖exp(↑x * ↑ξ * I) - 1 - ↑x * ↑ξ * I‖ ≤ (2 + 3 * ξ²) * x²
    set z : ℂ := ↑x * ↑ξ * I with hz_def
    have hz_eq : z = ↑(x * ξ) * I := by push_cast; ring
    have hz_norm : ‖z‖ = |x * ξ| := by
      rw [hz_eq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    by_cases hxξ : |x * ξ| ≤ 1
    · -- Sub-case |xξ| ≤ 1: use norm_exp_sub_one_sub_id_le
      have hle : ‖z‖ ≤ 1 := by rw [hz_norm]; exact hxξ
      have htaylor : ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := norm_exp_sub_one_sub_id_le hle
      calc ‖exp z - 1 - z‖ ≤ ‖z‖ ^ 2 := htaylor
        _ = (x * ξ) ^ 2 := by rw [hz_norm, sq_abs]
        _ = x ^ 2 * ξ ^ 2 := by ring
        _ ≤ (2 + 3 * ξ ^ 2) * x ^ 2 := by nlinarith [sq_nonneg ξ, sq_nonneg x]
    · -- Sub-case |xξ| > 1: use triangle inequality
      push_neg at hxξ
      have hexp : ‖exp z‖ = 1 := by rw [hz_eq]; exact norm_exp_ofReal_mul_I _
      -- Triangle: ‖exp(z) - 1 - z‖ ≤ ‖exp(z) - 1‖ + ‖z‖ ≤ 2 + |xξ|
      have htri : ‖exp z - 1 - z‖ ≤ 2 + |x * ξ| := by
        calc ‖exp z - 1 - z‖
            = ‖(exp z - 1) - z‖ := by ring_nf
          _ ≤ ‖exp z - 1‖ + ‖z‖ := norm_sub_le _ _
          _ ≤ (‖exp z‖ + ‖(1 : ℂ)‖) + ‖z‖ := by
              gcongr; exact norm_sub_le _ _
          _ = 2 + |x * ξ| := by rw [hexp, norm_one, hz_norm]; ring
      -- 2 + t ≤ 3t² when t ≥ 1 (since 3t² - t - 2 = (3t+2)(t-1) ≥ 0)
      have h3 : 2 + |x * ξ| ≤ 3 * (x * ξ) ^ 2 := by nlinarith [sq_abs (x * ξ)]
      calc ‖exp z - 1 - z‖ ≤ 2 + |x * ξ| := htri
        _ ≤ 3 * (x * ξ) ^ 2 := h3
        _ = 3 * ξ ^ 2 * x ^ 2 := by ring
        _ ≤ (2 + 3 * ξ ^ 2) * x ^ 2 := by nlinarith [sq_nonneg x]
  · -- Case |x| ≥ 1: indicator is 0
    push_neg at hx
    have hmin : min (1 : ℝ) (x ^ 2) = 1 :=
      min_eq_left ((one_le_sq_iff_one_le_abs x).mpr hx)
    rw [hmin]
    calc ‖levyCompensatedIntegrand ξ x‖ ≤ 2 := norm_levyCompensatedIntegrand_le_two hx
      _ ≤ (2 + 3 * ξ ^ 2) * 1 := by nlinarith [sq_nonneg ξ]

/-- The Lebesgue integral of `‖levyCompensatedIntegrand ξ ·‖ₑ` against a Lévy measure is finite. -/
theorem lintegral_enorm_levyCompensatedIntegrand_lt_top
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (ξ : ℝ) :
    ∫⁻ x, ‖levyCompensatedIntegrand ξ x‖ₑ ∂ν < ⊤ := by
  have hC : (0 : ℝ) ≤ 2 + 3 * ξ ^ 2 := by positivity
  calc ∫⁻ x, ‖levyCompensatedIntegrand ξ x‖ₑ ∂ν
      = ∫⁻ x, ENNReal.ofReal ‖levyCompensatedIntegrand ξ x‖ ∂ν := by
        simp only [ofReal_norm_eq_enorm]
    _ ≤ ∫⁻ x, ENNReal.ofReal ((2 + 3 * ξ ^ 2) * min 1 (x ^ 2)) ∂ν := by
        apply lintegral_mono
        intro x
        exact ENNReal.ofReal_le_ofReal (norm_levyCompensatedIntegrand_le ξ x)
    _ = ∫⁻ x, ENNReal.ofReal (2 + 3 * ξ ^ 2) * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        congr 1; ext x
        rw [← ENNReal.ofReal_mul hC]
    _ = ENNReal.ofReal (2 + 3 * ξ ^ 2) * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ofReal_lt_top hν.lintegral_min_one_sq_lt_top

/-- The compensated integrand is Bochner integrable against a Lévy measure. -/
theorem integrable_levyCompensatedIntegrand
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (ξ : ℝ) :
    Integrable (levyCompensatedIntegrand ξ) ν :=
  ⟨(measurable_levyCompensatedIntegrand ξ).aestronglyMeasurable,
    lintegral_enorm_levyCompensatedIntegrand_lt_top hν ξ⟩

end ProbabilityTheory
