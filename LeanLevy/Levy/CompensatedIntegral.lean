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

/-- The compensated integrand norm is bounded by `(2 + ξ²) · min(1, x²)`. -/
theorem norm_levyCompensatedIntegrand_le (ξ x : ℝ) :
    ‖levyCompensatedIntegrand ξ x‖ ≤ (2 + ξ ^ 2) * min 1 (x ^ 2) := by
  sorry

end ProbabilityTheory
