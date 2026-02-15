/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Fourier Transform of Finite Borel Measures

This file defines the Fourier transform (characteristic function) of a finite
Borel measure on ℝ using the probabilist convention `exp(iξx)`.

## Main definitions

* `MeasureTheory.FiniteMeasure.fourierTransform` — the Fourier transform of a
  finite measure μ, defined as `ξ ↦ ∫ x, exp(iξx) dμ(x)`.

## Main results

* `MeasureTheory.FiniteMeasure.norm_fourierTransform_le` — the Fourier transform
  is bounded by the total mass: `‖μ̂(ξ)‖ ≤ μ.mass`.
* `MeasureTheory.FiniteMeasure.continuous_fourierTransform` — the Fourier
  transform is continuous.
-/

open MeasureTheory Complex

namespace MeasureTheory.FiniteMeasure

variable (μ : FiniteMeasure ℝ)

/-- The Fourier transform of a finite Borel measure on ℝ, using the probabilist
convention: `μ̂(ξ) = ∫ x, exp(iξx) dμ(x)`. -/
noncomputable def fourierTransform (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, exp (↑(ξ * x) * I) ∂(μ : Measure ℝ)

/-- The Fourier transform of a finite measure is bounded by the total mass. -/
theorem norm_fourierTransform_le (ξ : ℝ) :
    ‖fourierTransform μ ξ‖ ≤ ↑μ.mass := by
  unfold fourierTransform
  calc ‖∫ x : ℝ, exp (↑(ξ * x) * I) ∂(μ : Measure ℝ)‖
      ≤ ∫ x : ℝ, ‖exp (↑(ξ * x) * I)‖ ∂(μ : Measure ℝ) :=
        norm_integral_le_integral_norm _
    _ = ∫ _ : ℝ, (1 : ℝ) ∂(μ : Measure ℝ) := by
        congr 1; ext x; simp only [norm_exp_ofReal_mul_I]
    _ = ↑μ.mass := by
        rw [integral_const, smul_eq_mul, mul_one, Measure.real,
            ← ennreal_mass, ENNReal.coe_toReal]

/-- The Fourier transform of a finite measure is continuous. -/
theorem continuous_fourierTransform :
    Continuous (fourierTransform μ) := by
  unfold fourierTransform
  apply continuous_of_dominated (bound := fun _ => 1)
  · intro ξ
    exact (by fun_prop : Continuous fun x => exp (↑(ξ * x) * I)).aestronglyMeasurable
  · intro ξ
    filter_upwards with x
    simp only [norm_exp_ofReal_mul_I, le_refl]
  · exact integrable_const 1
  · filter_upwards with x
    exact by fun_prop

end MeasureTheory.FiniteMeasure
