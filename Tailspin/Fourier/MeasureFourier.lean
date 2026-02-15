/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

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
  sorry

/-- The Fourier transform of a finite measure is continuous. -/
theorem continuous_fourierTransform :
    Continuous (fourierTransform μ) := by
  sorry

end MeasureTheory.FiniteMeasure
