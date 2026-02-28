/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Fourier.PositiveDefinite
import LeanLevy.Fourier.MeasureFourier
import LeanLevy.Probability.WeakConvergence

/-!
# Bochner's Theorem on ℝ

## Main results

* `ProbabilityTheory.bochner` — a continuous positive definite function `φ` with `φ(0) = 1`
  is the characteristic function of a probability measure.

## Proof strategy

Bochner uses Gaussian smoothing + Lévy continuity (no Riesz representation needed):

1. Multiply `φ` by Gaussian `exp(-ξ²/(2n))` to get an L¹ PD function `φₙ`.
2. Show the Fourier transform of `φₙ` is non-negative (from PD).
3. Construct probability measures `μₙ` with density proportional to `φ̂ₙ`.
4. Their characteristic functions converge to `φ` pointwise.
5. By Lévy continuity, extract the limit measure.

## Sorry audit

* `bochner` — sorry for the Fourier-analytic core (non-negativity of Fourier transform
  of L¹ PD function, which requires Parseval; not in mathlib).
-/

open MeasureTheory Complex ComplexConjugate Filter Topology
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- **Bochner's theorem (ℝ only).** A continuous positive definite function `φ : ℝ → ℂ`
with `φ(0) = 1` is the characteristic function of a unique probability measure on ℝ.

Proof strategy (Gaussian smoothing + Lévy continuity):
1. Define `φₙ(ξ) = φ(ξ) · exp(-ξ²/(2n))`. This is PD (Schur product with Gaussian charFun)
   and L¹ (bounded × Gaussian decay).
2. The Fourier transform `φ̂ₙ` is non-negative (from positive definiteness + Parseval).
3. Since `φ̂ₙ ≥ 0` and `∫ φ̂ₙ = φₙ(0) = 1`, define `μₙ = φ̂ₙ · dx` as a probability measure.
4. By construction, `charFun(μₙ) = φₙ → φ` pointwise as `n → ∞`.
5. Apply Lévy's continuity theorem (`tendsto_of_charFunTendsto`) to extract the limit. -/
theorem bochner
    (φ : ℝ → ℂ) (hφc : Continuous φ) (hpd : IsPositiveDefinite φ)
    (h0 : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ ξ, MeasureTheory.ProbabilityMeasure.characteristicFun μ ξ = φ ξ := by
  sorry

end ProbabilityTheory
