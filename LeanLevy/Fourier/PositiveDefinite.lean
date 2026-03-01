/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Probability.Characteristic

/-!
# Positive Definite Functions on ℝ

A function `φ : ℝ → ℂ` is **positive definite** if for every finite sequence of points
`x₁, …, xₙ` and complex weights `c₁, …, cₙ`, the Hermitian form
`∑ᵢ ∑ⱼ c̄ᵢ cⱼ φ(xᵢ − xⱼ)` has non-negative real part.

## Main definitions

* `ProbabilityTheory.IsPositiveDefinite` — the positive-definiteness predicate.

## Main results

* `IsPositiveDefinite.apply_zero_nonneg` — `φ(0).re ≥ 0`.
* `IsPositiveDefinite.mul` — Schur product: pointwise product of PD functions is PD.
* `IsPositiveDefinite.of_charFun` — characteristic function of a probability measure is PD.
* `IsPositiveDefinite.closure_pointwise` — pointwise limit of PD functions is PD.

## Sorry audit

* `mul` — Schur product theorem (requires Hadamard product PSD argument).
* `norm_le_one` — PD bound `‖φ(ξ)‖ ≤ 1` when `φ(0) = 1` (2x2 PSD + Hermitian symmetry).
-/

open MeasureTheory Complex ComplexConjugate Finset Filter Topology
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- A function `φ : ℝ → ℂ` is **positive definite** if for every `n`, points `x : Fin n → ℝ`,
and weights `c : Fin n → ℂ`, the Hermitian form `∑ᵢ ∑ⱼ c̄ᵢ cⱼ φ(xᵢ − xⱼ)` has
non-negative real part.

This matches the convention in `characteristicFun_positiveSemiDefinite`. -/
def IsPositiveDefinite (φ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)).re

namespace IsPositiveDefinite

variable {φ ψ : ℝ → ℂ}

/-- `φ(0).re ≥ 0`. Specialise to `n = 1`, `c = 1`, `x = 0`. -/
theorem apply_zero_nonneg (hφ : IsPositiveDefinite φ) : 0 ≤ (φ 0).re := by
  have h := hφ 1 (fun _ => 0) (fun _ => 1)
  simp [sub_self] at h
  exact h

/-- **Schur product theorem.** The pointwise product of two positive definite functions
is positive definite.

Proof: The matrix `(φ(xᵢ-xⱼ) ψ(xᵢ-xⱼ))` is the Hadamard product of two PSD matrices,
which is PSD by the Schur product theorem. -/
theorem mul (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (fun x => φ x * ψ x) := by
  sorry

/-- Pointwise limit of positive definite functions is positive definite. -/
theorem closure_pointwise {φs : ℕ → ℝ → ℂ} (hφs : ∀ n, IsPositiveDefinite (φs n))
    {φ : ℝ → ℂ} (hlim : ∀ x, Tendsto (fun n => φs n x) atTop (𝓝 (φ x))) :
    IsPositiveDefinite φ := by
  intro n x c
  have htend : Tendsto (fun m => (∑ i, ∑ j,
      starRingEnd ℂ (c i) * c j * φs m (x i - x j)).re) atTop
      (𝓝 (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * φ (x i - x j)).re) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    exact (hlim (x i - x j)).const_mul _
  exact ge_of_tendsto htend (Eventually.of_forall fun m => hφs m n x c)

/-- For a positive definite function with `φ(0) = 1`, `‖φ(ξ)‖ ≤ 1`.

Proof sketch: Take `n = 2`, `x = (0, ξ)`, `c = (1, -φ(ξ)/‖φ(ξ)‖)`. The PD condition yields
`0 ≤ 2 - 2‖φ(ξ)‖`, hence `‖φ(ξ)‖ ≤ 1`. Requires the Hermitian symmetry `φ(-ξ) = conj(φ(ξ))`
which follows from the PD condition. -/
theorem norm_le_one (hφ : IsPositiveDefinite φ) (h0 : φ 0 = 1) (ξ : ℝ) :
    ‖φ ξ‖ ≤ 1 := by
  sorry

/-- The characteristic function of a probability measure is positive definite. -/
theorem of_charFun (μ : ProbabilityMeasure ℝ) :
    IsPositiveDefinite (fun ξ => charFun (μ : Measure ℝ) ξ) := by
  intro n x c
  exact ProbabilityMeasure.characteristicFun_positiveSemiDefinite μ x c

end IsPositiveDefinite

end ProbabilityTheory
