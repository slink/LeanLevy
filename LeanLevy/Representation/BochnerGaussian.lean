/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Fourier.PositiveDefinite
import LeanLevy.Fourier.Bochner

/-!
# Bochner–Gaussian: Covariance Matrix and Bochner Identity

This file provides two pieces of API connecting positive definite functions to the
Bochner theorem.

## Main definitions

* `ProbabilityTheory.covMatrix` — for times `t : Fin n → ℝ` and `ψ : ℝ → ℂ`, the
  covariance matrix `covMatrix ψ t i j = ψ (t i - t j)`.

## Main results

* `ProbabilityTheory.covMatrix_is_psd` — the covariance matrix of a positive definite
  function is positive semidefinite.
* `ProbabilityTheory.bochner_identity` — Bochner's theorem in explicit-integral form:
  every continuous positive definite `ψ` with `ψ 0 = 1` is the characteristic function
  of a probability measure on `ℝ`.
-/

open MeasureTheory Complex
open scoped ComplexOrder

namespace ProbabilityTheory

/-! ## Covariance matrix -/

/-- The covariance matrix for a finite set of times `t : Fin n → ℝ` given a function `ψ`:
`covMatrix ψ t i j = ψ (t i - t j)`. -/
noncomputable def covMatrix {n : ℕ} (ψ : ℝ → ℂ) (t : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ψ (t i - t j)

@[simp]
theorem covMatrix_apply {n : ℕ} (ψ : ℝ → ℂ) (t : Fin n → ℝ) (i j : Fin n) :
    covMatrix ψ t i j = ψ (t i - t j) :=
  rfl

/-- The covariance matrix of a positive definite function is positive semidefinite. -/
lemma covMatrix_is_psd {n : ℕ} (ψ : ℝ → ℂ) (t : Fin n → ℝ)
    (hψ : IsPositiveDefinite ψ) :
    (covMatrix ψ t).PosSemidef :=
  hψ.pdMatrix_posSemidef n t

/-! ## Bochner Identity -/

/-- **Bochner Identity**: for a continuous positive definite function `ψ` with `ψ(0) = 1`,
there exists a spectral probability measure `μ` such that
`ψ t = ∫ x, exp(I · t · x) ∂μ` for all `t : ℝ`.

This follows directly from `bochner` by unfolding `characteristicFun` to an explicit integral. -/
lemma bochner_identity
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ t : ℝ, ψ t = ∫ x : ℝ, Complex.exp (Complex.I * ↑t * ↑x) ∂(μ : Measure ℝ) := by
  obtain ⟨μ, hμ⟩ := bochner ψ hψc hpd h0
  exact ⟨μ, fun t => by
    have h := (hμ t).symm
    simp only [MeasureTheory.ProbabilityMeasure.characteristicFun_def, charFun_apply_real] at h
    rw [h]; congr 1; ext x; ring_nf⟩

end ProbabilityTheory
