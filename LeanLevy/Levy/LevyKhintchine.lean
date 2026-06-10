/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Levy.InfiniteDivisible
import LeanLevy.Levy.LevyMeasure
import LeanLevy.Levy.CompensatedIntegral

/-!
# Lévy-Khintchine Representation

The **Lévy-Khintchine theorem** characterises infinitely divisible probability measures on `ℝ`:
their characteristic function has the form
`exp(ibξ − σ²ξ²/2 + ∫ (e^{ixξ} − 1 − ixξ·1_{|x|<1}) dν(x))`
where `(b, σ², ν)` is the Lévy-Khintchine triple.

## Main definitions

* `ProbabilityTheory.LevyKhintchineTriple` — the drift-diffusion-jump triple `(b, σ², ν)`.

## Main results

* `ProbabilityTheory.levyKhintchine_representation_finite` — the representation theorem
  in the finite-ν case (compound-Poisson + Gaussian pivot), under a uniform
  finite-small-mass hypothesis on the associated convolution semigroup. Fully proved.

## Proof structure

The representation theorem chains through four sub-lemmas to
`levyKhintchine_of_cnd_finite`, which uses Schoenberg + Bochner together with the
diagonal extraction `exists_drift_variance_jumpMeasure_along_seq`. The analytic
limit-identification core `psi_eq_levyKhintchine_formula` (the small-jump + large-jump
limit identifications) is fully proved. See `LevyKhintchineProof.lean` and `Bochner.lean`.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- The **Lévy-Khintchine triple** `(b, σ², ν)` consisting of a drift, Gaussian variance,
and Lévy measure. The Lévy measure satisfies `IsLevyMeasure`, i.e., `ν({0}) = 0` and
`∫ min(1, x²) dν < ∞`. -/
structure LevyKhintchineTriple where
  /-- Drift parameter. -/
  drift : ℝ
  /-- Gaussian variance (non-negative). -/
  gaussianVariance : ℝ≥0
  /-- Lévy measure satisfying `ν({0}) = 0` and `∫ min(1, x²) dν < ∞`. -/
  levyMeasure : Measure ℝ
  /-- The Lévy measure satisfies the Lévy measure conditions. -/
  levyMeasure_isLevyMeasure : IsLevyMeasure levyMeasure

namespace LevyKhintchineTriple

variable (T : LevyKhintchineTriple)

theorem levyMeasure_zero : T.levyMeasure {0} = 0 :=
  T.levyMeasure_isLevyMeasure.zero_singleton

theorem integrable_min_one_sq :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂T.levyMeasure < ⊤ :=
  T.levyMeasure_isLevyMeasure.lintegral_min_one_sq_lt_top

end LevyKhintchineTriple

end ProbabilityTheory
