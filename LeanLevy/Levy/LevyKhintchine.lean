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

* `ProbabilityTheory.levyKhintchine_representation` — the representation theorem (sorry).

## Sorry audit

The representation theorem chains through four sub-lemmas (1–3 fully proved) to
`levyKhintchine_of_cnd`, which uses Schoenberg + Bochner with a remaining sorry
for the convolution semigroup differentiation step. See `LevyKhintchineProof.lean`
and `Bochner.lean` for details.
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
