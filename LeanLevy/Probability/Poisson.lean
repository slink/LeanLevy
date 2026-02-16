/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import LeanLevy.Probability.Characteristic

/-!
# Poisson Distribution: Expectation, Variance, and Characteristic Function

This file proves three fundamental results about the Poisson distribution with rate `r`:

## Main results

* `ProbabilityTheory.poissonExpectation_hasSum` — E[X] = r
* `ProbabilityTheory.poissonVariance` — Var[X] = r
* `ProbabilityTheory.poissonCharFun_eq` — φ(ξ) = exp(r(e^{iξ} − 1))

## Implementation notes

All three proofs follow the same pattern: strip off the first few zero terms via
`hasSum_nat_add_iff'`, simplify the shifted summand using `Nat.factorial_succ`, and
reduce to `poissonPMFRealSum` (the normalization identity `∑ poissonPMFReal r n = 1`).

The characteristic function connects to the project's `Characteristic.lean` infrastructure
and is needed for future Lévy process / compound Poisson work.
-/

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset

namespace ProbabilityTheory

/-! ## PMF bridge lemmas -/

/-- The PMF value as a real number equals `poissonPMFReal`. -/
lemma poissonPMF_toReal (r : ℝ≥0) (n : ℕ) :
    (poissonPMF r n).toReal = poissonPMFReal r n := by
  change (ENNReal.ofReal (poissonPMFReal r n)).toReal = poissonPMFReal r n
  exact ENNReal.toReal_ofReal poissonPMFReal_nonneg

/-- The real-valued Poisson PMF is summable. -/
lemma summable_poissonPMFReal (r : ℝ≥0) : Summable (poissonPMFReal r) :=
  (poissonPMFRealSum r).summable

/-! ## Expectation: E[X] = r -/

/-- The key algebraic identity: `(n+1) * poissonPMFReal r (n+1) = r * poissonPMFReal r n`. -/
private lemma expectation_shift (r : ℝ≥0) (n : ℕ) :
    ↑(n + 1) * poissonPMFReal r (n + 1) = (r : ℝ) * poissonPMFReal r n := by
  simp only [poissonPMFReal, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have h1 : (↑(n !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  field_simp

/-- **Poisson expectation (HasSum form):** `∑ n * P(X = n) = r`. -/
theorem poissonExpectation_hasSum (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ↑n * poissonPMFReal r n) (r : ℝ) := by
  apply (hasSum_nat_add_iff' 1).mp
  simp only [sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
  simp_rw [expectation_shift]
  simpa [mul_one] using (poissonPMFRealSum r).mul_left (r : ℝ)

/-! ## Variance: Var[X] = r -/

/-- Algebraic identity for the factorial moment shift:
`(n+2)(n+1) * poissonPMFReal r (n+2) = r² * poissonPMFReal r n`. -/
private lemma factorial_moment_shift (r : ℝ≥0) (n : ℕ) :
    (↑(n + 2) : ℝ) * ↑(n + 1) * poissonPMFReal r (n + 2) =
    (r : ℝ) ^ 2 * poissonPMFReal r n := by
  simp only [poissonPMFReal, Nat.factorial_succ, Nat.cast_mul, pow_succ]
  have h1 : (↑(n !) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h2 : (↑(n + 1) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have h3 : (↑(n + 2) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **Second factorial moment:** `∑ n(n-1) * P(X = n) = r²`. -/
theorem poissonFactorialMoment2_hasSum (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ((↑n : ℝ) * (↑n - 1)) * poissonPMFReal r n) ((r : ℝ) ^ 2) := by
  apply (hasSum_nat_add_iff' 2).mp
  simp only [sum_range_succ, sum_range_zero, Nat.cast_zero, Nat.cast_one,
    zero_mul, zero_add, sub_self, mul_zero, sub_zero]
  have key : ∀ n : ℕ, ((↑(n + 2) : ℝ) * (↑(n + 2) - 1)) * poissonPMFReal r (n + 2) =
      (r : ℝ) ^ 2 * poissonPMFReal r n := by
    intro n
    have : (↑(n + 2) : ℝ) - 1 = ↑(n + 1) := by push_cast; ring
    rw [this]
    exact factorial_moment_shift r n
  simp_rw [key]
  simpa [mul_one] using (poissonPMFRealSum r).mul_left ((r : ℝ) ^ 2)

/-- **Second moment:** `∑ n² * P(X = n) = r² + r`. -/
theorem poissonSecondMoment_hasSum (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ (↑n : ℝ) ^ 2 * poissonPMFReal r n) ((r : ℝ) ^ 2 + r) := by
  have h1 := poissonFactorialMoment2_hasSum r
  have h2 := poissonExpectation_hasSum r
  -- n² = n(n-1) + n, so E[X²] = E[X(X-1)] + E[X]
  convert h1.add h2 using 1
  ext n; ring

/-- **Poisson variance:** `∑ (n - r)² * P(X = n) = r`. -/
theorem poissonVariance (r : ℝ≥0) :
    HasSum (fun (n : ℕ) ↦ ((↑n : ℝ) - ↑r) ^ 2 * poissonPMFReal r n) (r : ℝ) := by
  have h1 := poissonSecondMoment_hasSum r
  have h2 := poissonExpectation_hasSum r
  have h3 := poissonPMFRealSum r
  -- (n - r)² = n² - 2rn + r², so Var = E[X²] - 2r·E[X] + r²·1
  have := (h1.sub (h2.mul_left (2 * (r : ℝ)))).add (h3.mul_left ((r : ℝ) ^ 2))
  convert this using 1
  · ext n; ring
  · ring

/-! ## Characteristic function -/

/-- The characteristic function of the Poisson distribution, defined as a tsum over ℕ. -/
noncomputable def poissonCharFun (r : ℝ≥0) (ξ : ℝ) : ℂ :=
  ∑' n : ℕ, cexp (↑ξ * ↑(n : ℝ) * I) * ↑(poissonPMFReal r n)

/-- The summand of the Poisson characteristic function is summable. -/
private lemma summable_poissonCharFun (r : ℝ≥0) (ξ : ℝ) :
    Summable (fun (n : ℕ) ↦ cexp (↑ξ * ↑(n : ℝ) * I) * ↑(poissonPMFReal r n)) := by
  refine (summable_poissonPMFReal r).of_norm_bounded fun n ↦ ?_
  rw [norm_mul, show (↑ξ : ℂ) * ↑(n : ℝ) * I = ↑(ξ * ↑n) * I from by push_cast; ring,
    norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, norm_of_nonneg poissonPMFReal_nonneg]

/-- Algebraic identity: each term of the characteristic function sum factors through `exp`. -/
private lemma charFun_term_eq (r : ℝ≥0) (ξ : ℝ) (n : ℕ) :
    cexp (↑ξ * ↑(n : ℝ) * I) * (↑(poissonPMFReal r n) : ℂ) =
    ↑(rexp (-(r : ℝ))) * (((r : ℝ) * cexp (↑ξ * I)) ^ n / (n ! : ℂ)) := by
  simp only [poissonPMFReal]
  rw [show (↑ξ : ℂ) * ↑(n : ℝ) * I = ↑n * (↑ξ * I) from by push_cast; ring,
    Complex.exp_nat_mul]
  push_cast
  rw [mul_pow]
  ring

/-- **Poisson characteristic function (closed form):**
`φ(ξ) = exp(r(e^{iξ} − 1))`. -/
theorem poissonCharFun_eq (r : ℝ≥0) (ξ : ℝ) :
    poissonCharFun r ξ = cexp ((r : ℝ) * (cexp (↑ξ * I) - 1)) := by
  unfold poissonCharFun
  simp_rw [charFun_term_eq r ξ]
  rw [tsum_mul_left]
  -- The inner tsum is exp(r * exp(iξ)) via expSeries_div_hasSum_exp
  have hsum := NormedSpace.expSeries_div_hasSum_exp
    ((↑(r : ℝ) : ℂ) * cexp ((↑ξ : ℂ) * I))
  rw [hsum.tsum_eq, ← Complex.exp_eq_exp_ℂ]
  -- exp(-r) * exp(r * exp(iξ)) = exp(r * exp(iξ) - r) = exp(r * (exp(iξ) - 1))
  rw [ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end ProbabilityTheory
