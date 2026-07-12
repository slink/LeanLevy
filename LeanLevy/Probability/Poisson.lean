/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Probability.Distributions.Poisson
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.MeasureTheory.Group.Convolution
import LeanLevy.Probability.Characteristic

/-!
# Poisson Distribution: Expectation, Variance, and Characteristic Function

This file collects the basic facts about the Poisson distribution with rate `r`: its moments,
its characteristic function (in both the ℕ-level and ℝ-pushforward forms), the additivity of
independent Poisson laws under convolution, and the degenerate zero-rate case.

## Main results

* `ProbabilityTheory.poissonExpectation_hasSum` — E[X] = r
* `ProbabilityTheory.poissonVariance` — Var[X] = r
* `ProbabilityTheory.integral_id_poissonMeasure`, `ProbabilityTheory.integral_factorialMoment_poissonMeasure`
  — the mean and second factorial moment as Bochner integrals against `poissonMeasure r`
* `ProbabilityTheory.poissonCharFun_eq` — φ(ξ) = exp(r(e^{iξ} − 1))
* `ProbabilityTheory.charFun_poissonMeasure_eq` — the same identity for the ℝ-pushforward of
  `poissonMeasure r`
* `ProbabilityTheory.poissonMeasure_add_conv` — the sum of two independent Poisson variables is
  Poisson with the summed rate
* `ProbabilityTheory.poissonMeasure_zero` — the zero-rate law is the Dirac mass at `0`

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

/-! ## Moment integrals against `poissonMeasure` -/

/-- A real function on `ℕ` is integrable against `poissonMeasure r` whenever its norm,
weighted by the PMF, is summable. This is the bridge from the `HasSum` moment identities
(which give summability) to `Integrable`, unlocking `PMF.integral_eq_tsum`. -/
private lemma integrable_poissonMeasure_of_summable {r : ℝ≥0} {f : ℕ → ℝ}
    (hf : Summable fun n ↦ ‖f n‖ * poissonPMFReal r n) :
    Integrable f (poissonMeasure r) := by
  refine ⟨Measurable.of_discrete.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_countable']
  have hterm : ∀ n, ‖f n‖ₑ * poissonMeasure r {n} =
      ENNReal.ofReal (‖f n‖ * poissonPMFReal r n) := by
    intro n
    rw [show (poissonMeasure r) {n} = ENNReal.ofReal (poissonPMFReal r n) from
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n),
      ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun n ↦ mul_nonneg (norm_nonneg _) poissonPMFReal_nonneg) hf]
  exact ENNReal.ofReal_lt_top

/-- **Mean of the Poisson distribution (integral form):**
`∫ n, n ∂(poissonMeasure r) = r`. -/
theorem integral_id_poissonMeasure (r : ℝ≥0) :
    ∫ n, (n : ℝ) ∂(poissonMeasure r) = r := by
  have hint : Integrable (fun n : ℕ ↦ (n : ℝ)) (poissonMeasure r) :=
    integrable_poissonMeasure_of_summable <|
      (poissonExpectation_hasSum r).summable.congr fun n ↦ by
        rw [Real.norm_of_nonneg (Nat.cast_nonneg n)]
  rw [show poissonMeasure r = (poissonPMF r).toMeasure from rfl,
    PMF.integral_eq_tsum _ _ hint]
  simp only [poissonPMF_toReal, smul_eq_mul]
  exact (tsum_congr fun n ↦ mul_comm _ _).trans (poissonExpectation_hasSum r).tsum_eq

/-- **Second factorial moment of the Poisson distribution (integral form):**
`∫ n, n(n - 1) ∂(poissonMeasure r) = r²`. -/
theorem integral_factorialMoment_poissonMeasure (r : ℝ≥0) :
    ∫ n, ((n : ℝ) * ((n : ℝ) - 1)) ∂(poissonMeasure r) = (r : ℝ) ^ 2 := by
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · exact mul_nonneg (Nat.cast_nonneg n) (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast h
        linarith)
  have hint : Integrable (fun n : ℕ ↦ (n : ℝ) * ((n : ℝ) - 1)) (poissonMeasure r) :=
    integrable_poissonMeasure_of_summable <|
      (poissonFactorialMoment2_hasSum r).summable.congr fun n ↦ by
        rw [Real.norm_of_nonneg (hnn n)]
  rw [show poissonMeasure r = (poissonPMF r).toMeasure from rfl,
    PMF.integral_eq_tsum _ _ hint]
  simp only [poissonPMF_toReal, smul_eq_mul]
  exact (tsum_congr fun n ↦ mul_comm _ _).trans (poissonFactorialMoment2_hasSum r).tsum_eq

/-! ## Characteristic function -/

/-- The characteristic function of the Poisson distribution, defined as a tsum over ℕ. -/
noncomputable def poissonCharFun (r : ℝ≥0) (ξ : ℝ) : ℂ :=
  ∑' n : ℕ, cexp (↑ξ * ↑(n : ℝ) * I) * ↑(poissonPMFReal r n)

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

/-! ## Degenerate rate -/

/-- At rate `0` the Poisson distribution is a point mass at `0`. -/
theorem poissonMeasure_zero : poissonMeasure 0 = Measure.dirac 0 := by
  refine Measure.ext_of_singleton fun n ↦ ?_
  rw [show poissonMeasure 0 = (poissonPMF 0).toMeasure from rfl,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n),
    Measure.dirac_apply' 0 (measurableSet_singleton n)]
  change ENNReal.ofReal (poissonPMFReal 0 n) = _
  by_cases hn : n = 0
  · subst hn; simp [poissonPMFReal]
  · simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
    simp [poissonPMFReal, zero_pow hn]
    exact fun h ↦ hn h.symm

/-! ## Characteristic function of the pushforward measure -/

/-- The characteristic function of the Poisson measure pushed forward to `ℝ` equals
`exp(r(e^{iξ} − 1))`.

**Proof:**
1. Unfold `charFun` via `charFun_apply_real`.
2. Pull through `Measure.map` via `integral_map`.
3. Unfold `poissonMeasure` as `(poissonPMF r).toMeasure`.
4. Apply `PMF.integral_eq_tsum`.
5. Rewrite `smul` to multiplication.
6. Match with `poissonCharFun` and apply `poissonCharFun_eq`. -/
theorem charFun_poissonMeasure_eq (r : ℝ≥0) (ξ : ℝ) :
    charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) ξ =
    cexp (↑(r : ℝ) * (cexp (↑ξ * I) - 1)) := by
  -- Step 1: Unfold charFun to integral
  rw [charFun_apply_real]
  -- Step 2: Pull integral through Measure.map
  rw [integral_map (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable
    (by fun_prop : Continuous (fun x : ℝ => cexp (↑ξ * ↑x * I))).aestronglyMeasurable]
  -- Step 3: Unfold poissonMeasure as PMF.toMeasure
  change ∫ n, cexp (↑ξ * ↑(n : ℝ) * I) ∂(poissonPMF r).toMeasure = _
  -- Step 4: Apply PMF.integral_eq_tsum
  have hint : Integrable (fun n : ℕ => cexp (↑ξ * ↑(n : ℝ) * I)) (poissonPMF r).toMeasure := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (by fun_prop : Continuous (fun n : ℕ => cexp (↑ξ * ↑(n : ℝ) * I))).measurable.aestronglyMeasurable
    · filter_upwards with n
      rw [show (↑ξ : ℂ) * ↑(n : ℝ) * I = ↑(ξ * ↑n) * I from by push_cast; ring,
        norm_exp_ofReal_mul_I]
  rw [PMF.integral_eq_tsum _ _ hint]
  -- Step 5: Rewrite smul to mul and match poissonCharFun
  simp only [poissonPMF_toReal]
  -- Match poissonCharFun (which has the factors in opposite order) via commutativity
  convert poissonCharFun_eq r ξ using 1
  unfold poissonCharFun
  congr 1; ext n; erw [Algebra.smul_def]; exact mul_comm _ _

/-! ## Poisson convolution on ℕ -/

set_option maxHeartbeats 800000 in
/-- Poisson convolution at the `ℕ` level: pushing forward the product
`poissonMeasure(a) ⊗ poissonMeasure(b)` through addition gives `poissonMeasure(a + b)`.
Derived from the `ℝ`-level characteristic function identity via `Nat.cast` injectivity. -/
theorem poissonMeasure_add_conv (a b : ℝ≥0) :
    ((poissonMeasure a).prod (poissonMeasure b)).map (fun p : ℕ × ℕ => p.1 + p.2) =
    poissonMeasure (a + b) := by
  -- Nat.cast : ℕ → ℝ is a measurable embedding
  have hembed : MeasurableEmbedding (Nat.cast : ℕ → ℝ) :=
    ⟨Nat.cast_injective, measurable_from_top,
      fun {t} _ => (t.to_countable.image _).measurableSet⟩
  -- The ℝ-level convolution: Poisson(a).map cast ∗ Poisson(b).map cast = Poisson(a+b).map cast
  have hR : (poissonMeasure a).map (Nat.cast : ℕ → ℝ) ∗
      (poissonMeasure b).map (Nat.cast : ℕ → ℝ) =
      (poissonMeasure (a + b)).map (Nat.cast : ℕ → ℝ) := by
    apply Measure.ext_of_charFun; funext ξ
    rw [charFun_conv, charFun_poissonMeasure_eq, charFun_poissonMeasure_eq,
      charFun_poissonMeasure_eq, NNReal.coe_add, Complex.ofReal_add, add_mul]
    exact (Complex.exp_add _ _).symm
  -- Key: map Nat.cast of our LHS = convolution on ℝ
  have h_cast_lhs :
      (((poissonMeasure a).prod (poissonMeasure b)).map (fun p : ℕ × ℕ => p.1 + p.2)).map
        (Nat.cast : ℕ → ℝ) =
      (poissonMeasure a).map (Nat.cast : ℕ → ℝ) ∗
      (poissonMeasure b).map (Nat.cast : ℕ → ℝ) := by
    -- Convolution μ ∗ ν = (μ.prod ν).map (+)
    rw [Measure.map_map hembed.measurable Measurable.of_discrete]
    show ((poissonMeasure a).prod (poissonMeasure b)).map
      ((Nat.cast : ℕ → ℝ) ∘ fun p : ℕ × ℕ => p.1 + p.2) = _
    have hcomp : (Nat.cast : ℕ → ℝ) ∘ (fun p : ℕ × ℕ => p.1 + p.2) =
        (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (Nat.cast : ℕ → ℝ) (Nat.cast : ℕ → ℝ) := by
      ext ⟨x, y⟩; simp [Prod.map]
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
        ← Measure.map_prod_map _ _ hembed.measurable hembed.measurable]
    rfl
  -- Combine: map cast of LHS = conv = map cast of RHS
  exact hembed.map_injective (h_cast_lhs.trans hR)

/-- Singleton-level Poisson convolution: the convolution sum at a single point. -/
theorem poissonMeasure_conv_singleton (a b : ℝ≥0) (m : ℕ) :
    (∑' n : ℕ, if n ≤ m then poissonMeasure a {n} * poissonMeasure b {m - n} else 0) =
    poissonMeasure (a + b) {m} := by
  have hpc := poissonMeasure_add_conv a b
  -- Evaluate both sides at {m}
  have hpc' : ((poissonMeasure a).prod (poissonMeasure b)).map
      (fun p : ℕ × ℕ => p.1 + p.2) {m} = poissonMeasure (a + b) {m} := by rw [hpc]
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton m)] at hpc'
  rw [← hpc']
  -- Express preimage as disjoint union of singletons {(n, m-n)}
  have hfib : (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' {m} =
      ⋃ n : ℕ, if n ≤ m then {⟨n, m - n⟩} else ∅ := by
    ext ⟨a', b'⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
    constructor
    · intro hab; exact ⟨a', by rw [if_pos (by omega)]; ext <;> simp; omega⟩
    · rintro ⟨n, hn⟩
      by_cases hle : n ≤ m
      · rw [if_pos hle] at hn; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hn; omega
      · rw [if_neg hle] at hn; exact absurd hn (by simp)
  rw [hfib, measure_iUnion₀
    (by intro i j hij; simp only [Function.onFun, AEDisjoint]
        by_cases hi : i ≤ m
        · by_cases hj : j ≤ m
          · rw [if_pos hi, if_pos hj]
            exact (Set.disjoint_singleton.mpr (fun h => hij (Prod.mk.inj h).1)).aedisjoint
          · rw [if_neg hj]; simp
        · rw [if_neg hi]; simp)
    (by intro n; by_cases hn : n ≤ m
        · rw [if_pos hn]; exact (measurableSet_singleton _).nullMeasurableSet
        · rw [if_neg hn]; exact MeasurableSet.empty.nullMeasurableSet)]
  congr 1; ext n
  by_cases hn : n ≤ m
  · rw [if_pos hn, if_pos hn,
      show ({⟨n, m - n⟩} : Set (ℕ × ℕ)) = {n} ×ˢ {m - n} from (Set.singleton_prod_singleton).symm,
      Measure.prod_prod]
  · rw [if_neg hn, if_neg hn, measure_empty]

end ProbabilityTheory
