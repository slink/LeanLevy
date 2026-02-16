/-
Copyright (c) 2026 Tailspin Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tailspin Contributors
-/
import Tailspin.Processes.LevyProcess
import Tailspin.Processes.PoissonProcess
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Infinite Divisibility and Iterated Convolution

This file develops the theory of infinitely divisible probability measures and connects it to
Lévy processes.

## Main definitions

* `MeasureTheory.Measure.iteratedConv` — the `n`-fold convolution power `μ^{∗n}`.
* `ProbabilityTheory.IsInfinitelyDivisible` — a probability measure `μ` is infinitely divisible
  if for every `n ≥ 1` there exists a probability measure `ν` with `μ = ν^{∗n}`.
* `ProbabilityTheory.LevyKhintchineTriple` — the drift-diffusion-jump triple `(b, σ², ν)`.

## Main results

* `MeasureTheory.Measure.charFun_iteratedConv` — `charFun (μ^{∗n}) t = (charFun μ t) ^ n`.
* `ProbabilityTheory.isInfinitelyDivisible_poissonMeasure_map` — the Poisson distribution
  is infinitely divisible.
* `ProbabilityTheory.IsLevyProcess.charFun_marginal_nat_pow` — for a Lévy process,
  `charFun(X(n)) = charFun(X(1))^n`.

## Sorry audit

Two sorries remain:
* `IsLevyProcess.isInfinitelyDivisible_marginal` — partition bookkeeping with `ℝ≥0`.
* `levyKhintchine_representation` — deep analytic theorem (Fourier analysis + Lévy measures).
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal ENNReal

/-! ## Section 1: Iterated convolution -/

namespace MeasureTheory.Measure

variable {E : Type*} [AddCommMonoid E] [MeasurableSpace E]

/-- The `n`-fold convolution power of a measure: `μ^{∗0} = δ₀`, `μ^{∗(n+1)} = μ ∗ μ^{∗n}`. -/
noncomputable def iteratedConv (μ : Measure E) : ℕ → Measure E
  | 0 => dirac 0
  | n + 1 => μ ∗ (iteratedConv μ n)

@[simp]
theorem iteratedConv_zero (μ : Measure E) : μ.iteratedConv 0 = dirac 0 := rfl

@[simp]
theorem iteratedConv_succ (μ : Measure E) (n : ℕ) :
    μ.iteratedConv (n + 1) = μ ∗ μ.iteratedConv n := rfl

variable [MeasurableAdd₂ E]

@[simp]
theorem iteratedConv_one (μ : Measure E) [SFinite μ] :
    μ.iteratedConv 1 = μ := conv_dirac_zero μ

instance isProbabilityMeasure_iteratedConv (μ : Measure E) [IsProbabilityMeasure μ] :
    ∀ n : ℕ, IsProbabilityMeasure (μ.iteratedConv n)
  | 0 => by rw [iteratedConv_zero]; infer_instance
  | n + 1 => by
    haveI := isProbabilityMeasure_iteratedConv μ n
    show IsProbabilityMeasure (μ ∗ μ.iteratedConv n)
    show IsProbabilityMeasure
      (Measure.map (fun p : E × E ↦ p.1 + p.2) (μ.prod (μ.iteratedConv n)))
    exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem charFun_iteratedConv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (t : E) :
    charFun (μ.iteratedConv n) t = (charFun μ t) ^ n := by
  induction n with
  | zero =>
    simp only [iteratedConv_zero, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, pow_zero]
  | succ n ih =>
    haveI := isProbabilityMeasure_iteratedConv μ n
    rw [iteratedConv_succ, charFun_conv, ih, pow_succ, mul_comm]

end MeasureTheory.Measure

/-! ## Section 2: Infinite divisibility -/

namespace ProbabilityTheory

variable {E : Type*} [AddCommMonoid E] [MeasurableSpace E]

/-- A probability measure `μ` is **infinitely divisible** if for every `n ≥ 1`,
there exists a probability measure `ν` such that `μ = ν^{∗n}`. -/
def IsInfinitelyDivisible (μ : Measure E) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ν : Measure E, IsProbabilityMeasure ν ∧ μ = ν.iteratedConv n

/-! ## Section 3: Poisson is infinitely divisible -/

set_option maxHeartbeats 400000 in
/-- Convolution of Poisson measures pushed to ℝ corresponds to addition of rates:
`Poisson(a).map ℕ↪ℝ ∗ Poisson(b).map ℕ↪ℝ = Poisson(a+b).map ℕ↪ℝ`.
The proof compares characteristic functions and applies `Measure.ext_of_charFun`. -/
theorem poissonMeasure_map_natCast_conv (a b : ℝ≥0) :
    (poissonMeasure a).map (Nat.cast : ℕ → ℝ) ∗ (poissonMeasure b).map (Nat.cast : ℕ → ℝ) =
    (poissonMeasure (a + b)).map (Nat.cast : ℕ → ℝ) := by
  apply Measure.ext_of_charFun
  funext ξ
  rw [charFun_conv, charFun_poissonMeasure_eq, charFun_poissonMeasure_eq,
    charFun_poissonMeasure_eq]
  rw [NNReal.coe_add, Complex.ofReal_add, add_mul]
  exact (Complex.exp_add _ _).symm

set_option maxHeartbeats 800000 in
/-- The Poisson distribution (pushed to ℝ) is infinitely divisible. For each `n`, take
`ν = Poisson(r/n).map ℕ↪ℝ`; then `ν^{∗n}` has characteristic function
`exp(n · (r/n) · (e^{iξ} − 1)) = exp(r · (e^{iξ} − 1))`. -/
theorem isInfinitelyDivisible_poissonMeasure_map (r : ℝ≥0) :
    IsInfinitelyDivisible ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) := by
  intro n hn
  set ν := (poissonMeasure (r / ↑n)).map (Nat.cast : ℕ → ℝ) with hν_def
  haveI hνP : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable
  refine ⟨ν, hνP, ?_⟩
  apply Measure.ext_of_charFun
  funext ξ
  rw [hν_def, Measure.charFun_iteratedConv, charFun_poissonMeasure_eq,
    charFun_poissonMeasure_eq, ← Complex.exp_nat_mul]
  congr 1
  have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [NNReal.coe_div, NNReal.coe_natCast, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← mul_assoc, mul_div_cancel₀ _ hne]

/-! ## Section 4: Lévy process charFun at natural times -/

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- When `X 0 = 0`, the increment from `0` to `t` equals `X t`. -/
private theorem increment_zero_eq' {E : Type*} [AddGroup E]
    {X : ℝ≥0 → Ω → E} (h0 : X 0 = fun _ => 0) (t : ℝ≥0) :
    increment X 0 t = X t := by
  ext ω; show X t ω - X 0 ω = X t ω
  rw [show X 0 ω = 0 from congr_fun h0 ω, sub_zero]

/-- For a Lévy process, `charFun(X(n)) = charFun(X(1))^n` where `n : ℕ` is cast to `ℝ≥0`.

The proof proceeds by induction on `n`:
* Base: `X 0 = 0` gives `μ.map (X 0) = dirac 0`, so `charFun = 1`.
* Step: Decompose `X(n+1) = X(n) + increment(n, n+1)`, use independent increments to factor
  the charFun as a product, and use stationary increments to identify each factor. -/
theorem IsLevyProcess.charFun_marginal_nat_pow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (n : ℕ) (ξ : E) :
    charFun (μ.map (X (n : ℝ≥0))) ξ = (charFun (μ.map (X 1)) ξ) ^ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, pow_zero]
    have hmap : μ.map (X (0 : ℝ≥0)) = dirac (0 : E) := by
      rw [h.start_zero, Measure.map_const, measure_univ, one_smul]
    rw [hmap, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  | succ n ih =>
    have h_cast : (↑(n + 1) : ℝ≥0) = (↑n : ℝ≥0) + 1 := by push_cast; ring
    -- Decompose: X(n+1) = X(n) + increment X n (n+1)
    have h_decomp : X ((↑n : ℝ≥0) + 1) =
        X (↑n : ℝ≥0) + increment X (↑n : ℝ≥0) ((↑n : ℝ≥0) + 1) := by
      ext ω; simp only [Pi.add_apply, increment_apply]; abel
    -- Independence: increment X 0 n ⊥ increment X n (n+1), rewrite to X n ⊥ increment
    have h_incr_eq : increment X (0 : ℝ≥0) (↑n : ℝ≥0) = X (↑n : ℝ≥0) :=
      increment_zero_eq' h.start_zero _
    have h_indep : IndepFun (X (↑n : ℝ≥0))
        (increment X (↑n : ℝ≥0) ((↑n : ℝ≥0) + 1)) μ := by
      have := h.indepFun_increment (s := 0) (t := ↑n) (u := ↑n + 1) (zero_le _) le_self_add
      rwa [h_incr_eq] at this
    -- μ.map (X n + incr) = μ.map (X n) ∗ μ.map (incr), via independence
    have hmI : AEMeasurable (increment X (↑n : ℝ≥0) ((↑n : ℝ≥0) + 1)) μ :=
      (measurable_increment (hX _) (hX _)).aemeasurable
    have h_conv : μ.map (X (↑n : ℝ≥0) + increment X (↑n : ℝ≥0) ((↑n : ℝ≥0) + 1)) =
        μ.map (X (↑n : ℝ≥0)) ∗ μ.map (increment X (↑n : ℝ≥0) ((↑n : ℝ≥0) + 1)) :=
      h_indep.map_add_eq_map_conv_map₀ (hX _).aemeasurable hmI
    -- Stationarity: μ.map (increment X n (n+1)) = μ.map (X 1)
    have h_stat := (h.identDistrib_increment (↑n : ℝ≥0) 1).map_eq
    have h_incr1 : increment X (0 : ℝ≥0) 1 = X 1 := increment_zero_eq' h.start_zero _
    have h_stat_map : μ.map (increment X (↑n : ℝ≥0) ((↑n : ℝ≥0) + 1)) = μ.map (X 1) := by
      rw [h_stat, h_incr1]
    -- Combine: charFun(X(n+1)) = charFun(X n) * charFun(X 1) = charFun(X 1)^n * charFun(X 1)
    rw [h_cast, h_decomp, h_conv, charFun_conv, h_stat_map, ih, pow_succ]

/-! ## Section 5: Lévy process marginals are infinitely divisible -/

/-- Every marginal `μ.map (X t)` of a Lévy process is infinitely divisible.

**Strategy (sorry'd):** Partition `[0, t]` into `n` equal pieces of length `t/n`,
use independent stationary increments to write the marginal as an `n`-fold convolution
of `μ.map (X (t/n))`. The bookkeeping with `ℝ≥0` arithmetic and `iIndepFun` extraction
is extensive. -/
theorem IsLevyProcess.isInfinitelyDivisible_marginal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (t : ℝ≥0) :
    IsInfinitelyDivisible (μ.map (X t)) := by
  sorry -- Partition [0,t] into n equal pieces, use independent stationary increments

/-! ## Section 6: Lévy-Khintchine representation -/

/-- The **Lévy-Khintchine triple** `(b, σ², ν)` consisting of a drift, Gaussian variance,
and Lévy measure. The Lévy measure satisfies the integrability condition
`∫ min(1, x²) dν < ∞`. -/
structure LevyKhintchineTriple where
  /-- Drift parameter. -/
  drift : ℝ
  /-- Gaussian variance (non-negative). -/
  gaussianVariance : ℝ≥0
  /-- Lévy measure: a σ-finite measure on `ℝ \ {0}` satisfying `∫ min(1, x²) dν < ∞`. -/
  levyMeasure : Measure ℝ
  /-- The Lévy measure assigns zero mass to the origin. -/
  levyMeasure_zero : levyMeasure {0} = 0
  /-- Integrability condition: `∫ min(1, x²) dν < ∞`. -/
  integrable_min_one_sq : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂levyMeasure < ⊤

/-- **Lévy-Khintchine representation theorem**: every infinitely divisible probability measure
on `ℝ` has a characteristic function of the form
`exp(ibξ − σ²ξ²/2 + ∫ (e^{ixξ} − 1 − ixξ·1_{|x|≤1}) dν(x))`.

This is a deep analytic result requiring Fourier analysis and Lévy measure theory. -/
theorem levyKhintchine_representation
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ∃ T : LevyKhintchineTriple, ∀ ξ : ℝ,
      charFun μ ξ = Complex.exp (
        ↑T.drift * ↑ξ * Complex.I
        - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
        + ∫ x, (Complex.exp (↑x * ↑ξ * Complex.I) - 1
          - ↑x * ↑ξ * Complex.I * if |x| ≤ 1 then 1 else 0) ∂T.levyMeasure) := by
  sorry -- Deep analytic theorem (Fourier analysis + Lévy measure theory)

end ProbabilityTheory
