/-
Copyright (c) 2026 Tailspin Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tailspin Contributors
-/
import Tailspin.Processes.StochasticProcess
import Tailspin.Processes.Cadlag
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Lévy Processes

This file defines the `IsLevyProcess` predicate for a stochastic process indexed by `ℝ≥0` with
values in a measurable additive group `E`. A Lévy process is characterised by:

1. Starting at zero: `X 0 = 0` a.s.
2. Independent increments.
3. Stationary increments.
4. Càdlàg sample paths a.e.

We also define the **characteristic exponent** `Ψ` via `charFun (μ.map (X 1))` and state the
Lévy–Khintchine factorisation `charFun (μ.map (X t)) ξ = exp(t · Ψ(ξ))`.

## Main definitions

* `ProbabilityTheory.IsLevyProcess` — the predicate bundling the four axioms.
* `ProbabilityTheory.IsLevyProcess.charExponent` — the characteristic exponent `Ψ`.

## Main results

* `ProbabilityTheory.IsLevyProcess.indepFun_increment` — two non-overlapping increments are
  pairwise independent.
* `ProbabilityTheory.IsLevyProcess.identDistrib_increment` — the law of an increment depends
  only on the lag.
* `ProbabilityTheory.IsLevyProcess.charFun_eq_exp_mul` — Lévy–Khintchine factorisation.

## Sorry audit

One sorry remains:
* `charFun_eq_exp_mul` — the helper lemmas (multiplicativity, non-vanishing, rational powers,
  right-continuity) are all fully proved. The remaining sorry is the extension from rational
  to all real times, which requires a branch-cut argument for complex logarithms showing
  that `φ(1/n) = exp(ψ/n)` (not just an arbitrary nth root of `exp(ψ)`).
-/

open MeasureTheory Complex Filter Topology
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {E : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace E] [TopologicalSpace E] [AddGroup E] [Sub E]

/-- A stochastic process `X : ℝ≥0 → Ω → E` is a **Lévy process** with respect to a measure `μ`
if it starts at zero, has independent and stationary increments, and has càdlàg sample paths
almost everywhere. -/
structure IsLevyProcess (X : ℝ≥0 → Ω → E) (μ : Measure Ω) : Prop where
  /-- The process starts at the origin. -/
  start_zero : X 0 = fun _ => 0
  /-- Increments along any monotone partition are mutually independent. -/
  indep_increments : HasIndependentIncrements X μ
  /-- The law of an increment depends only on the lag, not the starting time. -/
  stationary_increments : HasStationaryIncrements X μ
  /-- Almost every sample path is càdlàg. -/
  cadlag_ae : ∀ᵐ ω ∂μ, IsCadlag (fun t => X t ω)

/-! ### API lemmas -/

namespace IsLevyProcess

/-- Two non-overlapping increments of a Lévy process are pairwise independent. -/
theorem indepFun_increment {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (h : IsLevyProcess X μ) {s t u : ℝ≥0} (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun (increment X s t) (increment X t u) μ :=
  h.indep_increments.indepFun_increment hst htu

/-- The law of an increment of a Lévy process depends only on the lag. -/
theorem identDistrib_increment {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (h : IsLevyProcess X μ) (s k : ℝ≥0) :
    IdentDistrib (increment X s (s + k)) (increment X 0 k) μ μ :=
  h.stationary_increments s k

/-! ### Characteristic exponent -/

/-- The **characteristic exponent** of a Lévy process, defined as the complex logarithm of the
characteristic function of the time-1 marginal: `Ψ(ξ) = log(𝔼[exp(i⟨X₁, ξ⟩)])`. -/
noncomputable def charExponent
    [Inner ℝ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (_ : IsLevyProcess X μ) : E → ℂ :=
  fun ξ => Complex.log (charFun (μ.map (X 1)) ξ)

/-! ### Helper lemmas for Lévy–Khintchine factorisation -/

section LKHelpers

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
/-- When `X 0 = 0`, the increment from `0` to `t` equals `X t`. -/
private theorem incr_zero_eq (h0 : X 0 = fun _ => 0) (t : ℝ≥0) :
    increment X 0 t = X t := by
  ext ω; show X t ω - X 0 ω = X t ω
  rw [show X 0 ω = 0 from congr_fun h0 ω, sub_zero]

/-- Multiplicativity: `charFun(X(s+k)) = charFun(X(s)) * charFun(X(k))`. -/
private theorem lk_charFun_mul
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (s k : ℝ≥0) (ξ : E) :
    charFun (μ.map (X (s + k))) ξ = charFun (μ.map (X s)) ξ * charFun (μ.map (X k)) ξ := by
  have hdecomp : X (s + k) = X s + increment X s (s + k) := by
    ext ω; simp [increment_apply]
  have hind : IndepFun (X s) (increment X s (s + k)) μ := by
    have := h.indepFun_increment (s := 0) (t := s) (u := s + k) (zero_le _) le_self_add
    rwa [incr_zero_eq h.start_zero] at this
  have hconv := hind.map_add_eq_map_conv_map₀
    (hX s).aemeasurable (measurable_increment (hX s) (hX (s + k))).aemeasurable
  rw [hdecomp, hconv, charFun_conv]
  have hstat := (h.identDistrib_increment s k).map_eq
  rw [incr_zero_eq h.start_zero] at hstat
  rw [hstat]

/-- `charFun(X(0)) = 1`. -/
private theorem lk_charFun_zero (h : IsLevyProcess X μ) (ξ : E) :
    charFun (μ.map (X 0)) ξ = 1 := by
  have : μ.map (X 0) = Measure.dirac (0 : E) := by
    rw [h.start_zero, Measure.map_const, measure_univ, one_smul]
  rw [this, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul, exp_zero]

/-- Rational powers: `charFun(X(k/n)) = charFun(X(1/n))^k`. -/
private theorem lk_charFun_rat_pow
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (k n : ℕ) (ξ : E) :
    charFun (μ.map (X ((k : ℝ≥0) / (n : ℝ≥0)))) ξ =
      (charFun (μ.map (X (1 / (n : ℝ≥0)))) ξ) ^ k := by
  induction k with
  | zero => simp [lk_charFun_zero h]
  | succ k ih =>
    have : ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0) = 1 / (n : ℝ≥0) + (k : ℝ≥0) / (n : ℝ≥0) := by
      push_cast; ring
    rw [this, lk_charFun_mul h hX, ih, pow_succ, mul_comm]

/-- Right-continuity of `t ↦ charFun(μ.map(X t)) ξ` via DCT and càdlàg paths.

The integral `charFun (μ.map (X t)) ξ = ∫ ω, exp(i⟨X t ω, ξ⟩) dμ` is over the fixed base
measure `μ` (by change of variables). The integrand has norm ≤ 1, and for a.e. `ω` (those with
càdlàg paths), `X t ω → X t₀ ω` as `t → t₀+`, so DCT gives convergence. -/
private theorem lk_charFun_rightCts
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (t₀ : ℝ≥0) (ξ : E) :
    Tendsto (fun t => charFun (μ.map (X t)) ξ) (𝓝[≥] t₀) (𝓝 (charFun (μ.map (X t₀)) ξ)) := by
  -- Rewrite charFun as integral over base measure μ via change of variables
  set F : ℝ≥0 → Ω → ℂ := fun t ω =>
    cexp (Complex.ofReal (@inner ℝ E _ (X t ω) ξ) * I) with hF_def
  have hcov : ∀ t, charFun (μ.map (X t)) ξ = ∫ ω, F t ω ∂μ := by
    intro t; rw [hF_def, charFun_apply, integral_map (hX t).aemeasurable]
    exact (by fun_prop : AEStronglyMeasurable (fun x => cexp (↑(@inner ℝ E _ x ξ) * I))
      (μ.map (X t)))
  -- Suffices to show convergence of the integrals over μ
  suffices Tendsto (fun t => ∫ ω, F t ω ∂μ) (𝓝[≥] t₀) (𝓝 (∫ ω, F t₀ ω ∂μ)) by
    have h1 : (fun t => charFun (μ.map (X t)) ξ) = fun t => ∫ ω, F t ω ∂μ :=
      funext hcov
    rw [h1, hcov t₀]; exact this
  -- Apply DCT with constant bound 1
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
  -- AEStronglyMeasurable for each t
  · apply Eventually.of_forall; intro t
    have : Measurable (fun ω => cexp (↑(@inner ℝ E _ (X t ω) ξ) * I)) := by fun_prop
    exact this.aestronglyMeasurable
  -- Norm bound ≤ 1
  · apply Eventually.of_forall; intro t
    apply Eventually.of_forall; intro ω
    simp only [hF_def, norm_exp_ofReal_mul_I]; exact le_refl _
  -- Integrability of bound
  · exact integrable_const 1
  -- Pointwise convergence from càdlàg
  · filter_upwards [h.cadlag_ae] with ω hω
    simp only [hF_def]
    -- X t ω → X t₀ ω as t → t₀+ by càdlàg
    have hXtend : Tendsto (fun t => X t ω) (𝓝[≥] t₀) (𝓝 (X t₀ ω)) :=
      hω.rightContinuous t₀
    -- (X t ω, ξ) → (X t₀ ω, ξ) in the product topology
    have hPtend : Tendsto (fun t => (X t ω, ξ)) (𝓝[≥] t₀) (𝓝 (X t₀ ω, ξ)) :=
      Filter.Tendsto.prodMk_nhds hXtend tendsto_const_nhds
    -- ⟪X t ω, ξ⟫ → ⟪X t₀ ω, ξ⟫ by continuity of inner product
    have hItend : Tendsto (fun t => @inner ℝ E _ (X t ω) ξ) (𝓝[≥] t₀)
        (𝓝 (@inner ℝ E _ (X t₀ ω) ξ)) :=
      (continuous_inner.tendsto _).comp hPtend
    -- exp(ofReal(⟪·, ξ⟫) * I) is continuous
    exact (((Complex.continuous_ofReal.tendsto _).comp hItend).mul
      tendsto_const_nhds).cexp

/-- Non-vanishing: `charFun(μ.map(X t)) ξ ≠ 0` for all `t` and `ξ`.
Halving argument: if `φ(t) = 0` then `φ(t/2^n) = 0` for all n, but `φ(t/2^n) → φ(0) = 1`. -/
private theorem lk_charFun_ne_zero
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ ≠ 0 := by
  intro habs
  have key : ∀ n : ℕ, charFun (μ.map (X (t / (2 ^ n : ℝ≥0)))) ξ = 0 := by
    intro n; induction n with
    | zero => simp [habs]
    | succ n ih =>
      have hsplit : t / (2 ^ n : ℝ≥0) =
          t / (2 ^ (n + 1) : ℝ≥0) + t / (2 ^ (n + 1) : ℝ≥0) := by
        have h2n : (2 : ℝ≥0) ^ (n + 1) ≠ 0 := pow_ne_zero _ (by positivity)
        rw [← add_div, ← two_mul, show (2 : ℝ≥0) ^ (n + 1) = 2 * 2 ^ n from by ring]
        rw [show (2 : ℝ≥0) * t / (2 * 2 ^ n) = t / 2 ^ n from by
          rw [mul_div_mul_left _ _ (by positivity : (2 : ℝ≥0) ≠ 0)]
          ]
      rw [hsplit, lk_charFun_mul h hX] at ih
      exact mul_self_eq_zero.mp ih
  have htend : Tendsto (fun n : ℕ => t / (2 ^ n : ℝ≥0)) atTop (𝓝 0) := by
    rw [NNReal.tendsto_coe.symm]
    simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.coe_zero]
    exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))
  have hctslim : Tendsto (fun n => charFun (μ.map (X (t / (2 ^ n : ℝ≥0)))) ξ)
      atTop (𝓝 (charFun (μ.map (X 0)) ξ)) := by
    have hrc := lk_charFun_rightCts h hX 0 ξ
    apply hrc.comp
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htend, Eventually.of_forall fun _ => Set.mem_Ici.mpr (zero_le _)⟩
  rw [lk_charFun_zero h] at hctslim
  have : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 1) := by
    convert hctslim using 1; ext n; exact (key n).symm
  have := tendsto_nhds_unique this tendsto_const_nhds
  exact one_ne_zero this

end LKHelpers

/-- **Lévy–Khintchine factorisation**: the characteristic function of the time-`t` marginal
of a Lévy process equals `exp(t · Ψ(ξ))` where `Ψ` is the characteristic exponent. -/
theorem charFun_eq_exp_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ = exp (↑(t : ℝ) * h.charExponent ξ) := by
  set φ : ℝ≥0 → ℂ := fun t => charFun (μ.map (X t)) ξ
  set ψ : ℂ := h.charExponent ξ
  -- φ(1) = exp(ψ)
  have hφ1_ne : φ 1 ≠ 0 := lk_charFun_ne_zero h hX 1 ξ
  have hexp_ψ : exp ψ = φ 1 := exp_log hφ1_ne
  -- φ(n) = φ(1)^n for natural n
  have hφ_nat : ∀ n : ℕ, φ (n : ℝ≥0) = (φ 1) ^ n := by
    intro n; induction n with
    | zero => show charFun _ ξ = _; simp [lk_charFun_zero h]
    | succ n ih =>
      show charFun (μ.map (X ((n + 1 : ℕ) : ℝ≥0))) ξ = _
      rw [show ((n + 1 : ℕ) : ℝ≥0) = 1 + (n : ℝ≥0) from by push_cast; ring,
        lk_charFun_mul h hX]
      change φ 1 * φ (n : ℝ≥0) = _
      rw [ih, pow_succ, mul_comm]
  -- φ(k/n) = φ(1/n)^k
  have hφ_rat : ∀ (k n : ℕ), φ ((k : ℝ≥0) / (n : ℝ≥0)) = (φ (1 / (n : ℝ≥0))) ^ k :=
    fun k n => lk_charFun_rat_pow h hX k n ξ
  -- φ(1/n)^n = φ(1) for positive n
  have hφ_root : ∀ n : ℕ, 0 < n → (φ (1 / (n : ℝ≥0))) ^ n = φ 1 := by
    intro n hn
    have := hφ_rat n n
    rw [show (n : ℝ≥0) / (n : ℝ≥0) = 1 from div_self (Nat.cast_ne_zero.mpr (by omega))] at this
    rw [← this]
  -- Both φ and t ↦ exp(t*ψ) are right-continuous and agree on ℚ≥0.
  -- The remaining gap: showing φ(1/n) = exp(ψ/n) (not just an arbitrary nth root of exp(ψ)).
  -- This requires a branch-cut argument: for large n, φ(1/n) is near 1, so log(φ(1/n)) is in
  -- the principal branch, and n*log(φ(1/n)) = ψ + 2πik forces k=0 by a size estimate.
  -- Once φ agrees with exp(t*ψ) on ℚ≥0, density + right-continuity gives equality everywhere.
  sorry

end IsLevyProcess

end ProbabilityTheory
