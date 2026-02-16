/-
Copyright (c) 2026 Tailspin Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tailspin Contributors
-/
import Tailspin.Processes.StochasticProcess
import Tailspin.Processes.Cadlag
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log

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

/-- The **characteristic exponent** of a Lévy process, defined as the limit
`Ψ(ξ) = lim_{t→0+} log(φ(t))/t` where `φ(t) = charFun(μ.map(X t)) ξ`.

For small `t > 0`, the characteristic function `φ(t)` is near 1 (since `φ(0) = 1` and `φ` is
right-continuous), so the principal branch logarithm is well-defined and continuous. The limit
exists because `log(φ(t))/t` is eventually constant (equal to the true exponent `c` satisfying
`φ(t) = exp(tc)` for all `t`). -/
noncomputable def charExponent
    [Inner ℝ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (_ : IsLevyProcess X μ) : E → ℂ :=
  fun ξ => limUnder (𝓝[>] (0 : ℝ≥0))
    (fun t => Complex.log (charFun (μ.map (X t)) ξ) / ↑(t : ℝ))

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

/-- Natural multiplicativity: `φ(n·s) = φ(s)^n`. -/
private theorem lk_charFun_nat_mul
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (n : ℕ) (s : ℝ≥0) (ξ : E) :
    charFun (μ.map (X ((n : ℝ≥0) * s))) ξ = (charFun (μ.map (X s)) ξ) ^ n := by
  induction n with
  | zero => simp [show (0 : ℝ≥0) * s = 0 from zero_mul s, lk_charFun_zero h]
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℝ≥0) * s = s + (n : ℝ≥0) * s from by push_cast; ring,
        lk_charFun_mul h hX, ih, pow_succ, mul_comm]

end LKHelpers

/-- **Lévy–Khintchine factorisation**: the characteristic function of the time-`t` marginal
of a Lévy process equals `exp(t · Ψ(ξ))` where `Ψ` is the characteristic exponent. -/
theorem charFun_eq_exp_mul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ = exp (↑(t : ℝ) * h.charExponent ξ) := by
  set φ : ℝ≥0 → ℂ := fun t => charFun (μ.map (X t)) ξ with hφ_def
  -- Basic properties
  have hφ0 : φ 0 = 1 := lk_charFun_zero h ξ
  have hφ_ne : ∀ t, φ t ≠ 0 := fun t => lk_charFun_ne_zero h hX t ξ
  have hφ_mul : ∀ s k, φ (s + k) = φ s * φ k :=
    fun s k => lk_charFun_mul h hX s k ξ
  have hφ_pow : ∀ (n : ℕ) (s : ℝ≥0), φ ((n : ℝ≥0) * s) = (φ s) ^ n :=
    fun n s => lk_charFun_nat_mul h hX n s ξ
  have hφ_rat : ∀ (k n : ℕ), φ ((k : ℝ≥0) / (n : ℝ≥0)) = (φ (1 / (n : ℝ≥0))) ^ k :=
    fun k n => lk_charFun_rat_pow h hX k n ξ
  -- 𝓝[≥] 0 = 𝓝 0 in ℝ≥0 (all elements are ≥ 0)
  have hIci_eq : 𝓝[≥] (0 : ℝ≥0) = 𝓝 0 := by
    rw [show Set.Ici (0 : ℝ≥0) = Set.univ from
      Set.eq_univ_of_forall (fun x => zero_le x), nhdsWithin_univ]
  -- φ → 1 as t → 0 in ℝ≥0
  have hφ_tendsto0 : Tendsto φ (𝓝 (0 : ℝ≥0)) (𝓝 1) := by
    rw [← hIci_eq, ← hφ0]; exact lk_charFun_rightCts h hX 0 ξ
  -- ═══════════════════════════════════════════════════════
  -- PHASE 1: Find δ > 0 with 0 < re(φ(t)) for t < δ
  -- ═══════════════════════════════════════════════════════
  obtain ⟨δ, hδ_pos, hδ_re⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : ℝ≥0, t < δ → 0 < (φ t).re := by
    have hmem : {z : ℂ | 0 < z.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.eventually_nhds_iff.mp (hφ_tendsto0.eventually hmem)
    refine ⟨⟨ε, hε_pos.le⟩, ?_, fun t ht => hε_sub ?_⟩
    · exact_mod_cast hε_pos
    · simp only [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]
      exact_mod_cast ht
  -- ═══════════════════════════════════════════════════════
  -- PHASE 2: Log-additivity for t < δ
  -- ═══════════════════════════════════════════════════════
  -- When 0 < re(φ(t)), |arg(φ(t))| < π/2
  have harg_small : ∀ t : ℝ≥0, t < δ → |arg (φ t)| < Real.pi / 2 :=
    fun t ht => abs_arg_lt_pi_div_two_iff.mpr (Or.inl (hδ_re t ht))
  -- log(φ(s) * φ(t)) = log(φ(s)) + log(φ(t)) when s, t < δ
  have hlog_mul : ∀ s t : ℝ≥0, s < δ → t < δ →
      log (φ s * φ t) = log (φ s) + log (φ t) := by
    intro s t hs ht
    apply log_mul (hφ_ne s) (hφ_ne t)
    constructor
    · have h1 := (abs_lt.mp (harg_small s hs)).1
      have h2 := (abs_lt.mp (harg_small t ht)).1
      linarith
    · have h1 := (abs_lt.mp (harg_small s hs)).2
      have h2 := (abs_lt.mp (harg_small t ht)).2
      linarith
  -- log(φ(n*s)) = n * log(φ(s)) when n*s < δ
  have hlog_pow : ∀ (n : ℕ) (s : ℝ≥0), (n : ℝ≥0) * s < δ →
      log (φ ((n : ℝ≥0) * s)) = ↑(n : ℤ) * log (φ s) := by
    intro n; induction n with
    | zero => intro s _; simp [show (0 : ℝ≥0) * s = 0 from zero_mul s, hφ0, log_one]
    | succ n ih =>
      intro s hs
      have hs_lt : s < δ := lt_of_le_of_lt
        (le_mul_of_one_le_left s.2 (by exact_mod_cast Nat.succ_pos n)) hs
      have hns_lt : (n : ℝ≥0) * s < δ := lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) s.2) hs
      rw [show ((n + 1 : ℕ) : ℝ≥0) * s = s + (n : ℝ≥0) * s from by push_cast; ring]
      rw [show φ (s + (n : ℝ≥0) * s) = φ s * φ ((n : ℝ≥0) * s) from hφ_mul _ _]
      rw [hlog_mul s ((n : ℝ≥0) * s) hs_lt hns_lt, ih s hns_lt]
      push_cast; ring
  -- ═══════════════════════════════════════════════════════
  -- PHASE 3: Define the exponent c and prove constancy
  -- ═══════════════════════════════════════════════════════
  obtain ⟨N, hN_pos, hN_small⟩ : ∃ N : ℕ, 0 < N ∧ (1 : ℝ≥0) / (N : ℝ≥0) < δ := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((δ : ℝ)⁻¹)
    have hn_pos : 0 < n := by
      exact_mod_cast lt_trans (inv_pos.mpr (by positivity : (0 : ℝ) < δ)) hn
    refine ⟨n, hn_pos, ?_⟩
    rw [show (1 : ℝ≥0) / (n : ℝ≥0) < δ ↔ ((1 : ℝ) / (n : ℝ) < (δ : ℝ)) from by
      rw [← NNReal.coe_lt_coe]; simp]
    rw [one_div]
    calc (↑n : ℝ)⁻¹ = 1 / ↑n := (one_div _).symm
      _ < 1 / (δ : ℝ)⁻¹ :=
          one_div_lt_one_div_of_lt (inv_pos.mpr (by positivity : (0 : ℝ) < ↑δ)) hn
      _ = ↑δ := by rw [one_div, inv_inv]
  set c : ℂ := ↑(N : ℤ) * log (φ (1 / (N : ℝ≥0))) with hc_def
  -- n * log(φ(1/n)) = c for all n with 1/n < δ and n > 0
  have hconst : ∀ n : ℕ, 0 < n → (1 : ℝ≥0) / (n : ℝ≥0) < δ →
      ↑(n : ℤ) * log (φ (1 / (n : ℝ≥0))) = c := by
    intro n hn hn_lt
    have hn_ne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hN_ne : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    -- Key identities in ℝ≥0
    have hNnN : (N : ℝ≥0) * (1 / ((n * N : ℕ) : ℝ≥0)) = 1 / (n : ℝ≥0) := by
      rw [Nat.cast_mul, one_div, one_div, mul_inv, mul_comm (n : ℝ≥0)⁻¹,
          ← mul_assoc, mul_inv_cancel₀ hN_ne, one_mul]
    have hnnN : (n : ℝ≥0) * (1 / ((n * N : ℕ) : ℝ≥0)) = 1 / (N : ℝ≥0) := by
      rw [Nat.cast_mul, one_div, one_div, mul_inv, ← mul_assoc,
          mul_inv_cancel₀ hn_ne, one_mul]
    -- Apply hlog_pow in both directions
    have h1 := hlog_pow N (1 / ((n * N : ℕ) : ℝ≥0)) (by rw [hNnN]; exact hn_lt)
    rw [hNnN] at h1
    have h2 := hlog_pow n (1 / ((n * N : ℕ) : ℝ≥0)) (by rw [hnnN]; exact hN_small)
    rw [hnnN] at h2
    -- n * log(φ(1/n)) = n * N * log(φ(1/(nN))) = N * log(φ(1/N)) = c
    calc ↑(n : ℤ) * log (φ (1 / (n : ℝ≥0)))
        = ↑(n : ℤ) * (↑(N : ℤ) * log (φ (1 / ((n * N : ℕ) : ℝ≥0)))) := by rw [h1]
      _ = ↑(N : ℤ) * (↑(n : ℤ) * log (φ (1 / ((n * N : ℕ) : ℝ≥0)))) := by ring
      _ = ↑(N : ℤ) * log (φ (1 / (N : ℝ≥0))) := by rw [h2]
  -- ═══════════════════════════════════════════════════════
  -- PHASE 4: Rational formula φ(k/n) = exp(c * k/n)
  -- ═══════════════════════════════════════════════════════
  -- Helper: φ(1/n) = exp(c/n) for all n > 0
  have hφ_inv_exp : ∀ n : ℕ, 0 < n → φ (1 / (n : ℝ≥0)) = exp (c / ↑(n : ℕ)) := by
    intro n hn
    have hn_ne : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hN_ne : (N : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hnN_pos : 0 < n * N := Nat.mul_pos hn hN_pos
    have hnN_ne : (n * N : ℕ) ≠ 0 := by omega
    -- 1/(nN) < δ since N ≤ nN and 1/N < δ
    have hnN_small : (1 : ℝ≥0) / ((n * N : ℕ) : ℝ≥0) < δ :=
      lt_of_le_of_lt
        (one_div_le_one_div_of_le (Nat.cast_pos.mpr hN_pos)
          (by exact_mod_cast Nat.le_mul_of_pos_left N hn))
        hN_small
    -- (nN) * log(φ(1/(nN))) = c
    have hlog_nN := hconst (n * N) hnN_pos hnN_small
    -- φ(1/(nN)) = exp(c/(nN))
    have hφ_nN : φ (1 / ((n * N : ℕ) : ℝ≥0)) = exp (c / ↑(n * N : ℕ)) := by
      rw [← exp_log (hφ_ne _)]; congr 1
      have hne : (↑(n * N : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hnN_ne
      have hmul : (↑(n * N : ℕ) : ℂ) * log (φ (1 / ↑(n * N))) = c := by exact_mod_cast hlog_nN
      rw [mul_comm] at hmul
      exact (div_eq_of_eq_mul hne hmul.symm).symm
    -- φ(1/n) = φ(N/(nN)) = φ(1/(nN))^N
    have hNnN : (N : ℝ≥0) * (1 / ((n * N : ℕ) : ℝ≥0)) = 1 / (n : ℝ≥0) := by
      rw [Nat.cast_mul, one_div, one_div, mul_inv, mul_comm (n : ℝ≥0)⁻¹,
          ← mul_assoc, mul_inv_cancel₀ hN_ne, one_mul]
    rw [← hNnN, hφ_pow N, hφ_nN, ← exp_nat_mul]; congr 1
    push_cast [Nat.cast_mul]
    field_simp [show (n : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (by omega),
                show (N : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (by omega)]
  -- Rational formula: φ(k/n) = exp(c * k/n)
  have hrat_exp : ∀ (k n : ℕ), 0 < n →
      φ ((k : ℝ≥0) / (n : ℝ≥0)) = exp (c * ↑((k : ℝ) / (n : ℝ))) := by
    intro k n hn
    rw [hφ_rat k n, hφ_inv_exp n hn, ← exp_nat_mul]; congr 1
    push_cast
    field_simp [show (n : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (by omega)]
  -- ═══════════════════════════════════════════════════════
  -- PHASE 5: Extension to all t via right-continuity + density
  -- ═══════════════════════════════════════════════════════
  have hext : ∀ t : ℝ≥0, φ t = exp (c * ↑(t : ℝ)) := by
    intro t
    -- Work with ℝ-valued ceiling sequence f(m) = ⌈t*(m+1)⌉₊/(m+1)
    have hf_ge : ∀ m : ℕ, (t : ℝ) ≤ ↑⌈(t : ℝ) * ↑(m + 1)⌉₊ / ↑(m + 1) :=
      fun m => (le_div_iff₀ (by positivity : (0 : ℝ) < ↑(m + 1))).mpr (Nat.le_ceil _)
    have hf_le : ∀ m : ℕ, (↑⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ) / ↑(m + 1) ≤ (t : ℝ) + 1 / ↑(m + 1) :=
      fun m => by
        have hm_pos : (0 : ℝ) < ↑(m + 1) := by positivity
        calc (↑⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ) / ↑(m + 1)
            ≤ ((t : ℝ) * ↑(m + 1) + 1) / ↑(m + 1) :=
              div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hm_pos.le
          _ = (t : ℝ) + 1 / ↑(m + 1) := by
              rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hm_pos)]
    have hf_tendsto : Tendsto (fun m : ℕ => (↑⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ) / ↑(m + 1))
        atTop (𝓝 (t : ℝ)) := by
      have h_upper : Tendsto (fun m : ℕ => (t : ℝ) + 1 / ↑(m + 1)) atTop (𝓝 (t : ℝ)) := by
        have h0 : Tendsto (fun m : ℕ => (1 : ℝ) / (↑(m + 1) : ℝ)) atTop (𝓝 0) :=
          (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
            ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
        have := (tendsto_const_nhds (x := (t : ℝ))).add h0
        rwa [add_zero] at this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper
        hf_ge hf_le
    -- Lift to NNReal for right-continuity argument
    -- g m = ⌈t*(m+1)⌉₊/(m+1) as NNReal
    let g : ℕ → ℝ≥0 := fun m =>
      (⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
    have hg_coe : ∀ m, (g m : ℝ) = ↑⌈(t : ℝ) * ↑(m + 1)⌉₊ / ↑(m + 1) := fun m => by
      show NNReal.toReal _ = _; rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    have hg_ge : ∀ m, t ≤ g m := fun m =>
      NNReal.coe_le_coe.mp (by rw [hg_coe]; exact hf_ge m)
    have hg_real : Tendsto (fun m => (g m : ℝ)) atTop (𝓝 (t : ℝ)) :=
      hf_tendsto.congr (fun m => (hg_coe m).symm)
    -- g m → t in 𝓝[≥] t
    have hg_nhds : Tendsto g atTop (𝓝[≥] t) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨NNReal.tendsto_coe.mp hg_real, Eventually.of_forall fun m => hg_ge m⟩
    -- φ(g m) → φ(t) via right-continuity
    have hφ_lim : Tendsto (fun m => φ (g m)) atTop (𝓝 (φ t)) :=
      (lk_charFun_rightCts h hX t ξ).comp hg_nhds
    -- φ(g m) = exp(c * g m) by hrat_exp
    have hg_eq : ∀ m, φ (g m) = exp (c * ↑(g m : ℝ)) := fun m => by
      rw [hg_coe]; exact hrat_exp _ _ (by omega)
    -- exp(c * g m) → exp(c * t) via continuity
    have hexp_lim : Tendsto (fun m => exp (c * ↑(g m : ℝ))) atTop (𝓝 (exp (c * ↑(t : ℝ)))) :=
      (continuous_exp.tendsto _).comp
        (tendsto_const_nhds.mul ((continuous_ofReal.tendsto _).comp hg_real))
    -- Conclude by uniqueness of limits
    rw [show (fun m => φ (g m)) = (fun m => exp (c * ↑(g m : ℝ))) from funext hg_eq] at hφ_lim
    exact tendsto_nhds_unique hφ_lim hexp_lim
  -- ═══════════════════════════════════════════════════════
  -- PHASE 6: charExponent = c
  -- ═══════════════════════════════════════════════════════
  have hce : h.charExponent ξ = c := by
    simp only [charExponent]
    apply Filter.Tendsto.limUnder_eq
    -- For small t > 0, log(φ t)/t = log(exp(ct))/t = ct/t = c
    set δ₂ : ℝ≥0 := ⟨Real.pi / (|c.im| + 1), by positivity⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ≥0) < δ₂ from by
        change (0 : ℝ) < Real.pi / (|c.im| + 1); positivity))]
      with t (ht_pos : 0 < t) (ht_small : t < δ₂)
    symm; change log (φ t) / ↑↑t = c
    have ht_real_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
    rw [hext t]
    -- Need: log(exp(c * ↑t)) = c * ↑t, then divide by ↑t
    have him : (c * ↑(t : ℝ)).im = c.im * (t : ℝ) := by
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    have him_bound : |c.im * (t : ℝ)| < Real.pi := by
      by_cases hc : c.im = 0
      · simp [hc, Real.pi_pos]
      · have ht_lt : (t : ℝ) < Real.pi / (|c.im| + 1) := by exact_mod_cast ht_small
        calc |c.im * (t : ℝ)|
            = |c.im| * (t : ℝ) := by rw [abs_mul, abs_of_nonneg ht_real_pos.le]
          _ < |c.im| * (Real.pi / (|c.im| + 1)) :=
              mul_lt_mul_of_pos_left ht_lt (abs_pos.mpr hc)
          _ ≤ Real.pi := by
              have hne : |c.im| + 1 ≠ 0 := by linarith [abs_nonneg c.im]
              calc |c.im| * (Real.pi / (|c.im| + 1))
                  ≤ (|c.im| + 1) * (Real.pi / (|c.im| + 1)) :=
                    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
                      (div_nonneg Real.pi_pos.le (by linarith [abs_nonneg c.im]))
                _ = Real.pi := mul_div_cancel₀ Real.pi hne
    rw [log_exp (by rw [him]; linarith [(abs_lt.mp him_bound).1])
                (by rw [him]; linarith [(abs_lt.mp him_bound).2]),
        mul_div_cancel_right₀ c (by exact_mod_cast ne_of_gt ht_real_pos : (↑(t:ℝ) : ℂ) ≠ 0)]
  -- Conclusion
  show φ t = exp (↑(t : ℝ) * h.charExponent ξ)
  rw [hce, mul_comm, hext t]

end IsLevyProcess

end ProbabilityTheory
