/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Levy.InfiniteDivisible
import LeanLevy.Levy.LevyMeasure
import LeanLevy.Levy.CompensatedIntegral
import LeanLevy.Levy.LevyKhintchine
import LeanLevy.Probability.Characteristic
import LeanLevy.Levy.CharacteristicExponent
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible

/-!
# Lévy-Khintchine Proof Components

Sub-lemmas for the Lévy-Khintchine representation theorem, decomposed into
four independently provable steps.

## Sub-lemma 1: Non-vanishing
The characteristic function of an infinitely divisible distribution never vanishes.

## Sub-lemma 2: Continuous logarithm
An infinitely divisible characteristic function has a unique continuous logarithm.

## Sub-lemma 3: Conditional negative definiteness
The logarithm of an infinitely divisible char function is conditionally negative definite.

## Sub-lemma 4: Integral representation
A continuous, conditionally negative definite function with ψ(0)=0 has the
Lévy-Khintchine integral representation.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-! ## Sub-lemma 1: Non-vanishing -/

section NonVanishing

/-! ### PSD norm bound

The key technical ingredient: if a probability measure `ν` on `ℝ` has `charFun ν ξ₀ = 0`,
then `‖charFun ν (ξ₀ / 2)‖ ≤ 3/4`.

This follows from positive semi-definiteness of the characteristic function with
phase-adapted weights. -/

/-- If `charFun ν ξ₀ = 0` for a probability measure `ν`, then `‖charFun ν (ξ₀ / 2)‖ ≤ 3/4`.

**Proof:** Apply positive semi-definiteness of the characteristic function with
weights `(conj u, -2, u)` and frequencies `(0, ξ₀/2, ξ₀)` where `u = z/‖z‖`
and `z = charFun ν (ξ₀/2)`. The PSD quadratic form evaluates to
`2 + 4 - 8‖z‖ ≥ 0`, giving `‖z‖ ≤ 3/4`. -/
theorem norm_charFun_half_le_of_charFun_eq_zero
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {ξ₀ : ℝ} (hξ : charFun ν ξ₀ = 0) :
    ‖charFun ν (ξ₀ / 2)‖ ≤ 3 / 4 := by
  set z := charFun ν (ξ₀ / 2) with hz_def
  by_cases hz : z = 0
  · simp [hz]; positivity
  · have hr_pos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hr_ne : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
    set u := z / (↑‖z‖ : ℂ) with hu_def
    -- Wrap ν as ProbabilityMeasure to use PSD
    set P : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
    -- Key charFun values
    have hφ0 : charFun ν 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
    -- PSD applied with n=3, ξ = (0, ξ₀/2, ξ₀), c = (conj u, -2, u)
    have hpsd := MeasureTheory.ProbabilityMeasure.characteristicFun_positiveSemiDefinite P
      (![0, ξ₀ / 2, ξ₀]) (![(starRingEnd ℂ) u, -2, u])
    -- Unfold characteristicFun to charFun, replace ↑P with ν
    simp only [MeasureTheory.ProbabilityMeasure.characteristicFun_def,
      show (↑P : Measure ℝ) = ν from rfl] at hpsd
    -- Expand the Fin 3 double sum and evaluate all matrix lookups
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hpsd
    -- Simplify frequency differences to canonical forms
    rw [show (0 : ℝ) - ξ₀ / 2 = -(ξ₀ / 2) from by ring,
        show (0 : ℝ) - ξ₀ = -ξ₀ from by ring,
        show ξ₀ / 2 - ξ₀ = -(ξ₀ / 2) from by ring,
        show ξ₀ - ξ₀ / 2 = ξ₀ / 2 from by ring] at hpsd
    -- Substitute charFun values and simplify
    simp only [_root_.sub_self, _root_.sub_zero, charFun_neg, hξ, hφ0, map_zero,
      starRingEnd_self_apply, map_neg, map_ofNat, mul_zero, add_zero, mul_one] at hpsd
    -- hpsd is now: 0 ≤ (u*conj u + u*(-2)*conj z + ... + conj u*u).re
    -- with all charFun terms being either z or conj z.
    -- Rewrite the complex expression inside .re using algebraic identities.
    -- Key identities for our specific u = z/‖z‖:
    have hu_norm : ‖u‖ = 1 := by
      rw [hu_def, norm_div, Complex.norm_real, Real.norm_of_nonneg hr_pos.le,
        div_self (ne_of_gt hr_pos)]
    -- u * conj u = 1
    have huu : u * (starRingEnd ℂ) u = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu_norm, one_pow, Complex.ofReal_one]
    -- conj u * u = 1
    have huu' : (starRingEnd ℂ) u * u = 1 := by rw [mul_comm, huu]
    -- Substitute these into hpsd
    simp only [huu, huu'] at hpsd
    -- hpsd should now be: 0 ≤ (1 + (-2)*(u*conj z) + (-2)*(conj u*z) + 4 + (-2)*(u*conj z) + (-2)*(conj u*z) + 1).re
    -- which equals 0 ≤ 6 - 4*Re(u*conj z) - 4*Re(conj u*z)
    -- Now use Re(u*conj z) = ‖z‖ and Re(conj u*z) = ‖z‖
    have hre1 : (u * (starRingEnd ℂ) z).re = ‖z‖ := by
      rw [hu_def, div_mul_eq_mul_div, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [show (↑(‖z‖ ^ 2) : ℂ) / ↑‖z‖ = ↑‖z‖ from by
        rw [Complex.ofReal_pow, sq, mul_div_cancel_left₀ _ hr_ne]]
      exact Complex.ofReal_re ‖z‖
    have hre2 : ((starRingEnd ℂ) u * z).re = ‖z‖ := by
      have : ((starRingEnd ℂ) u * z).re = (u * (starRingEnd ℂ) z).re := by
        rw [show ((starRingEnd ℂ) u * z).re = ((starRingEnd ℂ) (u * (starRingEnd ℂ) z)).re from by
          simp [map_mul]]
        exact Complex.conj_re _
      rw [this, hre1]
    -- Replace charFun ν (ξ₀ / 2) with z in hpsd (they are definitionally equal)
    change 0 ≤ _ at hpsd
    simp only [show charFun ν (ξ₀ / 2) = z from rfl] at hpsd
    -- Now distribute .re over the additions and simplify
    simp only [Complex.add_re] at hpsd
    -- All multiplication terms have the form: (a * b * c).re or (a * b).re
    -- where a, b, c are from {u, conj u, z, conj z, -2, 0, 1}
    -- Rewrite to use hre1, hre2 for the key Re values
    -- First, for real scalar (-2): (-2 * X).re = -2 * X.re
    have hscalar : ∀ (w : ℂ), ((-2 : ℂ) * w).re = -2 * w.re := by
      intro w; simp [Complex.mul_re]
    -- Rewrite all triple products to pull -2 out
    -- (-2) * conj_u * z = (-2) * (conj_u * z)
    -- (-2) * u * conj_z = (-2) * (u * conj_z)
    -- u * (-2) * conj_z = (-2) * (u * conj_z)
    -- conj_u * (-2) * z = (-2) * (conj_u * z)
    rw [show (-2 : ℂ) * (starRingEnd ℂ) u * z = (-2) * ((starRingEnd ℂ) u * z) from by ring,
        show (-2 : ℂ) * u * (starRingEnd ℂ) z = (-2) * (u * (starRingEnd ℂ) z) from by ring,
        show u * (-2 : ℂ) * (starRingEnd ℂ) z = (-2) * (u * (starRingEnd ℂ) z) from by ring,
        show (starRingEnd ℂ) u * (-2 : ℂ) * z = (-2) * ((starRingEnd ℂ) u * z) from by ring]
      at hpsd
    simp only [hscalar, hre1, hre2, Complex.one_re, Complex.zero_re,
      Complex.neg_re, Complex.re_ofNat] at hpsd
    -- hpsd: 0 ≤ 1 + -2 * ‖z‖ + (-2 * ‖z‖ + -2 * -2 + -2 * ‖z‖) + (0 + -2 * ‖z‖ + 1)
    linarith

/-- If `μ` is infinitely divisible and `charFun μ ξ₀ = 0`, then `charFun μ (ξ₀ / 2) = 0`.

**Proof:** For each `n ≥ 1`, the `n`-th root measure `ν_n` satisfies `charFun ν_n ξ₀ = 0`,
hence `‖charFun ν_n (ξ₀/2)‖ ≤ 3/4` by `norm_charFun_half_le_of_charFun_eq_zero`.
Then `‖charFun μ (ξ₀/2)‖ = ‖charFun ν_n (ξ₀/2)‖^n ≤ (3/4)^n → 0`. -/
private theorem charFun_half_eq_zero_of_charFun_eq_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ)
    {ξ₀ : ℝ} (hξ : charFun μ ξ₀ = 0) :
    charFun μ (ξ₀ / 2) = 0 := by
  rw [← norm_eq_zero]
  suffices hle : ∀ n : ℕ, 0 < n → ‖charFun μ (ξ₀ / 2)‖ ≤ (3 / 4 : ℝ) ^ n by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hc; push_neg at hc
    have htend : Tendsto (fun n : ℕ => (3 / 4 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have hev := htend.eventually (Iio_mem_nhds hc)
    obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
    have h1 := hle (N + 1) (Nat.succ_pos N)
    have h2 := hN (N + 1) (by omega)
    linarith
  intro n hn
  obtain ⟨ν, hν_prob, hμ_eq⟩ := h n hn
  have hpow : ∀ ξ, charFun μ ξ = (charFun ν ξ) ^ n := by
    intro ξ; rw [hμ_eq, charFun_iteratedConv]
  have hν_zero : charFun ν ξ₀ = 0 := by
    have h1 := hpow ξ₀; rw [hξ] at h1
    exact (pow_eq_zero_iff (by omega : n ≠ 0)).mp h1.symm
  have hν_half := norm_charFun_half_le_of_charFun_eq_zero hν_zero
  calc ‖charFun μ (ξ₀ / 2)‖
      = ‖charFun ν (ξ₀ / 2)‖ ^ n := by rw [hpow, norm_pow]
    _ ≤ (3 / 4 : ℝ) ^ n := pow_le_pow_left₀ (norm_nonneg _) hν_half n

/-- The characteristic function of an infinitely divisible probability measure never vanishes.

**Proof:** Suppose `charFun μ ξ₀ = 0` for some `ξ₀`. By repeated halving,
`charFun μ (ξ₀ / 2^k) = 0` for all `k`. But `ξ₀ / 2^k → 0` and `charFun μ` is continuous
with `charFun μ 0 = 1`, contradiction. -/
theorem IsInfinitelyDivisible.charFun_ne_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) (ξ : ℝ) :
    charFun μ ξ ≠ 0 := by
  intro habs
  have hzero : ∀ k : ℕ, charFun μ (ξ / 2 ^ k) = 0 := by
    intro k; induction k with
    | zero => simpa using habs
    | succ k ih =>
      rw [show ξ / 2 ^ (k + 1) = ξ / 2 ^ k / 2 from by rw [div_div, ← pow_succ]]
      exact charFun_half_eq_zero_of_charFun_eq_zero h ih
  have htend : Tendsto (fun k : ℕ => ξ / (2 : ℝ) ^ k) atTop (nhds 0) := by
    have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
    exact tendsto_const_nhds.div_atTop h2
  have hcont : Continuous (charFun μ) := MeasureTheory.continuous_charFun
  have hφ0 : charFun μ 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
  have hlim : Tendsto (fun k => charFun μ (ξ / 2 ^ k)) atTop (nhds 1) := by
    rw [← hφ0]; exact (hcont.tendsto 0).comp htend
  have hlim0 : Tendsto (fun k => charFun μ (ξ / 2 ^ k)) atTop (nhds 0) := by
    rw [show (fun k => charFun μ (ξ / 2 ^ k)) = fun _ => (0 : ℂ) from funext hzero]
    exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hlim0 hlim).symm

end NonVanishing

/-! ## Sub-lemma 2: Continuous logarithm -/

/-- An infinitely divisible probability measure has a continuous logarithm of its
characteristic function: there exists `ψ : ℝ → ℂ` continuous with `ψ 0 = 0` and
`charFun μ ξ = exp(ψ ξ)` for all `ξ`. -/
theorem IsInfinitelyDivisible.exists_continuous_log
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ ψ 0 = 0 ∧ ∀ ξ, charFun μ ξ = exp (ψ ξ) := by
  -- The characteristic function is continuous and never vanishes
  have hcont : Continuous (charFun μ) := MeasureTheory.continuous_charFun
  have hne : ∀ ξ, charFun μ ξ ≠ 0 := h.charFun_ne_zero
  -- charFun μ 0 = 1
  have hφ0 : charFun μ 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
  -- Build the ContinuousMap f : C(ℝ, ℂ) for the characteristic function
  set f : C(ℝ, ℂ) := ⟨charFun μ, hcont⟩
  -- exp 0 = 1 = charFun μ 0 = f 0
  have he : Complex.exp (0 : ℂ) = f (0 : ℝ) := by simp [f, hφ0]
  -- charFun μ maps into ℂ \ {0}
  have hs : ∀ ξ : ℝ, f ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ => Set.mem_compl_singleton_iff.mpr (hne ξ)
  -- Apply the lifting theorem for covering maps:
  -- exp : ℂ → ℂ is a covering map on {0}ᶜ, ℝ is simply connected and locally path-connected
  obtain ⟨F, ⟨hF0, hFexp⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
  -- F is our continuous logarithm
  exact ⟨F, F.continuous, hF0, fun ξ => by
    have := congr_fun hFexp ξ
    simp [Function.comp] at this
    exact this.symm⟩

/-! ## Sub-lemma 3: Conditional negative definiteness -/

/-- A function `ψ : ℝ → ℂ` is **conditionally negative definite** if for all finite
sequences `ξ₁, ..., ξₙ` and `c₁, ..., cₙ ∈ ℂ` with `∑ cₖ = 0`,
the real part of `∑ᵢ ∑ⱼ c̄ᵢ cⱼ ψ(ξᵢ - ξⱼ)` is non-negative.

This follows the convention of Applebaum (Def 3.6.1) and Jacob: a continuous function
`ψ` with `ψ(0) = 0` is CND iff `exp(-tψ)` is positive definite for all `t > 0`. -/
def IsConditionallyNegativeDefinite (ψ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (ξ : Fin n → ℝ) (c : Fin n → ℂ),
    ∑ i, c i = 0 →
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (ξ i - ξ j)).re

/-- For a probability measure, `charFun ν 0 = 1`. -/
private theorem charFun_zero_eq_one {ν : Measure ℝ} [IsProbabilityMeasure ν] :
    charFun ν 0 = 1 := by
  simp [charFun_zero, Measure.real, measure_univ]

/-- When `∑ c = 0`, the constant term `∑ᵢ ∑ⱼ c̄ᵢ cⱼ` equals zero. -/
private theorem double_sum_conj_mul_eq_zero {n : ℕ} {c : Fin n → ℂ} (hc : ∑ i, c i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j = 0 := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp [hc]

/-- PSD of characteristic function: the Hermitian form with charFun values is non-negative.
This wraps the ProbabilityMeasure-level statement for bare Measures. -/
private theorem charFun_psd {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * charFun ν (ξ i - ξ j)).re := by
  exact MeasureTheory.ProbabilityMeasure.characteristicFun_positiveSemiDefinite
    (⟨ν, inferInstance⟩ : ProbabilityMeasure ℝ) ξ c

/-- When `∑ c = 0`, PSD implies the "1 minus charFun" form is non-positive. -/
private theorem one_sub_charFun_form_nonpos {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) (hc : ∑ i, c i = 0) :
    (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (1 - charFun ν (ξ i - ξ j))).re ≤ 0 := by
  have hpsd := charFun_psd ξ c (ν := ν)
  have hzero := double_sum_conj_mul_eq_zero hc
  have : ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (1 - charFun ν (ξ i - ξ j)) =
    -(∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * charFun ν (ξ i - ξ j)) := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
    simp [hzero]
  rw [this, Complex.neg_re]
  linarith

/-- If `(charFun ν)^m = exp(ψ)` where `ψ` is a continuous log with `ψ(0) = 0`,
then `charFun ν = exp(ψ/m)`.

This uses the uniqueness of lifts through the exponential covering map:
both `charFun ν` and `exp(ψ/m)` are continuous, map `0 ↦ 1`, and satisfy
`f^m = exp(ψ)`. -/
private theorem charFun_eq_exp_div {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    {m : ℕ} (hm : 0 < m) (hpow : ∀ ξ, (charFun ν ξ) ^ m = exp (ψ ξ)) :
    ∀ ξ, charFun ν ξ = exp (ψ ξ / ↑m) := by
  -- Step 1: charFun ν is continuous and never zero (from hpow + exp_ne_zero)
  have hcont : Continuous (charFun ν) := MeasureTheory.continuous_charFun
  have hne : ∀ ξ, charFun ν ξ ≠ 0 := by
    intro ξ habs
    have : (charFun ν ξ) ^ m = 0 := by rw [habs, zero_pow (by omega)]
    rw [hpow] at this
    exact exp_ne_zero _ this
  -- Step 2: Lift charFun ν through exp to get logν : C(ℝ, ℂ) with logν(0) = 0
  have hφ0 : charFun ν 0 = 1 := charFun_zero_eq_one
  set fν : C(ℝ, ℂ) := ⟨charFun ν, hcont⟩
  have heν : Complex.exp (0 : ℂ) = fν (0 : ℝ) := by simp [fν, hφ0]
  have hsν : ∀ ξ : ℝ, fν ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ =>
    Set.mem_compl_singleton_iff.mpr (hne ξ)
  obtain ⟨logν, ⟨hlogν0, hlogν_exp⟩, hlogν_unique⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts fν heν hsν
  -- logν 0 = 0 and exp ∘ logν = charFun ν
  -- Step 3: Build the base map g := exp ∘ ψ as a ContinuousMap
  set g : C(ℝ, ℂ) := ⟨fun ξ => exp (ψ ξ), hψ_cont.exp⟩
  -- g maps into ℂ \ {0}
  have hsg : ∀ ξ : ℝ, g ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ =>
    Set.mem_compl_singleton_iff.mpr (exp_ne_zero _)
  have heg : Complex.exp (0 : ℂ) = g (0 : ℝ) := by simp [g, hψ_zero]
  -- Step 4: ψ is a lift of g through exp
  set ψ_cm : C(ℝ, ℂ) := ⟨ψ, hψ_cont⟩
  have hψ_lift_val : ψ_cm (0 : ℝ) = 0 := hψ_zero
  have hψ_lift_comp : Complex.exp ∘ ψ_cm = g := by
    ext ξ; simp [ψ_cm, g]
  -- Step 5: m * logν is also a lift of g through exp
  set mlogν : C(ℝ, ℂ) := ⟨fun ξ => (↑m : ℂ) * logν ξ,
    continuous_const.mul logν.continuous⟩
  have hmlogν_val : mlogν (0 : ℝ) = 0 := by simp [mlogν, hlogν0]
  have hmlogν_comp : Complex.exp ∘ mlogν = g := by
    ext ξ
    simp only [Function.comp_apply, ContinuousMap.coe_mk, g]
    -- exp(m * logν(ξ)) = (exp(logν(ξ)))^m = (charFun ν ξ)^m = exp(ψ ξ)
    rw [Complex.exp_nat_mul]
    have hexp_logν : Complex.exp (logν ξ) = charFun ν ξ := by
      have := congr_fun hlogν_exp ξ
      simp [Function.comp_apply] at this
      exact this
    rw [hexp_logν, hpow]
  -- Step 6: By uniqueness of lifts, ψ = m * logν
  obtain ⟨_, ⟨_, _⟩, huniq⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts g heg hsg
  have hψ_eq_mlogν : ψ_cm = mlogν := by
    have hψ_uniq := huniq ψ_cm ⟨hψ_lift_val, hψ_lift_comp⟩
    have hmlogν_uniq := huniq mlogν ⟨hmlogν_val, hmlogν_comp⟩
    rw [hψ_uniq, hmlogν_uniq]
  -- Step 7: Therefore charFun ν = exp(logν) = exp(ψ/m)
  intro ξ
  have hexp_logν : Complex.exp (logν ξ) = charFun ν ξ := by
    have := congr_fun hlogν_exp ξ
    simp [Function.comp_apply] at this
    exact this
  rw [← hexp_logν]
  congr 1
  -- logν ξ = ψ ξ / m, from ψ ξ = m * logν ξ
  have hψ_eq : ψ ξ = (↑m : ℂ) * logν ξ := by
    have := congr_fun (congrArg DFunLike.coe hψ_eq_mlogν) ξ
    simp [ψ_cm, mlogν] at this
    exact this
  rw [hψ_eq]
  rw [mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.mpr (by omega)

/-- The complex limit `m * (1 - exp(z / m)) → -z` as `m → ∞`. -/
private theorem tendsto_mul_one_sub_exp_div (z : ℂ) :
    Tendsto (fun m : ℕ => (↑m : ℂ) * (1 - exp (z / ↑m))) atTop (nhds (-z)) := by
  -- m * (1 - exp(z/m)) → -z follows from (exp w - 1)/w → 1 as w → 0
  sorry

/-- The continuous logarithm of an infinitely divisible characteristic function is
conditionally negative definite. -/
theorem IsInfinitelyDivisible.isConditionallyNegativeDefinite_log
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ)
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_exp : ∀ ξ, charFun μ ξ = exp (ψ ξ)) :
    IsConditionallyNegativeDefinite ψ := by
  intro n ξ c hc
  -- For each m ≥ 1, PSD of the m-th root measure gives:
  --   (∑ᵢ ∑ⱼ c̄ᵢ cⱼ · m(1 - exp(ψ(ξᵢ-ξⱼ)/m))).re ≤ 0
  -- As m → ∞, m(1 - exp(z/m)) → -z, so the limit gives CND.

  -- The bound for each m
  have hbound : ∀ m : ℕ, 0 < m →
      (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j *
          ((↑m : ℂ) * (1 - exp (ψ (ξ i - ξ j) / ↑m)))).re ≤ 0 := by
    intro m hm
    obtain ⟨ν, hνP, hμ_eq⟩ := h m hm
    haveI := hνP
    have hpow : ∀ ξ', (charFun ν ξ') ^ m = exp (ψ ξ') := by
      intro ξ'; rw [← hψ_exp, hμ_eq, charFun_iteratedConv]
    have hν_exp := charFun_eq_exp_div hψ_cont hψ_zero hm hpow
    have hsub : ∀ i j : Fin n,
        1 - charFun ν (ξ i - ξ j) = 1 - exp (ψ (ξ i - ξ j) / ↑m) := by
      intro i j; rw [hν_exp]
    have hnonpos := one_sub_charFun_form_nonpos ξ c hc (ν := ν)
    simp_rw [hsub] at hnonpos
    -- Factor out m from each summand
    have hfactor : ∀ i j : Fin n,
        starRingEnd ℂ (c i) * c j * ((↑m : ℂ) * (1 - exp (ψ (ξ i - ξ j) / ↑m))) =
        (↑m : ℂ) * (starRingEnd ℂ (c i) * c j * (1 - exp (ψ (ξ i - ξ j) / ↑m))) := by
      intro i j; ring
    simp_rw [hfactor, ← Finset.mul_sum]
    -- (↑m : ℂ) * S has .re = m * S.re (since m is real, i.e., (↑m).im = 0)
    have hm_re : ((↑m : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * (1 - exp (ψ (ξ i - ξ j) / ↑m)))).re =
      ↑m * (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * (1 - exp (ψ (ξ i - ξ j) / ↑m))).re := by
      rw [Complex.mul_re]
      simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    rw [hm_re]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg' m) hnonpos

  -- The limit as m → ∞
  have hlim : Tendsto
      (fun m : ℕ => (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j *
          ((↑m : ℂ) * (1 - exp (ψ (ξ i - ξ j) / ↑m)))).re)
      atTop
      (nhds (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * (-ψ (ξ i - ξ j))).re) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    apply tendsto_finset_sum
    intro i _
    apply tendsto_finset_sum
    intro j _
    apply Filter.Tendsto.const_mul
    exact tendsto_mul_one_sub_exp_div (ψ (ξ i - ξ j))

  -- The limit of non-positive values is non-positive
  have hle : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (-ψ (ξ i - ξ j))).re ≤ 0 :=
    le_of_tendsto hlim (Eventually.of_forall fun m => by
      by_cases hm : m = 0
      · simp [hm]
      · exact hbound m (Nat.pos_of_ne_zero hm))

  -- ∑ c̄ᵢ cⱼ (-ψ) = -(∑ c̄ᵢ cⱼ ψ), so -(∑ ... ψ).re ≤ 0 ⇒ (∑ ... ψ).re ≥ 0
  have hneg : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (-ψ (ξ i - ξ j))).re =
    -(∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * ψ (ξ i - ξ j)).re := by
    simp_rw [mul_neg, Finset.sum_neg_distrib, Complex.neg_re]
  linarith [hneg]

/-! ## Sub-lemma 4: Integral representation (deepest) -/

/-- A continuous, conditionally negative definite function `ψ : ℝ → ℂ` with `ψ(0) = 0`
has the Lévy-Khintchine integral representation.

This is the deepest sub-lemma, requiring Bochner's theorem (not yet in mathlib). -/
theorem levyKhintchine_of_cnd
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cnd : IsConditionallyNegativeDefinite ψ) :
    ∃ T : LevyKhintchineTriple, ∀ ξ : ℝ,
      ψ ξ = ↑T.drift * ↑ξ * I
        - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
        + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure := by
  sorry

/-! ## Assembly: Lévy-Khintchine representation -/

/-- **Lévy-Khintchine representation theorem**: every infinitely divisible probability measure
on `ℝ` has a characteristic function of the form
`exp(ibξ − σ²ξ²/2 + ∫ f(ξ,x) dν(x))` where `f` is the compensated integrand
`exp(ixξ) − 1 − ixξ·1_{|x|<1}`.

**Proof via sub-lemmas:**
1. `charFun_ne_zero` — characteristic function never vanishes (Sub-lemma 1)
2. `exists_continuous_log` — continuous logarithm ψ with charFun = exp(ψ) (Sub-lemma 2)
3. `isConditionallyNegativeDefinite_log` — ψ is CND (Sub-lemma 3)
4. `levyKhintchine_of_cnd` — CND function has the integral representation (Sub-lemma 4) -/
theorem levyKhintchine_representation
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ∃ T : LevyKhintchineTriple, ∀ ξ : ℝ,
      charFun μ ξ = exp (
        ↑T.drift * ↑ξ * I
        - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
        + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure) := by
  -- Sub-lemma 2: continuous logarithm
  obtain ⟨ψ, hψ_cont, hψ_zero, hψ_exp⟩ := h.exists_continuous_log
  -- Sub-lemma 3: ψ is conditionally negative definite
  have hψ_cnd := h.isConditionallyNegativeDefinite_log hψ_cont hψ_zero hψ_exp
  -- Sub-lemma 4: CND function has LK integral representation
  obtain ⟨T, hT⟩ := levyKhintchine_of_cnd hψ_cont hψ_zero hψ_cnd
  -- Combine: charFun μ ξ = exp(ψ ξ) = exp(ibξ - σ²ξ²/2 + ∫ f dν)
  exact ⟨T, fun ξ => by rw [hψ_exp ξ, hT ξ]⟩

end ProbabilityTheory
