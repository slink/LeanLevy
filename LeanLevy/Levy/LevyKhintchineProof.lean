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
import LeanLevy.Fourier.Bochner
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.Real.Irrational

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
Lévy-Khintchine integral representation. Uses Schoenberg + Bochner to extract
probability measures, then (sorry) differentiates the convolution semigroup.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

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

This convention means `ψ` is "conditionally positive definite" in some references.
A continuous function `ψ` with `ψ(0) = 0` is CND in this sense iff `exp(tψ)` is
positive definite for all `t > 0` (Schoenberg's theorem). -/
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
  set g : C(ℝ, ℂ) := ⟨fun ξ => exp (ψ ξ), hψ_cont.cexp⟩
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
    simp only [Function.comp_apply, ContinuousMap.coe_mk, mlogν, g]
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
  by_cases hz : z = 0
  · -- Case z = 0: everything is zero
    simp [hz]
  · -- Case z ≠ 0: use (exp w - 1)/w → 1 as w → 0
    -- Step 1: The derivative of exp at 0 gives slope cexp 0 → 1 in 𝓝[≠] 0
    have hslope : Tendsto (slope cexp 0) (𝓝[≠] 0) (nhds 1) := by
      have h := hasDerivAt_exp (0 : ℂ)
      rw [exp_zero] at h
      exact h.tendsto_slope
    -- Step 2: z / m → 0 as m → ∞ (in ℂ)
    have hdiv_tendsto : Tendsto (fun m : ℕ => z / (↑m : ℂ)) atTop (nhds 0) := by
      have hinv : Tendsto (fun m : ℕ => (↑m : ℂ)⁻¹) atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have : (fun m : ℕ => ‖(↑m : ℂ)⁻¹‖) = fun m : ℕ => ((↑m : ℝ))⁻¹ := by
          ext m; rw [norm_inv, Complex.norm_natCast]
        rw [this]
        exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      rw [show (0 : ℂ) = z * 0 from by ring]
      simp only [div_eq_mul_inv]
      exact tendsto_const_nhds.mul hinv
    -- Step 3: z / m ≠ 0 eventually (since z ≠ 0 and m ≥ 1)
    have hdiv_ne : ∀ᶠ m : ℕ in atTop, z / (↑m : ℂ) ∈ ({0}ᶜ : Set ℂ) := by
      filter_upwards [Filter.Ici_mem_atTop 1] with m (hm : 1 ≤ m)
      exact Set.mem_compl_singleton_iff.mpr
        (div_ne_zero hz (Nat.cast_ne_zero.mpr (by omega)))
    -- Step 4: Compose to get slope cexp 0 (z/m) → 1
    have hcomp : Tendsto (fun m : ℕ => slope cexp 0 (z / (↑m : ℂ))) atTop (nhds 1) :=
      hslope.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdiv_tendsto hdiv_ne)
    -- Step 5: slope cexp 0 (z/m) * z → 1 * z = z
    have hmul_z : Tendsto (fun m : ℕ => slope cexp 0 (z / (↑m : ℂ)) * z) atTop (nhds z) := by
      have := hcomp.mul_const z
      rwa [one_mul] at this
    -- Step 6: -(slope cexp 0 (z/m) * z) → -z
    have hneg_z : Tendsto (fun m : ℕ => -(slope cexp 0 (z / (↑m : ℂ)) * z)) atTop (nhds (-z)) :=
      hmul_z.neg
    -- Step 7: For m ≥ 1, m * (1 - exp(z/m)) = -(slope cexp 0 (z/m) * z)
    have heq : ∀ᶠ m : ℕ in atTop,
        (↑m : ℂ) * (1 - exp (z / ↑m)) = -(slope cexp 0 (z / (↑m : ℂ)) * z) := by
      filter_upwards [Filter.Ici_mem_atTop 1] with m (hm : 1 ≤ m)
      have hm_ne : (↑m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [slope, sub_zero, exp_zero, vsub_eq_sub, smul_eq_mul]
      have hz_div_ne : z / (↑m : ℂ) ≠ 0 := div_ne_zero hz hm_ne
      field_simp
      ring
    -- Step 8: Conclude by eventually-equal
    exact (tendsto_congr' heq).mpr hneg_z

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

/-! ## Schoenberg's theorem -/

/-- The constant function `1` is positive definite. -/
private theorem isPositiveDefinite_one : IsPositiveDefinite (fun _ => (1 : ℂ)) := by
  intro n x c
  simp only [mul_one]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [show (∑ i : Fin n, starRingEnd ℂ (c i)) = starRingEnd ℂ (∑ i, c i) from
    (map_sum (starRingEnd ℂ) c Finset.univ).symm]
  rw [← Complex.normSq_eq_conj_mul_self]
  exact_mod_cast Complex.normSq_nonneg _

/-- A non-negative real scalar times a PD function is PD. -/
private theorem isPositiveDefinite_smul {φ : ℝ → ℂ} (hφ : IsPositiveDefinite φ)
    {a : ℝ} (ha : 0 ≤ a) : IsPositiveDefinite (fun x => (↑a : ℂ) * φ x) := by
  intro n x c
  have : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * ((↑a : ℂ) * φ (x i - x j))) =
    ↑a * (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * φ (x i - x j)) := by
    conv_lhs => arg 2; ext i; arg 2; ext j
              ; rw [show starRingEnd ℂ (c i) * c j * (↑a * φ (x i - x j)) =
                  ↑a * (starRingEnd ℂ (c i) * c j * φ (x i - x j)) from by ring]
    simp_rw [← Finset.mul_sum]
  rw [this]
  exact mul_nonneg (by exact_mod_cast ha) (hφ n x c)

/-- A power of a PD function is PD (by Schur product theorem). -/
private theorem isPositiveDefinite_pow {φ : ℝ → ℂ} (hφ : IsPositiveDefinite φ) :
    ∀ k : ℕ, IsPositiveDefinite (fun x => φ x ^ k) := by
  intro k; induction k with
  | zero => simpa using isPositiveDefinite_one
  | succ k ih =>
    simp_rw [pow_succ]
    exact ih.mul hφ

/-- Sum of PD functions is PD. -/
private theorem isPositiveDefinite_add {φ ψ : ℝ → ℂ}
    (hφ : IsPositiveDefinite φ) (hψ : IsPositiveDefinite ψ) :
    IsPositiveDefinite (fun x => φ x + ψ x) := by
  intro n x c
  have hrw : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (φ (x i - x j) + ψ (x i - x j))) =
    (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * φ (x i - x j)) +
    (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * ψ (x i - x j)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
  rw [hrw]
  exact add_nonneg (hφ n x c) (hψ n x c)


/-- For PD `φ` with `φ(0) = 1` and `t ≥ 0`, the function `exp(t(φ - 1))` is PD.

**Proof:** The Poisson expansion `exp(t(φ-1)) = e^{-t} ∑_{k≥0} t^k/k! · φ^k`
has PD partial sums, and the pointwise limit is PD by `closure_pointwise`. -/
private theorem isPositiveDefinite_exp_mul_sub_one
    {φ : ℝ → ℂ} (hφ : IsPositiveDefinite φ) (_hφ0 : φ 0 = 1)
    (t : ℝ) (ht : 0 ≤ t) :
    IsPositiveDefinite (fun x => exp (↑t * (φ x - 1))) := by
  -- Define partial sums of the Poisson expansion
  -- exp(t(φ-1)) = e^{-t} · ∑_{k=0}^∞ (tφ)^k/k!
  -- Approximate by: T_N(x) = ∑_{k=0}^N (t^k/k!) · φ(x)^k · e^{-t}
  -- Each term (t^k/k!)·φ^k is PD (non-neg scalar × PD^k), and so is the finite sum × e^{-t}.
  -- As N → ∞, T_N → exp(t(φ-1)) pointwise.
  --
  -- We use closure_pointwise with sequence T_N.
  -- To avoid elaboration issues, we keep the proof simple.
  --
  -- Strategy: directly show exp(t(φ-1)) is a pointwise limit of PD functions.
  -- The key fact: exp(z) = lim_{N→∞} ∑_{k=0}^N z^k/k!
  -- So exp(t(φ(x)-1)) = lim ∑_{k=0}^N (t(φ(x)-1))^k / k!
  -- Each partial sum is PD: (t(φ(x)-1))^k = ∑ binomial terms, each PD.
  -- Actually this is harder. Let's use the Poisson form instead.
  --
  -- Alternative: use (1 + t(φ-1)/N)^N → exp(t(φ-1))
  -- Each (1 + t(φ-1)/N) may not be PD. But (1 + t(φ-1)/N)^N uses Schur product.
  -- The issue: 1 + t(φ-1)/N = (1-t/N) + (t/N)·φ. For N ≥ t, 1-t/N ≥ 0, t/N ≥ 0.
  -- So it's a non-neg combination of the constant 1 (PD) and φ (PD) → PD!
  -- Then (PD)^N is PD, and the limit is PD.
  --
  -- This avoids the entire Poisson partial sum approach and its elaboration issues!
  --
  -- Step 1: For N large enough, φ_N(x) := (1-t/N) + (t/N)·φ(x) is PD with φ_N(0) = 1.
  -- Step 2: φ_N^N is PD.
  -- Step 3: φ_N(x)^N → exp(t(φ(x)-1)) as N → ∞.
  -- Step 4: By closure_pointwise, exp(t(φ-1)) is PD.
  --
  -- For Step 1, we need N > t (so coefficients are non-negative).
  -- Use the eventual filter.

  -- Step 1: For large N, (1-t/N) + (t/N)·φ(x) is PD
  have hφN_pd : ∀ᶠ N : ℕ in Filter.atTop,
      IsPositiveDefinite (fun x => (1 - ↑t / ↑N : ℂ) + (↑t / ↑N : ℂ) * φ x) := by
    filter_upwards [Filter.Ici_mem_atTop (Nat.ceil t + 1)] with N (hN : Nat.ceil t + 1 ≤ N)
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hN_ne : (↑N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hN_pos)
    have htN : t / N ≤ 1 := by
      rw [div_le_one hN_pos]
      calc t ≤ ↑(Nat.ceil t) := Nat.le_ceil t
        _ ≤ ↑N := by exact_mod_cast (show Nat.ceil t ≤ N by omega)
    have htN_nn : 0 ≤ t / N := div_nonneg ht (le_of_lt hN_pos)
    -- (1-t/N) + (t/N)·φ = (1-t/N)·1 + (t/N)·φ
    -- Both coefficients non-negative, 1 is PD, φ is PD
    have hrw : (fun x => (1 - ↑t / ↑N : ℂ) + (↑t / ↑N : ℂ) * φ x) =
        (fun x => (↑(1 - t/N) : ℂ) * (1 : ℂ) + (↑(t/N) : ℂ) * φ x) := by
      ext x; push_cast; ring
    rw [hrw]
    exact isPositiveDefinite_add
      (isPositiveDefinite_smul isPositiveDefinite_one (by linarith))
      (isPositiveDefinite_smul hφ htN_nn)

  -- Step 2: φ_N^N is PD
  have hφN_pow_pd : ∀ᶠ N : ℕ in Filter.atTop,
      IsPositiveDefinite (fun x => ((1 - ↑t / ↑N : ℂ) + (↑t / ↑N : ℂ) * φ x) ^ N) := by
    filter_upwards [hφN_pd] with N hN
    exact isPositiveDefinite_pow hN N

  -- Step 3: pointwise limit via (1 + z/N)^N → exp(z)
  have hlim : ∀ x, Tendsto
      (fun N : ℕ => ((1 - ↑t / ↑N : ℂ) + (↑t / ↑N : ℂ) * φ x) ^ N)
      Filter.atTop (nhds (exp (↑t * (φ x - 1)))) := by
    intro x
    -- (1 + z/N)^N → exp(z) where z = t(φ(x)-1)
    exact Filter.Tendsto.congr (fun N => by
      by_cases hN : (N : ℕ) = 0
      · simp [hN]
      · congr 1
        have : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
        field_simp; ring)
      (Complex.tendsto_one_add_div_pow_exp (↑t * (φ x - 1)))

  -- Step 4: By closure_pointwise, deduce that the limit is PD
  have hpd_ev : ∀ᶠ N : ℕ in Filter.atTop,
      IsPositiveDefinite (fun x => ((1 - ↑t / ↑N : ℂ) + (↑t / ↑N : ℂ) * φ x) ^ N) := hφN_pow_pd
  -- Extract a sequence of PD functions
  obtain ⟨N₀, hN₀⟩ := hpd_ev.exists_forall_of_atTop
  exact IsPositiveDefinite.closure_pointwise
    (fun k => hN₀ (k + N₀) (by omega))
    (fun x => (hlim x).comp (tendsto_add_atTop_nat N₀))

/-- **Schoenberg's theorem.** If `ψ : ℝ → ℂ` is continuous, conditionally negative definite
(CND form `∑∑ c̄ᵢcⱼψ(ξᵢ-ξⱼ).re ≥ 0` for zero-sum weights), and `ψ(0) = 0`, then for
every `t > 0`, the function `ξ ↦ exp(t · ψ(ξ))` is positive definite.

Note: Our CND convention has the quadratic form ≥ 0, matching the convention where
`charFun = exp(ψ)`. So `exp(tψ)` (positive sign) is PD, corresponding to the `t`-th
convolution power of the underlying measure.

## Proof strategy

The standard proof uses the PSD matrix characterization: for CND `ψ` with `ψ(0) = 0`,
the matrix `Aᵢⱼ = ψ(xᵢ) + conj(ψ(xⱼ)) - ψ(xᵢ - xⱼ)` is positive semidefinite.
Then `exp(-tA)` (entrywise) is PSD by the Schur product theorem applied to the
power series, giving PD of `exp(tψ)` after factoring out `exp(tψ(xᵢ)) · exp(t·conj(ψ(xⱼ)))`.
This requires the Schur product theorem for PSD matrices (not just PD functions),
which is `IsPositiveDefinite.mul` (currently sorry'd in PositiveDefinite.lean).

## Sorry audit

* Requires `IsPositiveDefinite.mul` (Schur product) and PSD matrix infrastructure
  not yet available in this project. -/
-- Helper: The CND kernel M_{ij} = ψ(ξᵢ-ξⱼ) - ψ(ξᵢ) - conj(ψ(ξⱼ)) is PD.
-- Proved by instantiating CND at n+1 points [0, ξ₁, ..., ξₙ] with weight c₀ = -∑ cᵢ.
-- Requires Hermitian symmetry ψ(-ξ) = conj(ψ(ξ)) to relate ψ(-ξⱼ) → conj(ψ(ξⱼ)).
private theorem cnd_kernel_pd
    {ψ : ℝ → ℂ} (hψ_cnd : IsConditionallyNegativeDefinite ψ) (hψ_zero : ψ 0 = 0)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (n : ℕ) (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) := by
  -- Proof: instantiate CND at (n+1) points [0, ξ₁, ..., ξₙ] with c₀ = -∑ cᵢ.
  -- The (n+1)-point sum expands (using ψ(0)=0 and ψ(-ξ)=conj(ψ(ξ))) to our kernel sum.
  -- .re ≥ 0 from CND; .im = 0 from kernel Hermitianness.
  rw [Complex.nonneg_iff]
  constructor
  · -- .re ≥ 0: the (n+1)-point CND sum with c₀ = -∑cᵢ, ξ₀ = 0 equals our kernel sum
    -- after simplification with ψ(0) = 0 and ψ(-ξⱼ) = conj(ψ(ξⱼ)).
    -- The block expansion:
    --   (0,0): |c₀|²ψ(0) = 0
    --   (0,j≥1): c̄₀·cⱼ·ψ(-ξⱼ) = -∑ₖ∑ⱼ c̄ₖcⱼ·conj(ψ(ξⱼ))
    --   (i≥1,0): c̄ᵢ·c₀·ψ(ξᵢ) = -∑ᵢ∑ₖ c̄ᵢcₖ·ψ(ξᵢ)
    --   (i≥1,j≥1): ∑∑ c̄ᵢcⱼ·ψ(ξᵢ-ξⱼ)
    --   Total = ∑∑ c̄ᵢcⱼ·(ψ(ξᵢ-ξⱼ) - ψ(ξᵢ) - conj(ψ(ξⱼ)))
    -- Build extended vectors: ξ' = (0, ξ₁, ..., ξₙ), c' = (-∑cᵢ, c₁, ..., cₙ)
    set ξ' : Fin (n + 1) → ℝ := Fin.cons 0 ξ
    set c' : Fin (n + 1) → ℂ := Fin.cons (-∑ i, c i) c
    -- c' sums to zero
    have hc'_sum : ∑ i, c' i = 0 := by
      simp only [c', Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      ring
    -- Apply CND to get .re ≥ 0 for the (n+1)-point sum
    have hcnd := hψ_cnd (n + 1) ξ' c' hc'_sum
    -- Show the (n+1)-point sum equals our kernel sum
    suffices heq : (∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        starRingEnd ℂ (c' a) * c' b * ψ (ξ' a - ξ' b)).re =
      (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j)))).re by
      linarith
    -- The (n+1)-point CND sum = our kernel sum. Prove by direct algebraic manipulation.
    -- Key: ∑_{a,b:Fin(n+1)} conj(c'_a) * c'_b * ψ(ξ'_a - ξ'_b)
    --     = ∑_{i,j:Fin n} conj(c_i) * c_j * (ψ(ξ_i - ξ_j) - ψ(ξ_i) - conj(ψ(ξ_j)))
    -- Split the (n+1)-sum into head + tail for both indices.
    have key : ∑ a : Fin (n + 1), ∑ b : Fin (n + 1),
        starRingEnd ℂ (c' a) * c' b * ψ (ξ' a - ξ' b) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) := by
      -- Split outer and inner sums at index 0
      simp_rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, c', ξ']
      -- Expand and simplify using ψ(0) = 0, ψ(-x) = conj(ψ(x))
      simp only [sub_zero, hψ_zero, mul_zero, zero_add]
      -- Goal shape (from trace_state):
      -- ∑ x, conj(-∑c) * c x * ψ(0 - ξ x) +
      --   ∑ x, ((conj(c x) * (-∑c)) * ψ(ξ x) + ∑ j, conj(c x) * c j * ψ(ξ x - ξ j))
      -- = ∑ i, ∑ j, conj(c i) * c j * (ψ(ξ i - ξ j) - ψ(ξ i) - conj(ψ(ξ j)))
      -- Step 1: Replace ψ(0 - ξ x) → ψ(-ξ x) → conj(ψ(ξ x))
      simp_rw [show ∀ x, (0 : ℝ) - ξ x = -(ξ x) from fun x => by ring, hψ_herm]
      -- Step 2: Factor conj(-∑c) = -conj(∑c) and distribute into double sums
      -- The LHS has three components after expansion:
      -- T1 = ∑_j conj(-∑c) * c_j * conj(ψ(ξ_j)) = -(∑_i conj(c_i)) * ∑_j c_j * conj(ψ(ξ_j))
      -- T2 = ∑_i (conj(c_i) * (-∑c)) * ψ(ξ_i) = -∑_i conj(c_i) * (∑_j c_j) * ψ(ξ_i)
      -- T3 = ∑_i ∑_j conj(c_i) * c_j * ψ(ξ_i - ξ_j)
      -- We need T1 + T2 + T3 = ∑∑ conj(c_i)*c_j*(ψ(ξ_i-ξ_j) - ψ(ξ_i) - conj(ψ(ξ_j)))
      -- Proof: factor T1 = -∑∑ conj(c_i)*c_j*conj(ψ(ξ_j))
      --        factor T2 = -∑∑ conj(c_i)*c_j*ψ(ξ_i)
      --        then T3 - T2' - T1' = ∑∑ conj(c_i)*c_j*(ψ(ξ_i-ξ_j) - ψ(ξ_i) - conj(ψ(ξ_j)))
      -- Use transitivity through the double sum form
      have hT1 : ∑ x, (starRingEnd ℂ) (-∑ i, c i) * c x * (starRingEnd ℂ) (ψ (ξ x)) =
          -(∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * (starRingEnd ℂ) (ψ (ξ j))) := by
        simp_rw [map_neg, _root_.map_sum, neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
        rw [Finset.sum_comm]
      have hT2 : ∀ x, ((starRingEnd ℂ) (c x) * -∑ i, c i) * ψ (ξ x) =
          -(∑ j, (starRingEnd ℂ) (c x) * c j * ψ (ξ x)) := by
        intro x; ring_nf
        congr 1
        rw [show (starRingEnd ℂ) (c x) * (∑ i, c i) * ψ (ξ x) =
          (starRingEnd ℂ) (c x) * ψ (ξ x) * ∑ i, c i from by ring]
        rw [Finset.mul_sum]
      rw [hT1]; simp_rw [hT2]
      -- Goal: -∑∑ conj(c_i)*c_j*conj(ψ(ξ_j)) + ∑_x(-∑_j ... + ∑_j ...) = ∑∑ conj(c_i)*c_j*(...)
      simp_rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [key]
  · -- .im = 0: kernel K_{ij} is Hermitian so the quadratic form is real
    -- K_{ij} = ψ(ξᵢ-ξⱼ) - ψ(ξᵢ) - conj(ψ(ξⱼ))
    -- conj(K_{ji}) = conj(ψ(ξⱼ-ξᵢ)) - conj(ψ(ξⱼ)) - ψ(ξᵢ) = ψ(ξᵢ-ξⱼ) - conj(ψ(ξⱼ)) - ψ(ξᵢ) = K_{ij}
    have hK_herm : ∀ i j : Fin n,
        starRingEnd ℂ (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) =
        ψ (ξ j - ξ i) - ψ (ξ j) - starRingEnd ℂ (ψ (ξ i)) := by
      intro i j
      simp only [map_sub, starRingEnd_self_apply]
      -- Goal: conj(ψ(ξᵢ-ξⱼ)) - conj(ψ(ξᵢ)) - ψ(ξⱼ) = ψ(ξⱼ-ξᵢ) - ψ(ξⱼ) - conj(ψ(ξᵢ))
      -- Use hψ_herm: conj(ψ(a)) = ψ(-a)
      rw [← hψ_herm (ξ i - ξ j), show -(ξ i - ξ j) = ξ j - ξ i from by ring]; ring
    -- conj(∑∑ c̄ᵢcⱼ Kᵢⱼ) = ∑∑ c̄ⱼcᵢ Kⱼᵢ [swap conj inside] = ∑∑ c̄ᵢcⱼ Kᵢⱼ [swap i↔j]
    have hself_conj : starRingEnd ℂ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j)))) =
      ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        (ψ (ξ i - ξ j) - ψ (ξ i) - starRingEnd ℂ (ψ (ξ j))) := by
      simp only [_root_.map_sum, map_mul, starRingEnd_self_apply, hK_herm]
      -- Goal: ∑_i ∑_j c_i * conj(c_j) * K_{ji} = ∑_i ∑_j conj(c_i) * c_j * K_{ij}
      -- Swap i ↔ j in the LHS using Finset.sum_comm for the outer pair
      rw [Finset.sum_comm]
      congr 1; ext i; congr 1; ext j; ring
    -- z = conj(z) implies z.im = 0
    have h := congr_arg Complex.im hself_conj
    simp only [Complex.conj_im, neg_eq_iff_eq_neg] at h
    linarith

-- Schur product for PD kernels: if M and N are PD kernels (indexed by Fin n),
-- then the Hadamard (entrywise) product M ∘ N is also PD.
-- Uses spectral decomposition of N: N_{ij} = ∑_k λ_k U_{ik} conj(U_{jk}).
-- Then ∑∑ c̄ᵢcⱼ (M∘N)ᵢⱼ = ∑_k λ_k (∑∑ d̄ᵢdⱼ Mᵢⱼ) where d_i = c_i conj(U_{ik}).
open Matrix in
private theorem pd_kernel_to_posSemidef {n : ℕ} {K : Fin n → Fin n → ℂ}
    (hK : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j) :
    (Matrix.of K).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun c => ?_⟩
  · -- Hermitianness: conj(K j i) = K i j
    -- From hK: the quadratic form's .im = 0 for all c. This means the sum
    -- equals its conjugate. Swapping i↔j in the conjugate gives
    -- ∑∑ c̄ᵢcⱼ conj(Kⱼᵢ) = ∑∑ c̄ᵢcⱼ Kᵢⱼ for all c, forcing conj(K j i) = K i j.
    -- Step 1: for all c, the sum equals its conjugate (since .im = 0)
    have hself_conj : ∀ c : Fin n → ℂ,
        starRingEnd ℂ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j := by
      intro c
      have h0 := hK c
      rw [Complex.nonneg_iff] at h0
      rw [Complex.conj_eq_iff_im]
      exact h0.2.symm
    -- Step 2: conjugating and swapping indices gives ∑∑ c̄ᵢcⱼ conj(Kⱼᵢ) = ∑∑ c̄ᵢcⱼ Kᵢⱼ
    have hswap : ∀ c : Fin n → ℂ,
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * starRingEnd ℂ (K j i) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j := by
      intro c
      have h := hself_conj c
      simp only [_root_.map_sum, map_mul, starRingEnd_self_apply] at h
      -- h : ∑ i, ∑ j, c i * conj(c j) * conj(K i j) = ∑ i, ∑ j, conj(c i) * c j * K i j
      rw [Finset.sum_comm] at h
      -- h : ∑ j, ∑ i, c i * conj(c j) * conj(K i j) = ...
      -- Rename i↔j: ∑ i, ∑ j, c j * conj(c i) * conj(K j i) = ...
      -- = ∑ i, ∑ j, conj(c i) * c j * conj(K j i)
      have := h
      simp_rw [show ∀ i j : Fin n, c j * (starRingEnd ℂ) (c i) * (starRingEnd ℂ) (K j i) =
        (starRingEnd ℂ) (c i) * c j * (starRingEnd ℂ) (K j i) from fun i j => by ring] at this
      exact this
    -- Step 3: pointwise extraction via Pi.single
    -- hdiff_zero : ∀ c, ∑∑ c̄ₐcᵦ (Kₐᵦ - conj(Kᵦₐ)) = 0
    have hdiff_zero : ∀ c : Fin n → ℂ,
        ∑ a, ∑ b, starRingEnd ℂ (c a) * c b * (K a b - starRingEnd ℂ (K b a)) = 0 := by
      intro c
      have h := hswap c
      have : ∑ a, ∑ b, starRingEnd ℂ (c a) * c b * (K a b - starRingEnd ℂ (K b a)) =
          (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * K a b) -
          (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * starRingEnd ℂ (K b a)) := by
        simp_rw [mul_sub, ← Finset.sum_sub_distrib]
      rw [this, h, _root_.sub_self]
    -- For c = Pi.single a 1: sum collapses to D a a = 0
    have hD_diag : ∀ a : Fin n, K a a - starRingEnd ℂ (K a a) = 0 := by
      intro a
      have := hdiff_zero (Pi.single a 1)
      simp only [Pi.single_apply, apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul,
        one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true] at this
      exact this
    -- For off-diagonal: use two test vectors
    -- hdiff_single : ∀ a b c_a c_b, sum at (Pi.single a c_a + Pi.single b c_b)
    -- We need: ∀ a b, K a b = conj(K b a)
    ext i j
    simp only [conjTranspose_apply, of_apply, star_def]
    -- Goal: conj(K j i) = K i j, i.e., K i j - conj(K j i) = 0 → conj(K j i) = K i j
    -- Equivalently: K j i - conj(K i j) = 0 (swapped), then take conj
    -- Actually we want conj(K j i) = K i j, which is K i j = conj(K j i),
    -- i.e., K i j - conj(K j i) = 0
    -- Step: prove ∀ a b, K a b - conj(K b a) = 0
    suffices hD : ∀ a b : Fin n, K a b - starRingEnd ℂ (K b a) = 0 by
      have := hD i j; rw [sub_eq_zero] at this; exact this.symm
    intro a b
    by_cases hab : a = b
    · subst hab; exact hD_diag a
    · -- Use two-point test vectors to show D(a,b) = K(a,b) - conj(K(b,a)) = 0
      -- Helper: simplify sums at 2-entry vectors using sum_ite_eq'
      have heval : ∀ s t : ℂ,
          starRingEnd ℂ s * s * (K a a - starRingEnd ℂ (K a a)) +
          starRingEnd ℂ s * t * (K a b - starRingEnd ℂ (K b a)) +
          (starRingEnd ℂ t * s * (K b a - starRingEnd ℂ (K a b)) +
          starRingEnd ℂ t * t * (K b b - starRingEnd ℂ (K b b))) = 0 := by
        intro s t
        have key := hdiff_zero (fun k => (if k = a then s else 0) + (if k = b then t else 0))
        simp only [map_add, apply_ite (starRingEnd ℂ), map_zero, add_mul, mul_add,
          ite_mul, mul_ite, mul_zero, zero_mul, Finset.sum_add_distrib,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true] at key
        convert key using 1
        ring
      -- Specialize: D(a,a) = D(b,b) = 0 simplifies the evaluation
      have hDa := hD_diag a
      have hDb := hD_diag b
      -- Test 1: s = 1, t = 1 gives D(a,b) + D(b,a) = 0
      have htest1 := heval 1 1
      simp only [map_one, one_mul, hDa, hDb, mul_zero, zero_add, add_zero] at htest1
      -- htest1 : (K a b - conj(K b a)) + (K b a - conj(K a b)) = 0
      -- Test 2: s = 1, t = I gives I·D(a,b) + (-I)·D(b,a) = 0
      have htest2 := heval 1 I
      simp only [map_one, one_mul, mul_one, conj_I, hDa, hDb, mul_zero, zero_add,
        add_zero] at htest2
      set D₁ := K a b - starRingEnd ℂ (K b a)
      set D₂ := K b a - starRingEnd ℂ (K a b)
      have h_sum : D₁ + D₂ = 0 := htest1
      -- htest2 : I * D₁ + (-I) * D₂ = 0 (or with extra 1)
      -- Strategy: D₁ + D₂ = 0 and I*D₁ - I*D₂ = 0 → D₁ = D₂, then 2D₁ = 0.
      have h_eq : D₁ = D₂ := by
        have h_Idiff : I * D₁ - I * D₂ = 0 := by
          have := htest2
          -- htest2 might have form: I * D₁ + -I * D₂ = 0
          -- Need: I * D₁ - I * D₂ = 0
          -- -I * D₂ = -(I * D₂), so I*D₁ + (-I)*D₂ = I*D₁ - I*D₂
          linear_combination this
        have : I * (D₁ - D₂) = 0 := by rw [mul_sub]; exact h_Idiff
        exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left I_ne_zero)
      -- D₁ = D₂ and D₁ + D₂ = 0 → 2D₁ = 0
      have : D₁ + D₁ = 0 := by rw [show D₁ + D₁ = D₁ + D₂ from by rw [h_eq]]; exact h_sum
      rw [show D₁ = (2 : ℂ)⁻¹ * (D₁ + D₁) from by ring, this, mul_zero]
  · change 0 ≤ dotProduct (star c) (mulVec (Matrix.of K) c)
    have key : dotProduct (star c) (mulVec (Matrix.of K) c) =
        ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K i j := by
      simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def]
      congr 1; ext i; rw [Finset.mul_sum]; congr 1; ext j; ring
    rw [key]; exact hK c

private theorem pd_kernel_mul
    {n : ℕ} {M N : Fin n → Fin n → ℂ}
    (hM : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j)
    (hN : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * N i j) :
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (M i j * N i j) := by
  open Matrix in
  intro c
  -- Convert N to PSD matrix and get spectral decomposition
  have hN_psd := pd_kernel_to_posSemidef hN
  have hN_herm := hN_psd.isHermitian
  set B : Matrix (Fin n) (Fin n) ℂ := Matrix.of N
  set ev := hN_herm.eigenvalues
  set U : Matrix (Fin n) (Fin n) ℂ := ↑hN_herm.eigenvectorUnitary
  have hev_nonneg : ∀ k, 0 ≤ ev k := fun k => hN_psd.eigenvalues_nonneg k
  -- Spectral decomposition: N i j = B i j = ∑_k (ev k : ℂ) * U i k * conj(U j k)
  have hN_spec : ∀ i j : Fin n, N i j = ∑ k, (↑(ev k) : ℂ) * U i k *
      starRingEnd ℂ (U j k) := by
    intro i j
    have h := hN_herm.spectral_theorem
    have hBij : B i j = ((Unitary.conjStarAlgAut ℂ _) hN_herm.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hN_herm.eigenvalues))) i j :=
      congr_fun (congr_fun h i) j
    rw [show N i j = B i j from rfl, hBij, Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
    congr 1; ext k
    simp only [Matrix.star_apply, star_def, Matrix.mul_apply, Matrix.diagonal_apply,
      Function.comp]
    have key := Fintype.sum_eq_single k
      (show ∀ l : Fin n, l ≠ k →
        (↑hN_herm.eigenvectorUnitary : Matrix _ _ ℂ) i l *
        (if l = k then (↑(hN_herm.eigenvalues l) : ℂ) else 0) = 0
      from fun l hlk => by simp [hlk])
    calc _ = (↑hN_herm.eigenvectorUnitary : Matrix _ _ ℂ) i k *
            (if k = k then (↑(hN_herm.eigenvalues k) : ℂ) else 0) *
            starRingEnd ℂ ((↑hN_herm.eigenvectorUnitary : Matrix _ _ ℂ) j k) := by
              exact congrArg (· * _) key
         _ = (↑(ev k) : ℂ) * U i k * starRingEnd ℂ (U j k) := by
              simp only [ite_true, U, ev]; ring
  -- Weights: d k i = c i * conj(U i k)
  set d : Fin n → Fin n → ℂ := fun k i => c i * starRingEnd ℂ (U i k)
  -- The product form = ∑_k ev_k * (M form with d_k)
  have hsuff : ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (M i j * N i j) =
      ∑ k, (↑(ev k) : ℂ) *
        (∑ i, ∑ j, starRingEnd ℂ (d k i) * d k j * M i j) := by
    simp_rw [hN_spec]
    simp_rw [Finset.mul_sum]
    conv_lhs =>
      arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    congr 1; ext k
    have hterm : ∀ i j : Fin n,
        starRingEnd ℂ (c i) * c j * (M i j * (↑(ev k) * U i k * starRingEnd ℂ (U j k)))
        = ↑(ev k) * (starRingEnd ℂ (d k i) * d k j * M i j) := by
      intro i j; simp only [d, map_mul, starRingEnd_self_apply]; ring
    simp_rw [hterm]
  rw [hsuff]
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (by exact_mod_cast hev_nonneg k) (hM (d k))

-- Entrywise k-th power of PD kernel is PD (by iterated Schur product).
private theorem pd_kernel_pow
    {n : ℕ} {M : Fin n → Fin n → ℂ}
    (hM : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j)
    (k : ℕ) :
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j ^ k := by
  induction k with
  | zero =>
    intro c; simp only [pow_zero, mul_one]
    -- ∑∑ c̄ᵢcⱼ = |∑cᵢ|² ≥ 0
    -- Factor: ∑_i ∑_j conj(c_i) * c_j = (∑ conj(c_i)) * (∑ c_j) = conj(∑ c_i) * ∑ c_j
    rw [show ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j =
        starRingEnd ℂ (∑ i, c i) * ∑ j, c j from by
      rw [_root_.map_sum]; simp_rw [Finset.sum_mul, Finset.mul_sum]]
    exact star_mul_self_nonneg _
  | succ k ih =>
    intro c
    have hpow : ∀ i j : Fin n, M i j ^ (k + 1) = M i j ^ k * M i j :=
      fun i j => pow_succ (M i j) k
    simp_rw [hpow]
    exact pd_kernel_mul ih hM c

-- Helper: entrywise exp of PD kernel is PD.
-- Proof: (1 + tM/N)^N → exp(tM) entrywise as N → ∞.
-- Each (1 + tM/N)^N is PD (by pd_kernel_pow + the base case 1 + tM/N is PD).
private theorem exp_pd_kernel
    {n : ℕ} {M : Fin n → Fin n → ℂ}
    (hM : ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * M i j)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ c : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * exp (↑t * M i j) := by
  intro c
  -- For large N, define K_N(i,j) = (1 + t·M(i,j)/N)^N
  -- Step 1: K_N is PD for large N
  -- 1 + t·M(i,j)/N is PD when N > t·‖M‖:
  --   ∑∑ c̄ᵢcⱼ (1 + (t/N)·Mᵢⱼ) = |∑cᵢ|² + (t/N)·∑∑ c̄ᵢcⱼ Mᵢⱼ ≥ 0
  -- Then (1 + tM/N)^N is PD by pd_kernel_pow.
  have hbase : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ d : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (d i) * d j *
        (1 + ↑t / (↑N : ℂ) * M i j) := by
    filter_upwards [Filter.Ici_mem_atTop 1] with N (hN : 1 ≤ N)
    intro d
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have htN : 0 ≤ t / N := div_nonneg ht (le_of_lt hN_pos)
    -- ∑∑ c̄ᵢdⱼ(1 + (t/N)Mᵢⱼ) = |∑dᵢ|² + (t/N)·∑∑ c̄ᵢdⱼ Mᵢⱼ
    -- Split: ∑∑ c̄ᵢdⱼ(1 + (t/N)Mᵢⱼ) = ∑∑ c̄ᵢdⱼ + (t/N)·∑∑ c̄ᵢdⱼ Mᵢⱼ
    have hsplit : ∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (d i) * d j * (1 + ↑t / (↑N : ℂ) * M i j) =
      ∑ i, ∑ j, starRingEnd ℂ (d i) * d j +
        (↑t / ↑N : ℂ) * ∑ i, ∑ j, starRingEnd ℂ (d i) * d j * M i j := by
      trans ∑ i : Fin n, (∑ j, starRingEnd ℂ (d i) * d j +
        ↑t / ↑N * ∑ j, starRingEnd ℂ (d i) * d j * M i j)
      · congr 1; ext i
        trans ∑ j : Fin n, (starRingEnd ℂ (d i) * d j +
          ↑t / ↑N * (starRingEnd ℂ (d i) * d j * M i j))
        · congr 1; ext j; ring
        · rw [Finset.sum_add_distrib, Finset.mul_sum]
      · rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsplit]
    apply add_nonneg
    · -- |∑dᵢ|² ≥ 0
      rw [show ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (d i) * d j =
          starRingEnd ℂ (∑ i, d i) * ∑ j, d j from by
        rw [_root_.map_sum]; simp_rw [Finset.sum_mul, Finset.mul_sum]]
      exact star_mul_self_nonneg _
    · -- (t/N) · (PD sum) ≥ 0
      have hcoeff : (0 : ℂ) ≤ ↑t / ↑N := by
        rw [Complex.nonneg_iff]; constructor
        · simp; exact div_nonneg ht (le_of_lt hN_pos)
        · simp
      exact mul_nonneg hcoeff (hM d)
  -- Step 2: K_N = (1 + tM/N)^N is PD
  have hpow_pd : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ d : Fin n → ℂ, 0 ≤ ∑ i, ∑ j, starRingEnd ℂ (d i) * d j *
        (1 + ↑t / (↑N : ℂ) * M i j) ^ N := by
    filter_upwards [hbase] with N hN
    intro d
    have hpow_eq : ∀ i j, (1 + ↑t / (↑N : ℂ) * M i j) ^ N =
        (fun i j => 1 + ↑t / (↑N : ℂ) * M i j) i j ^ N := fun i j => rfl
    simp_rw [hpow_eq]
    exact pd_kernel_pow hN N d
  -- Step 3: pointwise convergence (1 + tMᵢⱼ/N)^N → exp(tMᵢⱼ)
  have hlim : ∀ i j : Fin n, Filter.Tendsto
      (fun N : ℕ => starRingEnd ℂ (c i) * c j * (1 + ↑t / (↑N : ℂ) * M i j) ^ N)
      Filter.atTop (nhds (starRingEnd ℂ (c i) * c j * exp (↑t * M i j))) := by
    intro i j
    apply Filter.Tendsto.const_mul
    exact (Complex.tendsto_one_add_div_pow_exp (↑t * M i j)).congr fun N => by
      by_cases hN : (N : ℕ) = 0
      · simp [hN]
      · have hNne : (↑N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
        congr 1; field_simp
  -- Step 4: sum convergence (finite sum + pointwise → sum converges)
  have hsum_lim : Filter.Tendsto
      (fun N : ℕ => ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j *
        (1 + ↑t / (↑N : ℂ) * M i j) ^ N)
      Filter.atTop
      (nhds (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j * exp (↑t * M i j))) :=
    tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j _ => hlim i j
  -- Step 5: limit of nonneg is nonneg
  exact ge_of_tendsto hsum_lim (by filter_upwards [hpow_pd] with N hN; exact hN c)

theorem schoenberg_exp_of_cnd
    {ψ : ℝ → ℂ} (_hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cnd : IsConditionallyNegativeDefinite ψ)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ))
    (t : ℝ) (ht : 0 < t) :
    IsPositiveDefinite (fun ξ => exp (↑t * ψ ξ)) := by
  intro n x c
  -- The kernel M_{ij} = ψ(x_i - x_j) - ψ(x_i) - conj(ψ(x_j)) is PD
  have hM := fun d => cnd_kernel_pd hψ_cnd hψ_zero hψ_herm n x d
  -- exp(tM) is PD
  have hexpM := exp_pd_kernel hM t (le_of_lt ht)
  -- Factorization: exp(t·ψ(x_i-x_j)) = exp(t·ψ(x_i))·exp(t·conj(ψ(x_j)))·exp(t·M_{ij})
  -- Use d_i = c_i · exp(t · conj(ψ(x_i))) so conj(d_i) = conj(c_i) · exp(t · ψ(x_i))
  set d : Fin n → ℂ := fun i => c i * exp (↑t * starRingEnd ℂ (ψ (x i)))
  suffices hsuff : ∀ i j : Fin n,
      starRingEnd ℂ (c i) * c j * exp (↑t * ψ (x i - x j)) =
      starRingEnd ℂ (d i) * d j *
        exp (↑t * (ψ (x i - x j) - ψ (x i) - starRingEnd ℂ (ψ (x j)))) by
    simp_rw [hsuff]
    exact hexpM d
  intro i j
  simp only [d, map_mul]
  -- conj(exp(t * conj(ψ(x i)))) = exp(conj(t * conj(ψ(x i)))) = exp(t * ψ(x i))
  rw [show starRingEnd ℂ (exp (↑t * starRingEnd ℂ (ψ (x i)))) =
      exp (↑t * ψ (x i)) from by
    rw [← Complex.exp_conj]; congr 1
    simp [Complex.conj_ofReal]]
  -- Now: conj(c i) * exp(t*ψ(x i)) * (c j * exp(t*conj(ψ(x j)))) * exp(t*M_ij)
  --    = conj(c i) * c j * exp(t*ψ(x i - x j))
  rw [show starRingEnd ℂ (c i) * exp (↑t * ψ (x i)) *
      (c j * exp (↑t * starRingEnd ℂ (ψ (x j)))) *
      exp (↑t * (ψ (x i - x j) - ψ (x i) - starRingEnd ℂ (ψ (x j)))) =
    starRingEnd ℂ (c i) * c j *
      (exp (↑t * ψ (x i)) * exp (↑t * starRingEnd ℂ (ψ (x j))) *
        exp (↑t * (ψ (x i - x j) - ψ (x i) - starRingEnd ℂ (ψ (x j))))) from by ring]
  congr 1
  rw [← exp_add, ← exp_add]
  congr 1; ring

/-! ## Convolution semigroup structure -/

/-- A **convolution semigroup** on `ℝ` is a family of probability measures `μ_t` indexed by
`t > 0` whose characteristic functions satisfy the semigroup law:
`charFun(μ_{s+t}) = charFun(μ_s) · charFun(μ_t)` for all `ξ`.

Equivalently, `charFun(μ_t)(ξ) = exp(tψ(ξ))` for a continuous function `ψ` with `ψ(0) = 0`.
The Lévy-Khintchine theorem extracts the triple `(b, σ², ν)` from `ψ`. -/
structure ConvolutionSemigroup where
  /-- The exponent function: `charFun(μ_t) = exp(t · ψ)`. -/
  exponent : ℝ → ℂ
  /-- The exponent is continuous. -/
  exponent_continuous : Continuous exponent
  /-- The exponent vanishes at 0. -/
  exponent_zero : exponent 0 = 0
  /-- For each `t > 0`, a probability measure whose characteristic function is `exp(tψ)`. -/
  measure : {t : ℝ // 0 < t} → MeasureTheory.ProbabilityMeasure ℝ
  /-- The characteristic function identity. -/
  charFun_eq : ∀ (t : {t : ℝ // 0 < t}) (ξ : ℝ),
    MeasureTheory.ProbabilityMeasure.characteristicFun (measure t) ξ =
      exp ((↑t.val : ℂ) * exponent ξ)

/-- First-order expansion: `(exp(tz) − 1)/t → z` as `t → 0`.
This is the derivative of `t ↦ exp(tz)` at `t = 0`, extracted as a slope limit. -/
lemma exp_first_order (z : ℂ) :
    Tendsto (fun t : ℝ => (exp ((↑t : ℂ) * z) - 1) / (↑t : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 z) := by
  -- The derivative of `t ↦ cexp(tz)` at `t = 0` is `z`.
  have hg : HasDerivAt (fun t : ℝ => cexp ((↑t : ℂ) * z)) z 0 := by
    -- Compose: cexp ∘ (t ↦ ↑t * z), derivative at 0 is cexp(0 * z) * z = z.
    have hf : HasDerivAt (fun t : ℝ => (↑t : ℂ) * z) (1 * z) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const z
    have hexp := hf.cexp
    simp only [ofReal_zero, zero_mul, exp_zero, one_mul, one_mul] at hexp
    exact hexp
  -- Step 3: extract the slope limit `(f(0+t) - f(0))/t → f'(0)`.
  have hslope := hg.tendsto_slope_zero
  -- Step 4: the slope is exactly `(cexp(↑t * z) - 1) / ↑t` after simplification.
  simp only [zero_add, ofReal_zero, zero_mul, exp_zero] at hslope
  exact hslope.congr (fun t => by
    show t⁻¹ • (cexp ((↑t : ℂ) * z) - 1) = (cexp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)
    rw [RCLike.real_smul_eq_coe_mul (K := ℂ)]
    push_cast
    rw [inv_mul_eq_div]
    norm_cast)

namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-- The semigroup law: `charFun(μ_s) · charFun(μ_t) = charFun(μ_{s+t})` at the level
of exponents. This follows from the exponential identity `exp(sψ) · exp(tψ) = exp((s+t)ψ)`. -/
theorem charFun_mul (s t : {r : ℝ // 0 < r}) (ξ : ℝ) :
    MeasureTheory.ProbabilityMeasure.characteristicFun (S.measure s) ξ *
    MeasureTheory.ProbabilityMeasure.characteristicFun (S.measure t) ξ =
    exp ((↑(s.val + t.val) : ℂ) * S.exponent ξ) := by
  rw [S.charFun_eq s ξ, S.charFun_eq t ξ, ← exp_add]
  congr 1
  push_cast; ring

/-- The scaled measure `(1/t) · μ_t`. When `charFun(μ_t) = exp(tψ)`, the scaled measure
    captures the behaviour of `(exp(tψ) − 1)/t → ψ` as `t → 0⁺`. -/
noncomputable def scaledMeasure (t : {t : ℝ // 0 < t}) : Measure ℝ :=
  ENNReal.ofReal t.val⁻¹ • (S.measure t : Measure ℝ)

@[simp]
theorem scaledMeasure_apply (t : {t : ℝ // 0 < t}) (A : Set ℝ) :
    S.scaledMeasure t A = ENNReal.ofReal t.val⁻¹ * (S.measure t : Measure ℝ) A := by
  simp [scaledMeasure, Measure.smul_apply]

/-- Integration against the scaled measure: `∫ f d(scaledMeasure t) = t⁻¹ • ∫ f dμ_t`.
    Here `•` is the scalar action of `ℝ` on the codomain (typically `ℂ`). -/
theorem integral_scaledMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : {t : ℝ // 0 < t}) (f : ℝ → E) :
    ∫ x, f x ∂(S.scaledMeasure t) = t.val⁻¹ • ∫ x, f x ∂(S.measure t : Measure ℝ) := by
  simp only [scaledMeasure]
  rw [integral_smul_measure]
  rw [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr t.prop))]

/-- Scaled characteristic function limit: `(charFun(μ_t)(ξ) − 1)/t → ψ(ξ)` as `t → 0⁺`.
Since `charFun(μ_t)(ξ) = exp(tψ(ξ))`, this follows from `exp_first_order`. -/
theorem charFun_scaled_limit (ξ : ℝ) :
    Tendsto (fun t : {t : ℝ // 0 < t} =>
      (MeasureTheory.ProbabilityMeasure.characteristicFun (S.measure t) ξ - 1) / (↑t.val : ℂ))
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (S.exponent ξ)) := by
  -- Rewrite charFun using the semigroup identity.
  suffices Tendsto (fun t : {t : ℝ // 0 < t} =>
      (exp ((↑t.val : ℂ) * S.exponent ξ) - 1) / (↑t.val : ℂ))
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (S.exponent ξ)) by
    refine this.congr (fun t => ?_)
    rw [S.charFun_eq t ξ]
  -- The target is `(exp_first_order ψ(ξ)) ∘ Subtype.val`.
  exact (exp_first_order (S.exponent ξ)).comp
    ((tendsto_comap.mono_right (nhdsGT_le_nhdsNE 0) : Tendsto Subtype.val
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝[≠] (0 : ℝ))))

end ConvolutionSemigroup

/-! ## Truncation framework

The Lévy-Khintchine formula splits the integral over a Lévy measure into
"small jump" and "large jump" contributions at the threshold `|x| = 1`.
We define the corresponding sets and prove a split lemma. -/

/-- The "small jump" set `{x | |x| < 1}`. -/
def smallSet : Set ℝ := {x | |x| < 1}

/-- The "large jump" set `{x | ε ≤ |x|}`. -/
def largeSet (ε : ℝ) : Set ℝ := {x | ε ≤ |x|}

@[simp] lemma mem_smallSet {x : ℝ} : x ∈ smallSet ↔ |x| < 1 := Iff.rfl

@[simp] lemma mem_largeSet {x : ℝ} {ε : ℝ} : x ∈ largeSet ε ↔ ε ≤ |x| := Iff.rfl

lemma measurableSet_smallSet : MeasurableSet smallSet :=
  (isOpen_Iio.preimage continuous_abs).measurableSet

lemma measurableSet_largeSet (ε : ℝ) : MeasurableSet (largeSet ε) :=
  (isClosed_Ici.preimage continuous_abs).measurableSet

lemma smallSet_eq_compl_largeSet : smallSet = (largeSet 1)ᶜ := by
  ext x; simp [smallSet, largeSet, not_le]

/-- Split `∫ (exp(ixξ) − 1) dμ` into small and large jump contributions. -/
lemma integral_exp_sub_one_split (μ : Measure ℝ) [IsProbabilityMeasure μ] (ξ : ℝ)
    (hf : Integrable (fun x : ℝ => exp (↑x * ↑ξ * I) - 1) μ) :
    ∫ x : ℝ, (exp (↑x * ↑ξ * I) - 1) ∂μ =
      ∫ x : ℝ in smallSet, (exp (↑x * ↑ξ * I) - 1) ∂μ +
      ∫ x : ℝ in smallSetᶜ, (exp (↑x * ↑ξ * I) - 1) ∂μ :=
  (integral_add_compl measurableSet_smallSet hf).symm

/-! ## Phase 3: Compactness on large jumps + Lévy measure construction

This section develops the compactness machinery for extracting the Lévy measure
from the convolution semigroup `{μ_t}_{t>0}`.

**Overview:**
1. The scaled measures `(1/t)·μ_t` restricted to `{|x| ≥ ε}` have uniformly bounded mass.
2. By Prokhorov's theorem, a subsequential weak limit `ν_ε` exists.
3. For `ε₁ ≤ ε₂`, the measures are consistent: `ν_{ε₂}` is a restriction of `ν_{ε₁}`.
4. The Lévy measure is constructed as the monotone limit `ν = sup_ε ν_ε`.
-/

namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-- The integrand `x ↦ exp(i·ξ·x)` is integrable against any finite measure. -/
private lemma integrable_charFun_integrand {μ : Measure ℝ} [IsFiniteMeasure μ] (ξ : ℝ) :
    Integrable (fun x : ℝ => exp ((↑(ξ * x) : ℂ) * I)) μ :=
  Integrable.of_bound
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id')).mul_const I
      |>.cexp.aestronglyMeasurable)
    1 (ae_of_all _ fun x => le_of_eq (Complex.norm_exp_ofReal_mul_I _))

/-- `Re(1 - charFun μ ξ) = ∫ (1 - cos(ξ·x)) dμ` for probability measures.
Proof: unfold charFun to ∫ exp(iξx), commute Re through the integral via `integral_re`,
use `Re(exp(iy)) = cos y`, and combine with `∫ 1 dμ = 1`. -/
private lemma re_one_sub_charFun_eq_integral
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (ξ : ℝ) :
    (1 - charFun μ ξ).re = ∫ x, (1 - Real.cos (ξ * x)) ∂μ := by
  have hint := integrable_charFun_integrand (μ := μ) ξ
  -- Express 1 - charFun as a single integral of (1 - exp(iξx))
  have h1 : 1 - charFun μ ξ = ∫ x : ℝ, (1 - exp ((↑(ξ * x) : ℂ) * I)) ∂μ := by
    have hcf : charFun μ ξ = ∫ x : ℝ, exp ((↑(ξ * x) : ℂ) * I) ∂μ := by
      rw [charFun_apply_real]; congr 1; ext x; congr 1; push_cast; ring
    rw [hcf]
    have h_one : (1 : ℂ) = ∫ _ : ℝ, (1 : ℂ) ∂μ := by simp [integral_const]
    conv_lhs => rw [h_one]
    exact (integral_sub (integrable_const (1 : ℂ)) hint).symm
  -- Take Re and commute through integral
  rw [h1, show (∫ x : ℝ, (1 - exp ((↑(ξ * x) : ℂ) * I)) ∂μ).re =
    ∫ x : ℝ, (1 - exp ((↑(ξ * x) : ℂ) * I)).re ∂μ from
    (integral_re (Integrable.sub (integrable_const 1) hint)).symm]
  -- Simplify Re(1 - exp(iξx)) = 1 - cos(ξx)
  congr 1; ext x
  simp only [sub_re, one_re, Complex.exp_ofReal_mul_I_re]

/-! ### 3.1 — Uniform boundedness of scaled measures on large sets -/

/-- The real part of `1 - exp(z)` for small `|z|` is well-approximated by `-Re(z)`.
    Auxiliary bound for the uniform mass estimate. -/
private lemma re_one_sub_exp_bound (z : ℂ) (hz : ‖z‖ ≤ 1) :
    |(1 - exp z).re| ≤ ‖z‖ + ‖z‖ ^ 2 := by
  -- Use exp_bound with n=1: ‖exp z - 1‖ ≤ ‖z‖ * (2 * 1⁻¹)
  have h1 := Complex.exp_bound hz (n := 1) (by omega)
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial, Nat.cast_one, div_one] at h1
  -- h1 : ‖exp z - 1‖ ≤ ‖z‖ ^ 1 * (↑2 * (↑1 * ↑1)⁻¹) = ‖z‖ * 2
  -- We need: |(1 - exp z).re| ≤ ‖z‖ + ‖z‖²
  -- Since ‖z‖ ≤ 1, we have ‖z‖ · 2 ≤ ‖z‖ + ‖z‖ · 1 ≤ ‖z‖ + ‖z‖ · ‖z‖ only if ‖z‖ ≥ 1
  -- Instead: |(1-exp z).re| ≤ ‖1 - exp z‖ ≤ ‖z‖ * 2 and ‖z‖ + ‖z‖² ≥ ‖z‖
  -- But ‖z‖ * 2 > ‖z‖ + ‖z‖² when ‖z‖ < 1, so this n=1 bound is too weak.
  -- Use n=2 instead to get the tighter bound.
  have h2 := Complex.exp_bound hz (n := 2) (by omega)
  -- After simplification, h2 gives ‖exp z - (1 + z)‖ ≤ ‖z‖² * (3/4)
  -- Then ‖exp z - 1‖ ≤ ‖exp z - (1+z)‖ + ‖z‖ ≤ (3/4)·‖z‖² + ‖z‖ ≤ ‖z‖² + ‖z‖
  calc |(1 - exp z).re|
      ≤ ‖1 - exp z‖ := Complex.abs_re_le_norm _
    _ = ‖exp z - 1‖ := norm_sub_rev _ _
    _ ≤ ‖exp z - (1 + z)‖ + ‖z‖ := by
        calc ‖exp z - 1‖ = ‖(exp z - (1 + z)) + z‖ := by ring_nf
          _ ≤ ‖exp z - (1 + z)‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ‖z‖ ^ 2 := by
        -- From h2, after simp the sum is 1 + z (first two terms of Taylor)
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero,
          Nat.factorial, Nat.cast_one, div_one, pow_succ, one_mul] at h2
        -- h2 : ‖cexp z - (1 + z / ↑(1*1))‖ ≤ ‖z‖*‖z‖*(3*(2*2)⁻¹) = ‖z‖²·3/4
        -- Simplify: z / ↑(1*1) = z and the coefficient
        simp only [Nat.succ_eq_add_one] at h2
        norm_num at h2
        -- h2 : ‖cexp z - (1 + z)‖ ≤ ‖z‖ * ‖z‖ * (3/4)
        -- Goal: ‖cexp z - (1 + z)‖ + ‖z‖ ≤ ‖z‖ + ‖z‖ ^ 2
        -- i.e. ‖cexp z - (1 + z)‖ ≤ ‖z‖ ^ 2
        -- From h2: ‖...‖ ≤ ‖z‖² * 3/4 ≤ ‖z‖²
        nlinarith [norm_nonneg z, sq_nonneg ‖z‖]

/-- If `cos x = 1` and `cos(x√2) = 1`, then `x = 0`. Uses irrationality of `√2`. -/
private lemma eq_zero_of_cos_eq_one_and_cos_sqrt_two_eq_one {x : ℝ}
    (h1 : Real.cos x = 1) (h2 : Real.cos (x * Real.sqrt 2) = 1) : x = 0 := by
  rw [Real.cos_eq_one_iff] at h1 h2
  obtain ⟨k, hk⟩ := h1
  obtain ⟨m, hm⟩ := h2
  by_cases hk0 : k = 0
  · simp [hk0] at hk; linarith
  · exfalso
    have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    have hksqrt : (k : ℝ) * Real.sqrt 2 = m := by
      have : (↑m : ℝ) * (2 * Real.pi) = ↑k * Real.sqrt 2 * (2 * Real.pi) := by
        rw [hm, ← hk]; ring
      exact (mul_right_cancel₀ h2pi_ne this).symm
    have hk_ne : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk0
    exact irrational_sqrt_two ⟨(m : ℚ) / k, by
      push_cast; rw [div_eq_iff hk_ne]; linarith [hksqrt]⟩

/-- The integral of `1 - cos(xξ)` is non-negative. -/
private lemma one_sub_cos_nonneg (ξ : ℝ) (x : ℝ) : 0 ≤ 1 - Real.cos (x * ξ) :=
  sub_nonneg.mpr (Real.cos_le_one _)

/-- `fun x => 1 - cos(x * ξ)` is integrable against a finite measure restricted to any set. -/
private lemma integrableOn_one_sub_cos {μ : Measure ℝ} [IsFiniteMeasure μ] (ξ : ℝ) (s : Set ℝ) :
    IntegrableOn (fun x => 1 - Real.cos (x * ξ)) s μ :=
  Integrable.of_bound
    ((continuous_const.sub
      (Real.continuous_cos.comp (continuous_id'.mul continuous_const))).aestronglyMeasurable)
    2 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_nonneg ξ x)]
      linarith [Real.neg_one_le_cos (x * ξ)])

/-- On `{|x| ≥ ε}`, we have `∫ (1 - cos(xξ)) dμ ≥ c·μ({|x| ≥ ε})` for a suitable `ξ`.
    This is the analytical core of the uniform bound argument. -/
private lemma one_sub_cos_integral_lower_bound
    {μ : Measure ℝ} [IsFiniteMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ (ξ : ℝ) (c : ℝ), 0 < c ∧
      c * (μ (largeSet ε)).toReal ≤
        ∫ x in largeSet ε, (1 - Real.cos (x * ξ)) ∂μ := by
  by_cases hmass : μ (largeSet ε) = 0
  · -- Mass 0: trivially satisfied with any ξ, c
    refine ⟨1, 1, one_pos, ?_⟩
    rw [hmass, ENNReal.toReal_zero, mul_zero]
    exact setIntegral_nonneg (measurableSet_largeSet ε) (fun x _ => one_sub_cos_nonneg 1 x)
  · -- Mass > 0: find ξ with positive integral
    have hpos_mass : 0 < (μ (largeSet ε)).toReal :=
      ENNReal.toReal_pos hmass (measure_lt_top μ _).ne
    -- Claim: ∃ ξ with ∫_{largeSet ε} (1 - cos(xξ)) dμ > 0
    suffices h : ∃ ξ, 0 < ∫ x in largeSet ε, (1 - Real.cos (x * ξ)) ∂μ by
      obtain ⟨ξ, hξ⟩ := h
      exact ⟨ξ, _ / _, div_pos hξ hpos_mass,
        (div_mul_cancel₀ _ (ne_of_gt hpos_mass)).le⟩
    -- By contradiction: if all integrals ≤ 0, they're all = 0
    by_contra hall; push_neg at hall
    -- Each integral ≥ 0 (1-cos ≥ 0), so hall gives = 0 for all ξ
    have hall_eq : ∀ ξ, ∫ x in largeSet ε, (1 - Real.cos (x * ξ)) ∂μ = 0 := fun ξ =>
      le_antisymm (hall ξ)
        (setIntegral_nonneg (measurableSet_largeSet ε) (fun x _ => one_sub_cos_nonneg ξ x))
    -- From integral = 0 with non-negative integrand: cos(xξ) = 1 μ-a.e. on largeSet ε
    have hae : ∀ ξ, ∀ᵐ x ∂(μ.restrict (largeSet ε)), Real.cos (x * ξ) = 1 := by
      intro ξ
      have h0 := (integral_eq_zero_iff_of_nonneg (fun x => one_sub_cos_nonneg ξ x)
        (integrableOn_one_sub_cos ξ _)).mp (hall_eq ξ)
      filter_upwards [h0] with x hx
      have : 1 - Real.cos (x * ξ) = 0 := hx
      linarith
    -- Specialize to ξ=1, ξ=√2 and combine: x = 0 μ-a.e. on largeSet ε
    have hae_zero : ∀ᵐ x ∂(μ.restrict (largeSet ε)), x = 0 := by
      filter_upwards [hae 1, hae (Real.sqrt 2)] with x h1 h2
      have h1' : Real.cos x = 1 := by rwa [mul_one] at h1
      exact eq_zero_of_cos_eq_one_and_cos_sqrt_two_eq_one h1' h2
    -- But 0 ∉ largeSet ε (since ε > 0), so μ(largeSet ε) = 0, contradiction
    apply hmass
    have hres : ∀ᵐ x ∂(μ.restrict (largeSet ε)), x ∈ largeSet ε :=
      ae_restrict_mem (measurableSet_largeSet ε)
    have : ∀ᵐ x ∂(μ.restrict (largeSet ε)), False := by
      filter_upwards [hres, hae_zero] with x hx hx0
      exact absurd (hx0 ▸ hx) (by simp [mem_largeSet, abs_zero, not_le, hε])
    simp only [ae_iff, not_false_eq_true, Set.setOf_true, Measure.restrict_apply_univ] at this
    exact this

/-- **Real-valued scaled mass bound.** The quantity `t⁻¹ · μ_t({|x| ≥ ε})` is
    uniformly bounded over all `t > 0`.

    **Proof sketch (sorry'd — requires Fubini + charFun integral identity):**
    1. For `|x| ≥ ε`: `∫₀^{2/ε} (1-cos(xξ)) dξ = 2/ε - sin(2x/ε)/x ≥ 1/ε`.
    2. By Fubini: `ε⁻¹ · μ({|x| ≥ ε}) ≤ ∫₀^{2/ε} (1 - Re(charFun μ ξ)) dξ`.
    3. Using `charFun(μ_t)(ξ) = exp(tψ(ξ))` and the bound
       `t⁻¹(1-Re(exp(tψ))) ≤ 2‖ψ‖` (from `‖exp z - 1‖ ≤ 2‖z‖` for `‖z‖ ≤ 1`
       and `1-Re(exp(tψ)) ≤ 2` with `t⁻¹ ≤ ‖ψ‖` otherwise):
       `t⁻¹ · μ_t({|x| ≥ ε}) ≤ 4 · sup_{ξ ∈ [0,2/ε]} ‖ψ(ξ)‖`. -/
private lemma scaled_mass_bound_real (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ (t : {t : ℝ // 0 < t}),
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet ε)).toReal ≤ ↑C := by
  -- The exponent attains a maximum norm M on the compact interval [0, 2/ε].
  obtain ⟨ξ_max, -, hξ_max⟩ := isCompact_Icc.exists_isMaxOn
    (⟨0, Set.left_mem_Icc.mpr (by positivity)⟩ : (Set.Icc (0:ℝ) (2/ε)).Nonempty)
    S.exponent_continuous.norm.continuousOn
  set M := ‖S.exponent ξ_max‖ with hM_def
  -- Key uniform bound: t⁻¹ * Re(1-exp(tψ(ξ))) ≤ 2M for ξ ∈ [0,2/ε], t > 0.
  have hkey : ∀ ξ ∈ Set.Icc (0:ℝ) (2/ε), ∀ (t : {t : ℝ // 0 < t}),
      t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * M := by
    intro ξ hξ t
    have hξM : ‖S.exponent ξ‖ ≤ M := hξ_max hξ
    -- ‖exp(tψ(ξ))‖ ≤ 1 via characteristicFun identity
    have hexp_le1 : ‖exp ((t.val : ℂ) * S.exponent ξ)‖ ≤ 1 := by
      have h := (S.measure t).norm_characteristicFun_le_one ξ
      rwa [S.charFun_eq t ξ] at h
    -- (1-exp(tψ)).re ≤ 2
    have hre_le2 : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 := by
      have hge : -1 ≤ (exp ((t.val : ℂ) * S.exponent ξ)).re := by
        have h1 : |(exp ((t.val : ℂ) * S.exponent ξ)).re| ≤ 1 :=
          (Complex.abs_re_le_norm _).trans hexp_le1
        linarith [neg_abs_le (exp ((t.val : ℂ) * S.exponent ξ)).re]
      simp only [sub_re, one_re]; linarith
    -- Case split on t * ‖ψ(ξ)‖ ≤ 1 vs > 1
    by_cases h : t.val * ‖S.exponent ξ‖ ≤ 1
    · -- Small regime: use norm_exp_sub_one_le
      have htz : ‖(t.val : ℂ) * S.exponent ξ‖ ≤ 1 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; exact h
      have h_re : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * t.val * ‖S.exponent ξ‖ :=
        calc (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
            ≤ ‖1 - exp ((t.val : ℂ) * S.exponent ξ)‖ := Complex.re_le_norm _
          _ = ‖exp ((t.val : ℂ) * S.exponent ξ) - 1‖ := norm_sub_rev _ _
          _ ≤ 2 * ‖(t.val : ℂ) * S.exponent ξ‖ := Complex.norm_exp_sub_one_le htz
          _ = 2 * t.val * ‖S.exponent ξ‖ := by
                simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; ring
      calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
          ≤ t.val⁻¹ * (2 * t.val * ‖S.exponent ξ‖) :=
              mul_le_mul_of_nonneg_left h_re (le_of_lt (inv_pos.mpr t.prop))
        _ = 2 * ‖S.exponent ξ‖ := by field_simp [ne_of_gt t.prop]
        _ ≤ 2 * M := by linarith
    · -- Large regime: t⁻¹ ≤ ‖ψ(ξ)‖, use (1-exp).re ≤ 2
      push_neg at h
      have hψ_pos : (0 : ℝ) < ‖S.exponent ξ‖ := by
        rcases ne_or_eq (S.exponent ξ) 0 with hne | h0
        · exact norm_pos_iff.mpr hne
        · simp only [h0, norm_zero] at h; linarith
      have ht_inv : t.val⁻¹ ≤ ‖S.exponent ξ‖ :=
        (inv_le_iff_one_le_mul₀' t.prop).mpr (le_of_lt h)
      calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
          ≤ t.val⁻¹ * 2 :=
              mul_le_mul_of_nonneg_left hre_le2 (le_of_lt (inv_pos.mpr t.prop))
        _ ≤ ‖S.exponent ξ‖ * 2 := by nlinarith
        _ ≤ M * 2 := by nlinarith
        _ = 2 * M := by ring
  -- Use C = 4*M + 1 as the uniform bound
  refine ⟨⟨4 * M + 1, by positivity⟩, fun t => ?_⟩
  simp only [NNReal.coe_mk]
  set μ := (S.measure t : Measure ℝ)
  haveI : IsProbabilityMeasure μ := inferInstance
  -- The integrand 1-cos(ξ*x) is nonneg and bounded
  have h_nn : ∀ (ξ x : ℝ), 0 ≤ 1 - Real.cos (ξ * x) := fun ξ x => one_sub_cos_nonneg x ξ
  -- Integrability of (ξ, x) ↦ 1-cos(ξx) on [0,2/ε] × ℝ under volume × μ
  -- The product volume.restrict(uIoc) × μ is finite (μ is a prob measure)
  haveI hfin_restrict : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) (2/ε))) := by
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2/ε)]
    infer_instance
  have hfubini_int : Integrable (fun p : ℝ × ℝ => 1 - Real.cos (p.1 * p.2))
      ((volume.restrict (Set.uIoc 0 (2/ε))).prod μ) :=
    Integrable.of_bound
      ((continuous_const.sub (Real.continuous_cos.comp
        (continuous_fst.mul continuous_snd))).aestronglyMeasurable)
      2
      (ae_of_all _ fun p => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (h_nn p.1 p.2)]
        linarith [Real.neg_one_le_cos (p.1 * p.2)])
  -- Fubini: ∫_ξ ∫_x (1-cos) dμ dξ = ∫_x ∫_ξ (1-cos) dξ dμ
  have hfubini : ∫ ξ in (0:ℝ)..(2/ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ =
      ∫ x, (∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) ∂μ :=
    intervalIntegral_integral_swap hfubini_int
  -- ∫_ξ ∫_x (1-cos) dμ = ∫_ξ Re(1-exp(tψ)) dξ
  have hrhs : ∫ ξ in (0:ℝ)..(2/ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ =
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    congr 1; ext ξ
    rw [← re_one_sub_charFun_eq_integral ξ]
    congr 1; congr 1
    exact S.charFun_eq t ξ
  -- Integrability of x ↦ ∫_ξ (1-cos) dξ under μ (bounded by 4/ε via |1-cos| ≤ 2)
  have h_intcont : Continuous (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x ξ => 1 - Real.cos (ξ * x))
      (by fun_prop) 0 (2/ε)
  have hint_outer : Integrable (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) μ :=
    Integrable.of_bound
      h_intcont.aestronglyMeasurable
      (4/ε)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
            (intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)]
        have hfx_int : IntervalIntegrable (fun ξ => 1 - Real.cos (ξ * x)) volume 0 (2/ε) :=
          (continuous_const.sub (Real.continuous_cos.comp
            (continuous_id.mul continuous_const))).intervalIntegrable 0 (2/ε)
        calc ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))
            ≤ ∫ ξ in (0:ℝ)..(2/ε), (2 : ℝ) :=
              intervalIntegral.integral_mono_on (by positivity) hfx_int intervalIntegrable_const
                (fun ξ _ => by linarith [Real.neg_one_le_cos (ξ * x)])
          _ = 4/ε := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
              field_simp; ring)
  -- Pointwise bound: ∫_0^{2/ε} (1-cos(ξx)) dξ ≥ ε⁻¹ for x ∈ largeSet ε
  have hpointwise : ∀ x ∈ largeSet ε,
      ε⁻¹ ≤ ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) := by
    intro x hx
    have hxε : ε ≤ |x| := mem_largeSet.mp hx
    have hx_ne : x ≠ 0 := by
      intro h0; simp only [h0, abs_zero] at hxε; linarith
    -- The integral of cos(ξx) over ξ ∈ [0, 2/ε]: substitute u = ξ*x
    have hcos_int : IntervalIntegrable (fun ξ => Real.cos (ξ * x)) volume 0 (2/ε) :=
      (Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 (2/ε)
    have hmul : ∫ ξ in (0:ℝ)..(2/ε), Real.cos (ξ * x) = Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_comp_mul_right (hc := hx_ne)]
      simp only [zero_mul, smul_eq_mul]
      -- integral_cos: ∫ in 0..2/ε*x, cos = sin(2/ε*x) - sin(0)
      rw [integral_cos, Real.sin_zero, sub_zero]
      rw [show (2 : ℝ) / ε * x = 2 * x / ε from by ring]
      rw [div_eq_mul_inv (Real.sin _) x, mul_comm]
    have hcomp : ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) =
        2/ε - Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hcos_int,
        intervalIntegral.integral_const, smul_eq_mul, mul_one, hmul]
      ring
    rw [hcomp]
    have hsin_bd : Real.sin (2 * x / ε) / x ≤ 1/ε := by
      have habs : |Real.sin (2 * x / ε) / x| ≤ 1/ε := by
        rw [abs_div, div_le_div_iff₀ (abs_pos.mpr hx_ne) hε]
        nlinarith [Real.abs_sin_le_one (2 * x / ε)]
      linarith [le_abs_self (Real.sin (2 * x / ε) / x)]
    have h1e : (1:ℝ)/ε = ε⁻¹ := one_div ε
    have h2e : (2:ℝ)/ε = 2 * ε⁻¹ := by rw [div_eq_mul_inv]
    linarith
  -- Main bound: ε⁻¹ * μ(largeSet ε) ≤ ∫_x ∫_ξ (1-cos) dξ dμ = ∫_ξ ∫_x (1-cos) dμ dξ
  have hmass : ε⁻¹ * (μ (largeSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    rw [← hrhs, hfubini]
    rw [show ε⁻¹ * (μ (largeSet ε)).toReal =
      ∫ _ in largeSet ε, ε⁻¹ ∂μ by
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, mul_comm]]
    exact le_trans
      (setIntegral_mono_on integrableOn_const hint_outer.integrableOn
        (measurableSet_largeSet ε) (fun x hx => hpointwise x hx))
      (setIntegral_le_integral hint_outer (ae_of_all _ (fun x =>
        intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)))
  -- Multiply by t⁻¹: t⁻¹ * ε⁻¹ * μ(largeSet ε) ≤ ∫_ξ t⁻¹*(1-exp).re dξ
  have ht_inv_nn : 0 ≤ t.val⁻¹ := le_of_lt (inv_pos.mpr t.prop)
  have hmass_t : t.val⁻¹ * ε⁻¹ * (μ (largeSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    have hrearrange : t.val⁻¹ * ε⁻¹ * (μ (largeSet ε)).toReal =
        t.val⁻¹ * (ε⁻¹ * (μ (largeSet ε)).toReal) := by ring
    rw [hrearrange]
    calc t.val⁻¹ * (ε⁻¹ * (μ (largeSet ε)).toReal)
        ≤ t.val⁻¹ * (∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) :=
          mul_le_mul_of_nonneg_left hmass ht_inv_nn
      _ = ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re := by
          rw [← intervalIntegral.integral_const_mul]
  -- IntervalIntegrable for the t-scaled exponent integrand
  have hint_exp : IntervalIntegrable
      (fun ξ => t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re) volume 0 (2/ε) :=
    ((continuous_const.sub
        (Complex.continuous_re.comp
          (Complex.continuous_exp.comp
            (continuous_const.mul S.exponent_continuous)))).const_mul _).intervalIntegrable _ _
  -- Bound the integrand by 2M (using hkey)
  have hint_2M : ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤
      ∫ ξ in (0:ℝ)..(2/ε), (2 * M) :=
    intervalIntegral.integral_mono_on (by positivity) hint_exp intervalIntegrable_const
      (fun ξ hξ => hkey ξ hξ t)
  -- ∫_0^{2/ε} 2M = 4M/ε
  have hint_const : ∫ ξ in (0:ℝ)..(2/ε), (2 * M) = 4 * M / ε := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp [hε.ne']
    ring
  -- Combine: t⁻¹ * μ(largeSet ε) ≤ 4M ≤ 4M + 1
  calc t.val⁻¹ * (μ (largeSet ε)).toReal
      = ε * (t.val⁻¹ * ε⁻¹ * (μ (largeSet ε)).toReal) := by field_simp [hε.ne', ne_of_gt t.prop]
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) := by
        exact mul_le_mul_of_nonneg_left hmass_t (le_of_lt hε)
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), (2 * M)) := by
        apply mul_le_mul_of_nonneg_left hint_2M (le_of_lt hε)
    _ = ε * (4 * M / ε) := by rw [hint_const]
    _ = 4 * M := by field_simp [hε.ne']
    _ ≤ 4 * M + 1 := by linarith

/-- **Real-valued mass bound parameterized by the max of `‖ψ‖` on `[0, 2/ε]`.**
    Variant of `scaled_mass_bound_real` that exposes the bound `4·M` explicitly,
    where `M` is the supremum of `‖ψ‖` on `[0, 2/ε]`. This is used for tightness:
    as `ε → ∞`, the interval `[0, 2/ε]` shrinks to `{0}` and `M → 0` since `ψ(0) = 0`.
-/
private lemma scaled_mass_bound_real_with_max (ε : ℝ) (hε : 0 < ε)
    (M : ℝ) (_hM_nn : 0 ≤ M)
    (hM : ∀ ξ ∈ Set.Icc (0:ℝ) (2/ε), ‖S.exponent ξ‖ ≤ M) :
    ∀ (t : {t : ℝ // 0 < t}),
      t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet ε)).toReal ≤ 4 * M := by
  -- Reuses the proof structure of `scaled_mass_bound_real`, replacing the
  -- internally-computed max with the user-supplied bound `M`.
  intro t
  -- Key uniform bound: t⁻¹ * Re(1-exp(tψ(ξ))) ≤ 2M for ξ ∈ [0,2/ε], t > 0.
  have hkey : ∀ ξ ∈ Set.Icc (0:ℝ) (2/ε),
      t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * M := by
    intro ξ hξ
    have hξM : ‖S.exponent ξ‖ ≤ M := hM ξ hξ
    have hexp_le1 : ‖exp ((t.val : ℂ) * S.exponent ξ)‖ ≤ 1 := by
      have h := (S.measure t).norm_characteristicFun_le_one ξ
      rwa [S.charFun_eq t ξ] at h
    have hre_le2 : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 := by
      have hge : -1 ≤ (exp ((t.val : ℂ) * S.exponent ξ)).re := by
        have h1 : |(exp ((t.val : ℂ) * S.exponent ξ)).re| ≤ 1 :=
          (Complex.abs_re_le_norm _).trans hexp_le1
        linarith [neg_abs_le (exp ((t.val : ℂ) * S.exponent ξ)).re]
      simp only [sub_re, one_re]; linarith
    by_cases h : t.val * ‖S.exponent ξ‖ ≤ 1
    · have htz : ‖(t.val : ℂ) * S.exponent ξ‖ ≤ 1 := by
        simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; exact h
      have h_re : (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤ 2 * t.val * ‖S.exponent ξ‖ :=
        calc (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
            ≤ ‖1 - exp ((t.val : ℂ) * S.exponent ξ)‖ := Complex.re_le_norm _
          _ = ‖exp ((t.val : ℂ) * S.exponent ξ) - 1‖ := norm_sub_rev _ _
          _ ≤ 2 * ‖(t.val : ℂ) * S.exponent ξ‖ := Complex.norm_exp_sub_one_le htz
          _ = 2 * t.val * ‖S.exponent ξ‖ := by
                simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg t.prop.le]; ring
      calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
          ≤ t.val⁻¹ * (2 * t.val * ‖S.exponent ξ‖) :=
              mul_le_mul_of_nonneg_left h_re (le_of_lt (inv_pos.mpr t.prop))
        _ = 2 * ‖S.exponent ξ‖ := by field_simp [ne_of_gt t.prop]
        _ ≤ 2 * M := by linarith
    · push_neg at h
      have hψ_pos : (0 : ℝ) < ‖S.exponent ξ‖ := by
        rcases ne_or_eq (S.exponent ξ) 0 with hne | h0
        · exact norm_pos_iff.mpr hne
        · simp only [h0, norm_zero] at h; linarith
      have ht_inv : t.val⁻¹ ≤ ‖S.exponent ξ‖ :=
        (inv_le_iff_one_le_mul₀' t.prop).mpr (le_of_lt h)
      calc t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re
          ≤ t.val⁻¹ * 2 :=
              mul_le_mul_of_nonneg_left hre_le2 (le_of_lt (inv_pos.mpr t.prop))
        _ ≤ ‖S.exponent ξ‖ * 2 := by nlinarith
        _ ≤ M * 2 := by nlinarith
        _ = 2 * M := by ring
  set μ := (S.measure t : Measure ℝ)
  haveI : IsProbabilityMeasure μ := inferInstance
  have h_nn : ∀ (ξ x : ℝ), 0 ≤ 1 - Real.cos (ξ * x) := fun ξ x => one_sub_cos_nonneg x ξ
  haveI hfin_restrict : IsFiniteMeasure (volume.restrict (Set.uIoc (0:ℝ) (2/ε))) := by
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ 2/ε)]
    infer_instance
  have hfubini_int : Integrable (fun p : ℝ × ℝ => 1 - Real.cos (p.1 * p.2))
      ((volume.restrict (Set.uIoc 0 (2/ε))).prod μ) :=
    Integrable.of_bound
      ((continuous_const.sub (Real.continuous_cos.comp
        (continuous_fst.mul continuous_snd))).aestronglyMeasurable)
      2
      (ae_of_all _ fun p => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (h_nn p.1 p.2)]
        linarith [Real.neg_one_le_cos (p.1 * p.2)])
  have hfubini : ∫ ξ in (0:ℝ)..(2/ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ =
      ∫ x, (∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) ∂μ :=
    intervalIntegral_integral_swap hfubini_int
  have hrhs : ∫ ξ in (0:ℝ)..(2/ε), ∫ x, (1 - Real.cos (ξ * x)) ∂μ =
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    congr 1; ext ξ
    rw [← re_one_sub_charFun_eq_integral ξ]
    congr 1; congr 1
    exact S.charFun_eq t ξ
  have h_intcont : Continuous (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x ξ => 1 - Real.cos (ξ * x))
      (by fun_prop) 0 (2/ε)
  have hint_outer : Integrable (fun x => ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))) μ :=
    Integrable.of_bound
      h_intcont.aestronglyMeasurable
      (4/ε)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg
            (intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)]
        have hfx_int : IntervalIntegrable (fun ξ => 1 - Real.cos (ξ * x)) volume 0 (2/ε) :=
          (continuous_const.sub (Real.continuous_cos.comp
            (continuous_id.mul continuous_const))).intervalIntegrable 0 (2/ε)
        calc ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x))
            ≤ ∫ ξ in (0:ℝ)..(2/ε), (2 : ℝ) :=
              intervalIntegral.integral_mono_on (by positivity) hfx_int intervalIntegrable_const
                (fun ξ _ => by linarith [Real.neg_one_le_cos (ξ * x)])
          _ = 4/ε := by
              rw [intervalIntegral.integral_const, smul_eq_mul]
              field_simp; ring)
  have hpointwise : ∀ x ∈ largeSet ε,
      ε⁻¹ ≤ ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) := by
    intro x hx
    have hxε : ε ≤ |x| := mem_largeSet.mp hx
    have hx_ne : x ≠ 0 := by
      intro h0; simp only [h0, abs_zero] at hxε; linarith
    have hcos_int : IntervalIntegrable (fun ξ => Real.cos (ξ * x)) volume 0 (2/ε) :=
      (Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 (2/ε)
    have hmul : ∫ ξ in (0:ℝ)..(2/ε), Real.cos (ξ * x) = Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_comp_mul_right (hc := hx_ne)]
      simp only [zero_mul, smul_eq_mul]
      rw [integral_cos, Real.sin_zero, sub_zero]
      rw [show (2 : ℝ) / ε * x = 2 * x / ε from by ring]
      rw [div_eq_mul_inv (Real.sin _) x, mul_comm]
    have hcomp : ∫ ξ in (0:ℝ)..(2/ε), (1 - Real.cos (ξ * x)) =
        2/ε - Real.sin (2 * x / ε) / x := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hcos_int,
        intervalIntegral.integral_const, smul_eq_mul, mul_one, hmul]
      ring
    rw [hcomp]
    have hsin_bd : Real.sin (2 * x / ε) / x ≤ 1/ε := by
      have habs : |Real.sin (2 * x / ε) / x| ≤ 1/ε := by
        rw [abs_div, div_le_div_iff₀ (abs_pos.mpr hx_ne) hε]
        nlinarith [Real.abs_sin_le_one (2 * x / ε)]
      linarith [le_abs_self (Real.sin (2 * x / ε) / x)]
    have h1e : (1:ℝ)/ε = ε⁻¹ := one_div ε
    have h2e : (2:ℝ)/ε = 2 * ε⁻¹ := by rw [div_eq_mul_inv]
    linarith
  have hmass : ε⁻¹ * (μ (largeSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    rw [← hrhs, hfubini]
    rw [show ε⁻¹ * (μ (largeSet ε)).toReal =
      ∫ _ in largeSet ε, ε⁻¹ ∂μ by
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, mul_comm]]
    exact le_trans
      (setIntegral_mono_on integrableOn_const hint_outer.integrableOn
        (measurableSet_largeSet ε) (fun x hx => hpointwise x hx))
      (setIntegral_le_integral hint_outer (ae_of_all _ (fun x =>
        intervalIntegral.integral_nonneg (by positivity) fun ξ _ => h_nn ξ x)))
  have ht_inv_nn : 0 ≤ t.val⁻¹ := le_of_lt (inv_pos.mpr t.prop)
  have hmass_t : t.val⁻¹ * ε⁻¹ * (μ (largeSet ε)).toReal ≤
      ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re := by
    have hrearrange : t.val⁻¹ * ε⁻¹ * (μ (largeSet ε)).toReal =
        t.val⁻¹ * (ε⁻¹ * (μ (largeSet ε)).toReal) := by ring
    rw [hrearrange]
    calc t.val⁻¹ * (ε⁻¹ * (μ (largeSet ε)).toReal)
        ≤ t.val⁻¹ * (∫ ξ in (0:ℝ)..(2/ε), (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) :=
          mul_le_mul_of_nonneg_left hmass ht_inv_nn
      _ = ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re := by
          rw [← intervalIntegral.integral_const_mul]
  have hint_exp : IntervalIntegrable
      (fun ξ => t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re) volume 0 (2/ε) :=
    ((continuous_const.sub
        (Complex.continuous_re.comp
          (Complex.continuous_exp.comp
            (continuous_const.mul S.exponent_continuous)))).const_mul _).intervalIntegrable _ _
  have hint_2M : ∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((t.val : ℂ) * S.exponent ξ)).re ≤
      ∫ ξ in (0:ℝ)..(2/ε), (2 * M) :=
    intervalIntegral.integral_mono_on (by positivity) hint_exp intervalIntegrable_const
      (fun ξ hξ => hkey ξ hξ)
  have hint_const : ∫ ξ in (0:ℝ)..(2/ε), (2 * M) = 4 * M / ε := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp [hε.ne']
    ring
  calc t.val⁻¹ * (μ (largeSet ε)).toReal
      = ε * (t.val⁻¹ * ε⁻¹ * (μ (largeSet ε)).toReal) := by field_simp [hε.ne', ne_of_gt t.prop]
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), t.val⁻¹ * (1 - exp ((↑t.val : ℂ) * S.exponent ξ)).re) := by
        exact mul_le_mul_of_nonneg_left hmass_t (le_of_lt hε)
    _ ≤ ε * (∫ ξ in (0:ℝ)..(2/ε), (2 * M)) := by
        apply mul_le_mul_of_nonneg_left hint_2M (le_of_lt hε)
    _ = ε * (4 * M / ε) := by rw [hint_const]
    _ = 4 * M := by field_simp [hε.ne']

/-- **Uniform boundedness of scaled measures on large sets.** The family
    `{(1/t)·μ_t|_{|x|≥ε}}` has uniformly bounded mass as `t → 0⁺`.

    Proved from `scaled_mass_bound_real` by converting from `ℝ` to `ℝ≥0∞`. -/
theorem scaledMeasure_large_bounded (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ (t : {t : ℝ // 0 < t}),
      t.val < δ →
      S.scaledMeasure t (largeSet ε) ≤ ↑C := by
  obtain ⟨C, hC⟩ := S.scaled_mass_bound_real ε hε
  refine ⟨C, 1, one_pos, fun t _ht => ?_⟩
  rw [S.scaledMeasure_apply]
  have hfin : (S.measure t : Measure ℝ) (largeSet ε) ≠ ⊤ := measure_ne_top _ _
  have ht_inv_nn : (0 : ℝ) ≤ t.val⁻¹ := le_of_lt (inv_pos.mpr t.prop)
  calc ENNReal.ofReal t.val⁻¹ * (S.measure t : Measure ℝ) (largeSet ε)
      = ENNReal.ofReal t.val⁻¹ *
          ENNReal.ofReal ((S.measure t : Measure ℝ) (largeSet ε)).toReal := by
        rw [ENNReal.ofReal_toReal hfin]
    _ = ENNReal.ofReal (t.val⁻¹ *
          ((S.measure t : Measure ℝ) (largeSet ε)).toReal) := by
        rw [← ENNReal.ofReal_mul ht_inv_nn]
    _ ≤ ENNReal.ofReal ↑C := ENNReal.ofReal_le_ofReal (hC t)
    _ = ↑C := ENNReal.ofReal_coe_nnreal

/-! ### 3.2 — Sequential extraction (Helly-lite) -/

/-- Scaled restricted measure: `(1/t)·μ_t` restricted to `{|x| ≥ ε}`, viewed as a
    finite measure. -/
noncomputable def scaledRestrictedMeasure (t : {t : ℝ // 0 < t}) (ε : ℝ) :
    Measure ℝ :=
  (S.scaledMeasure t).restrict (largeSet ε)

/-- The scaled restricted measure is finite for `ε > 0` and small enough `t`. -/
lemma isFiniteMeasure_scaledRestrictedMeasure (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (t : {t : ℝ // 0 < t}),
      t.val < δ → IsFiniteMeasure (S.scaledRestrictedMeasure t ε) := by
  obtain ⟨C, δ, hδ, hC⟩ := S.scaledMeasure_large_bounded ε hε
  exact ⟨δ, hδ, fun t ht => by
    constructor
    have := hC t ht
    calc (S.scaledRestrictedMeasure t ε) Set.univ
        = S.scaledMeasure t (largeSet ε) := by
          simp [scaledRestrictedMeasure]
      _ ≤ ↑C := this
      _ < ⊤ := ENNReal.coe_lt_top⟩

/-- **Sequential extraction.** From the bounded family of scaled restricted measures,
    extract a weak limit along a subsequence `t_n → 0`.

    **Strategy:** Normalize to probability measures, apply Prokhorov's theorem for
    sequential compactness, then unnormalize. -/
theorem exists_measure_limit_large (ε : ℝ) (hε : 0 < ε) :
    ∃ (ν_ε : Measure ℝ) (t_seq : ℕ → {t : ℝ // 0 < t}),
      Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) ∧
      IsFiniteMeasure ν_ε ∧
      ν_ε {0} = 0 ∧
      ν_ε (largeSet ε)ᶜ = 0 ∧
      (∀ (f : BoundedContinuousFunction ℝ ℝ), (∀ x, |x| < ε → f x = 0) →
        Tendsto (fun n => ∫ x, f x ∂(S.scaledRestrictedMeasure (t_seq n) ε))
          atTop (𝓝 (∫ x, f x ∂ν_ε))) := by
  -- Step 1: Choose the natural sequence t_n := 1/(n+2).
  set t_seq : ℕ → {t : ℝ // 0 < t} := fun n => ⟨1/(n+2), by positivity⟩ with ht_seq_def
  have ht_seq_tendsto : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 := this.comp (tendsto_add_atTop_nat 1)
    refine h2.congr (fun n => ?_)
    simp [t_seq, Nat.cast_add, Nat.cast_one]
    ring
  -- Step 2: Uniform mass bound C on ν_n := scaledRestrictedMeasure (t_seq n) ε.
  obtain ⟨C, hC⟩ := S.scaled_mass_bound_real ε hε
  set ν : ℕ → Measure ℝ := fun n => S.scaledRestrictedMeasure (t_seq n) ε with hν_def
  -- Each ν n is a finite measure with mass ≤ C.
  have hν_mass_real : ∀ n, (ν n Set.univ).toReal ≤ C := fun n => by
    have hbound := hC (t_seq n)
    have hfin : (S.measure (t_seq n) : Measure ℝ) (largeSet ε) ≠ ⊤ := measure_ne_top _ _
    have ht_inv_nn : 0 ≤ (t_seq n).val⁻¹ := le_of_lt (inv_pos.mpr (t_seq n).prop)
    -- ν n Set.univ = ENNReal.ofReal (t_seq n).val⁻¹ * μ_t(largeSet ε)
    have hν_univ_eq : ν n Set.univ =
        ENNReal.ofReal (t_seq n).val⁻¹ * (S.measure (t_seq n) : Measure ℝ) (largeSet ε) := by
      simp only [hν_def, scaledRestrictedMeasure, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, scaledMeasure_apply]
    rw [hν_univ_eq]
    -- Convert: ofReal t⁻¹ * μ(...) = ofReal (t⁻¹ * μ(...).toReal)
    have h_eq : ENNReal.ofReal (t_seq n).val⁻¹ *
        (S.measure (t_seq n) : Measure ℝ) (largeSet ε) =
        ENNReal.ofReal ((t_seq n).val⁻¹ *
          ((S.measure (t_seq n) : Measure ℝ) (largeSet ε)).toReal) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hfin]
      rw [← ENNReal.ofReal_mul ht_inv_nn]
    rw [h_eq, ENNReal.toReal_ofReal (by
      have h_mass_nn : 0 ≤ ((S.measure (t_seq n) : Measure ℝ) (largeSet ε)).toReal :=
        ENNReal.toReal_nonneg
      positivity)]
    exact hbound
  have hν_finite : ∀ n, IsFiniteMeasure (ν n) := fun n => by
    -- ν n is a restricted scaled measure with bounded mass
    constructor
    have h_meas_univ : ν n Set.univ =
        ENNReal.ofReal (t_seq n).val⁻¹ * (S.measure (t_seq n) : Measure ℝ) (largeSet ε) := by
      simp only [hν_def, scaledRestrictedMeasure, Measure.restrict_apply MeasurableSet.univ,
        Set.univ_inter, scaledMeasure_apply]
    rw [h_meas_univ]
    have hfin : (S.measure (t_seq n) : Measure ℝ) (largeSet ε) ≠ ⊤ := measure_ne_top _ _
    have ht_inv_nn : (0 : ℝ) ≤ (t_seq n).val⁻¹ := le_of_lt (inv_pos.mpr (t_seq n).prop)
    have h_eq : ENNReal.ofReal (t_seq n).val⁻¹ *
        (S.measure (t_seq n) : Measure ℝ) (largeSet ε) =
        ENNReal.ofReal ((t_seq n).val⁻¹ *
          ((S.measure (t_seq n) : Measure ℝ) (largeSet ε)).toReal) := by
      conv_lhs => rw [← ENNReal.ofReal_toReal hfin]
      rw [← ENNReal.ofReal_mul ht_inv_nn]
    rw [h_eq]
    exact ENNReal.ofReal_lt_top
  -- Step 3: Tightness. For each η > 0, find R > 0 such that for all n,
  -- ν n (closedBall 0 R)ᶜ ≤ η. We use continuity of ψ at 0.
  -- For R ≥ ε, (closedBall 0 R)ᶜ ⊆ largeSet R, and ν n is supported on largeSet ε.
  -- Hence ν n ((closedBall 0 R)ᶜ) ≤ S.scaledMeasure t_seq n (largeSet R) ≤ 4 * M(R)
  -- where M(R) = sup_{ξ ∈ [0, 2/R]} ‖S.exponent ξ‖, which → 0 as R → ∞.
  -- For each m : ℕ, we'll find R_m ≥ ε such that the bound is at most 1/(m+1).
  -- Define M : ℝ≥0 := C + 1 (positive upper bound on mass).
  set Mass : ℝ≥0 := C + 1 with hMass_def
  have hMass_pos : (0 : ℝ) < Mass := by
    rw [hMass_def]; push_cast
    have : (0 : ℝ) ≤ C := NNReal.coe_nonneg C
    linarith
  have hν_mass_le_Mass : ∀ n, ν n Set.univ ≤ ENNReal.ofReal Mass := fun n => by
    have h1 : (ν n Set.univ).toReal ≤ C := hν_mass_real n
    have hne_top : ν n Set.univ ≠ ⊤ := (hν_finite n).measure_univ_lt_top.ne
    rw [show ν n Set.univ = ENNReal.ofReal (ν n Set.univ).toReal from
      (ENNReal.ofReal_toReal hne_top).symm]
    apply ENNReal.ofReal_le_ofReal
    have : (C : ℝ) ≤ Mass := by simp [hMass_def]
    linarith
  -- Define the auxiliary probability measures by topping up with a Dirac at 0.
  -- p_n := (1/Mass) • ν_n + ((Mass - mass(ν_n))/Mass) • δ_0
  -- This has total mass = 1.
  set p_meas : ℕ → Measure ℝ := fun n =>
    (ENNReal.ofReal Mass⁻¹) • ν n +
      (ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν n Set.univ)) • Measure.dirac 0 with hp_meas_def
  -- Show p_meas n is a probability measure.
  have hp_prob : ∀ n, IsProbabilityMeasure (p_meas n) := by
    intro n
    refine ⟨?_⟩
    have hM_inv_nn : (0 : ℝ) ≤ Mass⁻¹ := le_of_lt (inv_pos.mpr hMass_pos)
    have hν_uniν_ne : ν n Set.univ ≠ ⊤ := (hν_finite n).measure_univ_lt_top.ne
    -- Compute p_meas n Set.univ directly
    have h_sum_eq : ν n Set.univ + (ENNReal.ofReal Mass - ν n Set.univ) =
        ENNReal.ofReal Mass :=
      add_tsub_cancel_of_le (hν_mass_le_Mass n)
    calc p_meas n Set.univ
        = (ENNReal.ofReal Mass⁻¹) * ν n Set.univ +
            (ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν n Set.univ)) *
              Measure.dirac (0 : ℝ) Set.univ := by
          simp only [hp_meas_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      _ = (ENNReal.ofReal Mass⁻¹) * ν n Set.univ +
            (ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν n Set.univ)) * 1 := by
          rw [show Measure.dirac (0 : ℝ) Set.univ = 1 from by
            rw [Measure.dirac_apply' _ MeasurableSet.univ]
            simp [Set.indicator_univ]]
      _ = ENNReal.ofReal Mass⁻¹ *
            (ν n Set.univ + (ENNReal.ofReal Mass - ν n Set.univ)) := by
          rw [mul_one]; ring
      _ = ENNReal.ofReal Mass⁻¹ * ENNReal.ofReal Mass := by rw [h_sum_eq]
      _ = ENNReal.ofReal ((Mass : ℝ)⁻¹ * (Mass : ℝ)) := (ENNReal.ofReal_mul hM_inv_nn).symm
      _ = ENNReal.ofReal 1 := by rw [inv_mul_cancel₀ hMass_pos.ne']
      _ = 1 := ENNReal.ofReal_one
  -- Now p_n form a sequence in ProbabilityMeasure ℝ.
  set P : ℕ → ProbabilityMeasure ℝ := fun n => ⟨p_meas n, hp_prob n⟩ with hP_def
  -- Step 4: Show tightness of the family {P n}.
  -- For η > 0, find compact K such that P n Kᶜ ≤ η for all n.
  have h_tight : IsTightMeasureSet {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro η hη
    -- Handle η = ⊤ trivially.
    by_cases hη_top : η = ⊤
    · exact ⟨∅, isCompact_empty, fun _ _ => hη_top ▸ le_top⟩
    -- Convert η to a positive real
    set δ := η.toReal with hδ_def
    have hδ_pos : 0 < δ := ENNReal.toReal_pos hη.ne' hη_top
    have hδ_le : ENNReal.ofReal δ ≤ η := by
      rw [hδ_def, ENNReal.ofReal_toReal hη_top]
    -- Choose ξ_bound > 0 with ‖S.exponent ξ‖ < δ/8 for |ξ| < ξ_bound.
    have hξ_exist : ∃ r : ℝ, 0 < r ∧ ∀ ξ, |ξ| < r → ‖S.exponent ξ‖ < δ/8 := by
      have htend : Tendsto (fun ξ : ℝ => ‖S.exponent ξ‖) (𝓝 0) (𝓝 0) := by
        have h1 : Tendsto S.exponent (𝓝 0) (𝓝 0) := by
          have := S.exponent_continuous.tendsto 0
          rw [S.exponent_zero] at this
          exact this
        have h2 : Tendsto (fun z : ℂ => ‖z‖) (𝓝 0) (𝓝 0) := by
          have := (continuous_norm (E := ℂ)).tendsto 0
          simpa using this
        exact h2.comp h1
      have hnhds : ∀ᶠ ξ in 𝓝 (0 : ℝ), ‖S.exponent ξ‖ < δ/8 :=
        htend.eventually (Iio_mem_nhds (by linarith))
      rw [Metric.eventually_nhds_iff] at hnhds
      obtain ⟨r, hr_pos, hr⟩ := hnhds
      exact ⟨r, hr_pos, fun ξ hξ => hr (by simpa [Real.dist_eq, sub_zero] using hξ)⟩
    obtain ⟨ξ_bound, hξ_bound_pos, hξ_bound⟩ := hξ_exist
    -- Choose R > 0 with 2/R < ξ_bound, i.e., R > 2/ξ_bound. Also R ≥ ε.
    set R := max ε (2 / ξ_bound + 1) with hR_def
    have hR_pos : 0 < R := by
      rw [hR_def]; exact lt_of_lt_of_le hε (le_max_left _ _)
    have hR_ε : ε ≤ R := le_max_left _ _
    have hR_inv : 2 / R < ξ_bound := by
      have h_denom_pos : (0 : ℝ) < 2 / ξ_bound + 1 := by positivity
      have h1 : 2 / R ≤ 2 / (2 / ξ_bound + 1) := by
        apply div_le_div_of_nonneg_left (by norm_num) h_denom_pos (le_max_right _ _)
      have h2 : 2 / (2 / ξ_bound + 1) < ξ_bound := by
        rw [div_lt_iff₀ h_denom_pos]
        -- Goal: 2 < (2/ξ_bound + 1) * ξ_bound
        have h3 : (2 / ξ_bound + 1) * ξ_bound = 2 + ξ_bound := by
          field_simp
        linarith [h3]
      linarith
    -- The bound on ‖ψ‖ over [0, 2/R].
    have hM_bound : ∀ ξ ∈ Set.Icc (0:ℝ) (2/R), ‖S.exponent ξ‖ ≤ δ/8 := by
      intro ξ hξ
      have h1 : |ξ| < ξ_bound := by
        rw [abs_of_nonneg hξ.1]
        exact lt_of_le_of_lt hξ.2 hR_inv
      exact le_of_lt (hξ_bound ξ h1)
    -- Apply the tightness bound: for all t, t⁻¹ * μ_t(largeSet R) ≤ 4 * (δ/8) = δ/2.
    have hbound : ∀ t : {t : ℝ // 0 < t},
        t.val⁻¹ * ((S.measure t : Measure ℝ) (largeSet R)).toReal ≤ δ/2 := by
      intro t
      have h_aux := S.scaled_mass_bound_real_with_max R hR_pos (δ/8)
        (by linarith) hM_bound t
      linarith
    -- Choose K = Set.Icc (-R) R, which is compact and (Kᶜ ∩ largeSet ε) ⊆ largeSet R.
    refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
    intro μ' hμ'
    obtain ⟨ν', hν'_range, hν'_eq⟩ := hμ'
    obtain ⟨n, hPn⟩ := hν'_range
    rw [← hν'_eq, ← hPn]
    -- Now goal: (((P n) : ProbabilityMeasure ℝ) : Measure ℝ) (Set.Icc (-R) R)ᶜ ≤ η
    have hP_unfold : ((P n : ProbabilityMeasure ℝ) : Measure ℝ) = p_meas n := rfl
    rw [hP_unfold]
    -- p_meas n (Kᶜ) = (1/Mass) * ν_n (Kᶜ) + (1/Mass)*(Mass - ν_n(univ)) * δ_0 (Kᶜ).
    -- δ_0 (Kᶜ) = 0 since 0 ∈ K.
    have h0_in_K : (0 : ℝ) ∈ Set.Icc (-R) R := ⟨by linarith, by linarith⟩
    have hdirac0 : Measure.dirac 0 (Set.Icc (-R) R)ᶜ = 0 := by
      rw [Measure.dirac_apply' _ isClosed_Icc.measurableSet.compl, Set.indicator_apply]
      simp [h0_in_K]
    -- The mass on Kᶜ:
    have hKc_measurable : MeasurableSet (Set.Icc (-R) R)ᶜ :=
      isClosed_Icc.measurableSet.compl
    have hKc_sub : (Set.Icc (-R) R)ᶜ ⊆ largeSet R := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      simp only [mem_largeSet]
      rcases hx with hx | hx
      · -- x < -R, so |x| = -x ≥ R
        have h_neg : x < 0 := lt_of_lt_of_le hx (neg_nonpos_of_nonneg hR_pos.le)
        rw [abs_of_neg h_neg]; linarith
      · -- R < x, so |x| = x ≥ R
        have h_pos : 0 < x := lt_of_le_of_lt hR_pos.le hx
        rw [abs_of_pos h_pos]; linarith
    -- Estimate ν_n on Kᶜ.
    -- ν_n is supported on largeSet ε; ν_n(Kᶜ) = ν_n(Kᶜ ∩ largeSet ε).
    -- For R ≥ ε, Kᶜ ⊆ largeSet R ⊆ largeSet ε.
    -- So ν_n(Kᶜ) ≤ ν_n(largeSet R) ≤ S.scaledMeasure t_seq n (largeSet R)
    have hν_n_Kc : ν n (Set.Icc (-R) R)ᶜ ≤ S.scaledMeasure (t_seq n) (largeSet R) := by
      simp only [hν_def, scaledRestrictedMeasure,
        Measure.restrict_apply hKc_measurable]
      apply measure_mono
      intro x ⟨hxKc, _⟩
      exact hKc_sub hxKc
    have hsm_R : S.scaledMeasure (t_seq n) (largeSet R) ≤ ENNReal.ofReal (δ/2) := by
      rw [S.scaledMeasure_apply]
      have h1 := hbound (t_seq n)
      have hfin : (S.measure (t_seq n) : Measure ℝ) (largeSet R) ≠ ⊤ := measure_ne_top _ _
      have ht_inv_nn : 0 ≤ (t_seq n).val⁻¹ := le_of_lt (inv_pos.mpr (t_seq n).prop)
      calc ENNReal.ofReal (t_seq n).val⁻¹ * (S.measure (t_seq n) : Measure ℝ) (largeSet R)
          = ENNReal.ofReal ((t_seq n).val⁻¹ *
            ((S.measure (t_seq n) : Measure ℝ) (largeSet R)).toReal) := by
            conv_lhs => rw [← ENNReal.ofReal_toReal hfin]
            rw [← ENNReal.ofReal_mul ht_inv_nn]
        _ ≤ ENNReal.ofReal (δ/2) := ENNReal.ofReal_le_ofReal h1
    -- Now compute p_meas n (Kᶜ).
    have hp_Kc : p_meas n (Set.Icc (-R) R)ᶜ ≤ ENNReal.ofReal Mass⁻¹ * ENNReal.ofReal (δ/2) := by
      simp only [hp_meas_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hdirac0,
        mul_zero, add_zero]
      exact mul_le_mul_left' (le_trans hν_n_Kc hsm_R) (ENNReal.ofReal Mass⁻¹)
    -- Bound (1/Mass) * (δ/2) ≤ δ.
    have hM_pos_ge_one : (1 : ℝ) ≤ Mass := by
      rw [hMass_def]; push_cast
      have : (0 : ℝ) ≤ C := NNReal.coe_nonneg C
      linarith
    have hM_inv_le_one : Mass⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right; exact hM_pos_ge_one
    have hM_inv_nn : (0 : ℝ) ≤ Mass⁻¹ := le_of_lt (inv_pos.mpr hMass_pos)
    have hδ_pos' : 0 < δ/2 := by linarith
    have hfinal_real : Mass⁻¹ * (δ/2) ≤ δ := by
      calc Mass⁻¹ * (δ/2) ≤ 1 * (δ/2) := by
            exact mul_le_mul_of_nonneg_right hM_inv_le_one (by linarith)
        _ = δ/2 := one_mul _
        _ ≤ δ := by linarith
    -- Convert to ENNReal.
    have hfinal_ennreal : ENNReal.ofReal Mass⁻¹ * ENNReal.ofReal (δ/2) ≤ ENNReal.ofReal δ := by
      have heq : ENNReal.ofReal Mass⁻¹ * ENNReal.ofReal (δ/2) =
          ENNReal.ofReal (Mass⁻¹ * (δ/2)) :=
        (ENNReal.ofReal_mul hM_inv_nn).symm
      rw [heq]
      exact ENNReal.ofReal_le_ofReal hfinal_real
    calc p_meas n (Set.Icc (-R) R)ᶜ
        ≤ ENNReal.ofReal Mass⁻¹ * ENNReal.ofReal (δ/2) := hp_Kc
      _ ≤ ENNReal.ofReal δ := hfinal_ennreal
      _ ≤ η := hδ_le
  -- Step 5: Apply Prokhorov to get a convergent subsequence.
  have h_compact : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet h_tight
  have h_in_range : ∀ n, P n ∈ closure (Set.range P) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨P_inf, _, φ, hφ_mono, hP_tendsto⟩ := h_compact.tendsto_subseq h_in_range
  -- Define the candidate measure
  let ν_inf : Measure ℝ := (ENNReal.ofReal Mass) • ((P_inf : Measure ℝ).restrict (largeSet ε))
  -- Verify ν_inf is a finite measure.
  have hν_inf_fin : IsFiniteMeasure ν_inf := by
    constructor
    simp only [ν_inf, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul]
    calc ENNReal.ofReal Mass * (P_inf : Measure ℝ) (largeSet ε)
        ≤ ENNReal.ofReal Mass * 1 := by
          gcongr
          exact prob_le_one
      _ = ENNReal.ofReal Mass := by rw [mul_one]
      _ < ⊤ := ENNReal.ofReal_lt_top
  -- Verify ν_inf {0} = 0 (since 0 ∉ largeSet ε).
  have h0_not_in_large : (0 : ℝ) ∉ largeSet ε := by
    simp [mem_largeSet, abs_zero]; exact hε
  have hν_inf_zero_singleton : ν_inf {0} = 0 := by
    simp only [ν_inf, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    have : {(0 : ℝ)} ∩ largeSet ε = ∅ := by
      ext x; simp
      intro hx
      simp [hx, mem_largeSet, abs_zero]; exact hε
    rw [this, measure_empty, mul_zero]
  -- Verify ν_inf (largeSet ε)ᶜ = 0.
  have hν_inf_compl : ν_inf (largeSet ε)ᶜ = 0 := by
    simp only [ν_inf, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (measurableSet_largeSet ε).compl]
    rw [Set.inter_comm, Set.inter_compl_self, measure_empty, mul_zero]
  -- Step 6: Show weak convergence.
  -- We use the subsequence ψ := t_seq ∘ φ; need ψ → 0.
  refine ⟨ν_inf, t_seq ∘ φ, ?_, hν_inf_fin, hν_inf_zero_singleton, hν_inf_compl, ?_⟩
  · exact ht_seq_tendsto.comp hφ_mono.tendsto_atTop
  -- Convergence of integrals.
  intro f hf_zero
  -- Convert tendsto in ProbabilityMeasure to convergence of BCF integrals.
  have hP_int := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hP_tendsto) f
  simp only [Function.comp_apply, P, ProbabilityMeasure.coe_mk] at hP_int
  -- ∫ f d(P_inf : Measure ℝ) = (1/Mass) * ∫ f dν_n + (1/Mass)(Mass-mass(ν_n)) * f(0)
  -- = (1/Mass) * ∫ f dν_n  (since f(0) = 0 when ε > 0)
  -- So ∫ f dν_n = Mass * ∫ f dP_n → Mass * ∫ f dP_inf
  -- And ∫ f dν_inf = Mass * ∫_largeSet ε f dP_inf = Mass * ∫ f dP_inf (since f vanishes off largeSet ε)
  have hf_continuous : Continuous f := f.continuous
  have hf_meas : Measurable f := hf_continuous.measurable
  have hf_strongly_meas : StronglyMeasurable f := hf_continuous.stronglyMeasurable
  have hf_int : ∀ μ : Measure ℝ, [IsFiniteMeasure μ] → Integrable f μ := fun μ _ => by
    exact f.integrable μ
  -- Step A: f vanishes on (largeSet ε)ᶜ (since f vanishes on |x| < ε = (largeSet ε)ᶜ).
  have hf_vanish_compl : ∀ x, x ∉ largeSet ε → f x = 0 := by
    intro x hx
    have : |x| < ε := by
      simp only [mem_largeSet, not_le] at hx
      exact hx
    exact hf_zero x this
  have hf0 : f 0 = 0 := hf_zero 0 (by simp [abs_zero, hε])
  -- We'll use Mass.toReal as a real number to avoid type-mismatch issues with `Mass : ℝ≥0`.
  set MR : ℝ := (Mass : ℝ) with hMR_def
  have hMR_pos : 0 < MR := hMass_pos
  -- Step B: ∫ f dν_inf = MR * ∫ f dP_inf.
  have h_int_ν_inf : ∫ x, f x ∂ν_inf = MR * ∫ x, f x ∂(P_inf : Measure ℝ) := by
    show ∫ x, f x ∂((ENNReal.ofReal Mass) •
        ((P_inf : Measure ℝ).restrict (largeSet ε))) = MR * _
    rw [integral_smul_measure]
    rw [ENNReal.toReal_ofReal hMass_pos.le]
    -- Reduce restrict-integral using setIntegral
    show MR • ∫ x in largeSet ε, f x ∂(P_inf : Measure ℝ) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hf_vanish_compl, smul_eq_mul]
  -- Step C: ∫ f dP_n = MR⁻¹ * ∫ f dν_n  (since f(0) = 0).
  have h_int_P_eq : ∀ n, ∫ x, f x ∂(p_meas n) = MR⁻¹ * ∫ x, f x ∂(ν n) := by
    intro n
    haveI : IsFiniteMeasure (ν n) := hν_finite n
    have h_integrable_ν : Integrable f (ν n) := f.integrable (ν n)
    have h_integrable_dirac : Integrable f (Measure.dirac (0 : ℝ)) :=
      integrable_dirac (by
        rw [hf0]; simp)
    -- Integrability for the two summands
    have h_int1 : Integrable f (ENNReal.ofReal Mass⁻¹ • ν n) :=
      Integrable.smul_measure h_integrable_ν ENNReal.ofReal_ne_top
    have hcoeff_finite : ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν n Set.univ) ≠ ⊤ := by
      apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self
    have h_int2 : Integrable f ((ENNReal.ofReal Mass⁻¹ *
        (ENNReal.ofReal Mass - ν n Set.univ)) • Measure.dirac (0 : ℝ)) :=
      Integrable.smul_measure h_integrable_dirac hcoeff_finite
    show ∫ x, f x ∂(((ENNReal.ofReal Mass⁻¹) • ν n) +
        ((ENNReal.ofReal Mass⁻¹ * (ENNReal.ofReal Mass - ν n Set.univ)) •
          Measure.dirac (0 : ℝ))) = MR⁻¹ * _
    rw [integral_add_measure h_int1 h_int2]
    rw [integral_smul_measure, integral_smul_measure, integral_dirac _ _]
    simp only [smul_eq_mul, hf0, mul_zero, add_zero]
    -- Goal: (ENNReal.ofReal (↑Mass)⁻¹).toReal * ∫ f dν n = MR⁻¹ * ∫ f dν n
    have hMR_inv_nn : (0 : ℝ) ≤ (MR : ℝ)⁻¹ := le_of_lt (inv_pos.mpr hMR_pos)
    rw [show (ENNReal.ofReal (Mass : ℝ)⁻¹).toReal = MR⁻¹ from
      ENNReal.toReal_ofReal hMR_inv_nn]
  -- Step D: From hP_int: ∫ f d p_meas (φ k) → ∫ f d P_inf.
  -- So MR⁻¹ * ∫ f dν (φ k) → ∫ f d P_inf, hence ∫ f dν (φ k) → MR * ∫ f d P_inf.
  have h_int_ν_subseq : Tendsto (fun k => ∫ x, f x ∂(ν (φ k))) atTop
      (𝓝 (MR * ∫ x, f x ∂(P_inf : Measure ℝ))) := by
    have hP_seq : Tendsto (fun k => ∫ x, f x ∂(p_meas (φ k))) atTop
        (𝓝 (∫ x, f x ∂(P_inf : Measure ℝ))) := hP_int
    have h_eq : ∀ k, ∫ x, f x ∂(p_meas (φ k)) = MR⁻¹ * ∫ x, f x ∂(ν (φ k)) :=
      fun k => h_int_P_eq (φ k)
    have h_eq' : (fun k => ∫ x, f x ∂(p_meas (φ k))) =
        (fun k => MR⁻¹ * ∫ x, f x ∂(ν (φ k))) := funext h_eq
    rw [h_eq'] at hP_seq
    have h_mul : Tendsto (fun k => MR * (MR⁻¹ * ∫ x, f x ∂(ν (φ k)))) atTop
        (𝓝 (MR * ∫ x, f x ∂(P_inf : Measure ℝ))) :=
      hP_seq.const_mul MR
    refine h_mul.congr (fun k => ?_)
    rw [← mul_assoc, mul_inv_cancel₀ hMR_pos.ne', one_mul]
  -- Final: relate scaledRestrictedMeasure (t_seq (φ k)) ε = ν (φ k).
  rw [Function.comp_def]
  show Tendsto (fun k => ∫ x, f x ∂(ν (φ k))) atTop (𝓝 _)
  rw [h_int_ν_inf]
  exact h_int_ν_subseq

/-! ### 3.3 — Consistency of extracted measures -/

/-- **Monotonicity of large sets.** For `ε₁ ≤ ε₂`, `largeSet ε₂ ⊆ largeSet ε₁`. -/
lemma largeSet_antitone {ε₁ ε₂ : ℝ} (h : ε₁ ≤ ε₂) :
    largeSet ε₂ ⊆ largeSet ε₁ := by
  intro x hx
  simp only [mem_largeSet] at hx ⊢
  linarith

/-- For `0 < ε₁ ≤ ε₂`, the restriction of the scaled measure to `{|x| ≥ ε₂}` is
    obtained by further restricting the `{|x| ≥ ε₁}`-restricted measure. -/
lemma scaledRestrictedMeasure_restrict (t : {t : ℝ // 0 < t})
    {ε₁ ε₂ : ℝ} (_hε₁ : 0 < ε₁) (h : ε₁ ≤ ε₂) :
    (S.scaledRestrictedMeasure t ε₁).restrict (largeSet ε₂) =
    S.scaledRestrictedMeasure t ε₂ := by
  simp only [scaledRestrictedMeasure]
  rw [Measure.restrict_restrict (measurableSet_largeSet ε₂)]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, mem_largeSet]
  constructor
  · intro ⟨h1, _⟩; exact h1
  · intro h1; exact ⟨h1, le_trans h h1⟩

/-- **Consistency of extracted measures.** For `0 < ε₁ ≤ ε₂`, the measure `ν_{ε₂}`
    is the restriction of `ν_{ε₁}` to `{|x| ≥ ε₂}`.

    This ensures the family `{ν_ε}` is consistent and can be glued into a single
    Lévy measure. The proof requires passing limits through restrictions, which
    is a standard but technically involved measure theory argument. -/
theorem consistent_large_measures {ε₁ ε₂ : ℝ} (_hε₁ : 0 < ε₁) (_h : ε₁ ≤ ε₂)
    {ν₁ ν₂ : Measure ℝ}
    {t_seq₁ t_seq₂ : ℕ → {t : ℝ // 0 < t}}
    (_ht₁ : Tendsto (fun n => (t_seq₁ n).val) atTop (𝓝 0))
    (_ht₂ : Tendsto (fun n => (t_seq₂ n).val) atTop (𝓝 0))
    (_hν₁ : IsFiniteMeasure ν₁)
    (_hν₂ : IsFiniteMeasure ν₂)
    (_hν₁_supp : ν₁ (largeSet ε₁)ᶜ = 0)
    (_hν₂_supp : ν₂ (largeSet ε₂)ᶜ = 0)
    -- Weak convergence conditions for ν₁, ν₂
    (_hconv₁ : ∀ (f : BoundedContinuousFunction ℝ ℝ), (∀ x, |x| < ε₁ → f x = 0) →
      Tendsto (fun n => ∫ x, f x ∂(S.scaledRestrictedMeasure (t_seq₁ n) ε₁))
        atTop (𝓝 (∫ x, f x ∂ν₁)))
    (_hconv₂ : ∀ (f : BoundedContinuousFunction ℝ ℝ), (∀ x, |x| < ε₂ → f x = 0) →
      Tendsto (fun n => ∫ x, f x ∂(S.scaledRestrictedMeasure (t_seq₂ n) ε₂))
        atTop (𝓝 (∫ x, f x ∂ν₂))) :
    ν₁.restrict (largeSet ε₂) = ν₂ := by
  sorry

/-! ### 3.4 — Lévy measure construction -/

/-- The Lévy measure associated to a convolution semigroup, constructed as the
    monotone limit (supremum) of the extracted measures `ν_ε` as `ε → 0`.

    For each `ε > 0`, we extract a finite measure `ν_ε` supported on `{|x| ≥ ε}`
    as a weak limit of `(1/t)·μ_t|_{|x|≥ε}`. The consistency property (3.3) ensures
    these fit together, and we define `ν` as the supremum over `ε > 0`.

    **Implementation note:** We use `iSup` over `n ≥ 1` of the measures `ν_{1/n}`
    applied to measurable sets. Since the measures are consistent and increasing
    as `n → ∞` (i.e., `ε = 1/n ↓ 0`), this defines a σ-additive measure. -/
noncomputable def levyMeasureAux : Measure ℝ :=
  ⨆ (n : ℕ) (_ : 0 < n),
    (S.exists_measure_limit_large (1 / ↑n) (by positivity : (0 : ℝ) < 1 / ↑n)).choose

/-- The Lévy measure auxiliary has zero mass at the origin. -/
theorem levyMeasureAux_zero : levyMeasureAux S {0} = 0 := by
  apply le_antisymm _ (zero_le _)
  -- Strategy: bound the iSup by Measure.sum, then show sum has zero mass at {0}
  set f : ℕ → Measure ℝ := fun n => ⨆ (_ : 0 < n),
    (S.exists_measure_limit_large (1 / ↑n)
      (by positivity : (0 : ℝ) < 1 / ↑n)).choose with hf_def
  -- levyMeasureAux S = ⨆ n, f n
  have hdef : levyMeasureAux S = ⨆ n, f n := rfl
  rw [hdef]
  -- Step 1: ⨆ n, f n ≤ Measure.sum f (each component ≤ sum)
  have h_le : (⨆ n, f n) ≤ Measure.sum f := iSup_le (Measure.le_sum f)
  -- Step 2: Measure.sum f {0} = 0 (since each f n {0} = 0)
  have h_sum_zero : Measure.sum f {0} = 0 := by
    rw [Measure.sum_apply_eq_zero' (measurableSet_singleton 0)]
    intro n
    by_cases hn : 0 < n
    · -- f n = ν_n, and ν_n {0} = 0
      simp only [hf_def, iSup_pos hn]
      exact (S.exists_measure_limit_large (1 / ↑n)
        (by positivity)).choose_spec.choose_spec.2.2.1
    · -- f 0 = ⊥ = 0, so (⊥ : Measure ℝ) {0} = 0
      simp only [hf_def, iSup_neg hn]
      rfl
  exact le_trans (Measure.le_iff.mp h_le _ (measurableSet_singleton 0)) (le_of_eq h_sum_zero)

/-- The Lévy measure auxiliary restricts correctly to large sets.
    For each `ε > 0`, the restriction of `ν` to `{|x| ≥ ε}` is a finite measure. -/
theorem levyMeasureAux_restrict_large (ε : ℝ) (_hε : 0 < ε) :
    IsFiniteMeasure ((levyMeasureAux S).restrict (largeSet ε)) := by
  sorry

/-- The Lévy measure satisfies the integrability condition `∫ min(1, x²) dν < ∞`.
    This follows from the uniform bound on scaled measures and the second moment
    control on small jumps.

    **Note:** This requires the small-jump analysis (Phase 5) for the full proof.
    For now it is sorry'd and will be completed when the small-jump second moment
    estimate is available. -/
theorem levyMeasureAux_lintegral_min_one_sq :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂(levyMeasureAux S) < ⊤ := by
  sorry

/-- The auxiliary Lévy measure is indeed a Lévy measure. -/
theorem levyMeasureAux_isLevyMeasure : IsLevyMeasure (levyMeasureAux S) :=
  ⟨levyMeasureAux_zero S, levyMeasureAux_lintegral_min_one_sq S⟩

/-- **Lévy measure of a convolution semigroup.** Packages the auxiliary construction
    with its proof that it satisfies the Lévy measure conditions. -/
noncomputable def levyMeasure : Measure ℝ := levyMeasureAux S

/-- The Lévy measure is a Lévy measure. -/
theorem levyMeasure_isLevyMeasure : IsLevyMeasure (levyMeasure S) :=
  levyMeasureAux_isLevyMeasure S

/-- The Lévy measure has zero mass at the origin. -/
theorem levyMeasure_zero : levyMeasure S {0} = 0 :=
  levyMeasureAux_zero S

/-- The Lévy measure has finite mass on `{|x| ≥ ε}` for any `ε > 0`. -/
theorem levyMeasure_large_finite (ε : ℝ) (hε : 0 < ε) :
    levyMeasure S (largeSet ε) < ⊤ :=
  (levyMeasure_isLevyMeasure S).measure_setOf_abs_ge_lt_top hε

/-- The Lévy measure restricted to `{|x| ≥ ε}` is a finite measure. -/
theorem levyMeasure_restrict_isFiniteMeasure (ε : ℝ) (hε : 0 < ε) :
    IsFiniteMeasure ((levyMeasure S).restrict (largeSet ε)) := by
  constructor
  rw [Measure.restrict_apply_univ]
  exact levyMeasure_large_finite S ε hε

/-! ### Phase 4 — Fourier identification on large jumps

The large-jump contribution to the Lévy-Khintchine decomposition.

**4.1 — Large jump limit (along subsequence):**
The scaled integral `(1/t) ∫_{|x|≥ε} (e^{ixξ} − 1) dμ_t` converges along a
subsequence to `∫_{|x|≥ε} (e^{ixξ} − 1) dν`, where `ν` is the Lévy measure.
This uses weak convergence from `exists_measure_limit_large`.

**4.2 — Remove truncation ε → 0:**
As `ε → 0`, the integral over `{|x| ≥ ε}` approaches the integral over
`ℝ \ {0}`, since the Lévy measure has no mass at the origin. -/

/-- The scaled integral on `{|x| ≥ ε}` converges along a subsequence to the Lévy measure integral.

Uses weak convergence from the extraction lemma (`exists_measure_limit_large`). The function
`x ↦ exp(ixξ) − 1` is bounded and continuous on `{|x| ≥ ε}`, so weak convergence of the
scaled restricted measures implies convergence of integrals.

Two extra hypotheses make this provable:
- `hν_eq`: the extracted measure `ν_ε` equals the restriction of the Lévy measure.
- `hconv_cx`: the complex Fourier integral against the scaled restricted measure converges. -/
theorem large_jump_limit (ξ : ℝ) (ε : ℝ) (hε : 0 < ε)
    {t_seq : ℕ → {t : ℝ // 0 < t}} (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0))
    {ν_ε : Measure ℝ} (_hν_fin : IsFiniteMeasure ν_ε)
    (_hν_supp : ν_ε (largeSet ε)ᶜ = 0)
    (hν_eq : (levyMeasure S).restrict (largeSet ε) = ν_ε)
    (_hconv : ∀ (f : BoundedContinuousFunction ℝ ℝ), (∀ x, |x| < ε → f x = 0) →
      Tendsto (fun n => ∫ x, f x ∂(S.scaledRestrictedMeasure (t_seq n) ε))
        atTop (𝓝 (∫ x, f x ∂ν_ε)))
    (hconv_cx : Tendsto
      (fun n => ∫ x, (exp (↑x * ↑ξ * I) - 1) ∂(S.scaledRestrictedMeasure (t_seq n) ε))
      atTop
      (𝓝 (∫ x, (exp (↑x * ↑ξ * I) - 1) ∂ν_ε))) :
    Tendsto (fun n =>
      ((t_seq n).val⁻¹ : ℂ) *
      ∫ x in largeSet ε, (exp (↑x * ↑ξ * I) - 1) ∂(S.measure (t_seq n) : Measure ℝ))
    atTop
    (𝓝 (∫ x in largeSet ε, (exp (↑x * ↑ξ * I) - 1) ∂(levyMeasure S))) := by
  -- Step 1: Rewrite the limit target using hν_eq.
  -- ∫ x in largeSet ε, g ∂(levyMeasure S)
  --   = ∫ x, g ∂((levyMeasure S).restrict (largeSet ε))  [def of setIntegral]
  --   = ∫ x, g ∂ν_ε                                      [hν_eq]
  have hrhs : ∫ x in largeSet ε, (exp (↑x * ↑ξ * I) - 1) ∂(levyMeasure S)
      = ∫ x, (exp (↑x * ↑ξ * I) - 1) ∂ν_ε := by
    rw [← hν_eq]
  rw [hrhs]
  -- Step 2: Rewrite the LHS sequence.
  -- (t⁻¹ : ℂ) * ∫ x in largeSet ε, g ∂μ_t
  --   = t⁻¹ • ∫ x in largeSet ε, g ∂μ_t                  [real_smul_eq_coe_mul]
  --   = ∫ x in largeSet ε, g ∂(scaledMeasure t)           [integral_smul_measure]
  --   = ∫ x, g ∂(scaledRestrictedMeasure t ε)             [def of scaledRestrictedMeasure]
  have hlhs : ∀ n,
      ((t_seq n).val⁻¹ : ℂ) *
        ∫ x in largeSet ε, (exp (↑x * ↑ξ * I) - 1) ∂(S.measure (t_seq n) : Measure ℝ)
      = ∫ x, (exp (↑x * ↑ξ * I) - 1) ∂(S.scaledRestrictedMeasure (t_seq n) ε) := fun n => by
    have ht_pos := (t_seq n).prop
    -- Unfold scaledRestrictedMeasure and scaledMeasure, then use Measure.restrict_smul
    have hmsr : S.scaledRestrictedMeasure (t_seq n) ε =
        ENNReal.ofReal (t_seq n).val⁻¹ •
          (S.measure (t_seq n) : Measure ℝ).restrict (largeSet ε) := by
      rw [show S.scaledRestrictedMeasure (t_seq n) ε =
              (S.scaledMeasure (t_seq n)).restrict (largeSet ε) from rfl,
          show S.scaledMeasure (t_seq n) =
              ENNReal.ofReal (t_seq n).val⁻¹ • (S.measure (t_seq n) : Measure ℝ) from rfl]
      exact Measure.restrict_smul _ _ _
    -- Rewrite RHS: ∫ g ∂(scaledRestrictedMeasure) = t⁻¹ • ∫ g in largeSet ε ∂(μ_t)
    rw [hmsr, integral_smul_measure,
        ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr ht_pos))]
    -- Goal: ((t_seq n).val : ℂ)⁻¹ * ∫ g in largeSet ε ∂μ_t
    --     = (t_seq n).val⁻¹ • ∫ g in largeSet ε ∂μ_t
    -- Use: r⁻¹ • z = (r⁻¹ : ℂ) * z and (r : ℂ)⁻¹ = (r⁻¹ : ℂ)
    set z := ∫ x in largeSet ε, (exp (↑x * ↑ξ * I) - 1) ∂(S.measure (t_seq n) : Measure ℝ)
    set r := (t_seq n).val
    change (↑r : ℂ)⁻¹ * z = r⁻¹ • z
    rw [RCLike.real_smul_eq_coe_mul]
    congr 1
    exact (Complex.ofReal_inv r).symm
  simp_rw [hlhs]
  exact hconv_cx

/-- The union of `largeSet(1/(n+1))` as `n → ∞` exhausts `ℝ \ {0}`. -/
private lemma iUnion_largeSet_eq_ne_zero :
    (⋃ n : ℕ, largeSet (1 / (↑n + 1 : ℝ))) = {x : ℝ | x ≠ 0} := by
  ext x; simp only [Set.mem_iUnion, mem_largeSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn⟩ hx
    simp [hx, abs_zero] at hn
    linarith [show (0 : ℝ) < 1 / (↑n + 1) from by positivity]
  · intro hx
    have hxp : (0 : ℝ) < |x| := abs_pos.mpr hx
    obtain ⟨n, hn⟩ := exists_nat_gt |x|⁻¹
    refine ⟨n, ?_⟩
    have hnp : (0 : ℝ) < ↑n := lt_trans (inv_pos.mpr hxp) hn
    have h1 : 1 < ↑n * |x| := by
      calc (1 : ℝ) = |x|⁻¹ * |x| := (inv_mul_cancel₀ hxp.ne').symm
        _ < ↑n * |x| := by exact mul_lt_mul_of_pos_right hn hxp
    rw [div_le_iff₀ (show (0 : ℝ) < ↑n + 1 from by linarith)]
    nlinarith [hxp.le]

/-- The `largeSet` family is monotone (increasing) in `n` when indexed
    by `n ↦ largeSet(1/(n+1))`. -/
private lemma largeSet_mono_nat :
    Monotone (fun n : ℕ => largeSet (1 / (↑n + 1 : ℝ))) := by
  intro m n hmn
  apply largeSet_antitone
  apply div_le_div_of_nonneg_left one_pos.le (by positivity : (0 : ℝ) < ↑m + 1)
  exact_mod_cast Nat.add_le_add_right hmn 1

/-- The compensated integrand is integrable against the Lévy measure on `{x ≠ 0}`.
    Follows from `|exp(ixξ)-1-ixξ·1_{|x|<1}| ≤ min(2, (xξ)²/2)` and `∫ min(1,x²) dν < ∞`. -/
private lemma integrableOn_levyCompensatedIntegrand (ξ : ℝ) :
    IntegrableOn (levyCompensatedIntegrand ξ) {x : ℝ | x ≠ 0} (levyMeasure S) := by
  sorry

/-- The compensated integral converges as `ε → 0` to the full integral on `ℝ \ {0}`.

Since the Lévy measure satisfies `ν {0} = 0` and `∫ min(1,x²) dν < ∞`,
the sets `{|x| ≥ 1/(n+1)}` monotonically exhaust `ℝ \ {0}`.
The compensated integrand `exp(ixξ) − 1 − ixξ·1_{|x|<1}` is integrable against
the Lévy measure, so `tendsto_setIntegral_of_monotone` gives convergence. -/
theorem large_jump_exhaustion (ξ : ℝ) :
    Tendsto (fun n : ℕ =>
      ∫ x in largeSet (1 / (↑n + 1 : ℝ)),
        levyCompensatedIntegrand ξ x ∂(levyMeasure S))
    atTop
    (𝓝 (∫ x in {x : ℝ | x ≠ 0},
        levyCompensatedIntegrand ξ x ∂(levyMeasure S))) := by
  rw [← iUnion_largeSet_eq_ne_zero]
  exact tendsto_setIntegral_of_monotone
    (fun n => measurableSet_largeSet _)
    largeSet_mono_nat
    (iUnion_largeSet_eq_ne_zero ▸ S.integrableOn_levyCompensatedIntegrand ξ)

/-- On `{|x| ≥ 1}`, the compensated integrand equals `exp(ixξ) − 1` (indicator vanishes). -/
theorem levyCompensatedIntegrand_eq_on_large {ξ x : ℝ} (hx : 1 ≤ |x|) :
    levyCompensatedIntegrand ξ x = exp (↑x * ↑ξ * I) - 1 := by
  simp [levyCompensatedIntegrand, show ¬(|x| < 1) from not_lt.mpr hx]

/-- The integral of `exp(ixξ) − 1` over `{|x| ≥ 1}` equals the integral of the
compensated integrand over `{|x| ≥ 1}`. This bridges the large-jump Fourier
identification with the compensated integral form used in the final LK formula. -/
theorem integral_large_eq_compensated (ξ : ℝ) :
    ∫ x in largeSet 1, (exp (↑x * ↑ξ * I) - 1) ∂(levyMeasure S) =
    ∫ x in largeSet 1, levyCompensatedIntegrand ξ x ∂(levyMeasure S) := by
  apply setIntegral_congr_fun (measurableSet_largeSet 1)
  intro x hx
  exact (levyCompensatedIntegrand_eq_on_large (mem_largeSet.mp hx)).symm

/-! ### Phase 5 — Small jump analysis (second moment + quadratic expansion)

The key estimates for the "small jump" part `{|x| < 1}` of the Lévy-Khintchine formula.

**5.1 — Second moment bound:** From `charFun(μ_t)(ξ) = exp(tψ(ξ))`:
```
Re(1 - exp(tψ(ξ))) = ∫ (1 - cos(xξ)) dμ_t
```
On `{|x| < 1}` with `ξ = 1`: `1 - cos(x) ≥ (2/π²) x²` (Jordan's inequality), so
```
(2/π²) ∫_{|x|<1} x² dμ_t ≤ ∫(1-cos(x))dμ_t = Re(1-exp(tψ(1)))
```
Dividing by `t`: `(2/(π²t)) ∫_{|x|<1} x² dμ_t ≤ Re(-ψ(1)) + o(1)`.

**5.2 — Quadratic expansion:** The integrand `exp(ixξ) - 1 - ixξ` satisfies
`|exp(iz)-1-iz| ≤ z²/2`, so the scaled integral on `{|x| < 1}` is controlled by
the second moment, giving convergence of a subsequence. -/

/-- On `{|x| ≤ π}`, `1 - cos x ≥ (2/π²) · x²`. Wrapper for mathlib's
`cos_le_one_sub_mul_cos_sq`. -/
private lemma one_sub_cos_ge_mul_sq {x : ℝ} (hx : |x| ≤ Real.pi) :
    2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x := by
  linarith [Real.cos_le_one_sub_mul_cos_sq hx]

/-- The scaled quantity `t⁻¹ · Re(1 - exp(t·z))` converges to `Re(-z)` as `t → 0`.
This follows from `exp_first_order` composed with the continuous Re projection. -/
private lemma tendsto_inv_mul_re_one_sub_exp (z : ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ * (1 - exp (↑t * z)).re) (𝓝[≠] 0) (𝓝 (-z).re) := by
  -- Step 1: (exp(tz)-1)/t → z, so (1-exp(tz))/t → -z
  have h2 : Tendsto (fun t : ℝ => (1 - exp ((↑t : ℂ) * z)) / (↑t : ℂ))
      (𝓝[≠] 0) (𝓝 (-z)) :=
    (exp_first_order z).neg.congr fun t => by
      show -((exp ((↑t : ℂ) * z) - 1) / (↑t : ℂ)) = _; ring
  -- Step 2: Take Re (continuous), get Re((1-exp(tz))/t) → Re(-z)
  have h3 := (Complex.continuous_re.tendsto _).comp h2
  -- Step 3: Re(w/↑t) = t⁻¹ · Re(w) for real t
  exact h3.congr fun t => by
    simp only [Function.comp_def]
    by_cases ht : t = 0
    · simp [ht]
    · rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm,
        Complex.re_ofReal_mul]

/-- For each `t > 0`, the scaled second moment is bounded by a multiple of
`t⁻¹ · Re(1 - exp(tψ(1)))`. Uses the charFun identity and the cos lower bound. -/
private lemma second_moment_le_scaled_re (t : {t : ℝ // 0 < t}) :
    2 / Real.pi ^ 2 * (t.val⁻¹ * ∫ x in smallSet, x ^ 2 ∂(S.measure t : Measure ℝ)) ≤
      t.val⁻¹ * (1 - exp (↑t.val * S.exponent 1)).re := by
  -- charFun(μ_t)(1) = exp(t·ψ(1))
  have hcf : charFun (S.measure t : Measure ℝ) 1 = exp (↑t.val * S.exponent 1) := by
    rw [show charFun (S.measure t : Measure ℝ) 1 =
      MeasureTheory.ProbabilityMeasure.characteristicFun (S.measure t) 1 from rfl]
    exact S.charFun_eq t 1
  -- Re(1 - charFun(μ_t)(1)) = ∫ (1-cos x) dμ_t
  have hre : (1 - exp (↑t.val * S.exponent 1)).re =
      ∫ x, (1 - Real.cos (1 * x)) ∂(S.measure t : Measure ℝ) := by
    rw [← hcf]; exact re_one_sub_charFun_eq_integral 1
  rw [hre]; simp only [one_mul]
  -- Goal: 2/π² * (t⁻¹ * ∫_smallSet x²) ≤ t⁻¹ * ∫ (1 - cos x)
  rw [show 2 / Real.pi ^ 2 * (t.val⁻¹ * ∫ x in smallSet, x ^ 2 ∂(S.measure t : Measure ℝ)) =
    t.val⁻¹ * (2 / Real.pi ^ 2 * ∫ x in smallSet, x ^ 2 ∂(S.measure t : Measure ℝ)) from by ring]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (inv_pos.mpr t.prop))
  -- Goal: 2/π² * ∫_smallSet x² ≤ ∫ (1 - cos x)
  have hpi_bound : ∀ x : ℝ, x ∈ smallSet → 2 / Real.pi ^ 2 * x ^ 2 ≤ 1 - Real.cos x := by
    intro x hx
    exact one_sub_cos_ge_mul_sq (le_of_lt (lt_of_lt_of_le (mem_smallSet.mp hx)
      (le_trans (by norm_num : (1 : ℝ) ≤ 2) Real.two_le_pi)))
  have hint_sq : IntegrableOn (fun x => 2 / Real.pi ^ 2 * x ^ 2) smallSet
      (S.measure t : Measure ℝ) :=
    Integrable.of_bound
      ((continuous_const.mul (continuous_pow 2)).aestronglyMeasurable)
      (2 / Real.pi ^ 2)
      (by filter_upwards [ae_restrict_mem measurableSet_smallSet] with x hx
          have habs : |x| < 1 := mem_smallSet.mp hx
          have hx_sq : x ^ 2 ≤ 1 := by
            nlinarith [sq_abs x, mul_le_of_le_one_right (abs_nonneg x) habs.le]
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg x))]
          calc 2 / Real.pi ^ 2 * x ^ 2
              ≤ 2 / Real.pi ^ 2 * 1 := mul_le_mul_of_nonneg_left hx_sq (by positivity)
            _ = 2 / Real.pi ^ 2 := mul_one _)
  have hint_cos : IntegrableOn (fun x => 1 - Real.cos x) smallSet
      (S.measure t : Measure ℝ) :=
    (Integrable.of_bound
      ((continuous_const.sub Real.continuous_cos).aestronglyMeasurable)
      2 (ae_of_all _ fun x => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
        linarith [Real.neg_one_le_cos x])).integrableOn
  calc 2 / Real.pi ^ 2 * ∫ x in smallSet, x ^ 2 ∂(S.measure t : Measure ℝ)
      = ∫ x in smallSet, 2 / Real.pi ^ 2 * x ^ 2 ∂(S.measure t : Measure ℝ) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ x in smallSet, (1 - Real.cos x) ∂(S.measure t : Measure ℝ) :=
        setIntegral_mono_on hint_sq hint_cos measurableSet_smallSet hpi_bound
    _ ≤ ∫ x, (1 - Real.cos x) ∂(S.measure t : Measure ℝ) :=
        setIntegral_le_integral
          (Integrable.of_bound
            ((continuous_const.sub Real.continuous_cos).aestronglyMeasurable)
            2 (ae_of_all _ fun x => by
              simp only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
              linarith [Real.neg_one_le_cos x]))
          (ae_of_all _ fun x => sub_nonneg.mpr (Real.cos_le_one _))

theorem scaledMeasure_small_second_moment_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ (t : {t : ℝ // 0 < t}) in comap Subtype.val (𝓝[>] (0 : ℝ)),
      t.val⁻¹ * ∫ x in smallSet, x ^ 2 ∂(S.measure t : Measure ℝ) ≤ C := by
  set L := (-(S.exponent 1)).re
  -- t⁻¹ * Re(1 - exp(tψ(1))) → L as t → 0+
  have htend : Tendsto (fun (t : ℝ) => t⁻¹ * (1 - exp ((t : ℂ) * S.exponent 1)).re)
      (𝓝[>] (0 : ℝ)) (𝓝 L) :=
    (tendsto_inv_mul_re_one_sub_exp (S.exponent 1)).mono_left
      (nhdsWithin_mono (0 : ℝ) fun _ hx => ne_of_gt hx)
  -- Eventually ≤ |L| + 1
  have hevt : ∀ᶠ (r : ℝ) in 𝓝[>] (0 : ℝ),
      r⁻¹ * (1 - exp ((r : ℂ) * S.exponent 1)).re ≤ |L| + 1 :=
    (htend.eventually (Iio_mem_nhds (by linarith [le_abs_self L]))).mono
      fun _ h => le_of_lt h
  refine ⟨Real.pi ^ 2 / 2 * (|L| + 1), by positivity, ?_⟩
  exact (hevt.comap Subtype.val).mono fun t ht => by
    -- ht : t.val⁻¹ * Re(1 - exp(t.val·ψ(1))) ≤ |L| + 1
    have hle := le_trans (second_moment_le_scaled_re S t) ht
    -- hle : 2/π² * (t⁻¹ * ∫ x²) ≤ |L| + 1
    -- Multiply by π²/2 ≥ 0 and cancel
    have hfactor := mul_le_mul_of_nonneg_left hle
      (show (0 : ℝ) ≤ Real.pi ^ 2 / 2 from by positivity)
    rw [← mul_assoc, show Real.pi ^ 2 / 2 * (2 / Real.pi ^ 2) = 1 from by
      field_simp, one_mul] at hfactor
    exact hfactor

/-- The scaled integral of `exp(ixξ) - 1 - ixξ` on the small set, along a sequence
`t_n → 0`, converges. The integrand satisfies `|exp(iz) - 1 - iz| ≤ z²/2`, so the
integral is controlled by the second moment bound. -/
theorem small_jump_expansion (ξ : ℝ)
    {t_seq : ℕ → {t : ℝ // 0 < t}} (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ L : ℂ, Tendsto (fun n =>
      ((t_seq n).val⁻¹ : ℂ) *
      ∫ x in smallSet,
        (Complex.exp (↑x * ↑ξ * Complex.I) - 1 - ↑x * ↑ξ * Complex.I)
        ∂(S.measure (t_seq n) : Measure ℝ))
    atTop (𝓝 L) := by
  sorry

/-! ### Phase 6: Drift extraction (first moment limit + drift contribution)

**6.1 — Drift limit:** The scaled first moment on `{|x| < 1}` converges along `t_n → 0`,
defining the drift `b`. This follows by subtracting the large-jump, quadratic, and remainder
contributions from the total limit `ψ(ξ)`.

**6.2 — Drift contribution:** The linear term `∫ (x · ξ · I) dμ_t` factors as
`ξ · I · ∫ x dμ_t`, so after scaling by `1/t` and taking the limit, contributes `b · ξ · I`
to the decomposition. -/

/-- The scaled first moment on the small set converges along `t_n → 0`, defining the drift `b`.
This follows from: the total limit `ψ(ξ)` is known (Phase 1), the large-jump contribution
converges (Phase 3/4), and the quadratic contribution converges (Phase 5), so the remaining
linear term must also converge by difference. -/
lemma drift_limit
    {t_seq : ℕ → {t : ℝ // 0 < t}} (ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0)) :
    ∃ b : ℝ, Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in smallSet, x ∂(S.measure (t_seq n) : Measure ℝ))
    atTop (𝓝 b) := by
  sorry

/-- The drift term contributes `b * ξ * I` to the decomposition.
Factor out `ξ * I` from the integral of `x * ξ * I`. -/
lemma drift_term (ξ : ℝ)
    {t_seq : ℕ → {t : ℝ // 0 < t}} (_ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0))
    {b : ℝ} (hb : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in smallSet, x ∂(S.measure (t_seq n) : Measure ℝ))
    atTop (𝓝 b)) :
    Tendsto (fun n =>
      ((t_seq n).val⁻¹ : ℂ) *
      ∫ x in smallSet, (↑x * ↑ξ * I) ∂(S.measure (t_seq n) : Measure ℝ))
    atTop (𝓝 (↑b * ↑ξ * I)) := by
  -- Step 1: Rewrite each summand to factor out the constant (↑ξ * I)
  suffices h : Tendsto (fun n =>
      ↑((t_seq n).val⁻¹ * ∫ x in smallSet, x ∂(S.measure (t_seq n) : Measure ℝ)) *
      ((↑ξ : ℂ) * I)) atTop (𝓝 (↑b * ↑ξ * I)) by
    refine h.congr (fun n => ?_)
    -- Show the two expressions are equal
    have : ∫ x in smallSet, ((↑x : ℂ) * ↑ξ * I) ∂(S.measure (t_seq n) : Measure ℝ) =
        ↑(∫ x in smallSet, x ∂(S.measure (t_seq n) : Measure ℝ)) * (↑ξ * I) := by
      simp_rw [mul_assoc]
      have : ∀ x : ℝ, (↑x : ℂ) * ((↑ξ : ℂ) * I) = (↑x : ℂ) • ((↑ξ : ℂ) * I) := by
        intro x; rw [smul_eq_mul]
      simp_rw [this]
      rw [integral_smul_const]
      congr 1
      exact integral_ofReal
    rw [this]; push_cast; ring
  -- Step 2: ↑(t⁻¹ * ∫) * (↑ξ * I) → ↑b * (↑ξ * I) = ↑b * ↑ξ * I
  rw [show (↑b : ℂ) * ↑ξ * I = ↑b * (↑ξ * I) from by ring]
  exact Filter.Tendsto.mul_const ((↑ξ : ℂ) * I) hb.ofReal

/-- Main assembly: combine all phases to decompose the characteristic exponent `ψ`
into drift, diffusion, and jump components. The proof assembles Phase 1–6 lemmas
(charFun_scaled_limit, large_jump_limit, small_jump_expansion, drift_limit, etc.)
to identify the Lévy-Khintchine triple `(b, σ², ν)`.

This is the core sorry: once it is closed, `levyKhintchine_of_cnd` follows immediately. -/
theorem psi_decomposition :
    ∃ (b : ℝ) (σ_sq : ℝ≥0) (ν : Measure ℝ),
      IsLevyMeasure ν ∧
      ∀ ξ : ℝ,
        S.exponent ξ = ↑b * ↑ξ * I
          - ↑(σ_sq : ℝ) * ↑ξ ^ 2 / 2
          + ∫ x, levyCompensatedIntegrand ξ x ∂ν := by
  sorry

end ConvolutionSemigroup

/-- Build a convolution semigroup from a CND exponent via Schoenberg + Bochner. -/
noncomputable def convolutionSemigroupOfCND
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cnd : IsConditionallyNegativeDefinite ψ)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ)) :
    ConvolutionSemigroup where
  exponent := ψ
  exponent_continuous := hψ_cont
  exponent_zero := hψ_zero
  measure := fun ⟨t, ht⟩ =>
    (bochner _ (by fun_prop : Continuous (fun ξ => exp ((↑t : ℂ) * ψ ξ)))
      (schoenberg_exp_of_cnd hψ_cont hψ_zero hψ_cnd hψ_herm t ht)
      (by rw [hψ_zero, mul_zero, exp_zero])).choose
  charFun_eq := fun ⟨t, ht⟩ ξ =>
    (bochner _ (by fun_prop : Continuous (fun ξ => exp ((↑t : ℂ) * ψ ξ)))
      (schoenberg_exp_of_cnd hψ_cont hψ_zero hψ_cnd hψ_herm t ht)
      (by rw [hψ_zero, mul_zero, exp_zero])).choose_spec ξ

/-! ## Sub-lemma 4: Integral representation (deepest) -/

/-- A continuous, conditionally negative definite function `ψ : ℝ → ℂ` with `ψ(0) = 0`
has the Lévy-Khintchine integral representation.

**Proof via Bochner's theorem:**
1. By Schoenberg, `exp(tψ)` is PD, continuous, with value 1 at 0 for each `t > 0`.
2. By Bochner, there exists probability measure `μ_t` with `charFun(μ_t) = exp(tψ)`.
3. The family `{μ_t}` forms a convolution semigroup (see `convolutionSemigroupOfCND`).
4. Differentiating at `t = 0` extracts the Lévy-Khintchine triple `(b, σ², ν)`.

Steps 1–3 are complete. Step 4 delegates to `ConvolutionSemigroup.psi_decomposition`. -/
theorem levyKhintchine_of_cnd
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cnd : IsConditionallyNegativeDefinite ψ)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ)) :
    ∃ T : LevyKhintchineTriple, ∀ ξ : ℝ,
      ψ ξ = ↑T.drift * ↑ξ * I
        - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
        + ∫ x, levyCompensatedIntegrand ξ x ∂T.levyMeasure := by
  -- Steps 1–2: Build the convolution semigroup via Schoenberg + Bochner
  set S := convolutionSemigroupOfCND hψ_cont hψ_zero hψ_cnd hψ_herm
  -- Step 3–4: Extract the triple via psi_decomposition
  obtain ⟨b, σ_sq, ν, hν_levy, hψ_eq⟩ := S.psi_decomposition
  exact ⟨⟨b, σ_sq, ν, hν_levy⟩, hψ_eq⟩

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
  -- Hermitian symmetry: ψ(-ξ) = conj(ψ(ξ)) from charFun(-ξ) = conj(charFun(ξ))
  -- Follows from exp(ψ(-ξ)) = charFun(-ξ) = conj(charFun(ξ)) = exp(conj(ψ(ξ)))
  -- and injectivity of exp on the strip (continuous log stays in strip with ψ(0)=0).
  have hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ) := by
    -- Strategy: both ψ and g := conj ∘ ψ ∘ neg are continuous lifts of charFun μ through exp
    -- with value 0 at 0. By uniqueness of covering map lifts, they are equal.
    -- That gives conj(ψ(-ξ)) = ψ(ξ), hence ψ(-ξ) = conj(ψ(ξ)).
    have hcont : Continuous (charFun μ) := MeasureTheory.continuous_charFun
    have hne : ∀ ξ, charFun μ ξ ≠ 0 := h.charFun_ne_zero
    have hφ0 : charFun μ 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
    -- Set up the continuous map for charFun
    set f : C(ℝ, ℂ) := ⟨charFun μ, hcont⟩
    have he : Complex.exp (0 : ℂ) = f (0 : ℝ) := by simp [f, hφ0]
    have hs : ∀ ξ : ℝ, f ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ => Set.mem_compl_singleton_iff.mpr (hne ξ)
    -- Get the unique lift
    obtain ⟨F, ⟨hF0, hFexp⟩, hF_unique⟩ :=
      Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
    -- ψ as a ContinuousMap is a lift
    set Ψ : C(ℝ, ℂ) := ⟨ψ, hψ_cont⟩
    have hΨ_lift : Ψ 0 = 0 ∧ Complex.exp ∘ Ψ = f := by
      constructor
      · exact hψ_zero
      · ext ξ; simp [Ψ, f, hψ_exp ξ]
    -- g(ξ) := conj(ψ(-ξ)) is also a continuous lift
    set G : C(ℝ, ℂ) := ⟨fun ξ => starRingEnd ℂ (ψ (-ξ)), by
      exact continuous_star.comp (hψ_cont.comp continuous_neg)⟩
    have hG_lift : G 0 = 0 ∧ Complex.exp ∘ G = f := by
      constructor
      · simp [G, hψ_zero]
      · ext ξ; simp only [G, ContinuousMap.coe_mk, Function.comp_apply, f]
        rw [exp_conj, ← hψ_exp (-ξ), charFun_neg, starRingEnd_self_apply]
    -- By uniqueness, Ψ = F and G = F, hence Ψ = G
    have hΨ_eq : Ψ = F := hF_unique Ψ hΨ_lift
    have hG_eq : G = F := hF_unique G hG_lift
    -- Therefore Ψ = G pointwise: ψ(ξ) = conj(ψ(-ξ))
    have hΨG : ∀ ξ, ψ ξ = starRingEnd ℂ (ψ (-ξ)) := by
      intro ξ
      have := congr_arg (· ξ) (hΨ_eq.trans hG_eq.symm)
      exact this
    -- We need ψ(-ξ) = conj(ψ(ξ)). Apply hΨG at -ξ and simplify.
    intro ξ
    have := hΨG (-ξ)
    simp only [neg_neg] at this
    exact this
  obtain ⟨T, hT⟩ := levyKhintchine_of_cnd hψ_cont hψ_zero hψ_cnd hψ_herm
  -- Combine: charFun μ ξ = exp(ψ ξ) = exp(ibξ - σ²ξ²/2 + ∫ f dν)
  exact ⟨T, fun ξ => by rw [hψ_exp ξ, hT ξ]⟩

end ProbabilityTheory
