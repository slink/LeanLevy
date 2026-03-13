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
    sorry
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
  · -- Hermitianness
    sorry
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
        · simp [Complex.div_ofReal_re]; exact div_nonneg ht (le_of_lt hN_pos)
        · simp [Complex.div_ofReal_im]
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
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
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
    simp [starRingEnd_self_apply, Complex.conj_ofReal]]
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

Steps 1–3 are complete. Step 4 (measure differentiation) is research-level and remains sorry'd. -/
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
  -- Step 3: The semigroup satisfies charFun(μ_t)(ξ) = exp(tψ(ξ))
  have _hcharfun : ∀ (t : {t : ℝ // 0 < t}) (ξ : ℝ),
      MeasureTheory.ProbabilityMeasure.characteristicFun (S.measure t) ξ =
        exp ((↑t.val : ℂ) * ψ ξ) := S.charFun_eq
  -- Step 4: Extract the triple by differentiating the convolution semigroup at t=0.
  -- This requires: vague limit of (μ_t - δ_0)/t as t↓0, identification of the
  -- limit as ν + σ²δ₀ + b·δ₀', and verification of the Lévy measure conditions.
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
  -- Hermitian symmetry: ψ(-ξ) = conj(ψ(ξ)) from charFun(-ξ) = conj(charFun(ξ))
  -- Follows from exp(ψ(-ξ)) = charFun(-ξ) = conj(charFun(ξ)) = exp(conj(ψ(ξ)))
  -- and injectivity of exp on the strip (continuous log stays in strip with ψ(0)=0).
  have hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ) := by sorry
  obtain ⟨T, hT⟩ := levyKhintchine_of_cnd hψ_cont hψ_zero hψ_cnd hψ_herm
  -- Combine: charFun μ ξ = exp(ψ ξ) = exp(ibξ - σ²ξ²/2 + ∫ f dν)
  exact ⟨T, fun ξ => by rw [hψ_exp ξ, hT ξ]⟩

end ProbabilityTheory
