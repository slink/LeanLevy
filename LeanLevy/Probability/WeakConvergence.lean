/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Probability.Characteristic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Sequences

/-!
# Weak Convergence and Lévy's Continuity Theorem

This file proves Lévy's continuity theorem: a sequence of probability measures
on ℝ converges weakly if and only if their characteristic functions converge
pointwise.

## Main definitions

* `MeasureTheory.ProbabilityMeasure.CharFunTendsto` — pointwise convergence of
  characteristic functions along a filter.

## Main results

* `MeasureTheory.ProbabilityMeasure.charFunTendsto_of_tendsto` — weak convergence
  implies pointwise convergence of characteristic functions.
* `MeasureTheory.ProbabilityMeasure.isTight_of_charFunTendsto` — pointwise convergence
  of characteristic functions implies tightness of the sequence.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_charFunTendsto` — pointwise convergence
  of characteristic functions implies weak convergence (Lévy's continuity theorem).
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_charFunTendsto` — the biconditional.

## References

* [P. Billingsley, *Convergence of Probability Measures*]
-/

open MeasureTheory Complex ComplexConjugate Filter Topology BoundedContinuousFunction

namespace MeasureTheory.ProbabilityMeasure

variable {ι : Type*} {F : Filter ι}

/-- Pointwise convergence of characteristic functions of probability measures
along a filter `F`. -/
def CharFunTendsto (μs : ι → ProbabilityMeasure ℝ) (F : Filter ι)
    (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ ξ : ℝ, Tendsto (fun i => characteristicFun (μs i) ξ) F (𝓝 (characteristicFun μ ξ))

@[simp]
theorem charFunTendsto_iff {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} :
    CharFunTendsto μs F μ ↔
    ∀ ξ : ℝ, Tendsto (fun i => characteristicFun (μs i) ξ) F (𝓝 (characteristicFun μ ξ)) :=
  Iff.rfl

/-- The exponential character `x ↦ exp(iξx)` as a bounded continuous function. -/
noncomputable def expBCF (ξ : ℝ) : ℝ →ᵇ ℂ :=
  .mkOfBound ⟨fun x => exp (↑(ξ * x) * I), by fun_prop⟩ 2
    (fun x y => by
      calc dist (exp (↑(ξ * x) * I)) (exp (↑(ξ * y) * I))
          ≤ ‖exp (↑(ξ * x) * I)‖ + ‖exp (↑(ξ * y) * I)‖ := dist_le_norm_add_norm _ _
        _ = 1 + 1 := by simp only [norm_exp_ofReal_mul_I]
        _ = 2 := by ring)

theorem integral_expBCF_eq_characteristicFun (μ : ProbabilityMeasure ℝ) (ξ : ℝ) :
    ∫ x, expBCF ξ x ∂(μ : Measure ℝ) = characteristicFun μ ξ := by
  simp only [characteristicFun, charFun_apply_real]
  congr 1; ext x
  simp only [expBCF, mkOfBound_coe, ContinuousMap.coe_mk]
  push_cast; ring

/-- **Easy direction of Lévy's continuity theorem.** Weak convergence of probability
measures implies pointwise convergence of characteristic functions. -/
theorem charFunTendsto_of_tendsto {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : Tendsto μs F (𝓝 μ)) : CharFunTendsto μs F μ := by
  intro ξ
  simp_rw [← integral_expBCF_eq_characteristicFun]
  exact (tendsto_iff_forall_integral_rclike_tendsto ℂ).mp h (expBCF ξ)

/-! ### Tightness from characteristic function convergence -/

section Tightness

open Set MeasureTheory ENNReal Metric

/-- Auxiliary: for any δ > 0, there exist r > 0 and n₀ such that for all n ≥ n₀,
the tail measure (μs n){x | r < |x|} is at most δ.

This follows from:
1. `measureReal_abs_gt_le_integral_charFun`: tail ≤ (1/2) r ‖∫ t in (-2/r)..(2/r), 1 - charFun‖
2. Continuity of charFun μ at 0 (so the integral for μ is small for small intervals)
3. Dominated convergence: the integrals for μₙ converge to those for μ
-/
-- For a fixed interval [-T, T], the integrals ∫ t in (-T)..T, (1 - charFun (μs n) t)
-- converge to ∫ t in (-T)..T, (1 - charFun μ t) as n → ∞, by dominated convergence.
private theorem tendsto_intervalIntegral_one_sub_charFun
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : CharFunTendsto μs atTop μ) (T : ℝ) :
    Tendsto (fun n => ∫ t in (-T)..T, (1 - charFun (μs n : Measure ℝ) t))
      atTop (𝓝 (∫ t in (-T)..T, (1 - charFun (μ : Measure ℝ) t))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (bound := fun _ => 2)
  -- 1. Each F_n is AEStronglyMeasurable on the interval
  · exact Eventually.of_forall fun n =>
      (stronglyMeasurable_const.sub stronglyMeasurable_charFun).aestronglyMeasurable
  -- 2. Norm bound: ‖1 - charFun (μs n) t‖ ≤ 2
  · exact Eventually.of_forall fun n => ae_of_all _ fun t _ => norm_one_sub_charFun_le_two
  -- 3. The bound function 2 is interval integrable
  · exact intervalIntegrable_const
  -- 4. Pointwise convergence: charFun (μs n) t → charFun μ t
  · apply ae_of_all
    intro t _
    have ht := h t
    simp only [characteristicFun_def] at ht
    exact tendsto_const_nhds.sub ht

-- The tail bound 2⁻¹ * r * ‖∫ t in (-2*r⁻¹)..(2*r⁻¹), 1 - charFun μ t‖ → 0 as r → ∞.
-- Proof: charFun μ is continuous with charFun μ 0 = 1, so 1 - charFun μ t → 0 as t → 0.
-- The interval length is 4/r → 0, and the integrand is bounded, so the integral
-- is O(1/r) * O(sup on [-2/r, 2/r]) → 0.
private theorem tendsto_tail_bound_of_charFun
    (μ : ProbabilityMeasure ℝ) :
    Tendsto (fun r => 2⁻¹ * r *
      ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - charFun (μ : Measure ℝ) t‖)
      atTop (𝓝 0) := by
  -- Let f(t) = 1 - charFun μ t. Then f is continuous and f(0) = 0.
  set f : ℝ → ℂ := fun t => 1 - charFun (μ : Measure ℝ) t with hf_def
  -- f is continuous (using continuity of characteristicFun = charFun)
  have hf_cont : Continuous f := continuous_const.sub (continuous_characteristicFun μ)
  -- f(0) = 0
  have hf_zero : f 0 = 0 := by simp [hf_def, charFun_zero]
  -- Suffices to show: for any ε > 0, eventually 2⁻¹ * r * ‖∫ f on (-2/r, 2/r)‖ < ε
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- By continuity of f at 0 with f(0) = 0: ‖f(t)‖ < ε/4 for |t| < η
  have hf_cont_at : ContinuousAt f 0 := hf_cont.continuousAt
  rw [ContinuousAt, hf_zero, Metric.tendsto_nhds] at hf_cont_at
  -- Extract η > 0 such that dist t 0 < η implies dist (f t) 0 < ε/4
  have hev := hf_cont_at (ε / 4) (by linarith)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη_pos, hη⟩ := hev
  -- Choose r₀ so that 2/r < η for r ≥ r₀. We need r > 2/η.
  refine ⟨max (2 / η + 1) 1, fun r hr => ?_⟩
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le one_pos (le_of_max_le_right hr)
  have hr_ge : r ≥ 2 / η + 1 := le_of_max_le_left hr
  -- 2 * r⁻¹ < η
  have h2r_lt : 2 * r⁻¹ < η := by
    rw [show (2 : ℝ) * r⁻¹ = 2 / r from by ring]
    calc 2 / r < 2 / (2 / η) := by
          apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 2)
            (by positivity) (by linarith)
      _ = η := by field_simp
  -- Bound ‖f(t)‖ on the interval: for |t| ≤ 2/r < η, ‖f(t)‖ < ε/4
  -- Since uIoc (-a) a for a > 0 is (-a, a], and we need |t| < η
  have h2r_pos : (0 : ℝ) < 2 * r⁻¹ := by positivity
  have hf_bound : ∀ t ∈ Set.uIoc (-2 * r⁻¹) (2 * r⁻¹), ‖f t‖ ≤ ε / 4 := by
    intro t ht
    -- uIoc (-a) a = (-a, a] when a ≥ 0
    rw [Set.uIoc_of_le (by linarith : -2 * r⁻¹ ≤ 2 * r⁻¹)] at ht
    -- |t| < η since |t| ≤ 2/r < η
    have ht_abs : |t| < η := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    -- dist t 0 < η
    have ht_dist : dist t 0 < η := by rwa [Real.dist_eq, sub_zero]
    -- ‖f(t)‖ < ε/4 by the continuity bound
    have := hη ht_dist
    rw [dist_zero_right] at this
    exact le_of_lt this
  -- Apply the integral bound: ‖∫ f‖ ≤ (ε/4) * |2/r - (-2/r)| = (ε/4) * (4/r)
  have hintegral_bound : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), f t‖ ≤
      ε / 4 * |2 * r⁻¹ - (-2 * r⁻¹)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hf_bound
  -- |2/r - (-2/r)| = 4/r
  have habs : |2 * r⁻¹ - (-2 * r⁻¹)| = 4 * r⁻¹ := by
    rw [show 2 * r⁻¹ - (-2 * r⁻¹) = 4 * r⁻¹ from by ring]
    exact abs_of_pos (by positivity)
  -- Combine: 2⁻¹ * r * ‖∫ f‖ ≤ 2⁻¹ * r * (ε/4 * 4/r) = ε/2 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hint_le : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), f t‖ ≤ ε / 4 * (4 * r⁻¹) := by
    calc ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), f t‖
        ≤ ε / 4 * |2 * r⁻¹ - (-2 * r⁻¹)| := hintegral_bound
      _ = ε / 4 * (4 * r⁻¹) := by rw [habs]
  have h2r_nonneg : (0 : ℝ) ≤ 2⁻¹ * r := by positivity
  have hle := mul_le_mul_of_nonneg_left hint_le h2r_nonneg
  have hstep : 2⁻¹ * r * (ε / 4 * (4 * r⁻¹)) = ε / 2 := by field_simp
  linarith

/-- Generalized tail bound: for any continuous `φ` with `φ 0 = 1`, the quantity
`2⁻¹ * r * ‖∫ t in (-2/r)..(2/r), 1 - φ t‖ → 0` as `r → ∞`.

Same proof as `tendsto_tail_bound_of_charFun` with `charFun μ` replaced by abstract `φ`. -/
theorem tendsto_tail_bound_of_continuous
    {φ : ℝ → ℂ} (hφc : Continuous φ) (hφ0 : φ 0 = 1) :
    Tendsto (fun r => 2⁻¹ * r *
      ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - φ t‖)
      atTop (𝓝 0) := by
  set f : ℝ → ℂ := fun t => 1 - φ t with hf_def
  have hf_cont : Continuous f := continuous_const.sub hφc
  have hf_zero : f 0 = 0 := by simp [hf_def, hφ0]
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf_cont_at : ContinuousAt f 0 := hf_cont.continuousAt
  rw [ContinuousAt, hf_zero, Metric.tendsto_nhds] at hf_cont_at
  have hev := hf_cont_at (ε / 4) (by linarith)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη_pos, hη⟩ := hev
  refine ⟨max (2 / η + 1) 1, fun r hr => ?_⟩
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le one_pos (le_of_max_le_right hr)
  have hr_ge : r ≥ 2 / η + 1 := le_of_max_le_left hr
  have h2r_lt : 2 * r⁻¹ < η := by
    rw [show (2 : ℝ) * r⁻¹ = 2 / r from by ring]
    calc 2 / r < 2 / (2 / η) := by
          apply div_lt_div_of_pos_left (by norm_num : (0:ℝ) < 2)
            (by positivity) (by linarith)
      _ = η := by field_simp
  have h2r_pos : (0 : ℝ) < 2 * r⁻¹ := by positivity
  have hf_bound : ∀ t ∈ Set.uIoc (-2 * r⁻¹) (2 * r⁻¹), ‖f t‖ ≤ ε / 4 := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith : -2 * r⁻¹ ≤ 2 * r⁻¹)] at ht
    have ht_abs : |t| < η := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have ht_dist : dist t 0 < η := by rwa [Real.dist_eq, sub_zero]
    have := hη ht_dist
    rw [dist_zero_right] at this
    exact le_of_lt this
  have hintegral_bound : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), f t‖ ≤
      ε / 4 * |2 * r⁻¹ - (-2 * r⁻¹)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hf_bound
  have habs : |2 * r⁻¹ - (-2 * r⁻¹)| = 4 * r⁻¹ := by
    rw [show 2 * r⁻¹ - (-2 * r⁻¹) = 4 * r⁻¹ from by ring]
    exact abs_of_pos (by positivity)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  have hint_le : ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), f t‖ ≤ ε / 4 * (4 * r⁻¹) := by
    calc ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹), f t‖
        ≤ ε / 4 * |2 * r⁻¹ - (-2 * r⁻¹)| := hintegral_bound
      _ = ε / 4 * (4 * r⁻¹) := by rw [habs]
  have h2r_nonneg : (0 : ℝ) ≤ 2⁻¹ * r := by positivity
  have hle := mul_le_mul_of_nonneg_left hint_le h2r_nonneg
  have hstep : 2⁻¹ * r * (ε / 4 * (4 * r⁻¹)) = ε / 2 := by field_simp
  linarith

/-- Generalized radius/threshold: for a sequence of probability measures whose charfuns
converge pointwise to a continuous `φ` with `φ 0 = 1`, there exist r > 0 and n₀ such that
for all n ≥ n₀, the tail measure (μs n){x | r < |x|} < δ. -/
theorem exists_radius_and_threshold_of_continuous_tendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (hφc : Continuous φ) (hφ0 : φ 0 = 1)
    (hconv : ∀ ξ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop (𝓝 (φ ξ)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℝ) (_ : 0 < r) (n₀ : ℕ),
      ∀ n, n₀ ≤ n → (μs n : Measure ℝ).real {x | r < |x|} < δ := by
  -- Choose r₀ large enough that the tail bound for abstract φ is < δ/2
  have hlim := tendsto_tail_bound_of_continuous hφc hφ0
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨r₀, hr₀⟩ := hlim (δ / 2) (half_pos hδ)
  set r := max r₀ 1 with hr_def
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hr_ge : r₀ ≤ r := le_max_left _ _
  have hφ_bound : 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
      (1 : ℂ) - φ t‖ < δ / 2 := by
    have := hr₀ r hr_ge
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg] at this
    positivity
  -- The integral for μₙ converges to the integral for φ on [-2/r, 2/r]
  have hneg_rw : -(2 * r⁻¹) = -2 * r⁻¹ := by ring
  have hconv₀ : Tendsto
      (fun n => ∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - charFun (μs n : Measure ℝ) t)
      atTop (𝓝 (∫ t in (-2 * r⁻¹)..(2 * r⁻¹), (1 : ℂ) - φ t)) := by
    rw [show (-2 * r⁻¹ : ℝ) = -(2 * r⁻¹) from by ring]
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (bound := fun _ => 2)
    · exact Eventually.of_forall fun n =>
        (stronglyMeasurable_const.sub stronglyMeasurable_charFun).aestronglyMeasurable
    · exact Eventually.of_forall fun n => ae_of_all _ fun t _ => norm_one_sub_charFun_le_two
    · exact intervalIntegrable_const
    · apply ae_of_all; intro t _
      exact tendsto_const_nhds.sub (hconv t)
  have hconv_scaled : Tendsto
      (fun n => 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
        (1 : ℂ) - charFun (μs n : Measure ℝ) t‖) atTop
      (𝓝 (2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
        (1 : ℂ) - φ t‖)) :=
    hconv₀.norm.const_mul _
  have hev : ∀ᶠ n in atTop, 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
      (1 : ℂ) - charFun (μs n : Measure ℝ) t‖ < δ := by
    apply (hconv_scaled.eventually (Iio_mem_nhds hφ_bound)).mono
    intro n hn
    calc 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
            (1 : ℂ) - charFun (μs n : Measure ℝ) t‖
        < δ / 2 := hn
      _ < δ := half_lt_self hδ
  obtain ⟨n₀, hn₀⟩ := hev.exists_forall_of_atTop
  refine ⟨r, hr_pos, n₀, fun n hn => ?_⟩
  calc (μs n : Measure ℝ).real {x | r < |x|}
      ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
          (1 : ℂ) - charFun (μs n : Measure ℝ) t‖ :=
        measureReal_abs_gt_le_integral_charFun hr_pos
    _ < δ := hn₀ n hn

private theorem exists_radius_and_threshold_of_charFunTendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : CharFunTendsto μs atTop μ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℝ) (_ : 0 < r) (n₀ : ℕ),
      ∀ n, n₀ ≤ n → (μs n : Measure ℝ).real {x | r < |x|} < δ := by
  -- The proof strategy:
  -- 1. measureReal_abs_gt_le_integral_charFun gives:
  --    (μs n).real {|x| > r} ≤ 2⁻¹ * r * ‖∫ t in (-2/r)..(2/r), 1 - charFun (μs n) t‖
  -- 2. By tendsto_tail_bound_of_charFun, the RHS for the limit μ → 0 as r → ∞
  -- 3. By tendsto_intervalIntegral_one_sub_charFun, for fixed r the RHS for μₙ
  --    converges to the RHS for μ
  -- 4. Choose r so the μ-bound < δ/2, then n₀ so the μₙ-bound is close
  -- Choose r₀ large enough that the tail bound for μ is < δ/2
  have hlim := tendsto_tail_bound_of_charFun μ
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨r₀, hr₀⟩ := hlim (δ / 2) (half_pos hδ)
  -- Set r = max r₀ 1 (to ensure r > 0)
  set r := max r₀ 1 with hr_def
  have hr_pos : (0 : ℝ) < r := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hr_ge : r₀ ≤ r := le_max_left _ _
  -- The tail bound for μ at radius r
  have hμ_bound : 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
      (1 : ℂ) - charFun (μ : Measure ℝ) t‖ < δ / 2 := by
    have := hr₀ r hr_ge
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg] at this
    positivity
  -- The integral for μₙ converges to the integral for μ on [-2/r, 2/r]
  have hconv₀ := tendsto_intervalIntegral_one_sub_charFun h (2 * r⁻¹)
  -- Normalize -(2 * r⁻¹) to -2 * r⁻¹ so it matches measureReal_abs_gt_le_integral_charFun
  have hneg_rw : -(2 * r⁻¹) = -2 * r⁻¹ := by ring
  rw [hneg_rw] at hconv₀
  -- So the norm of the integral also converges
  -- And thus 2⁻¹ * r * ‖integral‖ converges
  have hconv_scaled : Tendsto
      (fun n => 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
        (1 : ℂ) - charFun (μs n : Measure ℝ) t‖) atTop
      (𝓝 (2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
        (1 : ℂ) - charFun (μ : Measure ℝ) t‖)) :=
    hconv₀.norm.const_mul _
  -- Eventually the scaled norm for μₙ is < δ
  have hev : ∀ᶠ n in atTop, 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
      (1 : ℂ) - charFun (μs n : Measure ℝ) t‖ < δ := by
    apply (hconv_scaled.eventually (Iio_mem_nhds hμ_bound)).mono
    intro n hn
    calc 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
            (1 : ℂ) - charFun (μs n : Measure ℝ) t‖
        < δ / 2 := hn
      _ < δ := half_lt_self hδ
  -- Extract n₀
  obtain ⟨n₀, hn₀⟩ := hev.exists_forall_of_atTop
  refine ⟨r, hr_pos, n₀, fun n hn => ?_⟩
  -- Apply the tail bound for μs n
  calc (μs n : Measure ℝ).real {x | r < |x|}
      ≤ 2⁻¹ * r * ‖∫ t in (-2 * r⁻¹)..(2 * r⁻¹),
          (1 : ℂ) - charFun (μs n : Measure ℝ) t‖ :=
        measureReal_abs_gt_le_integral_charFun hr_pos
    _ < δ := hn₀ n hn

/-- **Tightness from characteristic function convergence.** If the characteristic
functions of a sequence of probability measures converge pointwise to the
characteristic function of a probability measure μ, then the sequence is tight.

The proof uses the tail bound `measureReal_abs_gt_le_integral_charFun` together
with dominated convergence for the integral of `1 - charFun` over symmetric intervals.
For n ≥ n₀ the tail bound gives uniform control; for the finitely many n < n₀,
each probability measure on ℝ (a Polish space) is individually tight. -/
theorem isTight_of_charFunTendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : CharFunTendsto μs atTop μ) :
    IsTightMeasureSet (Set.range (fun n => (μs n : Measure ℝ))) := by
  -- Reduce to the epsilon-delta characterization
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  -- Handle ε = ⊤ trivially
  by_cases hε_top : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ => hε_top ▸ le_top⟩
  -- Now ε < ⊤, so we can extract a positive real δ
  set δ := ε.toReal with hδ_def
  have hδ_pos : 0 < δ := ENNReal.toReal_pos hε.ne' hε_top
  have hδ_le : ENNReal.ofReal δ ≤ ε := by
    rw [hδ_def, ENNReal.ofReal_toReal hε_top]
  -- Step 1: Get r > 0 and n₀ from the charfun tail bound argument
  obtain ⟨r, hr, n₀, htail⟩ := exists_radius_and_threshold_of_charFunTendsto h hδ_pos
  -- Step 2: For each n < n₀, get a compact K_n with (μs n)(K_nᶜ) ≤ ε
  -- (each probability measure on ℝ is individually tight)
  have hfin : ∀ n : Fin n₀, ∃ K : Set ℝ, IsCompact K ∧ (μs n : Measure ℝ) Kᶜ ≤ ε := by
    intro ⟨n, hn⟩
    have := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := (μs n : Measure ℝ))) ε hε
    obtain ⟨K, hK, hKε⟩ := this
    exact ⟨K, hK, hKε _ rfl⟩
  choose Kfin hKfin_compact hKfin_meas using hfin
  -- Step 3: Build the compact set K = (⋃ i : Fin n₀, K_i) ∪ closedBall 0 r
  refine ⟨(⋃ i : Fin n₀, Kfin i) ∪ closedBall 0 r,
    (isCompact_iUnion fun i => hKfin_compact i).union (isCompact_closedBall 0 r), ?_⟩
  -- Step 4: Verify ν(Kᶜ) ≤ ε for all ν in range(μs)
  intro ν hν
  obtain ⟨n, rfl⟩ := hν
  by_cases hn : n < n₀
  · -- Case n < n₀: Kᶜ ⊆ (K_n)ᶜ, so measure is at most ε
    calc (μs n : Measure ℝ) ((⋃ i : Fin n₀, Kfin i) ∪ closedBall 0 r)ᶜ
        ≤ (μs n : Measure ℝ) (Kfin ⟨n, hn⟩)ᶜ := by
          apply measure_mono
          apply compl_subset_compl.mpr
          exact subset_union_of_subset_left (subset_iUnion Kfin ⟨n, hn⟩) _
      _ ≤ ε := hKfin_meas ⟨n, hn⟩
  · -- Case n ≥ n₀: use the tail bound from charfun convergence
    push_neg at hn
    -- The complement of our K is contained in (closedBall 0 r)ᶜ
    have hcompl_sub : ((⋃ i : Fin n₀, Kfin i) ∪ closedBall 0 r)ᶜ ⊆ (closedBall 0 r)ᶜ :=
      compl_subset_compl.mpr subset_union_right
    -- (closedBall 0 r)ᶜ = {x | r < |x|} on ℝ
    have hball_eq : (closedBall (0 : ℝ) r)ᶜ = {x | r < |x|} := by
      ext x
      simp only [mem_compl_iff, mem_closedBall, Real.dist_eq, sub_zero, not_le, mem_setOf_eq,
        lt_abs]
    calc (μs n : Measure ℝ) ((⋃ i : Fin n₀, Kfin i) ∪ closedBall 0 r)ᶜ
        ≤ (μs n : Measure ℝ) (closedBall 0 r)ᶜ := measure_mono hcompl_sub
      _ = (μs n : Measure ℝ) {x | r < |x|} := by rw [hball_eq]
      _ = ENNReal.ofReal ((μs n : Measure ℝ).real {x | r < |x|}) := by
          rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal δ := by
          exact ENNReal.ofReal_le_ofReal (le_of_lt (htail n hn))
      _ ≤ ε := hδ_le

end Tightness

/-! ### Lévy's continuity theorem -/

/-- **Lévy's continuity theorem (hard direction).** Pointwise convergence of characteristic
functions of probability measures on ℝ implies weak convergence.

Proof outline:
1. By `isTight_of_charFunTendsto`, the sequence is tight.
2. By Prokhorov's theorem (tight ⇒ relatively compact), every subsequence has a
   further weakly convergent subsequence.
3. By the easy direction + charfun injectivity (`Measure.ext_of_charFun`), all
   subsequential limits equal μ.
4. By `tendsto_of_subseq_tendsto`, the full sequence converges. -/
theorem tendsto_of_charFunTendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : CharFunTendsto μs atTop μ) : Tendsto μs atTop (𝓝 μ) := by
  -- Use the subsequence criterion: every subsequence has a further subsequence → μ.
  apply tendsto_of_subseq_tendsto
  intro ns hns
  -- Step 1: charfun convergence passes to the subsequence μs ∘ ns.
  have h_sub : CharFunTendsto (μs ∘ ns) atTop μ := fun ξ => (h ξ).comp hns
  -- Step 2: The subsequence is tight.
  have h_tight := isTight_of_charFunTendsto h_sub
  -- Step 3: By Prokhorov, the closure of the range is compact.
  -- We need to massage the tightness set to match Prokhorov's expected form.
  have h_tight' : IsTightMeasureSet
      {((ν : ProbabilityMeasure ℝ) : Measure ℝ) | ν ∈ Set.range (μs ∘ ns)} := by
    convert h_tight using 1
    ext x; simp [Set.mem_range]
  have h_compact : IsCompact (closure (Set.range (μs ∘ ns))) :=
    isCompact_closure_of_isTightMeasureSet h_tight'
  -- Step 4: Extract a convergent sub-subsequence.
  -- Every element of the sequence is in the closure of the range.
  have h_in_closure : ∀ n, (μs ∘ ns) n ∈ closure (Set.range (μs ∘ ns)) :=
    fun n => subset_closure (Set.mem_range_self n)
  obtain ⟨ν, _, φ, hφ_mono, hφ_tendsto⟩ :=
    h_compact.tendsto_subseq h_in_closure
  -- Step 5: Identify the limit ν = μ.
  -- The sub-subsequence converges weakly to ν, so charfuns converge to those of ν.
  have h_sub_sub_weak : CharFunTendsto (μs ∘ ns ∘ φ) atTop ν :=
    charFunTendsto_of_tendsto hφ_tendsto
  -- But also charfuns of the sub-subsequence converge to those of μ.
  have h_sub_sub_μ : CharFunTendsto (μs ∘ ns ∘ φ) atTop μ :=
    fun ξ => (h_sub ξ).comp hφ_mono.tendsto_atTop
  -- By uniqueness of limits (T2 space), characteristicFun ν = characteristicFun μ.
  have h_charfun_eq : charFun (ν : Measure ℝ) = charFun (μ : Measure ℝ) := by
    ext ξ
    have h1 := h_sub_sub_weak ξ
    have h2 := h_sub_sub_μ ξ
    simp only [Function.comp_def, characteristicFun_def] at h1 h2
    exact tendsto_nhds_unique h1 h2
  -- By charfun injectivity, (ν : Measure ℝ) = (μ : Measure ℝ).
  have h_meas_eq : (ν : Measure ℝ) = (μ : Measure ℝ) :=
    Measure.ext_of_charFun h_charfun_eq
  -- Lift to ν = μ.
  have h_eq : ν = μ := Subtype.ext h_meas_eq
  -- The sub-subsequence converges to μ.
  exact ⟨φ, h_eq ▸ hφ_tendsto⟩

/-- **Lévy's continuity theorem.** A sequence of probability measures on ℝ converges
weakly if and only if their characteristic functions converge pointwise. -/
theorem tendsto_iff_charFunTendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} :
    Tendsto μs atTop (𝓝 μ) ↔ CharFunTendsto μs atTop μ :=
  ⟨charFunTendsto_of_tendsto, tendsto_of_charFunTendsto⟩

/-! ### Convenience API -/

/-- Dot notation shorthand: `CharFunTendsto` implies weak convergence. -/
theorem CharFunTendsto.tendsto {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : CharFunTendsto μs atTop μ) : Tendsto μs atTop (𝓝 μ) :=
  tendsto_of_charFunTendsto h

/-- Subsequence compatibility: if characteristic functions converge along the full
sequence, they also converge along any subsequence. -/
theorem CharFunTendsto.comp {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : CharFunTendsto μs atTop μ) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    CharFunTendsto (μs ∘ ns) atTop μ :=
  fun ξ => (h ξ).comp hns

/-- Weak convergence of pushforward measures via characteristic functions.
If Xₙ are measurable maps and the characteristic functions of their pushforward
measures converge pointwise to those of X's pushforward, then the pushforward
measures converge weakly. -/
theorem tendsto_map_of_charFunTendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Xs : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXs : ∀ n, Measurable (Xs n)) (hX : Measurable X)
    (h : ∀ ξ : ℝ, Tendsto (fun n => ∫ ω, exp (↑(ξ * Xs n ω) * I) ∂P)
      atTop (𝓝 (∫ ω, exp (↑(ξ * X ω) * I) ∂P)))
    {μs : ℕ → ProbabilityMeasure ℝ}
    (hμs : ∀ n, (μs n : Measure ℝ) = P.map (Xs n))
    {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) = P.map X) :
    Tendsto μs atTop (𝓝 μ) := by
  -- It suffices to show CharFunTendsto and apply the hard direction.
  apply tendsto_of_charFunTendsto
  intro ξ
  simp only [characteristicFun_def, charFun_apply_real]
  -- Rewrite charFun integrals over pushforward measures via change of variables.
  simp_rw [hμs, hμ]
  have hfm : StronglyMeasurable (fun x : ℝ => exp (↑ξ * ↑x * I)) :=
    (by fun_prop : Continuous (fun x : ℝ => exp (↑ξ * ↑x * I))).stronglyMeasurable
  have hrw : ∀ n, ∫ x, exp (↑ξ * ↑x * I) ∂(P.map (Xs n)) =
      ∫ ω, exp (↑ξ * ↑(Xs n ω) * I) ∂P :=
    fun n => integral_map_of_stronglyMeasurable (hXs n) hfm
  have hrw_lim : ∫ x, exp (↑ξ * ↑x * I) ∂(P.map X) =
      ∫ ω, exp (↑ξ * ↑(X ω) * I) ∂P :=
    integral_map_of_stronglyMeasurable hX hfm
  simp_rw [hrw, hrw_lim]
  -- Now the goal matches the hypothesis up to a cast rewrite.
  convert h ξ using 2 <;> {congr 1; ext ω; push_cast; ring}

end MeasureTheory.ProbabilityMeasure
