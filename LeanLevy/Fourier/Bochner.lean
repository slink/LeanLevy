/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Fourier.PositiveDefinite
import LeanLevy.Fourier.MeasureFourier
import LeanLevy.Probability.WeakConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Bochner's Theorem on ℝ

## Main results

* `ProbabilityTheory.bochner` — a continuous positive definite function `φ` with `φ(0) = 1`
  is the characteristic function of a probability measure.

## Proof strategy

Bochner uses Gaussian smoothing + Lévy continuity (no Riesz representation needed):

1. Multiply `φ` by Gaussian `exp(-ξ²/(2n))` to get an L¹ PD function `φₙ`.
2. Show the Fourier transform of `φₙ` is non-negative (from PD + Parseval).
3. Construct probability measures `μₙ` with density proportional to `φ̂ₙ`.
4. Their characteristic functions converge to `φ` pointwise.
5. By tightness + Prokhorov, extract a convergent subsequence; identify the limit.

## Sorry audit

* `exists_probMeasure_of_pd_integrable` — PD + L¹ + normalised ⟹ ∃ probability measure.
  Core Fourier-analytic fact requiring Parseval.
* `isTight_of_charFun_pointwise_tendsto` — generalised tightness from charfun convergence
  to a continuous limit. Same proof as `isTight_of_charFunTendsto` but with abstract limit.
-/

open MeasureTheory Complex ComplexConjugate Filter Topology Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-! ### Sorry'd helper lemmas -/

/-- **Fourier inversion for PD L¹ functions.** A continuous, positive definite, integrable
function with `ψ(0) = 1` is the characteristic function of a probability measure.

**Sorry justification:** Requires showing the Fourier transform of an L¹ PD function is
non-negative (via Parseval/Plancherel), then constructing the probability density. -/
private theorem exists_probMeasure_of_pd_integrable
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hpd : IsPositiveDefinite ψ)
    (h0 : ψ 0 = 1) (_hI : Integrable ψ volume) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ ξ, ProbabilityMeasure.characteristicFun μ ξ = ψ ξ := by
  sorry

/-- **Generalised tightness from charfun convergence.** If the characteristic functions of
a sequence of probability measures converge pointwise to a continuous function `φ` with
`φ(0) = 1`, then the sequence is tight.

**Sorry justification:** Same proof as `isTight_of_charFunTendsto`, replacing `charFun μ`
with `φ` throughout. Uses `measureReal_abs_gt_le_integral_charFun`, dominated convergence,
and continuity of `φ` at 0. -/
private theorem isTight_of_charFun_pointwise_tendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {φ : ℝ → ℂ}
    (_hφc : Continuous φ) (_hφ0 : φ 0 = 1)
    (_hconv : ∀ ξ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop (𝓝 (φ ξ))) :
    IsTightMeasureSet (range (fun n => (μs n : Measure ℝ))) := by
  sorry

/-! ### Gaussian smoothing infrastructure -/

section GaussianSmoothing

/-- The Gaussian variance parameter for the n-th smoothing: `1/(n+1)` as an `ℝ≥0`. -/
private noncomputable def gaussianVar (n : ℕ) : ℝ≥0 := ⟨1 / (↑n + 1), by positivity⟩

/-- The `N(0, 1/(n+1))` Gaussian as a `ProbabilityMeasure`. -/
private noncomputable def gaussianPM (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 (gaussianVar n), inferInstance⟩

@[simp]
private theorem gaussianPM_val (n : ℕ) :
    (gaussianPM n : Measure ℝ) = gaussianReal 0 (gaussianVar n) := rfl

/-- The characteristic function of `N(0, 1/(n+1))` is positive definite. -/
private theorem pd_gaussianCharFun (n : ℕ) :
    IsPositiveDefinite (fun ξ => charFun (gaussianReal 0 (gaussianVar n)) ξ) := by
  show IsPositiveDefinite (fun ξ => charFun (gaussianPM n : Measure ℝ) ξ)
  exact IsPositiveDefinite.of_charFun (gaussianPM n)

/-- The smoothed function `φ · charFun(N(0,1/(n+1)))` is positive definite. -/
private theorem pd_smoothed {φ : ℝ → ℂ} (hpd : IsPositiveDefinite φ) (n : ℕ) :
    IsPositiveDefinite (fun ξ => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) :=
  hpd.mul (pd_gaussianCharFun n)

/-- The smoothed function at 0 equals 1. -/
private theorem smoothed_at_zero {φ : ℝ → ℂ} (h0 : φ 0 = 1) (n : ℕ) :
    φ 0 * charFun (gaussianReal 0 (gaussianVar n)) 0 = 1 := by
  simp [h0, charFun_zero]

/-- Continuity of the Gaussian characteristic function. -/
private theorem continuous_charFun_gaussianVar (n : ℕ) :
    Continuous (fun ξ => charFun (gaussianReal 0 (gaussianVar n)) ξ) := by
  simp_rw [charFun_gaussianReal]
  fun_prop

/-- Continuity of the smoothed function. -/
private theorem continuous_smoothed {φ : ℝ → ℂ} (hφc : Continuous φ) (n : ℕ) :
    Continuous (fun ξ => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) :=
  hφc.mul (continuous_charFun_gaussianVar n)

/-- The Gaussian charfun `ξ ↦ charFun(N(0,v))(ξ)` is integrable for `v > 0`.

Proof: `‖charFun(N(0,v)) ξ‖ = exp(-v/2 · ξ²)`, which is integrable as a Gaussian.
The norm equality follows from `charFun_gaussianReal` and the fact that the mean-0
Gaussian charfun has purely real, negative exponent. -/
private theorem integrable_charFun_gaussianVar (n : ℕ) :
    Integrable (fun ξ => charFun (gaussianReal 0 (gaussianVar n)) ξ) volume := by
  set v := gaussianVar n
  have hv_pos : (0 : ℝ) < (v : ℝ≥0) := by
    simp only [v, gaussianVar, NNReal.coe_mk]; positivity
  -- The norm of charFun(N(0,v)) ξ equals exp(-(v/2)·ξ²)
  have hnorm_eq : ∀ ξ : ℝ, ‖charFun (gaussianReal 0 v) ξ‖ = Real.exp (-((v : ℝ) / 2 * ξ ^ 2)) := by
    intro ξ
    rw [charFun_gaussianReal, Complex.norm_exp]
    congr 1
    simp only [ofReal_zero, mul_zero, zero_mul, zero_sub,
      Complex.neg_re, Complex.div_ofNat_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, sub_zero]
    rw [show ((↑ξ : ℂ) ^ 2).re = ξ ^ 2 by
      simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]]
    ring
  -- This function is integrable
  refine (integrable_exp_neg_mul_sq (by linarith : 0 < (v : ℝ) / 2)).mono'
    (continuous_charFun_gaussianVar n).aestronglyMeasurable ?_
  exact ae_of_all _ fun ξ => by
    rw [hnorm_eq]
    exact Real.exp_le_exp_of_le (by nlinarith)

/-- Integrability of the smoothed function (bounded by Gaussian). -/
private theorem integrable_smoothed {φ : ℝ → ℂ} (hφc : Continuous φ)
    (hpd : IsPositiveDefinite φ) (h0 : φ 0 = 1) (n : ℕ) :
    Integrable (fun ξ => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) volume := by
  exact (integrable_charFun_gaussianVar n).mono
    (continuous_smoothed hφc n).aestronglyMeasurable
    (ae_of_all _ fun ξ => by
      rw [norm_mul]
      calc ‖φ ξ‖ * ‖charFun (gaussianReal 0 (gaussianVar n)) ξ‖
          ≤ 1 * ‖charFun (gaussianReal 0 (gaussianVar n)) ξ‖ :=
            mul_le_mul_of_nonneg_right (hpd.norm_le_one h0 ξ) (norm_nonneg _)
        _ = ‖charFun (gaussianReal 0 (gaussianVar n)) ξ‖ := one_mul _)

/-- The Gaussian charfun at a fixed `ξ` tends to 1 as the variance → 0. -/
private theorem tendsto_gaussianCharFun_one (ξ : ℝ) :
    Tendsto (fun n => charFun (gaussianReal 0 (gaussianVar n)) ξ) atTop (𝓝 1) := by
  -- charFun(N(0,1/(n+1))) ξ → 1 as the Gaussian variance → 0
  simp_rw [charFun_gaussianReal]
  simp only [ofReal_zero, mul_zero, zero_mul, zero_sub]
  -- Goal: cexp(-(↑↑(gaussianVar n) * ↑ξ^2/2)) → 1
  rw [show (1 : ℂ) = cexp 0 from by simp]
  apply Filter.Tendsto.cexp
  -- The exponent -(v_n * ξ²/2) → 0 since v_n → 0
  rw [show (0 : ℂ) = -(0 * (↑ξ : ℂ) ^ 2 / 2) from by simp]
  -- Need: ↑↑(gaussianVar n) → 0 in ℂ
  have hv_tendsto : Tendsto (fun n : ℕ => (↑↑(gaussianVar n) : ℂ)) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ↑(0 : ℝ) from by simp]
    exact (Complex.continuous_ofReal.tendsto 0).comp (by
      show Tendsto (fun n : ℕ => (↑(gaussianVar n) : ℝ)) atTop (𝓝 0)
      simp only [NNReal.coe_mk, gaussianVar]
      exact tendsto_one_div_add_atTop_nhds_zero_nat)
  exact (((hv_tendsto.mul tendsto_const_nhds).div_const _).neg)

/-- The smoothed charfun converges pointwise to φ. -/
private theorem tendsto_smoothed (φ : ℝ → ℂ) (ξ : ℝ) :
    Tendsto (fun n => φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ) atTop (𝓝 (φ ξ)) := by
  conv_rhs => rw [show φ ξ = φ ξ * 1 from (mul_one _).symm]
  exact tendsto_const_nhds.mul (tendsto_gaussianCharFun_one ξ)

end GaussianSmoothing

/-! ### Main theorem -/

/-- **Bochner's theorem (ℝ only).** A continuous positive definite function `φ : ℝ → ℂ`
with `φ(0) = 1` is the characteristic function of a unique probability measure on ℝ.

Proof: Gaussian smoothing + Prokhorov + charfun identification. -/
theorem bochner
    (φ : ℝ → ℂ) (hφc : Continuous φ) (hpd : IsPositiveDefinite φ)
    (h0 : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ ξ, MeasureTheory.ProbabilityMeasure.characteristicFun μ ξ = φ ξ := by
  -- Step 1: For each n, the smoothed function φₙ(ξ) = φ(ξ) · charFun(N(0,1/(n+1)))(ξ)
  -- is continuous, PD, L¹, and equals 1 at 0.
  -- By exists_probMeasure_of_pd_integrable, get μₙ with charFun μₙ = φₙ.
  have hsmoothed : ∀ n : ℕ, ∃ μn : ProbabilityMeasure ℝ,
      ∀ ξ, ProbabilityMeasure.characteristicFun μn ξ =
        φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ :=
    fun n => exists_probMeasure_of_pd_integrable _ (continuous_smoothed hφc n)
      (pd_smoothed hpd n) (smoothed_at_zero h0 n) (integrable_smoothed hφc hpd h0 n)
  -- Extract the sequence using choice.
  choose μs hμs using hsmoothed
  -- Step 2: The characteristic functions of μₙ converge pointwise to φ.
  have hcharfun_conv :
      ∀ ξ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop (𝓝 (φ ξ)) := by
    intro ξ
    have : ∀ n, charFun (μs n : Measure ℝ) ξ =
        φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ := by
      intro n; exact (hμs n ξ).symm ▸ rfl
    simp_rw [this]
    exact tendsto_smoothed φ ξ
  -- Step 3: The sequence {μₙ} is tight.
  have htight := isTight_of_charFun_pointwise_tendsto hφc h0 hcharfun_conv
  -- Step 4: Convert to the right form for Prokhorov.
  have htight' : IsTightMeasureSet
      {((ν : ProbabilityMeasure ℝ) : Measure ℝ) | ν ∈ range μs} := by
    convert htight using 1
    ext x; simp [mem_range]
  -- Step 5: By Prokhorov, the closure of the range is compact.
  have hcompact : IsCompact (closure (range μs)) :=
    isCompact_closure_of_isTightMeasureSet htight'
  -- Step 6: Extract a convergent subsequence.
  have hin_closure : ∀ n, μs n ∈ closure (range μs) :=
    fun n => subset_closure (mem_range_self n)
  obtain ⟨ν, _, ns, hns_mono, hns_tendsto⟩ := hcompact.tendsto_subseq hin_closure
  -- Step 7: By the easy direction of Lévy, charFun ν = lim charFun μₙₖ.
  -- Also charFun μₙₖ → φ by our construction. By limit uniqueness, charFun ν = φ.
  have hcharfun_ν : ∀ ξ, ProbabilityMeasure.characteristicFun ν ξ = φ ξ := by
    intro ξ
    -- charFun (μs (ns n)) ξ → charFun ν ξ (by weak convergence)
    have h_weak := ProbabilityMeasure.charFunTendsto_of_tendsto hns_tendsto ξ
    simp only [Function.comp_def, ProbabilityMeasure.characteristicFun_def] at h_weak
    -- charFun (μs (ns n)) ξ → φ ξ (by our convergence + subsequence)
    have h_phi := (hcharfun_conv ξ).comp hns_mono.tendsto_atTop
    -- By uniqueness of limits
    exact (ProbabilityMeasure.characteristicFun_def ν ξ).symm ▸
      tendsto_nhds_unique h_weak h_phi
  -- Step 8: ν is the desired probability measure.
  exact ⟨ν, hcharfun_ν⟩

end ProbabilityTheory
