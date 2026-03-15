/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Fourier.PositiveDefinite
import LeanLevy.Fourier.MeasureFourier
import LeanLevy.Probability.WeakConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Fourier.Inversion

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

The main theorems `bochner` and `exists_probMeasure_of_pd_integrable` are fully proved modulo
five sorry'd helper lemmas. The proof of `charFun_inverseFourierDensity` is structured via
mathlib's Fourier inversion theorem (`Continuous.fourierInv_fourier_eq`), reducing to:

* `re_nonneg_double_integral` — the PD quadratic form `∫∫ ψ(s-t) e^{-ix(s-t)} ds dt` has
  non-negative real part (Riemann sum approximation of the PD condition).
* `fejerApproximant_eq_double_integral` — the Fejér integral equals `(1/N)` times the double
  integral over `[0,N]²` (change of variables `u = s-t`, Fubini).
* `fourierTransform_rescaled_eq` — convention bridge: `𝓕(ψ(2π·))(y) = ↑(ρ(y))` where
  ρ is the inverseFourierDensity (change of variables `u=2πw` + Hermitianness).
* `integrable_inverseFourierDensity` — `ρ ∈ L¹` (from ρ ≥ 0 + Gaussian regularization).
* Convention bridge in `charFun_inverseFourierDensity` — inner product on ℝ simplification.

Previously sorry'd and now proved:
* `tendsto_fejerApproximant` — `F_N(x) → ρ(x)` by DCT with triangle window convergence.
* `integral_inverseFourierDensity_eq_one` — `∫ ρ = 1`, derived from `charFun_inverseFourierDensity`
  at `ξ = 0`.
-/

open MeasureTheory Complex ComplexConjugate Filter Topology Set
open scoped NNReal ENNReal FourierTransform RealInnerProductSpace

namespace ProbabilityTheory

/-! ### Sorry'd helper lemmas -/

/-- The inverse Fourier density of an L¹ function, using the probabilist convention:
`ρ(x) = (1/(2π)) · Re(∫ ψ(u) e^{-ixu} du)`.

When `ψ` is a PD function with `ψ(0) = 1`, this gives the probability density whose
characteristic function is `ψ`. -/
private noncomputable def inverseFourierDensity (ψ : ℝ → ℂ) (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * (∫ u, ψ u * exp (-(↑x * ↑u * I))).re

/-- The Fejér approximant: the tapered inverse Fourier transform with triangle window.
`F_N(x) = (1/2π) ∫_{-N}^{N} ψ(u) e^{-ixu} (1 - |u|/N) du`.

This equals `(1/(2πN)) |∫_0^N e^{-ixu} du|²` when viewed through the PD lens. -/
private noncomputable def fejerApproximant (ψ : ℝ → ℂ) (N : ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) *
    (∫ u in Set.Icc (-N) N,
      ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re

/-- The integral of `ψ(s-t) e^{-ix(s-t)}` over the square `[0,N]²` has non-negative real part
when `ψ` is positive definite. This is the continuous analogue of the PD quadratic form. -/
private theorem re_nonneg_double_integral (ψ : ℝ → ℂ) (hpd : IsPositiveDefinite ψ)
    (N : ℝ) (hN : 0 < N) (x : ℝ) :
    0 ≤ (∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N,
      ψ (s - t) * exp (-(↑x * ↑(s - t) * I))).re := by
  sorry -- PD quadratic form: Riemann sums of ∑ᵢ ∑ⱼ conj(cᵢ)cⱼψ(sᵢ-sⱼ) ≥ 0 → limit ≥ 0

/-- The Fejér integral equals `(1/N)` times the double integral over `[0,N]²`. -/
private theorem fejerApproximant_eq_double_integral (ψ : ℝ → ℂ) (N : ℝ) (hN : 0 < N) (x : ℝ) :
    (∫ u in Set.Icc (-N) N,
      ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re =
    (1 / N) * (∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N,
      ψ (s - t) * exp (-(↑x * ↑(s - t) * I))).re := by
  -- Change of variables: u = s-t in the double integral gives the Fejér kernel weight.
  sorry

private theorem fejerApproximant_nonneg (ψ : ℝ → ℂ) (hpd : IsPositiveDefinite ψ)
    (N : ℝ) (hN : 0 < N) (x : ℝ) : 0 ≤ fejerApproximant ψ N x := by
  unfold fejerApproximant
  apply mul_nonneg
  · apply div_nonneg one_pos.le
    exact mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos |>.le
  · rw [fejerApproximant_eq_double_integral ψ N hN x]
    apply mul_nonneg
    · exact div_nonneg one_pos.le hN.le
    · exact re_nonneg_double_integral ψ hpd N hN x

/-- The Fejér approximants converge pointwise to the inverse Fourier density, under
the integrability assumption on `ψ`. By DCT: the tapered integrand converges to the
un-tapered integrand, dominated by `‖ψ‖ ∈ L¹`. -/
private theorem tendsto_fejerApproximant (ψ : ℝ → ℂ) (hI : Integrable ψ volume) (x : ℝ) :
    Tendsto (fun n : ℕ => fejerApproximant ψ (↑n + 1) x)
      atTop (𝓝 (inverseFourierDensity ψ x)) := by
  unfold fejerApproximant inverseFourierDensity
  -- It suffices to show the .re parts converge, then multiply by the constant.
  apply Filter.Tendsto.const_mul
  apply Complex.continuous_re.continuousAt.tendsto.comp
  -- Rewrite set integral as full integral with indicator.
  set f : ℝ → ℂ := fun u => ψ u * exp (-(↑x * ↑u * I))
  set F : ℕ → ℝ → ℂ := fun n u =>
    (Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1)).indicator
      (fun u => ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1)))) u
  have hset_eq : ∀ n : ℕ, ∫ u in Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1),
      ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1))) =
      ∫ u, F n u := by
    intro n; rw [← integral_indicator (measurableSet_Icc)]
  simp_rw [hset_eq]
  -- Apply DCT
  apply tendsto_integral_of_dominated_convergence (fun u => ‖ψ u‖)
  · -- F n is AEStronglyMeasurable
    intro n
    apply AEStronglyMeasurable.indicator _ measurableSet_Icc
    apply AEStronglyMeasurable.mul
    · exact (hI.1.mul ((((continuous_ofReal.comp continuous_const).mul continuous_ofReal).mul
        continuous_const).neg.cexp).aestronglyMeasurable)
    · exact (continuous_const.sub (continuous_ofReal.comp
        (continuous_abs.div_const _))).aestronglyMeasurable
  · exact hI.norm
  · -- ‖F n u‖ ≤ ‖ψ u‖
    intro n; apply ae_of_all; intro u
    simp only [F]
    by_cases hu : u ∈ Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1)
    · rw [Set.indicator_of_mem hu, norm_mul, norm_mul]
      have hN_pos : (0 : ℝ) < ↑n + 1 := by positivity
      have hu_abs_le : |u| ≤ ↑n + 1 :=
        abs_le.mpr ⟨by linarith [(Set.mem_Icc.mp hu).1], (Set.mem_Icc.mp hu).2⟩
      have hfrac_le : |u| / (↑n + 1) ≤ 1 := (div_le_one hN_pos).mpr hu_abs_le
      have hfrac_nn : 0 ≤ 1 - |u| / (↑n + 1) := by linarith
      calc ‖ψ u‖ * ‖exp (-(↑x * ↑u * I))‖ * ‖(1 - ↑(|u| / (↑n + 1)) : ℂ)‖
          ≤ ‖ψ u‖ * 1 * 1 := by
            gcongr
            · rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                norm_exp_ofReal_mul_I]
            · -- ‖1 - ↑(|u|/(n+1))‖ ≤ 1
              calc ‖(1 : ℂ) - ↑(|u| / (↑n + 1))‖
                  = ‖(↑(1 - |u| / (↑n + 1)) : ℂ)‖ := by push_cast; ring_nf
                _ = |1 - |u| / (↑n + 1)| := Complex.norm_real _
                _ = 1 - |u| / (↑n + 1) := abs_of_nonneg hfrac_nn
                _ ≤ 1 := by linarith [div_nonneg (abs_nonneg u) (le_of_lt hN_pos)]
        _ = ‖ψ u‖ := by ring
    · rw [Set.indicator_apply, if_neg hu, norm_zero]; exact norm_nonneg _
  · -- F n u → f u pointwise a.e.
    apply ae_of_all; intro u
    simp only [F]
    -- Eventually u ∈ Icc(-(n+1), n+1)
    have hmem : ∀ᶠ n : ℕ in atTop, u ∈ Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1) := by
      rw [Filter.eventually_atTop]
      exact ⟨⌈|u|⌉₊, fun n hn => by
        have hle : |u| ≤ ↑n + 1 := by
          calc |u| ≤ ↑⌈|u|⌉₊ := Nat.le_ceil |u|
            _ ≤ ↑n := Nat.cast_le.mpr hn
            _ ≤ ↑n + 1 := le_add_of_nonneg_right zero_le_one
        exact Set.mem_Icc.mpr ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩⟩
    -- Eventually the indicator is just the function value
    have heq : ∀ᶠ n : ℕ in atTop,
        (Set.Icc (-(↑n + 1 : ℝ)) (↑n + 1)).indicator
          (fun u => ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1)))) u =
        ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / (↑n + 1))) :=
      hmem.mono fun n hn => Set.indicator_of_mem hn _
    apply Tendsto.congr' (EventuallyEq.symm heq)
    -- ψ(u) * exp(...) * (1 - |u|/(n+1)) → ψ(u) * exp(...) as (1 - |u|/(n+1)) → 1
    have h_frac : Tendsto (fun n : ℕ => |u| / ((↑n : ℝ) + 1)) atTop (𝓝 0) := by
      apply Filter.Tendsto.div_atTop tendsto_const_nhds
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h_window : Tendsto (fun n : ℕ => (1 : ℂ) - ↑(|u| / ((↑n : ℝ) + 1))) atTop (𝓝 1) := by
      have hc : Tendsto (fun n : ℕ => (↑(|u| / ((↑n : ℝ) + 1)) : ℂ)) atTop (𝓝 0) := by
        rw [show (0 : ℂ) = ↑(0 : ℝ) from by simp]
        exact (Complex.continuous_ofReal.tendsto 0).comp h_frac
      have h1 : Tendsto (fun n : ℕ => (1 : ℂ) - ↑(|u| / ((↑n : ℝ) + 1))) atTop
          (𝓝 ((1 : ℂ) - 0)) := (tendsto_const_nhds (x := (1 : ℂ))).sub hc
      simp only [sub_zero] at h1
      exact h1
    conv_rhs => rw [show ψ u * exp (-(↑x * ↑u * I)) =
      ψ u * exp (-(↑x * ↑u * I)) * 1 from (mul_one _).symm]
    exact tendsto_const_nhds.mul h_window

/-- The inverse Fourier density is non-negative for PD + L¹ functions, as the pointwise
limit of non-negative Fejér approximants. -/
private theorem inverseFourierDensity_nonneg (ψ : ℝ → ℂ) (hpd : IsPositiveDefinite ψ)
    (hI : Integrable ψ volume) (x : ℝ) : 0 ≤ inverseFourierDensity ψ x :=
  ge_of_tendsto (tendsto_fejerApproximant ψ hI x)
    (Eventually.of_forall fun n => fejerApproximant_nonneg ψ hpd (↑n + 1) (by positivity) x)

/-- The inverse Fourier density is continuous (hence measurable) for continuous L¹ ψ.
Proof: the integrand `ψ(u) exp(-ixu)` is continuous in x, bounded by `‖ψ(u)‖ ∈ L¹`,
so by DCT the integral is continuous. -/
private theorem continuous_inverseFourierDensity (ψ : ℝ → ℂ)
    (hψc : Continuous ψ) (hI : Integrable ψ volume) :
    Continuous (inverseFourierDensity ψ) := by
  unfold inverseFourierDensity
  apply Continuous.const_mul
  apply Complex.continuous_re.comp
  -- The integral ∫ u, ψ u * exp(-ixu) is continuous in x : ℝ
  -- We use continuous_of_dominated with F(x, u) = ψ(u) * exp(-i·x·u)
  set G : ℝ → ℝ → ℂ := fun x u => ψ u * exp (-(↑x * ↑u * I)) with hG_def
  have hG_cont : Continuous fun x => ∫ u, G x u := by
    exact continuous_of_dominated
      (fun (x : ℝ) => by
        show AEStronglyMeasurable (fun u => ψ u * exp (-((x : ℂ) * ↑u * I))) volume
        exact (hψc.mul ((((continuous_ofReal.comp continuous_const).mul continuous_ofReal).mul
          continuous_const).neg.cexp)).aestronglyMeasurable)
      (fun x => ae_of_all _ fun u => by
        show ‖G x u‖ ≤ ‖ψ u‖
        simp only [G, norm_mul]
        rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
          norm_exp_ofReal_mul_I, mul_one])
      hI.norm
      (ae_of_all _ fun u => by
        show Continuous fun (y : ℝ) => G y u
        simp only [G]
        refine Continuous.mul continuous_const (Complex.continuous_exp.comp ?_)
        exact ((Complex.continuous_ofReal.mul continuous_const).mul continuous_const).neg)
  convert hG_cont using 1

/-- Bridge lemma: the Fourier transform of `w ↦ ψ(2πw)` (in the mathematician's convention)
equals `↑(inverseFourierDensity ψ y)` for PD integrable `ψ`. This uses that the FT integral
is real-valued by Hermitian symmetry, and changes variables `u = 2πw` in the integral. -/
private theorem fourierTransform_rescaled_eq (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (hI : Integrable ψ volume) (y : ℝ) :
    𝓕 (fun w => ψ (2 * Real.pi * w)) y = ↑(inverseFourierDensity ψ y) := by
  -- 𝓕 f(y) = ∫ exp(-2πi w y) ψ(2πw) dw
  -- Substitute u = 2πw, du = 2π dw:
  -- = (1/(2π)) ∫ exp(-i u y) ψ(u) du
  -- The integral ∫ ψ(u) exp(-iyu) du is real by Hermitianness of ψ.
  -- So this equals (1/(2π)) (∫ ψ(u) exp(-iyu) du).re = inverseFourierDensity ψ y.
  sorry

/-- The inverseFourierDensity is integrable for PD+continuous+L¹ functions.
Proof: ρ ≥ 0 (from Fejér argument) and the Gaussian regularization shows ∫ ρ = 1. -/
private theorem integrable_inverseFourierDensity (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) :
    Integrable (inverseFourierDensity ψ) volume := by
  -- ρ ≥ 0 (from inverseFourierDensity_nonneg, which uses Fejér ≥ 0)
  have hρ_nn := inverseFourierDensity_nonneg ψ hpd hI
  -- The approximate identity gives ∫ ρ(x) exp(-δx²) dx → ψ(0) = 1.
  -- Since ρ ≥ 0, by monotone convergence ∫ ρ = 1, hence ρ ∈ L¹.
  -- Alternatively: ρ = 𝓕 f (rescaled), and 𝓕 f ≥ 0 + ∫ 𝓕 f exp(-δ·²) → 1
  -- gives 𝓕 f ∈ L¹.
  sorry

set_option maxHeartbeats 800000 in
/-- The characteristic function of the measure with density `inverseFourierDensity ψ`
equals `ψ`, assuming `ψ` is continuous and L¹. This is the Fourier inversion theorem
specialized to the probabilist convention. -/
private theorem charFun_inverseFourierDensity (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) (ξ : ℝ) :
    ∫ x, (inverseFourierDensity ψ x : ℝ) • exp (↑ξ * ↑x * I) = ψ ξ := by
  -- Proof via Fourier inversion theorem (mathlib).
  -- Define the rescaled function f(w) = ψ(2πw).
  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  set f : ℝ → ℂ := fun w => ψ (2 * Real.pi * w) with hf_def
  have hf_int : Integrable f volume := by
    show Integrable (fun w => ψ (2 * Real.pi * w)) volume
    exact hI.comp_mul_left' h2pi_ne
  have hf_cont : Continuous f := hψc.comp (continuous_const.mul continuous_id)
  -- 𝓕 f = ↑ ∘ inverseFourierDensity ψ
  have hFf_eq : ∀ y, 𝓕 f y = ↑(inverseFourierDensity ψ y) :=
    fourierTransform_rescaled_eq ψ hψc hpd hI
  -- 𝓕 f is integrable (from ρ ≥ 0 + Gaussian regularization)
  have hFf_int : Integrable (𝓕 f) volume := by
    rw [show 𝓕 f = fun y => (↑(inverseFourierDensity ψ y) : ℂ) from funext hFf_eq]
    exact (integrable_inverseFourierDensity ψ hψc hpd h0 hI).ofReal
  -- Apply Fourier inversion: 𝓕⁻(𝓕 f)(v) = f(v) for all v.
  have hinv := hf_cont.fourierInv_fourier_eq hf_int hFf_int
  -- Evaluate at v = ξ/(2π)
  set v := ξ / (2 * Real.pi) with hv_def
  have hfv : f v = ψ ξ := by
    simp only [hf_def, hv_def, mul_div_cancel₀ _ h2pi_ne]
  -- hinv says 𝓕⁻(𝓕 f) = f, so 𝓕⁻(𝓕 f)(v) = ψ(ξ)
  have hinv_v := congr_fun hinv v
  rw [hfv] at hinv_v
  -- 𝓕⁻(𝓕 f)(v) = ∫ exp(2πi⟪y,v⟫) (𝓕 f)(y) dy = ∫ exp(2πi y ξ/(2π)) ↑(ρ(y)) dy
  -- = ∫ exp(iξy) ↑(ρ(y)) dy = ∫ ↑(ρ(y)) • exp(iξy) dy
  -- This equals our goal.
  rw [← hinv_v]
  -- Now show 𝓕⁻(𝓕 f)(v) = ∫ (inverseFourierDensity ψ x) • exp(iξx) dx
  -- 𝓕⁻(𝓕 f)(v) = ∫ y, 𝐞(⟪y,v⟫) • (𝓕 f)(y) = ∫ y, exp(2πi y v) • ↑(ρ(y))
  -- Since v = ξ/(2π): exp(2πi y v) = exp(iξy), so integrand = ↑(ρ(y)) • exp(iξy)
  -- Change of inner product convention: ⟪y,v⟫ = y*v on ℝ, so 2π⟪y,v⟫ = 2πyξ/(2π) = ξy.
  -- Convention bridge: 𝓕⁻(𝓕 f)(v) uses exp(2πi⟪y,v⟫) and our goal uses exp(iξy).
  -- Since v = ξ/(2π) and ⟪y,v⟫ = y·v on ℝ: 2π·y·ξ/(2π) = ξ·y.
  -- So the integrands match after this simplification.
  rw [Real.fourierInv_eq']
  simp_rw [hFf_eq]
  -- The integrands match: exp(2πi⟪y,v⟫) • ↑(ρ(y)) = ↑(ρ(y)) • exp(iξy)
  -- since ⟪y,v⟫ = y·v = y·ξ/(2π) on ℝ, so 2π⟪y,v⟫ = ξy.
  -- Both sides equal ↑(ρ(y)) * exp(iξy) after commuting the scalar mul.
  -- The integrands are equal after simplifying the inner product on ℝ:
  -- ⟪y,v⟫ = y*v, 2π*y*v = 2π*y*ξ/(2π) = ξ*y, so exp terms match.
  -- The scalar multiplication commutes: 𝐞(t) • ↑r = ↑r • 𝐞(t) since ℂ is commutative.
  congr 1; ext y
  -- Both sides equal ↑(ρ(y)) * cexp(↑ξ * ↑y * I).
  -- LHS: 𝐞(⟪y,v⟫) • ↑(ρ(y)) = cexp(2πi⟪y,v⟫) * ↑(ρ(y))
  -- with ⟪y,v⟫ = y*v = y*ξ/(2π), so 2π⟪y,v⟫ = ξy.
  -- RHS: ↑(ρ(y)) • cexp(↑ξ * ↑y * I) = ↑(ρ(y)) * cexp(↑ξ * ↑y * I)
  -- These are equal by commutativity of multiplication.
  simp only [Circle.smul_def, Real.fourierChar_apply, Complex.real_smul, hv_def,
    Complex.ofReal_mul, Complex.ofReal_div]
  -- Inner product on ℝ: ⟪y, v⟫ = y * v, then 2π(y·ξ/(2π)) = ξy.
  -- After unfolding, both sides are ↑(ρ(y)) * cexp(↑(ξ*y)*I).
  sorry

/-- The inverse Fourier density integrates to 1 when `ψ(0) = 1`.
Derived from `charFun_inverseFourierDensity` at `ξ = 0`. -/
private theorem integral_inverseFourierDensity_eq_one (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) :
    ∫ x, inverseFourierDensity ψ x = 1 := by
  -- Deduce from charFun_inverseFourierDensity at ξ = 0
  have h := charFun_inverseFourierDensity ψ hψc hpd h0 hI 0
  -- At ξ = 0, exp(0·x·I) = 1, so (r : ℝ) • 1 = ↑r
  have heq : ∀ x : ℝ, (inverseFourierDensity ψ x : ℝ) • exp ((0 : ℝ) * ↑x * I) =
      ↑(inverseFourierDensity ψ x) := by
    intro x; simp [Complex.real_smul]
  simp_rw [heq, h0] at h
  -- h : ∫ x, (↑(inverseFourierDensity ψ x) : ℂ) = 1
  have := congr_arg Complex.re h
  simp only [Complex.one_re] at this
  rwa [show (∫ x : ℝ, (↑(inverseFourierDensity ψ x) : ℂ)).re =
    ∫ x, inverseFourierDensity ψ x from by
    have : ∫ x : ℝ, (↑(inverseFourierDensity ψ x) : ℂ) =
      ↑(∫ x, inverseFourierDensity ψ x) := integral_ofReal
    rw [this, Complex.ofReal_re]] at this

/-- **Fourier inversion for PD L¹ functions.** A continuous, positive definite, integrable
function with `ψ(0) = 1` is the characteristic function of a probability measure.

Proof: The inverse Fourier density `ρ(x) = (1/2π) Re(∫ ψ(u) e^{-ixu} du)` is non-negative
(by the Fejér approximation argument), integrates to 1 (by Gaussian regularization), and
has characteristic function equal to `ψ` (by Fourier inversion). -/
private theorem exists_probMeasure_of_pd_integrable
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hpd : IsPositiveDefinite ψ)
    (h0 : ψ 0 = 1) (_hI : Integrable ψ volume) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ ξ, ProbabilityMeasure.characteristicFun μ ξ = ψ ξ := by
  -- Construct the measure with density ρ = inverseFourierDensity ψ
  set ρ := inverseFourierDensity ψ with hρ_def
  have hρ_nn : ∀ x, 0 ≤ ρ x := inverseFourierDensity_nonneg ψ hpd _hI
  have hρ_cont := continuous_inverseFourierDensity ψ hψc _hI
  have hρ_int : ∫ x, ρ x = 1 := integral_inverseFourierDensity_eq_one ψ hψc hpd h0 _hI
  have hρ_integrable : Integrable ρ volume := integrable_of_integral_eq_one hρ_int
  -- Define the measure
  set μ_raw : Measure ℝ := volume.withDensity (fun x => ENNReal.ofReal (ρ x)) with hμ_def
  -- Show it's a probability measure
  have hμ_prob : IsProbabilityMeasure μ_raw := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ]
    rw [Measure.restrict_univ]
    rw [show (∫⁻ x, ENNReal.ofReal (ρ x)) = ENNReal.ofReal (∫ x, ρ x) from by
      rw [ofReal_integral_eq_lintegral_ofReal hρ_integrable (ae_of_all _ hρ_nn)]]
    rw [hρ_int, ENNReal.ofReal_one]
  -- Wrap as ProbabilityMeasure
  set μ_pm : ProbabilityMeasure ℝ := ⟨μ_raw, hμ_prob⟩ with hμ_pm_def
  refine ⟨μ_pm, fun ξ => ?_⟩
  -- Show charFun μ_pm ξ = ψ ξ
  simp only [MeasureTheory.ProbabilityMeasure.characteristicFun_def, charFun_apply_real]
  change ∫ x, exp (↑ξ * ↑x * I) ∂μ_raw = ψ ξ
  -- Rewrite the integral against μ_raw = withDensity(ofReal ρ)
  rw [hμ_def, integral_withDensity_eq_integral_toReal_smul
    (hρ_cont.measurable.ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  -- Goal: ∫ x, (ENNReal.ofReal (inverseFourierDensity ψ x)).toReal • exp(ξxI) = ψ ξ
  -- Simplify toReal ∘ ofReal using non-negativity
  have h_eq : ∀ x : ℝ, (ENNReal.ofReal (inverseFourierDensity ψ x)).toReal =
      inverseFourierDensity ψ x := fun x => ENNReal.toReal_ofReal (hρ_nn x)
  simp_rw [h_eq]
  exact charFun_inverseFourierDensity ψ hψc hpd h0 _hI ξ

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
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun _ _ => hε_top ▸ le_top⟩
  set δ := ε.toReal with hδ_def
  have hδ_pos : 0 < δ := ENNReal.toReal_pos hε.ne' hε_top
  have hδ_le : ENNReal.ofReal δ ≤ ε := by
    rw [hδ_def, ENNReal.ofReal_toReal hε_top]
  obtain ⟨r, hr, n₀, htail⟩ :=
    MeasureTheory.ProbabilityMeasure.exists_radius_and_threshold_of_continuous_tendsto _hφc _hφ0 _hconv hδ_pos
  have hfin : ∀ n : Fin n₀, ∃ K : Set ℝ, IsCompact K ∧ (μs n : Measure ℝ) Kᶜ ≤ ε := by
    intro ⟨n, hn⟩
    have := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := (μs n : Measure ℝ))) ε hε
    obtain ⟨K, hK, hKε⟩ := this
    exact ⟨K, hK, hKε _ rfl⟩
  choose Kfin hKfin_compact hKfin_meas using hfin
  refine ⟨(⋃ i : Fin n₀, Kfin i) ∪ Metric.closedBall 0 r,
    (isCompact_iUnion fun i => hKfin_compact i).union (isCompact_closedBall 0 r), ?_⟩
  intro ν hν
  obtain ⟨n, rfl⟩ := hν
  by_cases hn : n < n₀
  · calc (μs n : Measure ℝ) ((⋃ i : Fin n₀, Kfin i) ∪ Metric.closedBall 0 r)ᶜ
        ≤ (μs n : Measure ℝ) (Kfin ⟨n, hn⟩)ᶜ := by
          apply measure_mono
          apply compl_subset_compl.mpr
          exact subset_union_of_subset_left (subset_iUnion Kfin ⟨n, hn⟩) _
      _ ≤ ε := hKfin_meas ⟨n, hn⟩
  · push_neg at hn
    have hcompl_sub : ((⋃ i : Fin n₀, Kfin i) ∪ Metric.closedBall 0 r)ᶜ ⊆
        (Metric.closedBall (0 : ℝ) r)ᶜ :=
      compl_subset_compl.mpr subset_union_right
    have hball_eq : (Metric.closedBall (0 : ℝ) r)ᶜ = {x | r < |x|} := by
      ext x
      simp only [mem_compl_iff, Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le,
        mem_setOf_eq, lt_abs]
    calc (μs n : Measure ℝ) ((⋃ i : Fin n₀, Kfin i) ∪ Metric.closedBall 0 r)ᶜ
        ≤ (μs n : Measure ℝ) (Metric.closedBall 0 r)ᶜ := measure_mono hcompl_sub
      _ = (μs n : Measure ℝ) {x | r < |x|} := by rw [hball_eq]
      _ = ENNReal.ofReal ((μs n : Measure ℝ).real {x | r < |x|}) := by
          rw [ofReal_measureReal]
      _ ≤ ENNReal.ofReal δ := by
          exact ENNReal.ofReal_le_ofReal (le_of_lt (htail n hn))
      _ ≤ ε := hδ_le

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
