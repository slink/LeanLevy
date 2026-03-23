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
import Mathlib.MeasureTheory.Integral.Prod

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

## Proof status

All helper lemmas are fully proved (no remaining sorries). Proof techniques:

* `fejerApproximant_nonneg` — direct PD Riemann sum proof via uniform continuity on [0,N]².
* `fourierTransform_rescaled_eq` — change of variables (`integral_comp_mul_left`) + Hermitian
  symmetry.
* `integrable_inverseFourierDensity` — MCT + Fubini + `fourierIntegral_gaussian`.
* `charFun_inverseFourierDensity` convention bridge — inner product simplification via
  `real_inner_eq_re_inner`.
* `tendsto_fejerApproximant` — DCT with triangle window convergence.
* `integral_inverseFourierDensity_eq_one` — derived from `charFun_inverseFourierDensity` at
  `ξ = 0`.
* `fubini_identity` — Fubini + `fourierIntegral_gaussian` evaluation.
-/

open MeasureTheory Complex ComplexConjugate Filter Topology Set Function
open scoped NNReal ENNReal FourierTransform RealInnerProductSpace

namespace ProbabilityTheory

/-- Local replacement for the removed `intervalIntegral.integral_eq_zero_of_forall_eq_zero`.
If `f` vanishes on the open interval `Ioo (min a b) (max a b)`, then `∫ t in a..b, f t = 0`,
since the endpoints have Lebesgue measure zero. -/
private theorem intervalIntegral_eq_zero_of_forall_eq_zero {a b : ℝ} {f : ℝ → ℝ}
    (hf : ∀ t, t ∈ Set.uIoo a b → f t = 0) :
    ∫ t in a..b, f t = 0 := by
  rcases le_or_gt a b with hab | hab
  · rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun t ht => hf t (Set.uIoo_of_le hab ▸ ht)
  · rw [intervalIntegral.integral_symm, neg_eq_zero,
      intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact fun t ht => hf t (Set.uIoo_comm a b ▸ Set.uIoo_of_le hab.le ▸ ht)

/-! ### Helper lemmas -/

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

/-- The product of a PD function `ψ` and `u ↦ exp(-ixu)` is PD. -/
private theorem isPositiveDefinite_mul_exp (ψ : ℝ → ℂ) (hpd : IsPositiveDefinite ψ) (x : ℝ) :
    IsPositiveDefinite (fun u => ψ u * exp (-(↑x * ↑u * I))) := by
  have hexp_pd : IsPositiveDefinite (fun u => exp (-(↑x * ↑u * I))) := by
    intro n pts c
    have hsum_eq : ∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
        exp (-(↑x * ↑(pts i - pts j) * I)) =
        ↑(Complex.normSq (∑ i, c i * exp (↑x * ↑(pts i) * I))) := by
      rw [Complex.normSq_eq_conj_mul_self, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul, ← exp_conj, conj_ofReal, conj_I, mul_neg]
      rw [show -(↑x * ↑(pts i - pts j) * I) =
          -(↑x * ↑(pts i) * I) + ↑x * ↑(pts j) * I from by push_cast; ring,
        exp_add]
      ring
    rw [hsum_eq]
    exact_mod_cast Complex.normSq_nonneg _
  exact hpd.mul hexp_pd

/-- PD Riemann sums R_m = (h²/N) * Re(∑ᵢ ∑ⱼ g((i-j)h)) are non-negative. -/
private theorem riemannSum_nonneg_of_pd (g : ℝ → ℂ) (hg_pd : IsPositiveDefinite g)
    (N : ℝ) (hN : 0 < N) (m : ℕ) :
    0 ≤ (N / ((m : ℝ) + 1)) ^ 2 / N *
      (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        g ((i : ℝ) * (N / ((m : ℝ) + 1)) - (j : ℝ) * (N / ((m : ℝ) + 1)))).re := by
  apply mul_nonneg
  · exact div_nonneg (sq_nonneg _) hN.le
  · have h := hg_pd (m + 1)
      (fun i => (i : ℝ) * (N / ((m : ℝ) + 1))) (fun _ => 1)
    simp only [map_one, one_mul] at h
    exact (Complex.nonneg_iff.mp h).1

set_option maxHeartbeats 800000 in
/-- The Fejér tent integral equals `(1/N) * ∫_0^N ∫_0^N Re(g(s-t)) ds dt` via
Fubini and the change of variables `u = s - t`. -/
private theorem tent_integral_eq_fubini (g : ℝ → ℂ) (hg_cont : Continuous g)
    (N : ℝ) (hN : 0 < N) :
    (∫ u in Set.Icc (-N) N,
      g u * (1 - ↑(|u| / N))).re =
    (1 / N) * ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, (g (s - t)).re := by
  -- Step 1: LHS = ∫ in Icc(-N,N), (g u).re * (1-|u|/N)
  have hf_int : Integrable (fun u => g u * (1 - ↑(|u| / N : ℝ) : ℂ))
      (volume.restrict (Set.Icc (-N) N)) :=
    (hg_cont.mul (continuous_const.sub
      (continuous_ofReal.comp
        ((continuous_abs.comp continuous_id).div_const N)))).continuousOn.integrableOn_Icc
  have hLHS : (∫ u in Set.Icc (-N) N,
      g u * (1 - ↑(|u| / N))).re =
      ∫ u in Set.Icc (-N) N, (g u).re * (1 - |u| / N) := by
    calc (∫ u in Set.Icc (-N) N,
            g u * (1 - ↑(|u| / N))).re
        = ∫ u in Set.Icc (-N) N,
            (g u * (1 - ↑(|u| / N))).re :=
            (integral_re hf_int).symm
      _ = ∫ u in Set.Icc (-N) N, (g u).re * (1 - |u| / N) := by
            congr 1; ext u
            have : (1 : ℂ) - ↑(|u| / N) = ↑((1 : ℝ) - |u| / N) := by push_cast; ring
            rw [this, re_mul_ofReal]
  rw [hLHS]
  -- Step 2: ∫∫ F = ∫_{-N}^N (g u).re * (N-|u|) (Fubini + change of variables)
  set F : ℝ → ℝ → ℝ := fun s t => (g (s - t)).re with hF_def
  have hF_cts : Continuous F.uncurry :=
    (Complex.continuous_re.comp hg_cont).comp (continuous_fst.sub continuous_snd)
  have hfub : ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t =
      ∫ u in Set.Icc (-N) N, (g u).re * (N - |u|) := by
    -- Build product integrability
    have hint : Integrable F.uncurry
        ((volume.restrict (Set.Icc 0 N)).prod (volume.restrict (Set.Icc 0 N))) := by
      rw [Measure.prod_restrict]
      exact hF_cts.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    -- Fubini swap: ∫_s ∫_t F = ∫_t ∫_s F
    have hswap : ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t =
        ∫ t in Set.Icc 0 N, ∫ s in Set.Icc 0 N, F s t :=
      integral_integral_swap hint
    rw [hswap]
    -- Inner integral: ∫_s F(s,t) = ∫_{-t}^{N-t} (g u).re via s → u=s-t
    have hinner2 : ∀ t ∈ Set.Icc (0:ℝ) N, ∫ s in Set.Icc 0 N, F s t =
        ∫ u in (-t)..(N - t), (g u).re := by
      intro t _
      simp only [F]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN.le,
          intervalIntegral.integral_comp_sub_right (fun u => (g u).re) t]
      congr 1; ring
    rw [setIntegral_congr_fun measurableSet_Icc hinner2]
    -- Extend inner interval integral to Icc(-N,N) with indicator, then Fubini
    have hlhs_ext : ∫ t in Set.Icc 0 N, ∫ u in (-t)..(N - t), (g u).re =
        ∫ t in (0 : ℝ)..N, ∫ u in Set.Icc (-N) N,
          (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN.le]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hN.le] at ht
      have hsubset : Set.Icc (-t) (N - t) ⊆ Set.Icc (-N) N :=
        fun u ⟨h1, h2⟩ => ⟨by linarith [ht.2], by linarith [ht.1]⟩
      -- Convert interval integral to set integral then extend
      show ∫ u in (-t)..(N - t), (g u).re =
        ∫ u in Set.Icc (-N) N, (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u
      rw [intervalIntegral.integral_of_le (show -t ≤ N - t by linarith [ht.1]),
          ← integral_Icc_eq_integral_Ioc]
      conv_rhs =>
        arg 2; ext u
        rw [show (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u =
            Set.indicator (Set.Icc (-t) (N - t)) (fun u => (g u).re) u from by
          simp [Set.indicator_apply]]
      rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsubset]
    rw [hlhs_ext]
    -- Fubini swap for the extended integral
    have hmeas_ind : Measurable (fun p : ℝ × ℝ =>
        (g p.2).re * Set.indicator (Set.Icc (-p.1) (N - p.1)) 1 p.2) :=
      ((Complex.continuous_re.comp hg_cont).measurable.comp measurable_snd).mul
        (Measurable.indicator measurable_const
          ((measurableSet_le (measurable_neg.comp measurable_fst) measurable_snd).inter
           (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))))
    -- Integrability: bound by |g u| which is integrable on Icc(-N,N)
    have h_re_int : Integrable (fun u => (g u).re)
        (volume.restrict (Set.Icc (-N) N)) :=
      (Complex.continuous_re.comp hg_cont).continuousOn.integrableOn_Icc
    haveI : IsFiniteMeasure (volume.restrict (Set.uIoc 0 N)) :=
      ⟨by simp [Real.volume_uIoc, abs_of_nonneg hN.le]⟩
    have hint_prod : Integrable
        (uncurry fun t u => (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u)
        ((volume.restrict (Set.uIoc 0 N)).prod
         (volume.restrict (Set.Icc (-N) N))) :=
      (h_re_int.comp_snd (volume.restrict (Set.uIoc 0 N))).mono
        hmeas_ind.aestronglyMeasurable (ae_of_all _ fun ⟨t, u⟩ => by
          simp only [uncurry]
          calc ‖(g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u‖
              ≤ ‖(g u).re‖ * ‖Set.indicator (Set.Icc (-t) (N - t)) (1 : ℝ → ℝ) u‖ :=
                norm_mul_le _ _
            _ ≤ ‖(g u).re‖ * 1 := by
                apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
                simp [Set.indicator_apply]; split_ifs <;> simp
            _ = ‖(g u).re‖ := mul_one _)
    rw [intervalIntegral_integral_swap hint_prod]
    -- Compute inner integral ∫ t in 0..N, Re(g u) * indicator(t ∈ Icc(-t,N-t))
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only
    have huN_bound : |u| ≤ N := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    -- indicator swap: u ∈ Icc(-t,N-t) ↔ t ∈ Icc(-u,N-u)
    have hcond_swap : ∀ t : ℝ,
        Set.indicator (Set.Icc (-t) (N - t)) (1 : ℝ → ℝ) u =
        Set.indicator (Set.Icc (-u) (N - u)) 1 t := fun t => by
      simp only [Set.indicator_apply, Set.mem_Icc]
      exact ite_congr
        (propext ⟨fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩,
                 fun ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩⟩)
        (fun _ => rfl) (fun _ => rfl)
    rw [show ∫ t in (0 : ℝ)..N,
            (g u).re * Set.indicator (Set.Icc (-t) (N - t)) 1 u =
        (g u).re * ∫ t in (0 : ℝ)..N,
            Set.indicator (Set.Icc (-t) (N - t)) (1 : ℝ → ℝ) u from
      intervalIntegral.integral_const_mul _ _]
    congr 1
    simp_rw [hcond_swap]
    -- Compute ∫ t in 0..N, 1_{Icc(-u,N-u)} t = N - |u|
    rcases le_or_gt u 0 with hu0 | hu0
    · -- u ≤ 0: interval is [-u, N] ∩ [0,N] = [-u, N], length = N+u = N-|u|
      have hint1 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume 0 (-u) :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      have hint2 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume (-u) N :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      rw [show ∫ t in (0 : ℝ)..(-u),
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t = 0 from
          intervalIntegral_eq_zero_of_forall_eq_zero fun t ht => by
            rw [Set.uIoo_of_le (by linarith [hu0])] at ht
            simp [Set.mem_Icc,
                  show ¬(-u ≤ t) from by linarith [ht.2]]]
      have hnu_le_N : -u ≤ N := by
        rw [abs_of_nonpos hu0] at huN_bound; linarith
      rw [show ∫ t in (-u)..N,
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t =
          ∫ t in (-u)..N, (1 : ℝ) from
          intervalIntegral.integral_congr fun t ht => by
            rw [Set.uIcc_of_le hnu_le_N] at ht
            simp [Set.indicator_apply, Set.mem_Icc, ht.1,
                  show t ≤ N - u from by linarith [hu0, ht.2]]]
      have hNu_nn : (0 : ℝ) ≤ N - (-u) := by linarith [hnu_le_N]
      simp [intervalIntegral.integral_const, abs_of_nonpos hu0,
            Real.norm_of_nonneg hNu_nn]
    · -- u > 0: interval is [-u, N-u] ∩ [0,N] = [0, N-u], length = N-u = N-|u|
      have huN : u ≤ N := by
        rw [abs_of_pos hu0] at huN_bound; exact huN_bound
      have hint1 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume 0 (N - u) :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      have hint2 : IntervalIntegrable (Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ))
          volume (N - u) N :=
        (integrable_indicator_iff measurableSet_Icc |>.mpr (integrableOn_const isCompact_Icc.measure_lt_top.ne)).intervalIntegrable
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
      rw [show ∫ t in (0 : ℝ)..(N - u),
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t =
          ∫ t in (0 : ℝ)..(N - u), (1 : ℝ) from
          intervalIntegral.integral_congr fun t ht => by
            rw [Set.uIcc_of_le (by linarith [huN])] at ht
            simp [Set.indicator_apply, Set.mem_Icc,
                  show -u ≤ t from by linarith [ht.1, hu0.le], ht.2]]
      rw [show ∫ t in (N - u)..N,
              Set.indicator (Set.Icc (-u) (N - u)) (1 : ℝ → ℝ) t = 0 from
          intervalIntegral_eq_zero_of_forall_eq_zero fun t ht => by
            rw [Set.uIoo_of_le (by linarith [huN])] at ht
            simp [Set.mem_Icc, show ¬(t ≤ N - u) from by
              linarith [ht.1]]]
      have hNu_nn : (0 : ℝ) ≤ N - u := by linarith [huN]
      simp [intervalIntegral.integral_const, abs_of_pos hu0]
  -- Step 3: Combine LHS with hfub
  rw [hfub, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  dsimp only
  have huN_abs : |u| ≤ N := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
  field_simp [hN.ne']

set_option maxHeartbeats 800000 in
private theorem fejerApproximant_nonneg (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (N : ℝ) (hN : 0 < N) (x : ℝ) : 0 ≤ fejerApproximant ψ N x := by
  -- Direct proof via PD Riemann sums, bypassing the double integral.
  -- Define g(u) = ψ(u) * exp(-ixu), which is PD and continuous.
  -- The Fejér approximant = (1/(2π)) * (∫_{[-N,N]} g(u)(1-|u|/N) du).re.
  -- The Riemann sum S_m = h * ∑_{k} g(kh)(1-|kh|/N) (h = N/m) equals
  -- (N/m²) * Re(∑ᵢ ∑ⱼ g((i-j)N/m)) which is ≥ 0 by PD (with cᵢ = 1).
  -- Since S_m → ∫ g(u)(1-|u|/N) du by 1D Riemann sum convergence, the integral is ≥ 0.
  unfold fejerApproximant
  apply mul_nonneg
  · apply div_nonneg one_pos.le
    exact mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos |>.le
  · -- Need: (∫ u in Icc(-N,N), g(u)(1-|u|/N)).re ≥ 0
    set g : ℝ → ℂ := fun u => ψ u * exp (-(↑x * ↑u * I)) with hg_def
    -- g is PD (product of ψ and exp(-ix·) which is PD)
    have hg_pd : IsPositiveDefinite g := isPositiveDefinite_mul_exp ψ hpd x
    -- g is continuous
    have hg_cont : Continuous g :=
      hψc.mul (((continuous_const.mul continuous_ofReal).mul continuous_const).neg.cexp)
    -- Step A: Define the approximating sequence.
    -- R_m = (N/(m+1)²) * Re(∑ᵢ ∑ⱼ g((i-j)*N/(m+1))) for m : ℕ.
    -- This equals the Riemann sum h * ∑_k g(kh)(1-|kh|/N) where h = N/(m+1).
    set R : ℕ → ℝ := fun m =>
      (N / ((m : ℝ) + 1)) ^ 2 / N *
      (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        g ((i : ℝ) * (N / ((m : ℝ) + 1)) - (j : ℝ) * (N / ((m : ℝ) + 1)))).re
    -- Step B: Each R_m ≥ 0 by PD (with cᵢ = 1)
    have hR_nn : ∀ m : ℕ, 0 ≤ R m := fun m => riemannSum_nonneg_of_pd g hg_pd N hN m
    -- Step C: R_m converges to (∫ g(u)(1-|u|/N)).re as m → ∞
    -- This is Riemann sum convergence for the continuous function
    -- u ↦ g(u)(1-|u|/N) on the compact interval [-N,N].
    -- The key combinatorial identity is:
    --   (h/N) * ∑_{i,j} g((i-j)h) = h * ∑_k g(kh)(1-|kh|/N)
    -- where the sum over k ranges over |k| ≤ m, and h = N/(m+1).
    -- This identity follows from counting pairs (i,j) with i-j = k:
    --   #{(i,j) ∈ [0,m]² : i-j = k} = m+1-|k| for |k| ≤ m.
    have hR_tendsto : Tendsto R atTop (𝓝 (∫ u in Set.Icc (-N) N,
        ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re) := by
      -- Strategy: define F(s,t) = Re(g(s-t)) on [0,N]².
      -- Then R m = (1/N) * h² * ∑_{i,j} F(i*h, j*h) and
      -- target = (1/N) * ∫_0^N ∫_0^N F s t dt ds (via Fubini + change of variables).
      -- Since F is uniformly continuous on [0,N]², the 2D Riemann sum converges to ∫∫ F.
      set F : ℝ → ℝ → ℝ := fun s t => (g (s - t)).re with hF_def
      have hF_cts : Continuous F.uncurry :=
        (Complex.continuous_re.comp hg_cont).comp (continuous_fst.sub continuous_snd)
      have hF_ucont : UniformContinuousOn F.uncurry
          (Set.Icc 0 N ×ˢ Set.Icc 0 N) :=
        (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
          hF_cts.continuousOn
      -- R m = (1/N) * h² * ∑_{i,j} F(i*h, j*h)
      have hR_form : ∀ m : ℕ, R m = (1 / N) * (N / ((m : ℝ) + 1)) ^ 2 *
          (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1)))) := by
        intro m
        simp only [R, F]
        rw [show (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            g (↑i * (N / (↑m + 1)) - ↑j * (N / (↑m + 1)))).re =
            ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            (g (↑i * (N / (↑m + 1)) - ↑j * (N / (↑m + 1)))).re from by
          simp [Complex.re_sum]]
        ring
      -- target = (1/N) * ∫_0^N ∫_0^N F (via Fubini + tent identity)
      have htarget_eq : (∫ u in Set.Icc (-N) N,
          ψ u * exp (-(↑x * ↑u * I)) * (1 - ↑(|u| / N))).re =
          (1 / N) * ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t :=
        tent_integral_eq_fubini g hg_cont N hN
      rw [htarget_eq]
      -- Step C3: 2D Riemann sum convergence via ε-δ with uniform continuity
      suffices hS : Tendsto (fun m : ℕ => (N / ((m : ℝ) + 1)) ^ 2 *
          ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1))))
          atTop (𝓝 (∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t)) by
        have hR_eq : R = fun (m : ℕ) => (1 / N) * ((N / ((m : ℝ) + 1)) ^ 2 *
            ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
              F ((i : ℝ) * (N / ((m : ℝ) + 1))) ((j : ℝ) * (N / ((m : ℝ) + 1)))) :=
          funext (fun m => by rw [hR_form]; ring)
        rw [hR_eq]
        exact (tendsto_const_nhds (x := 1 / N)).mul hS
      rw [Metric.tendsto_atTop]
      intro ε hε
      rw [Metric.uniformContinuousOn_iff] at hF_ucont
      obtain ⟨δ, hδ_pos, hδ⟩ := hF_ucont (ε / 2 / N ^ 2) (by positivity)
      have hδ' : 0 < δ / Real.sqrt 2 := by positivity
      refine ⟨⌈N / (δ / Real.sqrt 2)⌉₊, fun m hm => ?_⟩
      set h := N / ((m : ℝ) + 1) with hh_def
      have hh_pos : (0 : ℝ) < h := div_pos hN (by positivity)
      have hh_small : h < δ / Real.sqrt 2 := by
        have hM_le : (⌈N / (δ / Real.sqrt 2)⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have hM_pos : (0 : ℝ) < ⌈N / (δ / Real.sqrt 2)⌉₊ := by
          exact_mod_cast Nat.ceil_pos.mpr (by positivity)
        calc h = N / ((m : ℝ) + 1) := hh_def
            _ < N / (⌈N / (δ / Real.sqrt 2)⌉₊ : ℝ) := by
                apply div_lt_div_of_pos_left hN (by exact_mod_cast hM_pos)
                linarith
            _ ≤ N / (N / (δ / Real.sqrt 2)) := by
                apply div_le_div_of_nonneg_left hN.le (by positivity)
                exact_mod_cast Nat.le_ceil _
            _ = δ / Real.sqrt 2 := by field_simp [hN.ne']
      -- Split ∫∫ F into (m+1)² boxes
      have hbox_split : ∫ s in Set.Icc 0 N, ∫ t in Set.Icc 0 N, F s t =
          ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
            ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
            ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), F s t := by
        have hN_eq : N = (m + 1 : ℝ) * h := by push_cast [hh_def]; field_simp
        -- Continuity of s ↦ ∫_t F s t (needed for outer split integrability)
        have hφ_cont : Continuous (fun s => ∫ t in Set.Icc 0 N, F s t) :=
          continuous_parametric_integral_of_continuous hF_cts isCompact_Icc
        -- Helper: split ∫ in Icc 0 N into m+1 sub-intervals
        have h_Icc_split : ∀ (φ : ℝ → ℝ), ContinuousOn φ (Set.Icc 0 N) →
            ∫ u in Set.Icc 0 N, φ u =
            ∑ i : Fin (m + 1), ∫ u in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h), φ u := by
          intro φ hφ
          have h_a_def : ∀ k : ℕ, (k : ℝ) * h = (fun k : ℕ => (k : ℝ) * h) k := fun k => rfl
          rw [show (0 : ℝ) = (↑(0 : ℕ)) * h from by simp, hN_eq,
              show (↑m + (1 : ℝ)) * h = (↑(m + 1 : ℕ) : ℝ) * h from by push_cast; ring,
              integral_Icc_eq_integral_Ioc,
              ← intervalIntegral.integral_of_le (by push_cast; nlinarith [hh_pos])]
          rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico
            (a := fun k : ℕ => (k : ℝ) * h) (Nat.zero_le _)
            (fun k hk =>
              (hφ.mono (Set.Icc_subset_Icc (by push_cast; positivity)
                (by rw [hN_eq]; apply mul_le_mul_of_nonneg_right _ hh_pos.le
                    have : k + 1 ≤ m + 1 := hk.2
                    exact_mod_cast this))).intervalIntegrable_of_Icc
                (by push_cast; linarith [hh_pos, hk.1]))]
          rw [Nat.Ico_zero_eq_range, ← Fin.sum_univ_eq_sum_range]
          congr 1; ext i; push_cast
          rw [intervalIntegral.integral_of_le (by nlinarith [hh_pos]),
              ← integral_Icc_eq_integral_Ioc]
        -- Step 1: split outer integral
        rw [h_Icc_split _ hφ_cont.continuousOn]
        -- Step 2: for each i, split inner integral and pull ∑ outside
        congr 1; ext i
        rw [show ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
                ∫ t in Set.Icc 0 N, F s t =
            ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
              ∑ j : Fin (m + 1), ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
              F s t from by
          apply setIntegral_congr_fun measurableSet_Icc
          intro s _
          exact h_Icc_split (fun t => F s t)
            (hF_cts.comp (continuous_const.prodMk continuous_id)).continuousOn]
        rw [integral_finset_sum (Finset.univ : Finset (Fin (m + 1))) (fun (j : Fin (m + 1)) _ =>
          (continuous_parametric_integral_of_continuous hF_cts
            (isCompact_Icc (a := (j : ℝ) * h) (b := ((j : ℝ) + 1) * h))).continuousOn.integrableOn_Icc)]
      -- Bound the error
      rw [Real.dist_eq, hbox_split]
      calc |((N / ((m : ℝ) + 1)) ^ 2 * ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
              F ((i : ℝ) * h) ((j : ℝ) * h)) -
            ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
              ∫ s in Set.Icc (↑i * h) ((↑i + 1) * h),
              ∫ t in Set.Icc (↑j * h) ((↑j + 1) * h), F s t|
          = |∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
              (h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) -
               ∫ s in Set.Icc (↑i * h) ((↑i + 1) * h),
               ∫ t in Set.Icc (↑j * h) ((↑j + 1) * h), F s t)| := by
            congr 1
            simp_rw [← hh_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
        _ ≤ ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
              |h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) -
               ∫ s in Set.Icc (↑i * h) ((↑i + 1) * h),
               ∫ t in Set.Icc (↑j * h) ((↑j + 1) * h), F s t| :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
        _ ≤ ∑ i : Fin (m + 1), ∑ _j : Fin (m + 1), h ^ 2 * (ε / 2 / N ^ 2) := by
            apply Finset.sum_le_sum; intro i _
            apply Finset.sum_le_sum; intro j _
            have hile : (i : ℝ) * h ≤ ((i : ℝ) + 1) * h := by nlinarith [hh_pos]
            have hjle : (j : ℝ) * h ≤ ((j : ℝ) + 1) * h := by nlinarith [hh_pos]
            have hN_eq' : N = (↑m + 1) * h := by rw [hh_def]; field_simp
            have hi_bound : ((i : ℝ) + 1) * h ≤ N := by
              rw [hN_eq']; apply mul_le_mul_of_nonneg_right _ hh_pos.le
              have := i.2; exact_mod_cast this
            have hj_bound : ((j : ℝ) + 1) * h ≤ N := by
              rw [hN_eq']; apply mul_le_mul_of_nonneg_right _ hh_pos.le
              have := j.2; exact_mod_cast this
            have hi_nn : (0 : ℝ) ≤ (i : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh_pos.le
            have hj_nn : (0 : ℝ) ≤ (j : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh_pos.le
            have hint_const_j : IntegrableOn (fun _ => F ((i : ℝ) * h) ((j : ℝ) * h))
                (Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h)) :=
              integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
            have hint_F_inner : ∀ s : ℝ, IntegrableOn (fun t => F s t)
                (Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h)) := fun s =>
              (hF_cts.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc
            have hint_const_i : IntegrableOn
                (fun s => ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                  F ((i : ℝ) * h) ((j : ℝ) * h))
                (Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) :=
              integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne)
            have hint_F_outer : IntegrableOn
                (fun s => ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), F s t)
                (Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) :=
              (continuous_parametric_integral_of_continuous hF_cts
                (isCompact_Icc (a := (j : ℝ) * h) (b := ((j : ℝ) + 1) * h))).continuousOn.integrableOn_Icc
            -- Write h²*F_const - ∫∫F = ∫∫(F_const - F s t) via linearity
            have heq : h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) -
                ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
                ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h), F s t =
                ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
                ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t) := by
              rw [show h ^ 2 * F ((i : ℝ) * h) ((j : ℝ) * h) =
                  ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
                  ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                  F ((i : ℝ) * h) ((j : ℝ) * h) from by
                simp only [setIntegral_const, smul_eq_mul,
                  Real.volume_real_Icc_of_le hile, Real.volume_real_Icc_of_le hjle]
                ring]
              rw [← integral_sub hint_const_i hint_F_outer]
              congr 1; ext s
              rw [← integral_sub hint_const_j (hint_F_inner s)]
            rw [heq]
            -- Bound |∫∫(F_const - F s t)| ≤ ∫∫ |F_const - F s t| ≤ ∫∫(ε/2/N²) = h²*(ε/2/N²)
            have hint_diff_outer : IntegrableOn
                (fun s => ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                  (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t))
                (Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h)) := by
              have := hint_const_i.sub hint_F_outer
              simp only [integral_sub hint_const_j (hint_F_inner _)] at this ⊢
              exact this
            calc |∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
                    ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                    (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t)|
                ≤ ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
                  ‖∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                    (F ((i : ℝ) * h) ((j : ℝ) * h) - F s t)‖ :=
                    by rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
              _ ≤ ∫ s in Set.Icc ((i : ℝ) * h) (((i : ℝ) + 1) * h),
                  ∫ t in Set.Icc ((j : ℝ) * h) (((j : ℝ) + 1) * h),
                  ε / 2 / N ^ 2 := by
                  apply setIntegral_mono_on hint_diff_outer.norm
                    (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
                    measurableSet_Icc
                  intro s hs
                  apply le_trans (norm_integral_le_integral_norm _)
                  apply setIntegral_mono_on (hint_const_j.sub (hint_F_inner s)).norm
                    (integrableOn_const (hs := isCompact_Icc.measure_lt_top.ne))
                    measurableSet_Icc
                  intro t ht
                  simp only [Pi.sub_apply, Real.norm_eq_abs]
                  rw [show |F ((i : ℝ) * h) ((j : ℝ) * h) - F s t| =
                      dist (uncurry F ((i : ℝ) * h, (j : ℝ) * h))
                           (uncurry F (s, t)) from by
                    simp [uncurry, Real.dist_eq]]
                  apply le_of_lt
                  apply hδ
                  · exact ⟨⟨hi_nn, by linarith [hi_bound]⟩,
                          ⟨hj_nn, by linarith [hj_bound]⟩⟩
                  · exact ⟨⟨hi_nn.trans hs.1, hs.2.trans (by linarith [hi_bound])⟩,
                          ⟨hj_nn.trans ht.1, ht.2.trans (by linarith [hj_bound])⟩⟩
                  · rw [Prod.dist_eq]
                    have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
                    have hsqrt2_ge_one : (1 : ℝ) ≤ Real.sqrt 2 := by
                      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by norm_num)
                    calc max (dist ((i : ℝ) * h) s) (dist ((j : ℝ) * h) t)
                        ≤ Real.sqrt 2 * h := by
                          apply max_le
                          · rw [Real.dist_eq, abs_le]
                            exact ⟨by nlinarith [hs.2, hsqrt2_ge_one],
                                   by nlinarith [hs.1, hsqrt2_pos]⟩
                          · rw [Real.dist_eq, abs_le]
                            exact ⟨by nlinarith [ht.2, hsqrt2_ge_one],
                                   by nlinarith [ht.1, hsqrt2_pos]⟩
                      _ < δ := by
                          have : Real.sqrt 2 * h < Real.sqrt 2 * (δ / Real.sqrt 2) :=
                            mul_lt_mul_of_pos_left hh_small hsqrt2_pos
                          rwa [mul_div_cancel₀ _ hsqrt2_pos.ne'] at this
              _ = h ^ 2 * (ε / 2 / N ^ 2) := by
                  simp only [setIntegral_const, smul_eq_mul,
                    Real.volume_real_Icc_of_le hile, Real.volume_real_Icc_of_le hjle]
                  ring
        _ = ε / 2 := by
            simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
            have hm1_pos : (0 : ℝ) < ↑m + 1 := by positivity
            rw [hh_def]
            push_cast
            field_simp [hm1_pos.ne']
        _ < ε := by linarith
    -- Step D: Conclude by ge_of_tendsto
    exact ge_of_tendsto hR_tendsto (Eventually.of_forall hR_nn)


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
private theorem inverseFourierDensity_nonneg (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (hI : Integrable ψ volume) (x : ℝ) : 0 ≤ inverseFourierDensity ψ x :=
  ge_of_tendsto (tendsto_fejerApproximant ψ hI x)
    (Eventually.of_forall fun n => fejerApproximant_nonneg ψ hψc hpd (↑n + 1) (by positivity) x)

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
  have h2pi_ne : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  -- Define the post-substitution integrand g u = exp(-iuy) * ψ u
  -- The key formula: 𝓕(ψ(2π·))(y) = (1/2π) * ∫ u, g(u)
  let g : ℝ → ℂ := fun u => Complex.exp (↑(-(u * y)) * Complex.I) * ψ u
  -- Step 1: Unfold 𝓕 to the exp-form
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  -- Goal: ∫ v, exp(↑(-2π·v·y)·I) * ψ(2π·v) = ↑(inverseFourierDensity ψ y)
  -- Step 2: Change variables u = 2πv using integral_comp_mul_left
  -- Rewrite integrand pointwise to expose g(2π·v)
  have heq_integrand : ∀ v : ℝ,
      Complex.exp (↑(-2 * Real.pi * v * y) * Complex.I) * ψ (2 * Real.pi * v) =
      g (2 * Real.pi * v) := by
    intro v; simp only [g]
    congr 1; congr 1; push_cast; ring
  simp_rw [heq_integrand]
  -- Now apply integral_comp_mul_left and convert to a form involving ∫ u, g u
  -- Use suffices to avoid bound variable name issues with rw
  suffices h : |(2 * Real.pi)⁻¹| • ∫ u, g u = ↑(inverseFourierDensity ψ y) by
    calc ∫ v : ℝ, g (2 * Real.pi * v)
        = |(2 * Real.pi)⁻¹| • ∫ u, g u := Measure.integral_comp_mul_left g (2 * Real.pi)
      _ = ↑(inverseFourierDensity ψ y) := h
  rw [abs_inv, abs_of_pos h2pi_pos]
  -- Goal: (2π)⁻¹ • ∫ u, g u = ↑(inverseFourierDensity ψ y)
  -- Step 3: Show ∫ g is real using Hermitian symmetry of ψ
  have h_integral_im_zero : (∫ u, g u).im = 0 := by
    -- conj(g u) = g(-u) by Hermitian symmetry of ψ
    have h_conj_g : ∀ u : ℝ, conj (g u) = g (-u) := fun u => by
      simp only [g, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, conj_I, mul_neg]
      -- Goal: exp(-(↑(-(u*y))*I)) * conj(ψ u) = exp(↑(-(-u*y))*I) * ψ(-u)
      rw [← hpd.conj_neg u]
      -- Now: exp(-(↑(-(u*y))*I)) * conj(ψ u) = exp(↑(-(-u*y))*I) * conj(ψ u)
      congr 1
      -- Goal: exp(-(↑(-(u*y))*I)) = exp(↑(-(-u*y))*I)
      congr 1; push_cast; ring
    -- Show (∫ u, g u).im = 0 using conj(g u) = g(-u) and negation substitution.
    -- Key: ∫ g(-u) du = ∫ g u du, and ∫ conj(g) = ∫ g(-·) = ∫ g
    -- Hence Im(∫ g) = -Im(∫ g) → Im = 0.
    -- ∫ g(-u) du = ∫ g u du (substitution u ↦ -u)
    have h_neg_subst : ∫ u : ℝ, g (-u) = ∫ u : ℝ, g u := by
      have hfun : (fun u : ℝ => g (-u)) = fun u => g ((-1) * u) := by ext; simp
      rw [hfun, Measure.integral_comp_mul_left g (-1)]
      norm_num
    -- im(g u) = -im(g(-u)) since conj(g u) = g(-u) (and Im(conj z) = -Im z)
    have h_im_antisym : ∀ u : ℝ, Complex.im (g u) = -Complex.im (g (-u)) := fun u => by
      have heq := congr_arg Complex.im (h_conj_g u)
      simp only [conj_im] at heq
      linarith
    -- ∫ im(g u) = 0 by anti-symmetry: it equals its own negative
    have hint : ∫ u : ℝ, Complex.im (g u) = 0 := by
      -- ∫ im(g u) = ∫ -im(g(-u)) = -∫ im(g(-u)) = -∫ im(g u)
      -- Step 1: im(g u) = -im(g(-u))
      have heq1 : ∫ u : ℝ, Complex.im (g u) = ∫ u : ℝ, -Complex.im (g (-u)) := by
        congr 1; ext u; exact h_im_antisym u
      -- Step 2: ∫ im(g(-u)) = ∫ im(g u) via change-of-variables u ↦ -u
      have heq2 : ∫ u : ℝ, Complex.im (g (-u)) = ∫ u : ℝ, Complex.im (g u) := by
        have hfun : (fun u : ℝ => Complex.im (g (-u))) =
            fun u => (Complex.im ∘ g) ((-1) * u) := by ext; simp [Function.comp]
        rw [hfun, Measure.integral_comp_mul_left (Complex.im ∘ g) (-1)]
        norm_num
      have heq3 := integral_neg (f := fun u : ℝ => Complex.im (g (-u))) (μ := volume)
      linarith
    -- (∫ g).im = ∫ im(g) = 0
    have h_g_int_for_im : Integrable g volume := by
      apply Integrable.mono hI
      · show AEStronglyMeasurable (fun u : ℝ => Complex.exp (↑(-(u * y)) * I) * ψ u) volume
        exact ((Complex.continuous_exp.comp
          (((Complex.continuous_ofReal.comp
            ((continuous_id.mul continuous_const).neg)).mul
            continuous_const))).mul hψc).aestronglyMeasurable
      · apply ae_of_all; intro u
        show ‖Complex.exp (↑(-(u * y)) * I) * ψ u‖ ≤ ‖ψ u‖
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have h_im_eq : RCLike.im (∫ u : ℝ, g u) = 0 := by
      have key : ∫ u : ℝ, RCLike.im (g u) = RCLike.im (∫ u : ℝ, g u) :=
        integral_im h_g_int_for_im
      have hint' : (∫ u : ℝ, RCLike.im (g u)) = 0 := by exact_mod_cast hint
      linarith
    exact h_im_eq
  -- Step 4: Relate to inverseFourierDensity and finish
  unfold inverseFourierDensity
  push_cast
  -- The integral ∫ u, ψ u * exp(-iy·u) equals ∫ u, g u (just reordering factors)
  have h_eq_reorder : ∫ u : ℝ, ψ u * Complex.exp (-(↑y * ↑u * Complex.I)) =
      ∫ u : ℝ, g u := by
    congr 1; ext u; simp only [g]
    have hexpa : -(↑y * ↑u * Complex.I) = ↑(-(u * y)) * Complex.I := by push_cast; ring
    rw [hexpa, mul_comm]
  rw [h_eq_reorder]
  -- Since (∫ g).im = 0, write ∫ g = ↑(∫ g).re
  have h_int_re : (∫ u, g u) = ↑(∫ u, g u).re := by
    rw [Complex.ext_iff]; simp [h_integral_im_zero]
  rw [h_int_re]
  simp only [Complex.real_smul]
  push_cast [Complex.ofReal_re]
  rw [one_div]

set_option maxHeartbeats 800000 in
/-- The inverseFourierDensity is integrable for PD+continuous+L¹ functions.
Proof: ρ ≥ 0 (from Fejér argument) and the Gaussian regularization shows ∫ ρ = 1. -/
private theorem integrable_inverseFourierDensity (ψ : ℝ → ℂ) (hψc : Continuous ψ)
    (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) (hI : Integrable ψ volume) :
    Integrable (inverseFourierDensity ψ) volume := by
  -- ρ ≥ 0 (from inverseFourierDensity_nonneg, which uses Fejér ≥ 0)
  have hρ_nn := inverseFourierDensity_nonneg ψ hψc hpd hI
  have hρ_cont := continuous_inverseFourierDensity ψ hψc hI
  have hρ_meas : AEStronglyMeasurable (inverseFourierDensity ψ) volume :=
    hρ_cont.aestronglyMeasurable
  -- Strategy: show ∫⁻ ρ ≤ 1 < ∞ using MCT + Gaussian regularization.
  -- Step 1: Define the Gaussian-truncated functions gₙ(x) = ρ(x) · exp(-x²/(2(n+1))).
  -- These are integrable (bounded × Gaussian) and monotonically increase to ρ.
  -- Step 2: Show ∫ gₙ → 1 via Gaussian FT + DCT.
  -- Step 3: By MCT, ∫⁻ ρ = sup ∫⁻ gₙ ≤ 1 < ∞, hence ρ ∈ L¹.
  apply (lintegral_ofReal_ne_top_iff_integrable hρ_meas (ae_of_all _ hρ_nn)).mp
  -- Goal: ∫⁻ x, ENNReal.ofReal (ρ x) ∂volume ≠ ⊤
  -- Use MCT: gₙ ↗ ρ, so ∫⁻ ρ = sup ∫⁻ gₙ. Each ∫ gₙ ≤ 1 (from the Gaussian computation).
  -- Hence ∫⁻ ρ ≤ 1 < ⊤.
  -- Define the approximating sequence
  set gn : ℕ → ℝ → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (inverseFourierDensity ψ x * Real.exp (-(x ^ 2 / (2 * (↑n + 1)))))
  -- gn is monotone increasing to ENNReal.ofReal (ρ x)
  have hgn_mono : ∀ᵐ x ∂volume, Monotone (fun n => gn n x) := by
    apply ae_of_all; intro x
    intro m n hmn
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left
    · apply Real.exp_le_exp_of_le
      apply neg_le_neg
      apply div_le_div_of_nonneg_left (sq_nonneg x)
      · linarith [show (0 : ℝ) ≤ ↑n from Nat.cast_nonneg n]
      · linarith [show (0 : ℝ) ≤ ↑m from Nat.cast_nonneg m,
                   show (↑m : ℝ) ≤ ↑n from Nat.cast_le.mpr hmn]
    · exact hρ_nn x
  have hgn_tendsto : ∀ᵐ x ∂volume, Tendsto (fun n => gn n x) atTop
      (𝓝 (ENNReal.ofReal (inverseFourierDensity ψ x))) := by
    apply ae_of_all; intro x
    apply ENNReal.tendsto_ofReal
    conv_rhs => rw [show inverseFourierDensity ψ x =
      inverseFourierDensity ψ x * 1 from (mul_one _).symm]
    apply Tendsto.mul tendsto_const_nhds
    rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
    exact (Real.continuous_exp.tendsto 0).comp (by
      -- Goal: -(x²/(2(n+1))) → 0
      have : Tendsto (fun n : ℕ => x ^ 2 / (2 * (↑n + 1))) atTop (𝓝 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds
          ((Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop
            (by norm_num : (0 : ℝ) < 2))
      simpa using this.neg)
  have hgn_meas : ∀ n, AEMeasurable (gn n) volume := by
    intro n
    exact (hρ_cont.mul (Real.continuous_exp.comp (continuous_neg.comp
      ((continuous_pow 2).div_const _)))).measurable.ennreal_ofReal.aemeasurable
  -- By MCT: ∫⁻ ρ = lim ∫⁻ gₙ
  have hMCT := lintegral_tendsto_of_tendsto_of_monotone hgn_meas hgn_mono hgn_tendsto
  -- Each ∫⁻ gₙ = ENNReal.ofReal (∫ gₙ_real) since gₙ_real ≥ 0
  -- And ∫ gₙ_real → 1 by Gaussian FT + DCT (the hard computation).
  -- So ∫⁻ ρ = ENNReal.ofReal 1 ≠ ⊤.
  -- For now, we show ∫⁻ ρ < ⊤ by showing the limit is finite.
  have hgn_le_one : ∀ n, ∫⁻ x, gn n x ∂volume ≤ 1 := by
    intro n
    set σ2 : ℝ := ↑n + 1 with hσ2_def
    have hσ2_pos : 0 < σ2 := by positivity
    -- The real-valued integrand ρ(x) * exp(-x²/(2σ²)) is non-negative and integrable
    -- (ρ is bounded, Gaussian is integrable), so ∫⁻ = ENNReal.ofReal(∫).
    have hgn_nn : ∀ x, 0 ≤ inverseFourierDensity ψ x *
        Real.exp (-(x ^ 2 / (2 * σ2))) :=
      fun x => mul_nonneg (hρ_nn x) (Real.exp_nonneg _)
    -- ρ is bounded
    have hρ_bdd : ∃ C, ∀ x, inverseFourierDensity ψ x ≤ C := by
      use (1 / (2 * Real.pi)) * ∫ u, ‖ψ u‖
      intro x
      unfold inverseFourierDensity
      apply mul_le_mul_of_nonneg_left _ (div_nonneg one_pos.le
        (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos).le)
      calc (∫ u, ψ u * exp (-(↑x * ↑u * I))).re
          ≤ |(∫ u, ψ u * exp (-(↑x * ↑u * I))).re| := le_abs_self _
        _ ≤ ‖∫ u, ψ u * exp (-(↑x * ↑u * I))‖ := abs_re_le_norm _
        _ ≤ ∫ u, ‖ψ u * exp (-(↑x * ↑u * I))‖ := norm_integral_le_integral_norm _
        _ = ∫ u, ‖ψ u‖ := by
            congr 1; ext u; rw [norm_mul,
              show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
              norm_exp_ofReal_mul_I, mul_one]
    -- The product is integrable (bounded × Gaussian)
    have hgn_integrable : Integrable (fun x => inverseFourierDensity ψ x *
        Real.exp (-(x ^ 2 / (2 * σ2)))) volume := by
      -- Gaussian is integrable
      have hgauss_cont : Continuous (fun x : ℝ =>
          Real.exp (-(x ^ 2 / (2 * σ2)))) :=
        Real.continuous_exp.comp (continuous_neg.comp
          ((continuous_pow 2).div_const _))
      have hgauss_int : Integrable (fun x : ℝ =>
          Real.exp (-(x ^ 2 / (2 * σ2)))) volume := by
        have h := integrable_exp_neg_mul_sq (show 0 < 1 / (2 * σ2) by positivity)
        convert h using 1; ext x; congr 1; ring
      -- ρ is bounded, so ρ * Gaussian is integrable
      obtain ⟨C, hC⟩ := hρ_bdd
      exact hgauss_int.bdd_mul hρ_cont.aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hρ_nn x)]; exact hC x)
    -- Convert ∫⁻ to ∫
    rw [show gn n = fun x => ENNReal.ofReal (inverseFourierDensity ψ x *
        Real.exp (-(x ^ 2 / (2 * σ2)))) from by
      ext x; simp [gn, hσ2_def]]
    rw [← ofReal_integral_eq_lintegral_ofReal hgn_integrable (ae_of_all _ hgn_nn)]
    rw [ENNReal.ofReal_le_one]
    -- Goal: ∫ ρ(x) * exp(-x²/(2σ²)) dx ≤ 1
    -- We unfold ρ and bound using |ψ| ≤ 1 and norm_integral_le_integral_norm.
    -- The bound ρ(x) ≤ (1/(2π)) * ∫ ‖ψ(u)‖ du is too loose (grows with σ).
    -- Instead, we use a Fubini argument to swap the x and u integrals.
    -- ∫_x ρ(x) exp(-x²/(2σ²)) dx = (σ/√(2π)) Re ∫_u ψ(u) exp(-σ²u²/2) du
    -- ≤ (σ/√(2π)) ∫ exp(-σ²u²/2) du = 1.
    -- The Fubini swap + Gaussian FT evaluation is proved via fourierIntegral_gaussian.
    have hψ_norm_le : ∀ u, ‖ψ u‖ ≤ 1 := hpd.norm_le_one h0
    -- ∫ ρ(x) exp(-x²/(2σ²)) dx = (σ/√(2π)) Re ∫ ψ(u) exp(-σ²u²/2) du
    have gaussian_fubini_bound :
        ∫ x, inverseFourierDensity ψ x * Real.exp (-(x ^ 2 / (2 * σ2))) ≤
        Real.sqrt σ2 / Real.sqrt (2 * Real.pi) *
        ∫ u, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := by
      -- By Fubini + fourierIntegral_gaussian:
      -- ∫_x (∫_u ψ(u) exp(-ixu)).re * exp(-x²/(2σ²))
      -- = √(2πσ²) Re ∫_u ψ(u) exp(-σ²u²/2)
      -- ≤ √(2πσ²) ∫_u ‖ψ(u)‖ exp(-σ²u²/2)
      -- So the bound = (1/(2π)) * √(2πσ²) * ∫ ‖ψ‖ exp(...)
      -- = √σ²/√(2π) * ∫ ‖ψ‖ exp(-σ²u²/2).
      -- The Fubini+Gaussian FT identity:
      have fubini_identity :
          ∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))).re *
            Real.exp (-(x ^ 2 / (2 * σ2))) =
          Real.sqrt (2 * Real.pi * σ2) *
            (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re := by
        -- Step 1: Re(z) * r = Re(z * ↑r)
        have hstep1 : ∀ x : ℝ,
            (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))).re *
              Real.exp (-(x ^ 2 / (2 * σ2))) =
            ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2))))).re := by
          intro x
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
        simp_rw [hstep1]
        -- Step 2: ∫_x Re(f(x)) = Re(∫_x f(x)) by integral_re
        -- Need integrability of x ↦ (∫_u ψ exp(-ixu)) * ↑(exp(-x²/(2σ²)))
        have hψ_int_bdd : ∀ x : ℝ,
            ‖∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))‖ ≤ ∫ u, ‖ψ u‖ := by
          intro x
          calc ‖∫ u, ψ u * exp (-(↑x * ↑u * I))‖
              ≤ ∫ u, ‖ψ u * exp (-(↑x * ↑u * I))‖ := norm_integral_le_integral_norm _
            _ = ∫ u, ‖ψ u‖ := by
                congr 1; ext u; rw [norm_mul,
                  show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                  norm_exp_ofReal_mul_I, mul_one]
        have hgauss_int : Integrable (fun x : ℝ =>
            Real.exp (-(x ^ 2 / (2 * σ2)))) volume := by
          have h := integrable_exp_neg_mul_sq (show 0 < 1 / (2 * σ2) by positivity)
          convert h using 1; ext x; congr 1; ring
        have hf_int : Integrable (fun x : ℝ =>
            (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) volume := by
          -- Bound: ‖f(x)‖ ≤ (∫ ‖ψ‖) * exp(-x²/(2σ²))
          apply (hgauss_int.const_mul (∫ u, ‖ψ u‖)).mono'
          · apply AEStronglyMeasurable.mul
            · -- x ↦ ∫ ψ(u) exp(-ixu) du is continuous (by continuous_of_dominated)
              -- hence AEStronglyMeasurable
              have hcont_param : Continuous (fun x : ℝ =>
                  ∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) := by
                set G : ℝ → ℝ → ℂ := fun x u => ψ u * exp (-(↑x * ↑u * I))
                exact continuous_of_dominated
                  (fun (x : ℝ) => (hψc.mul ((((continuous_ofReal.comp continuous_const).mul
                    continuous_ofReal).mul continuous_const).neg.cexp)).aestronglyMeasurable)
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
                    exact ((Complex.continuous_ofReal.mul continuous_const).mul
                      continuous_const).neg)
              exact hcont_param.aestronglyMeasurable
            · exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
                (continuous_neg.comp ((continuous_pow 2).div_const _)))).aestronglyMeasurable
          · exact ae_of_all _ fun x => by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.exp_nonneg _)]
              exact mul_le_mul_of_nonneg_right (hψ_int_bdd x) (Real.exp_nonneg _)
        -- ∫ Re(f(x)) = Re(∫ f(x))
        conv_lhs =>
          arg 2; ext x
          rw [show ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2))))).re =
            Complex.re ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) from rfl]
        rw [show (fun x : ℝ => Complex.re ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2)))))) =
          (fun x : ℝ => RCLike.re ((∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2)))))) from rfl,
          integral_re hf_int]
        -- Prove the complex identity, then take .re
        suffices hcomplex : (∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
            ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) =
          ↑(Real.sqrt (2 * Real.pi * σ2)) *
            ∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2))) by
          show (∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2))))).re =
            Real.sqrt (2 * Real.pi * σ2) *
              (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re
          rw [hcomplex]
          simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
        -- Pull ↑exp inside the inner integral
        have hpull : ∀ x : ℝ,
            (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))) * ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) =
            ∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I)) * ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) := by
          intro x; exact (integral_mul_const _ _).symm
        simp_rw [hpull]
        -- Product integrability for Fubini
        have hcont_prod : Continuous (fun p : ℝ × ℝ =>
            ψ p.2 * exp (-(↑p.1 * ↑p.2 * I)) *
              ↑(Real.exp (-(p.1 ^ 2 / (2 * σ2))))) :=
          ((hψc.comp continuous_snd).mul
            (Complex.continuous_exp.comp
              (((continuous_ofReal.comp continuous_fst).mul
                (continuous_ofReal.comp continuous_snd)).mul
                continuous_const).neg)).mul
            (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
              (continuous_neg.comp ((continuous_pow 2 |>.comp continuous_fst).div_const _))))
        have hprod_int : Integrable (fun p : ℝ × ℝ =>
            ψ p.2 * exp (-(↑p.1 * ↑p.2 * I)) *
              ↑(Real.exp (-(p.1 ^ 2 / (2 * σ2))))) (volume.prod volume) := by
          rw [integrable_prod_iff hcont_prod.aestronglyMeasurable]
          refine ⟨?_, ?_⟩
          · exact ae_of_all _ fun x => by
              show Integrable (fun u => ψ u * exp (-(↑x * ↑u * I)) *
                ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) volume
              apply Integrable.mono' (hI.norm.mul_const (Real.exp (-(x ^ 2 / (2 * σ2)))))
              · exact (hcont_prod.comp
                  (continuous_const.prodMk continuous_id)).aestronglyMeasurable
              · exact ae_of_all _ fun u => by
                  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
                    abs_of_nonneg (Real.exp_nonneg _),
                    show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                    norm_exp_ofReal_mul_I, mul_one]
          · have hnorm_eq : (fun x => ∫ u, ‖(fun p : ℝ × ℝ => ψ p.2 *
                exp (-(↑p.1 * ↑p.2 * I)) *
                  ↑(Real.exp (-(p.1 ^ 2 / (2 * σ2))))) (x, u)‖) =
                fun x => (∫ u, ‖ψ u‖) * Real.exp (-(x ^ 2 / (2 * σ2))) := by
              ext x
              show ∫ u, ‖ψ u * exp (-(↑x * ↑u * I)) *
                ↑(Real.exp (-(x ^ 2 / (2 * σ2))))‖ =
                (∫ u, ‖ψ u‖) * Real.exp (-(x ^ 2 / (2 * σ2)))
              simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.exp_nonneg _)]
              rw [← integral_mul_const]
              congr 1; ext u
              rw [show -(↑x * ↑u * I) = ↑(-(x * u)) * I from by push_cast; ring,
                norm_exp_ofReal_mul_I, mul_one]
            rw [hnorm_eq]
            exact hgauss_int.const_mul _
        -- Apply Fubini
        rw [integral_integral_swap hprod_int]
        -- Evaluate the inner x-integral for each u
        have hinner_eq : ∀ u : ℝ,
            (∫ x : ℝ, ψ u * exp (-(↑x * ↑u * I)) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) =
            ψ u * (↑(Real.sqrt (2 * Real.pi * σ2)) *
              ↑(Real.exp (-(σ2 * u ^ 2 / 2)))) := by
          intro u
          have hassoc : ∀ x : ℝ, ψ u * exp (-(↑x * ↑u * I)) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) =
            ψ u * (exp (-(↑x * ↑u * I)) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2))))) := fun x => by ring
          simp_rw [hassoc]
          rw [show (∫ x : ℝ, ψ u * (exp (-(↑x * ↑u * I)) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2)))))) =
            ψ u * ∫ x : ℝ, exp (-(↑x * ↑u * I)) *
              ↑(Real.exp (-(x ^ 2 / (2 * σ2))))
            from integral_const_mul _ _]
          congr 1
          -- Evaluate via fourierIntegral_gaussian
          have hrw : ∀ x : ℝ,
              exp (-(↑x * ↑u * I)) * ↑(Real.exp (-(x ^ 2 / (2 * σ2)))) =
              cexp (I * (-↑u) * ↑x) *
                cexp (-(↑(1 / (2 * σ2)) : ℂ) * (↑x) ^ 2) := by
            intro x
            congr 1
            · congr 1; ring
            · rw [Complex.ofReal_exp]; congr 1; push_cast; ring
          simp_rw [hrw]
          have hb_re : (0 : ℝ) < (↑(1 / (2 * σ2)) : ℂ).re := by
            simp [Complex.ofReal_re]; positivity
          rw [fourierIntegral_gaussian hb_re (-↑u)]
          have h1 : (↑(1 / (2 * σ2)) : ℂ) = 1 / (2 * ↑σ2) := by push_cast; ring
          rw [h1]
          have h2piσ_nn : (0 : ℝ) ≤ 2 * Real.pi * σ2 := by positivity
          have hbase : (↑Real.pi : ℂ) / (1 / (2 * ↑σ2)) = ↑(2 * Real.pi * σ2) := by
            push_cast; field_simp
          rw [hbase, show (1 / 2 : ℂ) = ↑(1 / 2 : ℝ) from by push_cast; ring,
            ← ofReal_cpow h2piσ_nn,
            show (2 * Real.pi * σ2) ^ (1 / 2 : ℝ) = Real.sqrt (2 * Real.pi * σ2) from
              (Real.sqrt_eq_rpow _).symm]
          congr 1
          rw [Complex.ofReal_exp]; congr 1
          push_cast
          have hσ2_ne : (↑σ2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hσ2_pos)
          field_simp; ring
        -- Rewrite inner integrals and finish
        simp_rw [hinner_eq]
        simp_rw [show ∀ u : ℝ, ψ u * (↑(Real.sqrt (2 * Real.pi * σ2)) *
            ↑(Real.exp (-(σ2 * u ^ 2 / 2)))) =
          ↑(Real.sqrt (2 * Real.pi * σ2)) * (ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2))))
          from fun u => by ring]
        exact integral_const_mul _ _
      -- Unfold ρ and pull out 1/(2π)
      have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
      -- LHS = (1/(2π)) * ∫ Re(∫ ψ exp(-ixu)) * exp(-x²/(2σ²))
      have hLHS_eq : ∫ x, inverseFourierDensity ψ x *
          Real.exp (-(x ^ 2 / (2 * σ2))) =
        1 / (2 * Real.pi) * (∫ x : ℝ, (∫ u : ℝ, ψ u * exp (-(↑x * ↑u * I))).re *
          Real.exp (-(x ^ 2 / (2 * σ2)))) := by
        simp_rw [inverseFourierDensity, mul_assoc]
        rw [integral_const_mul]
      rw [hLHS_eq, fubini_identity]
      -- Goal: (1/(2π)) * (√(2πσ²) * Re(∫ ψ exp(-σ²u²/2)))
      --     ≤ √σ²/√(2π) * ∫ ‖ψ‖ exp(-σ²u²/2)
      have hRe_le : (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re ≤
          ∫ u : ℝ, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := by
        calc (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re
            ≤ ‖∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))‖ :=
              le_trans (le_abs_self _) (abs_re_le_norm _)
          _ ≤ ∫ u : ℝ, ‖ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))‖ :=
              norm_integral_le_integral_norm _
          _ = ∫ u : ℝ, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := by
              congr 1; ext u
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (Real.exp_nonneg _)]
      -- Simplify the constant: (1/(2π)) * √(2πσ²) = √σ²/√(2π)
      -- After rw hLHS_eq and fubini_identity, goal is:
      -- 1/(2π) * (√(2πσ²) * Re(∫ ψ exp(-σ²u²/2))) ≤ √σ²/√(2π) * ∫ ‖ψ‖ exp(-σ²u²/2)
      -- Bound Re ≤ ‖·‖ ≤ ∫ ‖·‖, simplify constant.
      set I_re := (∫ u : ℝ, ψ u * ↑(Real.exp (-(σ2 * u ^ 2 / 2)))).re
      set I_norm := ∫ u : ℝ, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2))
      have hI_norm_nn : 0 ≤ I_norm :=
        integral_nonneg fun u => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
      have hI_re_le_norm : I_re ≤ I_norm := hRe_le
      have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr hpi_pos
      have hsqrt_nn : 0 ≤ Real.sqrt σ2 := Real.sqrt_nonneg _
      -- The constant: 1/(2π) * √(2πσ²) = √σ²/√(2π)
      have hc_eq : 1 / (2 * Real.pi) * Real.sqrt (2 * Real.pi * σ2) =
          Real.sqrt σ2 / Real.sqrt (2 * Real.pi) := by
        rw [show (2 * Real.pi * σ2) = (2 * Real.pi) * σ2 from by ring,
          Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
        -- Goal: 1/(2π) * (√(2π) * √σ2) = √σ2/√(2π)
        have h := ne_of_gt hsqrt_pos
        field_simp
        rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      -- Goal: 1/(2π) * (√(2πσ²) * I_re) ≤ √σ²/√(2π) * I_norm
      -- = hc_eq ▸ √σ²/√(2π) * I_re ≤ √σ²/√(2π) * I_norm
      have h1 : 1 / (2 * Real.pi) * (Real.sqrt (2 * Real.pi * σ2) * I_re)
        = Real.sqrt σ2 / Real.sqrt (2 * Real.pi) * I_re := by
        rw [← hc_eq]; ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left hI_re_le_norm
        (div_nonneg hsqrt_nn hsqrt_pos.le)
    -- Now bound the RHS
    calc ∫ x, inverseFourierDensity ψ x * Real.exp (-(x ^ 2 / (2 * σ2)))
        ≤ Real.sqrt σ2 / Real.sqrt (2 * Real.pi) *
          ∫ u, ‖ψ u‖ * Real.exp (-(σ2 * u ^ 2 / 2)) := gaussian_fubini_bound
      _ ≤ Real.sqrt σ2 / Real.sqrt (2 * Real.pi) *
          ∫ u, Real.exp (-(σ2 * u ^ 2 / 2)) := by
          have hexp_int : Integrable (fun u : ℝ =>
              Real.exp (-(σ2 * u ^ 2 / 2))) volume := by
            apply (integrable_exp_neg_mul_sq (by positivity : 0 < σ2 / 2)).mono'
              (by fun_prop)
            exact ae_of_all _ fun u => by
              rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
              apply Real.exp_le_exp_of_le; linarith [sq_nonneg u]
          apply mul_le_mul_of_nonneg_left
          · apply integral_mono_of_nonneg
            · exact ae_of_all _ fun u => mul_nonneg (norm_nonneg _) (Real.exp_nonneg _)
            · exact hexp_int
            · exact ae_of_all _ fun u =>
                mul_le_of_le_one_left (Real.exp_nonneg _) (hψ_norm_le u)
          · exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = 1 := by
          -- ∫ exp(-σ²u²/2) du = √(2π/σ²) = √(2π)/√σ², so the product = 1.
          -- Rewrite the integral using integral_gaussian
          -- ∫ exp(-σ2 u²/2) du = √(2π/σ2), so √σ2/√(2π) * √(2π/σ2) = 1.
          have h_int_eq : (∫ u : ℝ, Real.exp (-(σ2 * u ^ 2 / 2))) =
              Real.sqrt (2 * Real.pi / σ2) := by
            have h1 := integral_gaussian (σ2 / 2)
            -- h1 : ∫ x, exp(-(σ2/2) * x²) = √(π/(σ2/2))
            -- We need: ∫ u, exp(-(σ2 * u²/2)) = √(2π/σ2)
            -- The integrands are equal: -(σ2/2)*x² = -(σ2*x²/2)
            -- The RHS: π/(σ2/2) = 2π/σ2
            calc (∫ u : ℝ, Real.exp (-(σ2 * u ^ 2 / 2)))
                = ∫ u : ℝ, Real.exp (-(σ2 / 2) * u ^ 2) := by
                  congr 1; ext u; congr 1; ring
              _ = Real.sqrt (Real.pi / (σ2 / 2)) := h1
              _ = Real.sqrt (2 * Real.pi / σ2) := by
                  congr 1; field_simp
          rw [h_int_eq, Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * Real.pi),
            div_mul_div_comm, mul_comm (Real.sqrt σ2) (Real.sqrt (2 * Real.pi)),
            div_self (ne_of_gt (mul_pos (Real.sqrt_pos.mpr
              (by positivity : 0 < 2 * Real.pi)) (Real.sqrt_pos.mpr hσ2_pos)))]
  have hbdd : ∫⁻ x, ENNReal.ofReal (inverseFourierDensity ψ x) ∂volume ≤ 1 :=
    le_of_tendsto' hMCT hgn_le_one
  exact ne_top_of_le_ne_top ENNReal.one_ne_top hbdd

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
  simp only [Complex.real_smul, hv_def, Complex.ofReal_mul]
  -- Goal: cexp (I * ↑π * ↑⟪y, ξ * π⁻¹ * 2⁻¹⟫ * 2) * ↑(ρ y) = ↑(ρ y) * cexp (↑ξ * ↑y * I)
  rw [mul_comm]
  -- Goal: ↑(ρ y) * cexp (↑ξ * ↑y * I) = ↑(ρ y) * cexp (I * ↑π * ↑⟪y, ξ * π⁻¹ * 2⁻¹⟫ * 2)
  congr 1
  -- Goal: cexp (↑ξ * ↑y * I) = cexp (I * ↑π * ↑⟪y, ξ * π⁻¹ * 2⁻¹⟫ * 2)
  -- Both sides are exp(i * ξ * y) up to reordering.
  congr 1
  -- Goal: ↑ξ * ↑y * I = I * ↑π * ↑⟪y, ξ * π⁻¹ * 2⁻¹⟫ * 2
  -- Key: ⟪y, c⟫_ℝ = c * y on ℝ.
  -- After rewriting the inner product, reduce to ring.
  -- Goal: ↑ξ * ↑y * I = ↑2 * ↑π * ↑⟪y, ξ / (2 * π)⟫ * I
  -- Compute ⟪y, c⟫ = c * y on ℝ (using RCLike inner product).
  have hInner : ⟪y, ξ / (2 * Real.pi)⟫ = ξ / (2 * Real.pi) * y := by
    rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial]
    exact AddMonoidHom.id_apply (M := ℝ) _
  -- Cast to ℂ, substitute hInner, then ring.
  have hCast : (↑⟪y, ξ / (2 * Real.pi)⟫ : ℂ) = ↑ξ / ↑(2 * Real.pi) * ↑y := by
    push_cast [hInner]; ring
  rw [hCast]
  push_cast
  field_simp [Real.pi_ne_zero]

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
  have hρ_nn : ∀ x, 0 ≤ ρ x := inverseFourierDensity_nonneg ψ hψc hpd _hI
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
