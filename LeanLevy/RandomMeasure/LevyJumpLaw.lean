/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.RandomMeasure.PoissonMartingale
import LeanLevy.Levy.LevyKhintchineUniqueness

/-!
# The assembled jump law

This file combines the two jump components of a Lévy process — the compound-Poisson large-jump
sum and the compensated small-jump integral — with a constant drift, and identifies the
characteristic function of their sum at a fixed time `t`.

The large-jump sum and the compensated small jumps are supported on the disjoint mark bands
`{|x| ≥ 1}` and `(-1, 1)`, so they are independent; their characteristic functions multiply.
Each factor is a compound-Poisson / compensated exponential of a band integral against the Lévy
measure `ν`, and the two band integrals reassemble the Lévy–Khintchine jump integral at split
radius `1`. Adding the deterministic drift `b · t` supplies the linear term, giving the
characteristic function `exp (t · ψ(ξ))` where `ψ` is the Lévy–Khintchine exponent of the triple
`(b, 0, ν)` — a triple with **zero Gaussian variance**, as befits a pure-jump process.

## Main results

* `ProbabilityTheory.charFun_map_levyJumpSum_eq_exponent` — **the assembled jump law**: for
  `0 ≤ t`, the fixed-time marginal law of `b · t + (large-jump sum) + (compensated small jumps)`
  has characteristic function `exp (t · (b, 0, ν).exponent ξ)`.

The scope is a **single fixed time `t`** (the marginal law), not the full process.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

/-- **The assembled jump law**: drift plus large-jump sum plus compensated small jumps
realizes the Lévy–Khintchine exponent of the triple `(b, 0, ν)` at time `t`. -/
theorem charFun_map_levyJumpSum_eq_exponent [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => b * t + levyLargeJumpSum K X t ω
        + levyCompensatedSmallJump hd hν t ω)) ξ
      = Complex.exp ((t : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
  set L := levyLargeJumpSum K X t with hLdef
  set S := fun ω => levyCompensatedSmallJump hd hν t ω with hSdef
  have hL : Measurable L :=
    measurable_levyLargeJumpSum hd.measurable_count hd.measurable_point
  have hS : AEMeasurable S μ := (Lp.aestronglyMeasurable _).aemeasurable
  have hcont : Continuous fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I) := by fun_prop
  -- Independence factorizes the characteristic function of the sum of the two jump components.
  have hLS : charFun (μ.map (fun ω => L ω + S ω)) ξ
      = charFun (μ.map L) ξ * charFun (μ.map S) ξ := by
    have h := (indepFun_levyLargeJumpSum_levyCompensatedSmallJump hd hν ht).charFun_map_fun_add_eq_mul
      hL.aemeasurable hS
    simpa [Pi.mul_apply] using congrFun h ξ
  -- Rewrite the summand to peel off the deterministic drift.
  have hmap_eq : (fun ω => b * t + L ω + S ω) = fun ω => b * t + (L ω + S ω) := by
    funext ω; ring
  rw [hmap_eq]
  have hgae : AEMeasurable (fun ω => b * t + (L ω + S ω)) μ :=
    aemeasurable_const.add (hL.aemeasurable.add hS)
  rw [charFun_apply_real, integral_map hgae hcont.aestronglyMeasurable]
  -- Peel the drift exponential off the integrand.
  have hpeel : ∀ ω, Complex.exp (↑ξ * ↑(b * t + (L ω + S ω)) * Complex.I)
      = Complex.exp (↑ξ * ↑(b * t) * Complex.I)
        * Complex.exp (↑ξ * ↑(L ω + S ω) * Complex.I) := by
    intro ω; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [hpeel]
  rw [integral_const_mul]
  -- Reassemble the remaining integral as the characteristic function of the two jump components.
  rw [show (∫ ω, Complex.exp (↑ξ * ↑(L ω + S ω) * Complex.I) ∂μ)
        = charFun (μ.map (fun ω => L ω + S ω)) ξ from by
      rw [charFun_apply_real, integral_map
        (show AEMeasurable (fun ω => L ω + S ω) μ from hL.aemeasurable.add hS)
        hcont.aestronglyMeasurable]]
  rw [hLS, charFun_map_levyLargeJumpSum hd hν ht ξ,
    charFun_map_levyCompensatedSmallJump hd hν ht ξ]
  -- Combine the three exponentials and match the Lévy–Khintchine exponent via the radius-1 split.
  rw [← Complex.exp_add, ← Complex.exp_add, LevyKhintchineTriple.exponent_def,
    integral_levyCompensatedIntegrand_eq_small_add_large hν ξ]
  congr 1
  push_cast
  ring
