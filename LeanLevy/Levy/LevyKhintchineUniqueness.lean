/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Levy.LevyKhintchineProof

/-!
# Uniqueness of the Lévy–Khintchine triple: the smeared canonical measure

This file begins Part B of the Lévy–Khintchine programme: the triple `(b, σ², ν)` is
determined by the characteristic exponent. The route follows Sato (Theorem 8.1): the
*smeared exponent*
`g(ξ) := ψ(ξ) − ½ ∫_{[-1,1]} ψ(ξ + u) du`
is the characteristic function of a **finite** measure `ρ` on `ℝ`, from which `σ²` is read
off as an atom and `ν` by untilting on `{0}ᶜ`.

## The smeared measure

We construct `ρ = smearedMeasure σ² ν` and prove it is finite and computes its atom at `0`.
Later tasks identify `charFun ρ` with the smeared exponent (giving `ρ` from the exponent alone)
and invert `ρ` back to `(σ², ν)`.

### Pinning the Gaussian coefficient (worked by hand)

The Gaussian piece of the LK exponent is `ψ_G(ξ) = −σ²ξ²/2`. Its smear is
```
g_G(ξ) = ψ_G(ξ) − ½ ∫_{-1}^{1} ψ_G(ξ + u) du
       = −σ²ξ²/2 + (σ²/4) ∫_{-1}^{1} (ξ + u)² du.
```
Since `∫_{-1}^{1} (ξ + u)² du = ∫_{-1}^{1} (ξ² + 2ξu + u²) du = 2ξ² + 0 + 2/3`, we get
```
g_G(ξ) = −σ²ξ²/2 + (σ²/4)(2ξ² + 2/3) = −σ²ξ²/2 + σ²ξ²/2 + σ²/6 = σ²/6.
```
The Gaussian smear is the **constant** `σ²/6`; a constant is the characteristic function of a
point mass at `0`, so `ρ` carries a Dirac atom of weight `σ²/6` (NOT `σ²`). Hence the
recovery formula `σ² = 6 · ρ{0}` (`smearedMeasure_singleton_zero`).

### The jump piece

The smear of the jump piece produces, via the Fourier identity
`½ ∫_{-1}^{1} e^{iux} du = Real.sinc x` (`intervalIntegral_exp_I_symm`), a density
`1 − Real.sinc x` against `ν`. We use the mathlib spelling `Real.sinc x` throughout — for a
Lévy measure `ν` with `ν{0} = 0` this agrees `ν`-a.e. with the classical `1 − sin x / x`, and
`Real.sinc` makes the sinc bounds from `LevyKhintchineProof` (`one_sub_sinc_le_mul_min`,
`mul_min_le_one_sub_sinc`) apply syntactically.

## Main definitions

* `ProbabilityTheory.smearedMeasure` — the finite measure `ρ = (σ²/6)•δ₀ + ν.withDensity(1 − sinc)`.

## Main results

* `ProbabilityTheory.smearedMeasure_lintegral_lt_top` — the withDensity mass is finite.
* `ProbabilityTheory.smearedMeasure_isFiniteMeasure` — `ρ` is a finite measure.
* `ProbabilityTheory.smearedMeasure_singleton_zero` — `ρ{0} = σ²/6`, so `σ² = 6·ρ{0}`.
-/

open MeasureTheory ENNReal Set
open scoped NNReal ENNReal Real

namespace ProbabilityTheory

variable (σ_sq : ℝ≥0) (ν : Measure ℝ)

/-- The **smeared canonical measure** `ρ` from Sato's uniqueness route. It is the finite
measure whose characteristic function is the smeared Lévy–Khintchine exponent
`g(ξ) = ψ(ξ) − ½ ∫_{[-1,1]} ψ(ξ + u) du`.

Its two pieces are pinned by the smear algebra:
* a Dirac atom at `0` of weight `σ²/6` (the smear of the Gaussian piece `−σ²ξ²/2` is the
  constant `σ²/6`; see the module docstring for the hand computation), and
* a density `1 − Real.sinc x` against the Lévy measure `ν` (the smear of the jump piece).

The `Real.sinc` spelling is chosen deliberately over the classical `1 − sin x / x`: the two
agree `ν`-a.e. when `ν{0} = 0`, and `Real.sinc` matches the sinc bounds proved in
`LevyKhintchineProof`. -/
noncomputable def smearedMeasure : Measure ℝ :=
  ((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)
    + ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))

/-- The density defining the jump piece of `smearedMeasure` is measurable. -/
theorem measurable_one_sub_sinc :
    Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.sinc x) :=
  ENNReal.measurable_ofReal.comp (measurable_const.sub Real.measurable_sinc)

/-- The mass of the jump (withDensity) piece of `smearedMeasure` is finite: it is dominated by
`2 · ∫⁻ min(1, x²) dν`, which is finite for a Lévy measure via `one_sub_sinc_le_mul_min`. -/
theorem smearedMeasure_lintegral_lt_top {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤ := by
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.min (measurable_id'.pow_const 2))
  calc ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν
      ≤ ∫⁻ x, 2 * ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        exact ENNReal.ofReal_le_ofReal (one_sub_sinc_le_mul_min x)
    _ = 2 * ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν := lintegral_const_mul 2 hmeas
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) hν.lintegral_min_one_sq_lt_top

/-- `smearedMeasure σ² ν` is a finite measure when `ν` is a Lévy measure: the Dirac piece has
finite mass `σ²/6` and the withDensity piece has finite mass by
`smearedMeasure_lintegral_lt_top`. -/
theorem smearedMeasure_isFiniteMeasure {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    IsFiniteMeasure (smearedMeasure σ_sq ν) := by
  refine ⟨?_⟩
  rw [smearedMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine ENNReal.add_lt_top.mpr ⟨?_, smearedMeasure_lintegral_lt_top hν⟩
  exact ENNReal.mul_lt_top (by simp [ENNReal.div_lt_top]) (measure_lt_top _ _)

/-- The atom of the smeared measure at the origin is `σ²/6`: the withDensity piece vanishes on
`{0}` because a Lévy measure gives no mass to the origin. This pins the σ²-recovery
`σ² = 6 · (smearedMeasure σ² ν){0}` as a pure rewrite. -/
theorem smearedMeasure_singleton_zero {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    smearedMeasure σ_sq ν {0} = (σ_sq : ℝ≥0∞) / 6 := by
  have hd : (Measure.dirac (0 : ℝ)) {0} = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton 0)
  rw [smearedMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hd, mul_one,
    withDensity_apply _ (measurableSet_singleton 0),
    setLIntegral_measure_zero _ _ hν.zero_singleton, add_zero]

end ProbabilityTheory
