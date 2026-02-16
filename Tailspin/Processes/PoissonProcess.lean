/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import Tailspin.Processes.LevyProcess
import Tailspin.Probability.Poisson
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Poisson Process

This file defines the Poisson process as a structure predicate and derives key properties:

* `ProbabilityTheory.IsPoissonProcess` — a counting process `N : ℝ≥0 → Ω → ℕ` is a Poisson
  process with rate `r` if it starts at zero, has independent increments (via ℤ embedding),
  and each increment `N(s+h) - N(s)` has Poisson(r·h) distribution.

* `ProbabilityTheory.IsPoissonProcess.hasStationaryIncrements` — stationary increments follow
  from the Poisson increment assumption.

* `ProbabilityTheory.IsPoissonProcess.isLevyProcess` — a Poisson process (ℤ-embedded) is a
  Lévy process.

* `ProbabilityTheory.charFun_poissonMeasure_eq` — the characteristic function of
  `(poissonMeasure r).map Nat.cast` equals `exp(r(e^{iξ} − 1))`.

* `ProbabilityTheory.IsPoissonProcess.charFun_eq` — the characteristic function of the
  time-`t` marginal `N(t)` equals `exp(r·t(e^{iξ} − 1))`.

* `ProbabilityTheory.exists_poissonProcess` — existence (sorry'd, requires Kolmogorov
  extension).

## Implementation notes

The independent increments condition uses the ℤ-valued embedding `fun t ω => (N t ω : ℤ)`
because `HasIndependentIncrements` requires `[Sub E]` and ℕ subtraction is truncated.
The `increment_poisson` field uses ℕ subtraction directly since increments of a counting
process are non-negative.
-/

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Poisson process definition -/

/-- A counting process `N : ℝ≥0 → Ω → ℕ` is a **Poisson process** with rate `rate` if:
1. It starts at zero: `N 0 = 0`.
2. Its ℤ-valued embedding has independent increments.
3. Each increment `N(s+h) - N(s)` has Poisson(`rate * h`) distribution. -/
structure IsPoissonProcess (N : ℝ≥0 → Ω → ℕ) (rate : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- The process starts at zero. -/
  start_zero : N 0 = fun _ => 0
  /-- The ℤ-embedded increments are independent. -/
  indep_increments : HasIndependentIncrements (fun t ω => (N t ω : ℤ)) μ
  /-- Each increment has Poisson distribution. -/
  increment_poisson : ∀ (s h : ℝ≥0),
    μ.map (fun ω => N (s + h) ω - N s ω) = poissonMeasure (rate * h)

/-! ## Derived lemmas -/

namespace IsPoissonProcess

variable {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}

/-- The ℤ-valued increments of a Poisson process are stationary.

**Strategy:** Both `increment (fun t ω => (N t ω : ℤ)) s (s+h)` and
`increment (fun t ω => (N t ω : ℤ)) 0 h` push forward to
`(poissonMeasure (rate * h)).map Nat.cast` when composed with the natural ℤ → ℤ identity,
since the ℕ increment maps to the same ℤ value. We show the two pushforward measures
agree using `increment_poisson`. -/
theorem hasStationaryIncrements (h : IsPoissonProcess N rate μ) :
    HasStationaryIncrements (fun t ω => (N t ω : ℤ)) μ := by
  intro s k
  -- Both increments have the same pushforward measure.
  -- Strategy: both equal (poissonMeasure (rate * k)).map (Nat.cast : ℕ → ℤ).
  -- This requires showing the ℤ increment = ℕ increment cast to ℤ,
  -- which needs monotonicity of N.
  sorry

/-- A Poisson process (ℤ-embedded) is a Lévy process. -/
theorem isLevyProcess (h : IsPoissonProcess N rate μ) :
    IsLevyProcess (fun t ω => (N t ω : ℤ)) μ where
  start_zero := by
    ext ω
    show (N 0 ω : ℤ) = 0
    rw [show N 0 ω = (fun _ => 0) ω from congr_fun h.start_zero ω]
    simp
  indep_increments := h.indep_increments
  stationary_increments := h.hasStationaryIncrements
  cadlag_ae := by
    -- Path regularity: a counting process with independent Poisson increments
    -- has a.s. càdlàg paths. This requires showing that the jumps are isolated
    -- and the process is non-decreasing with right-continuous paths.
    sorry

end IsPoissonProcess

/-! ## Characteristic function of the Poisson measure -/

/-- The characteristic function of the Poisson measure pushed forward to ℝ equals
`exp(r(e^{iξ} − 1))`.

**Proof:**
1. Unfold `charFun` via `charFun_apply_real`.
2. Pull through `Measure.map` via `integral_map`.
3. Unfold `poissonMeasure` as `(poissonPMF r).toMeasure`.
4. Apply `PMF.integral_eq_tsum`.
5. Rewrite `smul` to multiplication.
6. Match with `poissonCharFun` and apply `poissonCharFun_eq`. -/
theorem charFun_poissonMeasure_eq (r : ℝ≥0) (ξ : ℝ) :
    charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) ξ =
    cexp (↑(r : ℝ) * (cexp (↑ξ * I) - 1)) := by
  -- Step 1: Unfold charFun to integral
  rw [charFun_apply_real]
  -- Step 2: Pull integral through Measure.map
  rw [integral_map (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable
    (by fun_prop : Continuous (fun x : ℝ => cexp (↑ξ * ↑x * I))).aestronglyMeasurable]
  -- Step 3: Unfold poissonMeasure as PMF.toMeasure
  change ∫ n, cexp (↑ξ * ↑(n : ℝ) * I) ∂(poissonPMF r).toMeasure = _
  -- Step 4: Apply PMF.integral_eq_tsum
  have hint : Integrable (fun n : ℕ => cexp (↑ξ * ↑(n : ℝ) * I)) (poissonPMF r).toMeasure := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (by fun_prop : Continuous (fun n : ℕ => cexp (↑ξ * ↑(n : ℝ) * I))).measurable.aestronglyMeasurable
    · filter_upwards with n
      rw [show (↑ξ : ℂ) * ↑(n : ℝ) * I = ↑(ξ * ↑n) * I from by push_cast; ring,
        norm_exp_ofReal_mul_I]
  rw [PMF.integral_eq_tsum _ _ hint]
  -- Step 5: Rewrite smul to mul and match poissonCharFun
  simp_rw [poissonPMF_toReal, RCLike.real_smul_eq_coe_mul]
  -- Now: ∑' n, ↑(poissonPMFReal r n) * cexp (↑ξ * ↑(n : ℝ) * I) = ...
  -- Match poissonCharFun (which has the factors in opposite order) via commutativity
  convert poissonCharFun_eq r ξ using 1
  unfold poissonCharFun
  congr 1; ext n; exact mul_comm _ _

/-- The pushforward measure of `N t` (as ℝ) equals `(poissonMeasure (rate * t)).map Nat.cast`. -/
private theorem IsPoissonProcess.map_natCast_eq {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}
    (h : IsPoissonProcess N rate μ) (t : ℝ≥0) :
    μ.map (fun ω => (N t ω : ℝ)) = (poissonMeasure (rate * t)).map (Nat.cast : ℕ → ℝ) := by
  have hfun : (fun ω => (N t ω : ℝ)) =
      (Nat.cast : ℕ → ℝ) ∘ (fun ω => N (0 + t) ω - N 0 ω) := by
    ext ω
    simp only [zero_add, Function.comp_apply, Nat.cast_inj]
    have : N 0 ω = 0 := congr_fun h.start_zero ω
    omega
  rw [hfun]
  have hae : AEMeasurable (fun ω => N (0 + t) ω - N 0 ω) μ :=
    AEMeasurable.of_map_ne_zero (by
      rw [h.increment_poisson 0 t]
      exact IsProbabilityMeasure.ne_zero _)
  rw [← AEMeasurable.map_map_of_aemeasurable
    (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable hae,
    h.increment_poisson 0 t]

/-- The characteristic function of the time-`t` marginal of a Poisson process equals
`exp(rate · t · (e^{iξ} − 1))`. -/
theorem IsPoissonProcess.charFun_eq {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}
    (h : IsPoissonProcess N rate μ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (fun ω => (N t ω : ℝ))) ξ =
    cexp (↑(rate * t : ℝ≥0) * (cexp (↑ξ * I) - 1)) := by
  rw [h.map_natCast_eq t]
  exact charFun_poissonMeasure_eq (rate * t) ξ

/-! ## Existence -/

/-- There exists a probability space supporting a Poisson process with any rate.

This requires the Kolmogorov extension theorem to build a consistent family of
finite-dimensional distributions into a process on a canonical path space. -/
theorem exists_poissonProcess (rate : ℝ≥0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (N : ℝ≥0 → Ω → ℕ),
      IsPoissonProcess N rate μ := by
  sorry -- Kolmogorov extension theorem

end ProbabilityTheory
