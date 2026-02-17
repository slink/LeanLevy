/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.LevyProcess
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Local Characteristic Exponent

The characteristic exponent of a Lévy process requires taking `Complex.log` of the characteristic
function. Since `Complex.log` has a branch cut on the negative real axis, we construct the
exponent locally near `ξ = 0` where the characteristic function is near 1 (and hence in mathlib's
`slitPlane`).

## Design

We use a **general framework + Lévy specialisation**:

1. `LocalLog` defines the local log construction for any continuous function `φ` with `φ(0) = 1`.
2. `ProbabilityTheory.IsLevyProcess` applies it to the time-1 characteristic function.

## Main definitions

* `LocalLog.goodDomain` — the preimage of `slitPlane` under `φ`, where `Complex.log ∘ φ` is
  well-defined and continuous.
* `LocalLog.localCharExponent` — `Complex.log ∘ φ`.
* `IsLevyProcess.levyGoodDomain` — the good domain for the time-1 characteristic function.
* `IsLevyProcess.levyLocalCharExponent` — the local characteristic exponent.

## Main results

* `LocalLog.continuousOn_localCharExponent` — `log ∘ φ` is continuous on the good domain.
* `LocalLog.exists_ball_subset_goodDomain` — an open ball around 0 lies in the good domain.
* `IsLevyProcess.continuousOn_levyLocalCharExponent` — continuity of the local exponent.
-/

open MeasureTheory Complex Filter Topology
open scoped NNReal

set_option linter.unusedSectionVars false

/-! ### Continuity of the characteristic function -/

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure E} [IsFiniteMeasure ν]

/-- The characteristic function of a finite measure is continuous. -/
theorem continuous_charFun : Continuous (charFun ν) := by
  show Continuous (fun ξ => ∫ x, cexp (↑(@inner ℝ E _ x ξ) * I) ∂ν)
  apply continuous_of_dominated
  · intro ξ
    exact (by fun_prop : Measurable (fun x => cexp (↑(@inner ℝ E _ x ξ) * I))).aestronglyMeasurable
  · intro ξ; apply Eventually.of_forall; intro x
    simp only [Complex.norm_exp_ofReal_mul_I]; exact le_refl _
  · exact integrable_const 1
  · apply Eventually.of_forall; intro x
    exact (by fun_prop : Continuous (fun ξ => cexp (↑(@inner ℝ E _ x ξ) * I)))

end MeasureTheory

/-! ### General LocalLog framework -/

namespace LocalLog

variable {E : Type*} [TopologicalSpace E] [Zero E]

/-- The good domain where `φ` lands in the slit plane (avoids the branch cut). -/
def goodDomain (φ : E → ℂ) : Set E := φ ⁻¹' Complex.slitPlane

theorem mem_goodDomain_zero {φ : E → ℂ} (hφ_zero : φ 0 = 1) :
    (0 : E) ∈ goodDomain φ := by
  simp [goodDomain, Set.mem_preimage, hφ_zero, Complex.one_mem_slitPlane]

theorem isOpen_goodDomain {φ : E → ℂ} (hφ_cont : Continuous φ) :
    IsOpen (goodDomain φ) :=
  Complex.isOpen_slitPlane.preimage hφ_cont

/-- The local characteristic exponent: `Complex.log ∘ φ`. -/
noncomputable def localCharExponent (φ : E → ℂ) (ξ : E) : ℂ :=
  Complex.log (φ ξ)

theorem continuousOn_localCharExponent {φ : E → ℂ} (hφ_cont : Continuous φ) :
    ContinuousOn (localCharExponent φ) (goodDomain φ) :=
  hφ_cont.continuousOn.clog (fun _ hx => hx)

section MetricBall
variable {E : Type*} [SeminormedAddCommGroup E]

theorem charFun_near_one {φ : E → ℂ} (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    Tendsto φ (𝓝 0) (𝓝 1) := by
  rw [← hφ_zero]; exact hφ_cont.continuousAt.tendsto

theorem exists_ball_subset_goodDomain {φ : E → ℂ}
    (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    ∃ ε > 0, Metric.ball (0 : E) ε ⊆ goodDomain φ :=
  Metric.isOpen_iff.mp (isOpen_goodDomain hφ_cont) 0 (mem_goodDomain_zero hφ_zero)

end MetricBall

end LocalLog

/-! ### Lévy process specialisation -/

namespace ProbabilityTheory.IsLevyProcess

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The time-1 characteristic function is continuous. -/
theorem continuous_charFun_one (_hX : ∀ t, Measurable (X t)) :
    Continuous (fun ξ => charFun (μ.map (X 1)) ξ) := by
  haveI : IsFiniteMeasure (μ.map (X 1)) := Measure.isFiniteMeasure_map μ (X 1)
  exact MeasureTheory.continuous_charFun

/-- The time-1 characteristic function equals 1 at `ξ = 0`. -/
theorem charFun_one_zero (_h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    charFun (μ.map (X 1)) (0 : E) = 1 := by
  haveI : IsProbabilityMeasure (μ.map (X 1)) :=
    Measure.isProbabilityMeasure_map (hX 1).aemeasurable
  simp [charFun_zero]

/-- `Tendsto (charFun(μ.map(X 1))) (𝓝 0) (𝓝 1)`. -/
theorem charFun_one_near_one (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    Tendsto (fun ξ => charFun (μ.map (X 1)) ξ) (𝓝 0) (𝓝 1) :=
  LocalLog.charFun_near_one (continuous_charFun_one hX) (charFun_one_zero h hX)

/-- The good domain for the time-1 characteristic function. -/
def levyGoodDomain (_h : IsLevyProcess X μ) (_hX : ∀ t, Measurable (X t)) : Set E :=
  LocalLog.goodDomain (fun ξ => charFun (μ.map (X 1)) ξ)

theorem mem_levyGoodDomain_zero (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    (0 : E) ∈ h.levyGoodDomain hX :=
  LocalLog.mem_goodDomain_zero (charFun_one_zero h hX)

theorem isOpen_levyGoodDomain (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    IsOpen (h.levyGoodDomain hX) :=
  LocalLog.isOpen_goodDomain (continuous_charFun_one hX)

/-- The local characteristic exponent of the Lévy process. -/
noncomputable def levyLocalCharExponent
    (_h : IsLevyProcess X μ) (_hX : ∀ t, Measurable (X t)) : E → ℂ :=
  LocalLog.localCharExponent (fun ξ => charFun (μ.map (X 1)) ξ)

theorem continuousOn_levyLocalCharExponent (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    ContinuousOn (h.levyLocalCharExponent hX) (h.levyGoodDomain hX) :=
  LocalLog.continuousOn_localCharExponent (continuous_charFun_one hX)

end ProbabilityTheory.IsLevyProcess
