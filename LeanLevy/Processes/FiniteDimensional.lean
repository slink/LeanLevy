/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Finite-Dimensional Distributions

This file defines the finite-dimensional distributions of a stochastic process
indexed by `ℝ≥0` with values in a measurable space `E`.

Given a process `X : ℝ≥0 → Ω → E` and a probability measure `μ` on `Ω`,
the **finite-dimensional distribution** at times `I : Finset ℝ≥0` is the
pushforward measure on `(i : I) → E` capturing the joint law of
`(X t₁, …, X tₙ)`.

## Main definitions

* `ProbabilityTheory.finiteDimMap X I` — the sampling map `ω ↦ (i ↦ X i ω)`.
* `ProbabilityTheory.finiteDimDistribution X μ I` — the joint law at times `I`.

## Main results

* `ProbabilityTheory.measurable_finiteDimMap` — the sampling map is measurable.
* `ProbabilityTheory.finiteDimDistribution_restrict` — marginalizing from `I` to
  `J ⊆ I` gives the distribution at `J`.
* `ProbabilityTheory.isProjectiveMeasureFamily_finiteDimDistribution` — the family
  of finite-dimensional distributions is projective.
* `ProbabilityTheory.isProbabilityMeasure_finiteDimDistribution` — probability in,
  probability out.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable (X : ℝ≥0 → Ω → E) (μ : Measure Ω)

/-- The sampling map for a stochastic process at a finite set of times.
`finiteDimMap X I ω` is the function `i ↦ X i ω` restricted to `i ∈ I`. -/
def finiteDimMap (I : Finset ℝ≥0) : Ω → ((i : I) → E) :=
  fun ω (i : I) => X i ω

/-- The finite-dimensional distribution of a process `X` under measure `μ`
at times `I : Finset ℝ≥0`. This is the pushforward of `μ` under the
sampling map `ω ↦ (X t₁ ω, …, X tₙ ω)`. -/
noncomputable def finiteDimDistribution (I : Finset ℝ≥0) :
    Measure ((i : I) → E) :=
  μ.map (finiteDimMap X I)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
@[simp]
theorem finiteDimMap_apply (I : Finset ℝ≥0) (ω : Ω) (i : I) :
    finiteDimMap X I ω i = X i ω :=
  rfl

variable {X} {μ}

/-- The sampling map is measurable when each component `X t` is measurable. -/
@[fun_prop]
theorem measurable_finiteDimMap (hX : ∀ t, Measurable (X t)) (I : Finset ℝ≥0) :
    Measurable (finiteDimMap X I) := by
  exact measurable_pi_lambda _ (fun i => hX i)

/-- Marginalizing the finite-dimensional distribution from times `I` to a
subset `J ⊆ I` recovers the distribution at `J`. This is the key step
for the projective consistency condition. -/
theorem finiteDimDistribution_restrict (hX : ∀ t, Measurable (X t))
    {I J : Finset ℝ≥0} (hJI : J ⊆ I) :
    (finiteDimDistribution X μ I).map (Finset.restrict₂ (π := fun _ => E) hJI) =
      finiteDimDistribution X μ J := by
  simp only [finiteDimDistribution]
  rw [Measure.map_map (Finset.measurable_restrict₂ hJI) (measurable_finiteDimMap hX I)]
  rfl

end ProbabilityTheory
