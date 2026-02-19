/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Constructions.Projective
import LeanLevy.Processes.FiniteDimensional

/-!
# Projective Families of Measures

This file bundles a family of finite-dimensional measures together with their
projective consistency and probability-measure properties into a single
`ProjectiveFamily` structure. This is the natural input for the Kolmogorov
extension theorem: given a projective family, the theorem produces a measure
on the infinite product space whose finite-dimensional marginals match.

## Main definitions

* `ProbabilityTheory.ProjectiveFamily` — a structure bundling a family of
  measures indexed by `Finset ι`, consistency, and the probability property.
* `ProbabilityTheory.ProjectiveFamily.ofProcess` — constructs a projective
  family from a measurable stochastic process under a probability measure.

## Main results

* `ProbabilityTheory.ProjectiveFamily.restrict_eq` — restricting from `I` to
  `J ⊆ I` recovers `measure J`.
* `ProbabilityTheory.ProjectiveFamily.map_map_restrict` — composing two
  successive restrictions equals a single restriction.
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- A **projective family** of probability measures. This bundles:
- a family of measures on finite products, indexed by `Finset ι`;
- projective consistency (`IsProjectiveMeasureFamily`);
- the probability measure property for each index set.

This is the natural input to the Kolmogorov extension theorem. -/
structure ProjectiveFamily (ι : Type*) (α : ι → Type*)
    [∀ i, MeasurableSpace (α i)] where
  /-- The measure on `(j : J) → α j` for each finite index set `J`. -/
  measure : ∀ J : Finset ι, Measure (∀ j : J, α j)
  /-- The family is projective: marginalizing from `I` to `J ⊆ I` recovers `measure J`. -/
  consistent : IsProjectiveMeasureFamily measure
  /-- Each measure in the family is a probability measure. -/
  prob : ∀ J : Finset ι, IsProbabilityMeasure (measure J)

namespace ProjectiveFamily

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
variable (pf : ProjectiveFamily ι α)

instance isProbabilityMeasure (J : Finset ι) : IsProbabilityMeasure (pf.measure J) :=
  pf.prob J

/-- Restricting the measure at `I` to a subset `J ⊆ I` via `Finset.restrict₂`
gives back the measure at `J`. This is the forward form of projective consistency. -/
@[simp]
theorem restrict_eq {I J : Finset ι} (hJI : J ⊆ I) :
    (pf.measure I).map (Finset.restrict₂ hJI) = pf.measure J :=
  (pf.consistent I J hJI).symm

/-- Composing two successive restrictions `I → J → K` via `Measure.map` equals
a single restriction `I → K`. -/
theorem map_map_restrict {I J K : Finset ι} (hJI : J ⊆ I) (hKJ : K ⊆ J) :
    ((pf.measure I).map (Finset.restrict₂ hJI)).map (Finset.restrict₂ hKJ) =
      (pf.measure I).map (Finset.restrict₂ (hKJ.trans hJI)) := by
  rw [Measure.map_map (Finset.measurable_restrict₂ hKJ) (Finset.measurable_restrict₂ hJI),
      Finset.restrict₂_comp_restrict₂]

section OfProcess

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- Build a `ProjectiveFamily` from a measurable stochastic process `X : ℝ≥0 → Ω → E`
under a probability measure `μ`. The family at `I` is the finite-dimensional
distribution `finiteDimDistribution X μ I`, and consistency and probability
follow from the results in `FiniteDimensional.lean`. -/
noncomputable def ofProcess (X : ℝ≥0 → Ω → E) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : ∀ t, Measurable (X t)) : ProjectiveFamily ℝ≥0 (fun _ => E) where
  measure := finiteDimDistribution X μ
  consistent := isProjectiveMeasureFamily_finiteDimDistribution hX
  prob := isProbabilityMeasure_finiteDimDistribution hX

end OfProcess

end ProjectiveFamily

end ProbabilityTheory
