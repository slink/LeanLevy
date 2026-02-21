/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Constructions.Projective
import LeanLevy.Processes.ProjectiveFamily

/-!
# Kolmogorov Extension Theorem

Given a projective family of probability measures on finite-dimensional product
spaces, the Kolmogorov extension theorem produces a unique probability measure on
the full product (path) space `∀ i, α i` whose finite-dimensional marginals match
the given family.

This file states the theorem and defines the extended measure as a noncomputable
definition. The proof is sorry'd — the classical argument proceeds via:

1. **Content on cylinders**: assign `pf.measure I S` to each `cylinder I S`.
   Projective consistency ensures well-definedness.
2. **σ-additivity via tightness**: each `pf.measure I` is a probability measure
   on a Polish space, hence tight. Use tightness to promote the content to a
   premeasure.
3. **Carathéodory extension**: extend the premeasure from `measurableCylinders`
   to the full product σ-algebra `MeasurableSpace.pi`.

See also `Mathlib.Probability.Kernel.IonescuTulcea` for the `ℕ`-indexed case.

## Main definitions

* `ProbabilityTheory.ProjectiveFamily.kolmogorovExtension` — the extended measure
  on `∀ i, α i`.
* `Function.eval` (from mathlib) — evaluation map at index `i`.

## Main results

* `ProbabilityTheory.ProjectiveFamily.isProjectiveLimit_kolmogorovExtension` —
  the extended measure is a projective limit of the family.
* `ProbabilityTheory.ProjectiveFamily.kolmogorovExtension_unique` —
  any measure with matching marginals equals the extension.
* `ProbabilityTheory.ProjectiveFamily.kolmogorovExtension_apply_cylinder` —
  the measure of a cylinder set equals the finite-dimensional measure.

## References

* Kolmogorov, A.N. *Grundbegriffe der Wahrscheinlichkeitsrechnung*, 1933.
-/

open MeasureTheory

namespace ProbabilityTheory

namespace ProjectiveFamily

variable {ι : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)]

-- Note: The actual proofs of the Kolmogorov extension theorem require
-- `[∀ i, TopologicalSpace (α i)]`, `PolishSpace (α i)`, and
-- `BorelSpace (α i)` for each `i`. These assumptions will be added to each
-- definition and theorem when the sorry's are filled in. For the skeleton,
-- we omit them since the proofs are sorry'd and the type signatures do not
-- require them.

/-- The **Kolmogorov extension** of a projective family: a probability measure on the
product space `∀ i, α i` whose finite-dimensional marginals match `pf.measure`.

The construction proceeds by defining a content on `measurableCylinders α`,
proving σ-additivity via tightness of measures on Polish spaces, and applying the
Carathéodory extension theorem.

**Assumptions for the actual proof** (not yet needed for the sorry'd skeleton):
each `α i` must carry `TopologicalSpace`, `PolishSpace`, and `BorelSpace` instances. -/
noncomputable def kolmogorovExtension (pf : ProjectiveFamily ι α) : Measure (∀ i, α i) :=
  sorry
  -- TODO proof outline:
  -- 1. Define `projectiveFamilyContent pf.measure` on `measurableCylinders α`
  --    using `pf.consistent` to ensure well-definedness.
  -- 2. Prove the content is σ-subadditive. This is the hard step:
  --    use that each `pf.measure I` is tight (Polish space + probability)
  --    to get inner regularity, then show countable disjoint unions are handled.
  -- 3. Promote content to a premeasure via `MeasureTheory.Content.measure` or
  --    `MeasureTheory.OuterMeasure.ofFunction`.
  -- 4. Apply Carathéodory extension to get the measure on `MeasurableSpace.pi`.

/-- The Kolmogorov extension is a projective limit: for every finite index set `I`,
projecting the extended measure onto `(i : I) → α i` recovers `pf.measure I`. -/
theorem isProjectiveLimit_kolmogorovExtension (pf : ProjectiveFamily ι α) :
    IsProjectiveLimit pf.kolmogorovExtension pf.measure := by
  sorry
  -- TODO: Follows from the construction. The Carathéodory extension agrees
  -- with the content on measurable cylinders, and the content was defined
  -- to assign `pf.measure I S` to `cylinder I S`.

/-- The Kolmogorov extension of a projective family of probability measures
is itself a probability measure. -/
instance instIsProbabilityMeasureKolmogorovExtension (pf : ProjectiveFamily ι α) :
    IsProbabilityMeasure pf.kolmogorovExtension := by
  sorry
  -- TODO: Once `isProjectiveLimit_kolmogorovExtension` is proved, apply
  -- `IsProjectiveLimit.isProbabilityMeasure`.

/-- The Kolmogorov extension is the unique measure with matching marginals.
Any other measure that is a projective limit of the same family must equal it. -/
theorem kolmogorovExtension_unique (pf : ProjectiveFamily ι α) (μ : Measure (∀ i, α i))
    (hμ : IsProjectiveLimit μ pf.measure) :
    μ = pf.kolmogorovExtension := by
  sorry
  -- TODO: Apply `IsProjectiveLimit.unique` with
  -- `isProjectiveLimit_kolmogorovExtension` and `hμ`.
  -- Requires `IsFiniteMeasure` instances, which follow from
  -- `IsProbabilityMeasure`.

/-- The Kolmogorov extension assigns to each cylinder set `cylinder I S` the
measure `pf.measure I S`. This unfolds `IsProjectiveLimit` for direct use. -/
@[simp]
theorem kolmogorovExtension_apply_cylinder (pf : ProjectiveFamily ι α) (I : Finset ι)
    {S : Set (∀ i : I, α i)} (hS : MeasurableSet S) :
    pf.kolmogorovExtension (cylinder I S) = pf.measure I S := by
  sorry
  -- TODO: Apply `IsProjectiveLimit.measure_cylinder` with
  -- `isProjectiveLimit_kolmogorovExtension`.

end ProjectiveFamily

end ProbabilityTheory
