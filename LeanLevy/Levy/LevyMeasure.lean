/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Levy Measures

A **Levy measure** on `ℝ` is a Borel measure `ν` satisfying two conditions:

1. `ν {0} = 0` — no mass at the origin.
2. `∫⁻ x, min(1, x²) dν < ∞` — the integral of `min(1, x²)` is finite.

These conditions arise naturally in the Levy-Khintchine representation of infinitely
divisible distributions: the Levy measure captures the jump structure of the process,
while the vanishing at zero and the integrability condition ensure that the
characteristic exponent is well-defined.

## Main definitions

* `ProbabilityTheory.IsLevyMeasure` — predicate asserting that a measure on `ℝ` is a Levy measure.

## Main results

* `ProbabilityTheory.IsLevyMeasure.zero_singleton` — `ν {0} = 0`.
* `ProbabilityTheory.IsLevyMeasure.lintegral_min_one_sq_lt_top` — the integral condition.
* `ProbabilityTheory.isLevyMeasure_zero` — the zero measure is a Levy measure.
-/

open MeasureTheory ENNReal Set
open scoped NNReal ENNReal

namespace ProbabilityTheory

/-- A measure `ν` on `ℝ` is a **Levy measure** if it assigns zero mass to the origin and
the integral of `min(1, x²)` with respect to `ν` is finite. -/
def IsLevyMeasure (ν : Measure ℝ) : Prop :=
  ν {0} = 0 ∧ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤

namespace IsLevyMeasure

variable {ν : Measure ℝ}

/-- A measure is a Levy measure iff it vanishes at the origin and the integral of
`min(1, x²)` is finite. -/
@[simp]
theorem isLevyMeasure_iff :
    IsLevyMeasure ν ↔ ν {0} = 0 ∧ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤ :=
  Iff.rfl

/-- A Levy measure assigns zero mass to the origin. -/
theorem zero_singleton (hν : IsLevyMeasure ν) : ν {0} = 0 :=
  hν.1

/-- The integral of `min(1, x²)` with respect to a Levy measure is finite. -/
theorem lintegral_min_one_sq_lt_top (hν : IsLevyMeasure ν) :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤ :=
  hν.2

end IsLevyMeasure

/-- The zero measure is a Levy measure. -/
theorem isLevyMeasure_zero : IsLevyMeasure (0 : Measure ℝ) :=
  ⟨by simp, by simp⟩

end ProbabilityTheory
