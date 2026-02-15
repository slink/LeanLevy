/-
Copyright (c) 2026 Tailspin Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tailspin Contributors
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration

/-!
# Stochastic Processes

This file defines the basic vocabulary for stochastic processes indexed by an
ordered type `ι` with values in a measurable group `E`:

* `ProbabilityTheory.increment X s t` — the increment `X t - X s`.
* `ProbabilityTheory.HasIndependentIncrements X μ` — consecutive increments
  along any monotone partition are mutually independent.
* `ProbabilityTheory.HasStationaryIncrements X μ` — the law of an increment
  depends only on the length `h`, not the starting point `s`.
* `ProbabilityTheory.stronglyAdapted_naturalFiltration` — a process is adapted to
  its natural filtration.
* `ProbabilityTheory.HasIndependentIncrements.indepFun_increment` — consecutive
  non-overlapping increments are pairwise independent.
* `ProbabilityTheory.Adapted.measurable_increment` — increments of an adapted
  process are measurable w.r.t. the filtration at the later time.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {ι : Type*} {Ω : Type*} {E : Type*}

section Increment

variable [Sub E]

/-- The increment of a process `X` from time `s` to time `t`. -/
def increment (X : ι → Ω → E) (s t : ι) (ω : Ω) : E := X t ω - X s ω

@[simp]
theorem increment_apply (X : ι → Ω → E) (s t : ι) (ω : Ω) :
    increment X s t ω = X t ω - X s ω := rfl

end Increment

section IncrementLemmas

variable [AddCommGroup E] {X : ι → Ω → E}

@[simp]
theorem increment_self (X : ι → Ω → E) (t : ι) (ω : Ω) :
    increment X t t ω = 0 := sub_self _

theorem increment_add (X : ι → Ω → E) (r s t : ι) (ω : Ω) :
    increment X r s ω + increment X s t ω = increment X r t ω := by
  simp only [increment_apply]; abel

theorem increment_neg (X : ι → Ω → E) (s t : ι) (ω : Ω) :
    increment X s t ω = -increment X t s ω := by
  simp only [increment_apply]; abel

end IncrementLemmas

section MeasurableIncrement

variable [MeasurableSpace Ω] [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]

theorem measurable_increment {X : ι → Ω → E} {s t : ι}
    (hs : Measurable (X s)) (ht : Measurable (X t)) :
    Measurable (increment X s t) :=
  ht.sub hs

end MeasurableIncrement

/-- A process `X` has **independent increments** with respect to a measure `μ` if
for every monotone sequence of times `t₀ ≤ t₁ ≤ ⋯ ≤ tₙ`, the increments
`X(t₁) - X(t₀), …, X(tₙ) - X(tₙ₋₁)` are mutually independent. -/
def HasIndependentIncrements [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]
    (X : ι → Ω → E) (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ) (t : Fin (n + 1) → ι), Monotone t →
    iIndepFun (fun k : Fin n => increment X (t k.castSucc) (t k.succ)) μ

/-- A process `X` has **stationary increments** with respect to a measure `μ` if
the distribution of `X(s + h) - X(s)` depends only on `h`, not on `s`. -/
def HasStationaryIncrements [AddGroup ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]
    (X : ι → Ω → E) (μ : Measure Ω) : Prop :=
  ∀ (s h : ι), IdentDistrib (increment X s (s + h)) (increment X 0 h) μ μ

section IncrementIndependence

variable [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]

/-- For a process with independent increments, two consecutive non-overlapping
increments are pairwise independent. -/
theorem HasIndependentIncrements.indepFun_increment
    {X : ι → Ω → E} {μ : Measure Ω} (h : HasIndependentIncrements X μ)
    {s t u : ι} (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun (increment X s t) (increment X t u) μ := by
  -- Define the time sequence [s, t, u] : Fin 3 → ι
  let τ : Fin 3 → ι := ![s, t, u]
  -- Show the time sequence is monotone
  have hmono : Monotone τ := Fin.monotone_iff_le_succ.mpr fun i => by
    fin_cases i
    · show s ≤ t; exact hst
    · show t ≤ u; exact htu
  -- Get iIndepFun for the two increments
  have hind := h 2 τ hmono
  -- Extract pairwise independence for indices 0 and 1
  exact hind.indepFun (i := 0) (j := 1) (by decide)

end IncrementIndependence

section FiltrationAdapted

variable {m : MeasurableSpace Ω} [Preorder ι]
  [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
variable [TopologicalSpace.MetrizableSpace E]
variable [Sub E] [MeasurableSub₂ E]

omit [Sub E] [MeasurableSub₂ E] in
/-- A process is strongly adapted to its natural filtration. This is a convenience
wrapper around `Filtration.stronglyAdapted_natural` specialized to processes
with a single value type. -/
theorem stronglyAdapted_naturalFiltration
    {X : ι → Ω → E} (hX : ∀ i, StronglyMeasurable (X i)) :
    StronglyAdapted
      (Filtration.natural (fun i => X i) hX) (fun i => X i) :=
  Filtration.stronglyAdapted_natural hX

omit [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E] in
/-- If `X` is adapted to filtration `𝓕`, then `increment X s t` is `𝓕 t`-measurable
when `s ≤ t`. -/
theorem Adapted.measurable_increment
    {𝓕 : Filtration ι m} {X : ι → Ω → E}
    (hX : Adapted 𝓕 (fun i => X i))
    {s t : ι} (hst : s ≤ t) :
    Measurable[𝓕 t] (increment X s t) :=
  (hX t).sub ((hX s).mono (𝓕.mono hst) le_rfl)

end FiltrationAdapted

end ProbabilityTheory
