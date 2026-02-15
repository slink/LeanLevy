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

section NaturalFiltrationIndependence

variable [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] [AddGroup E]

omit [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] in
/-- When `X 0 = 0`, the increment from `0` to `j` equals `X j`. -/
private theorem increment_zero_eq [Zero ι] {X : ι → Ω → E}
    (h0 : X 0 = fun _ => 0) (j : ι) : increment X 0 j = X j := by
  ext ω; show X j ω - X 0 ω = X j ω
  rw [show X 0 ω = 0 from congr_fun h0 ω, sub_zero]

/-- For a process with independent increments starting at zero, `X j` is independent
of `increment X s t` whenever `0 ≤ j ≤ s ≤ t`. This follows from the partition
`[0, j, s, t]`. -/
private theorem indepFun_X_increment [Zero ι]
    {X : ι → Ω → E} {μ : Measure Ω}
    (h : HasIndependentIncrements X μ)
    (h0 : X 0 = fun _ => 0)
    {j s t : ι} (h0j : 0 ≤ j) (hjs : j ≤ s) (hst : s ≤ t) :
    IndepFun (X j) (increment X s t) μ := by
  -- Use partition [0, j, s, t] : Fin 4 → ι
  have hmono : Monotone (![0, j, s, t] : Fin 4 → ι) :=
    Fin.monotone_iff_le_succ.mpr fun i => by fin_cases i <;> assumption
  -- Get iIndepFun for the 3 consecutive increments from this partition
  have hind := h 3 ![0, j, s, t] hmono
  -- Extract IndepFun for indices 0 and 2 (increment 0→j vs increment s→t)
  have h02 := hind.indepFun (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  change IndepFun (increment X 0 j) (increment X s t) μ at h02
  rwa [increment_zero_eq h0] at h02

/-- For a process with independent increments starting at zero, the increment
`X(t) - X(s)` is independent of the natural filtration at time `s`.

This is a key structural property of Levy processes: the future is independent
of the past. The proof uses `indep_iSup_of_directed_le` over a directed family
indexed by finite subsets of `{j | j ≤ s}`, where each finite subset's independence
follows from the partition argument. -/
-- For a finset F of times ≤ s, the join of σ-algebras generated by {X j : j ∈ F}
-- is independent of the increment σ-algebra. The proof requires:
-- (1) Sorting F to build a monotone partition [0, j₁, ..., jₖ, s, t],
-- (2) Getting iIndep of consecutive increment σ-algebras from HasIndependentIncrements,
-- (3) Applying indep_iSup_of_disjoint on past vs future increment σ-algebras,
-- (4) Showing ⨆ j ∈ F, comap (X j) ≤ ⨆ past, comap (consec_incr) via the
--     telescoping identity X jᵢ = Σ consecutive increments (when X 0 = 0),
-- (5) Applying monotonicity of Indep.
private theorem indep_finset_X_increment [Zero ι]
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [BorelSpace E]
    {X : ι → Ω → E} {μ : Measure Ω}
    (_h : HasIndependentIncrements X μ)
    (_hX : ∀ i, StronglyMeasurable (X i))
    (_h0 : X 0 = fun _ => 0)
    (_h0le : ∀ (i : ι), 0 ≤ i)
    {s t : ι} (_hst : s ≤ t)
    (F : Finset {j : ι // j ≤ s}) :
    Indep (⨆ j ∈ F, MeasurableSpace.comap (X (j : ι)) ‹MeasurableSpace E›)
      (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›) μ := by
  sorry

theorem HasIndependentIncrements.indep_naturalFiltration
    [Zero ι]
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [BorelSpace E]
    [MeasurableSub₂ E]
    {X : ι → Ω → E} {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (h : HasIndependentIncrements X μ)
    (hX : ∀ i, StronglyMeasurable (X i))
    (h0 : X 0 = fun _ => 0)
    (h0le : ∀ (i : ι), 0 ≤ i)
    {s t : ι} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›)
      ((Filtration.natural (fun i => X i) hX).seq s) μ := by
  apply Indep.symm
  show Indep ((Filtration.natural (fun i => X i) hX).seq s)
    (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›) μ
  -- The filtration is: seq s = ⨆ j ≤ s, comap (X j) mE
  -- Unfold via simp
  simp only [Filtration.natural]
  -- Goal: Indep (⨆ j ≤ s, comap (X j) mE) (comap (incr s t) mE) μ
  -- Step 1: Rewrite ⨆ j ≤ s as ⨆ (j : {j // j ≤ s})
  rw [iSup_subtype']
  -- Step 2: Rewrite ⨆ j, m j as ⨆ F : Finset _, ⨆ j ∈ F, m j
  rw [iSup_eq_iSup_finset]
  -- Step 3: Apply indep_iSup_of_directed_le
  apply indep_iSup_of_directed_le
  -- Goal 1: ∀ F, Indep (⨆ j ∈ F, comap (X j) mE) (comap (incr s t) mE) μ
  · exact fun F => indep_finset_X_increment h hX h0 h0le hst F
  -- Goal 2: ∀ F, (⨆ j ∈ F, comap (X j) mE) ≤ _mΩ
  · intro F; exact iSup₂_le fun j _ => (hX j).measurable.comap_le
  -- Goal 3: comap (incr s t) mE ≤ _mΩ
  · exact ((hX t).measurable.sub (hX s).measurable).comap_le
  -- Goal 4: Directed (· ≤ ·) (fun F => ⨆ j ∈ F, comap (X j) mE)
  · exact directed_of_isDirected_le fun F₁ F₂ h12 =>
      biSup_mono fun j hj => Finset.mem_of_subset h12 hj

end NaturalFiltrationIndependence

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
