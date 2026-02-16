# Filtration Extensions Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Add 4 theorems to `StochasticProcess.lean` connecting the increment API to mathlib's filtration/independence framework.

**Architecture:** Extend the existing file with two new sections — one for filtration-adapted results, one for pairwise/σ-algebra independence. All core definitions come from mathlib; we only prove glue theorems.

**Tech Stack:** Lean 4 (v4.28.0-rc1), mathlib4 — `Mathlib.Probability.Process.Adapted`, `Mathlib.Probability.Process.Filtration`

---

### Task 1: Add imports and update module doc

**Files:**
- Modify: `LeanLevy/Processes/StochasticProcess.lean:1-21`

**Step 1: Add the new imports**

Add after line 8:
```lean
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
```

**Step 2: Update the module docstring**

Add to the bullet list in the `/-! ... -/` block:
```
* `ProbabilityTheory.stronglyAdapted_naturalFiltration` — a process is adapted to
  its natural filtration.
* `ProbabilityTheory.HasIndependentIncrements.indepFun_increment` — consecutive
  non-overlapping increments are pairwise independent.
* `ProbabilityTheory.Adapted.measurable_increment` — increments of an adapted
  process are measurable w.r.t. the filtration at the later time.
```

**Step 3: Build to verify imports resolve**

Run: `lake build LeanLevy.Processes.StochasticProcess`
Expected: SUCCESS (no errors)

**Step 4: Commit**

```
feat: add filtration imports to StochasticProcess
```

---

### Task 2: Prove `stronglyAdapted_naturalFiltration`

**Files:**
- Modify: `LeanLevy/Processes/StochasticProcess.lean` (add new section before `end ProbabilityTheory`)

**Step 1: Write the theorem statement with `sorry`**

Add a new section after `HasStationaryIncrements` (before `end ProbabilityTheory`):

```lean
section FiltrationAdapted

variable {m : MeasurableSpace Ω} [TopologicalSpace E] [MetrizableSpace E]
  [MeasurableSpace E] [BorelSpace E] [Preorder ι]

/-- A process is strongly adapted to its natural filtration. This is a convenience
wrapper around `Filtration.stronglyAdapted_natural` specialized to processes
with a single value type. -/
theorem stronglyAdapted_naturalFiltration
    {X : ι → Ω → E} (hX : ∀ i, StronglyMeasurable (X i)) :
    MeasureTheory.Filtration.StronglyAdapted
      (MeasureTheory.Filtration.natural (fun i => X i) hX) (fun i => X i) :=
  sorry

end FiltrationAdapted
```

**Step 2: Build to verify the statement type-checks**

Run: `lake build LeanLevy.Processes.StochasticProcess`
Expected: SUCCESS with sorry warning

**Step 3: Fill in the proof**

Replace `sorry` with:
```lean
  MeasureTheory.Filtration.stronglyAdapted_natural hX
```

Note: `stronglyAdapted_natural` takes `(hum : ∀ i, StronglyMeasurable[m] (u i))` and returns
`StronglyAdapted (Filtration.natural u hum) u`. Our `hX` should match directly.

If the types don't unify due to the dependent `β` parameter (mathlib uses `β : ι → Type*`,
we have constant `E`), the fix is to let Lean infer `β := fun _ => E` from the term
`(fun i => X i)`.

**Step 4: Build to verify no sorry**

Run: `lake build LeanLevy.Processes.StochasticProcess`
Expected: SUCCESS (no warnings)

**Step 5: Commit**

```
feat: prove process adapted to its natural filtration
```

---

### Task 3: Prove `HasIndependentIncrements.indepFun_increment`

**Files:**
- Modify: `LeanLevy/Processes/StochasticProcess.lean` (add to new section)

**Step 1: Write the theorem statement with `sorry`**

Add a new section after `FiltrationAdapted`:

```lean
section IncrementIndependence

variable [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]

/-- For a process with independent increments, two consecutive non-overlapping
increments are pairwise independent. -/
theorem HasIndependentIncrements.indepFun_increment
    {X : ι → Ω → E} {μ : Measure Ω} (h : HasIndependentIncrements X μ)
    {s t u : ι} (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun (increment X s t) (increment X t u) μ :=
  sorry

end IncrementIndependence
```

**Step 2: Build to verify the statement type-checks**

Run: `lake build LeanLevy.Processes.StochasticProcess`
Expected: SUCCESS with sorry warning

**Step 3: Fill in the proof**

The proof strategy:
1. Instantiate `h` with `n = 2` and times `![s, t, u] : Fin 3 → ι`.
2. Show `Monotone ![s, t, u]` from `hst` and `htu`.
3. Extract `iIndepFun` of the two increments.
4. Apply `iIndepFun.indepFun` with `(0 : Fin 2) ≠ (1 : Fin 2)`.
5. Show the resulting functions equal `increment X s t` and `increment X t u` via
   `Fin.cons` reduction (`Matrix.cons_val_zero`, `Matrix.cons_val_one`).

Approximate proof:
```lean
  have hmono : Monotone (![s, t, u] : Fin 3 → ι) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] <;> linarith
  have hindep := h 2 ![s, t, u] hmono
  -- hindep : iIndepFun (fun k : Fin 2 => increment X (![s,t,u] k.castSucc) (![s,t,u] k.succ)) μ
  have h01 := hindep.indepFun (show (0 : Fin 2) ≠ 1 from Fin.ne_of_val_ne (by norm_num))
  -- h01 : IndepFun (increment X s t) (increment X t u) μ
  -- May need convert/simp to reduce the Fin indexing
  convert h01 using 1 <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Fin.castSucc, Fin.val_zero, Fin.val_one]
```

This proof may need iteration. The main risk is Fin/Matrix `simp` lemmas not reducing
cleanly. Fallback: use `show` or `change` to manually state the simplified goal, then `rfl`.

**Step 4: Build to verify no sorry**

Run: `lake build LeanLevy.Processes.StochasticProcess`
Expected: SUCCESS (no warnings)

**Step 5: Commit**

```
feat: extract pairwise IndepFun from independent increments
```

---

### Task 4: Prove `Adapted.measurable_increment`

**Files:**
- Modify: `LeanLevy/Processes/StochasticProcess.lean` (add to `FiltrationAdapted` section)

**Step 1: Write the theorem statement with `sorry`**

Add inside the `FiltrationAdapted` section (requires additional variables):

```lean
variable [Sub E] [MeasurableSub₂ E] {𝓕 : MeasureTheory.Filtration ι m}

/-- If `X` is adapted to filtration `𝓕`, then `increment X s t` is `𝓕 t`-measurable
when `s ≤ t`. -/
theorem MeasureTheory.Filtration.Adapted.measurable_increment
    {X : ι → Ω → E} (hX : MeasureTheory.Filtration.Adapted 𝓕 (fun i => X i))
    {s t : ι} (hst : s ≤ t) :
    Measurable[𝓕 t] (increment X s t) :=
  sorry
```

**Step 2: Build to verify the statement type-checks**

Run: `lake build LeanLevy.Processes.StochasticProcess`
Expected: SUCCESS with sorry warning

**Step 3: Fill in the proof**

```lean
  (hX t).sub ((hX s).mono (𝓕.mono hst))
```

Explanation:
- `hX t : Measurable[𝓕 t] (X t)`
- `hX s : Measurable[𝓕 s] (X s)`
- `𝓕.mono hst : 𝓕 s ≤ 𝓕 t` (filtration monotonicity)
- `(hX s).mono (𝓕.mono hst) : Measurable[𝓕 t] (X s)`
- `.sub` gives `Measurable[𝓕 t] (X t - X s)` i.e. `Measurable[𝓕 t] (increment X s t)`

Note: `Measurable.sub` requires `[MeasurableSub₂ E]`. The `increment` definitional
unfolding (`X t ω - X s ω`) should make `Measurable.sub` apply directly, but if not,
use `show Measurable[𝓕 t] (fun ω => X t ω - X s ω) from ...`.

**Step 4: Build to verify no sorry**

Run: `lake build LeanLevy.Processes.StochasticProcess`
Expected: SUCCESS (no warnings)

**Step 5: Commit**

```
feat: prove increment measurability for adapted processes
```

---

### Task 5: Attempt `HasIndependentIncrements.indep_naturalFiltration`

**Files:**
- Modify: `LeanLevy/Processes/StochasticProcess.lean` (add to `IncrementIndependence` section)

**Step 1: Write the theorem statement with `sorry`**

```lean
/-- For a process with independent increments, the increment `X(t) - X(s)` is
independent of the natural filtration at time `s`. -/
theorem HasIndependentIncrements.indep_naturalFiltration
    [TopologicalSpace E] [MetrizableSpace E] [BorelSpace E]
    {X : ι → Ω → E} {μ : Measure Ω}
    (h : HasIndependentIncrements X μ)
    (hX : ∀ i, StronglyMeasurable (X i))
    {s t : ι} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›)
      ((MeasureTheory.Filtration.natural (fun i => X i) hX).seq s) μ :=
  sorry
```

**Step 2: Build to verify the statement type-checks**

Run: `lake build LeanLevy.Processes.StochasticProcess`
Expected: SUCCESS with sorry warning

**Step 3: Attempt the proof**

The key mathlib tool is `indep_iSup_of_disjoint`:
```lean
theorem indep_iSup_of_disjoint
  (h_le : ∀ i, m i ≤ _mΩ) (h_indep : iIndep m κ μ)
  {S T : Set ι} (hST : Disjoint S T) :
  Indep (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) κ μ
```

Proof sketch:
1. The natural filtration at `s` is `⨆ j ≤ s, comap (X j) mE`.
2. Express this as `⨆ j ∈ S, comap (X j) mE` where `S = {j | j ≤ s}`.
3. Express the increment σ-algebra via `comap (X t - X s)`.
4. The challenge: `HasIndependentIncrements` gives `iIndepFun` of *increments*,
   not of *process values*. We need `iIndep` of the `comap (X j)` σ-algebras,
   which requires going from increment independence to value independence.

This step is non-trivial. The mathematical argument:
- `X j = X 0 + Σ increments` so `σ(X 0, ..., X s) = σ(X 0, incr₁, ..., incrₖ)`
- Independence of increments → independence of these generators
- But formalizing the σ-algebra equality is hard

**Decision point:** If the proof compiles within reasonable effort, complete it.
If the σ-algebra equality is too hard to formalize, leave `sorry` with a clear
comment explaining what remains and why.

**Step 4: Build**

Run: `lake build LeanLevy.Processes.StochasticProcess`
Expected: SUCCESS (possibly with sorry warning if proof is incomplete)

**Step 5: Commit**

```
feat: add increment-filtration independence (with sorry if needed)
```

---

### Task 6: Final quality gate

**Step 1: Full build**

Run: `lake build`
Expected: SUCCESS

**Step 2: Check for sorry's**

Run: `grep -n sorry LeanLevy/Processes/StochasticProcess.lean`
Expected: Either no matches (all proofs complete) or only in Task 5's theorem

**Step 3: Final commit if needed**

Only if there were fixups from the quality gate.
