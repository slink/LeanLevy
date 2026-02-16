# Poisson & Lévy Process Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Define Lévy processes as a predicate, specialize to Poisson processes, prove the characterization theorem via characteristic functions, and sketch a Kolmogorov construction.

**Architecture:** Three new files (`Cadlag.lean`, `LevyProcess.lean`, `PoissonProcess.lean`) layered on top of the existing `StochasticProcess.lean`. Uses mathlib's `poissonMeasure`, `charFun`, `IdentDistrib`, `iIndepFun`. Poisson process is ℕ-valued with ℤ embedding for increment independence.

**Tech Stack:** Lean 4 (v4.28.0-rc1), mathlib4, `lake build`

---

## Task 0: Relax HasStationaryIncrements to AddMonoid

**Files:**
- Modify: `LeanLevy/Processes/StochasticProcess.lean:89`

**Why:** `HasStationaryIncrements` currently requires `[AddGroup ι]` but `ℝ≥0` only has `AddMonoid` (no negation). The definition only uses `s + h` and `0` on the index — `AddMonoid` suffices.

**Step 1: Edit the typeclass constraint**

Change line 89 from:
```lean
def HasStationaryIncrements [AddGroup ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]
```
to:
```lean
def HasStationaryIncrements [AddMonoid ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]
```

**Step 2: Build to verify nothing breaks**

Run: `lake build`
Expected: Success (no downstream uses of `AddGroup` features on `ι` in this def)

**Step 3: Commit**

```
git add LeanLevy/Processes/StochasticProcess.lean
git commit -m "refactor: relax HasStationaryIncrements to AddMonoid index"
```

---

## Task 1: Cadlag.lean — Definitions and basic lemmas

**Files:**
- Create: `LeanLevy/Processes/Cadlag.lean`

**Step 1: Write the file with definitions and basic lemmas**

```lean
/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Topology.Order.Basic

/-!
# Càdlàg Functions

A function `f : α → β` is *càdlàg* (continue à droite, limite à gauche) if it is
right-continuous at every point and has a left limit at every point.

## Main definitions

* `IsCadlagAt f t` — `f` is right-continuous at `t` and has a left limit at `t`.
* `IsCadlag f` — `f` is càdlàg everywhere.

## Main results

* `isCadlag_const` — constant functions are càdlàg.
* `IsCadlag.rightContinuous` — extract right-continuity.
* `IsCadlag.leftLim_exists` — extract left-limit existence.
* `Monotone.isCadlag_of_rightContinuous_nat` — a monotone, right-continuous,
  ℕ-valued function is càdlàg (left limits exist automatically by monotonicity).
-/

open Filter Set

namespace ProbabilityTheory

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
  [Preorder α]

/-- A function `f` is càdlàg at a point `t` if it is right-continuous at `t`
and has a left limit at `t`. -/
def IsCadlagAt (f : α → β) (t : α) : Prop :=
  ContinuousWithinAt f (Ici t) t ∧
  ∃ l, Tendsto f (nhdsWithin t (Iio t)) (nhds l)

/-- A function `f` is càdlàg if it is càdlàg at every point. -/
def IsCadlag (f : α → β) : Prop :=
  ∀ t, IsCadlagAt f t

theorem IsCadlag.rightContinuous (h : IsCadlag f) (t : α) :
    ContinuousWithinAt f (Ici t) t :=
  (h t).1

theorem IsCadlag.leftLim_exists (h : IsCadlag f) (t : α) :
    ∃ l, Tendsto f (nhdsWithin t (Iio t)) (nhds l) :=
  (h t).2

theorem isCadlag_const (c : β) : IsCadlag (fun _ : α => c) :=
  fun _ => ⟨continuousWithinAt_const, c, tendsto_const_nhds⟩

end ProbabilityTheory
```

**Step 2: Build**

Run: `lake build LeanLevy.Processes.Cadlag`
Expected: Success

---

## Task 2: Cadlag.lean — Monotone ℕ-valued left-limit lemma

**Files:**
- Modify: `LeanLevy/Processes/Cadlag.lean`

**Context:** A monotone ℕ-valued function always has left limits (the supremum of
past values is achieved since ℕ is discrete). Right-continuity is NOT automatic —
it must be assumed. We provide:
1. `Monotone.leftLim_exists_nat` — left limits exist for monotone ℕ-valued functions
2. `Monotone.isCadlag_of_rightContinuous_nat` — combined with right-continuity gives càdlàg

**Step 1: Add the monotone lemmas**

Append to the file before `end ProbabilityTheory`:

```lean
section MonotoneNat

variable {f : ℝ≥0 → ℕ}

/-- A monotone ℕ-valued function has a left limit at every point.
The left limit is `⨆ s < t, f s`, which is achieved because ℕ is discrete
and the range `{f s | s < t}` is bounded above by `f t`. -/
theorem Monotone.leftLim_exists_nat (hm : Monotone f) (t : ℝ≥0) :
    ∃ l, Tendsto f (nhdsWithin t (Iio t)) (nhds l) := by
  -- The left limit is the supremum of f on Iio t, which equals
  -- some n ≤ f t. Since {f s | s < t} ⊆ {0, ..., f t} is finite,
  -- the sup is achieved at some s₀ < t (or is 0 if Iio t = ∅).
  -- Then f is eventually equal to n on (s₀, t), so the limit is n.
  by_cases ht : t = 0
  · -- At t = 0, Iio 0 = ∅ in ℝ≥0, so nhdsWithin is ⊥
    subst ht
    exact ⟨f 0, by simp [nhdsWithin_Iio_self_eq_bot_of_isBot (isBot_zero)]⟩
  · -- For t > 0, use that f is bounded above by f(t) and ℕ is discrete
    -- The sup of f on Iio t is achieved, and f is eventually constant
    -- from the left at that value
    sorry

/-- A monotone, right-continuous, ℕ-valued function `ℝ≥0 → ℕ` is càdlàg. -/
theorem Monotone.isCadlag_of_rightContinuous_nat (hm : Monotone f)
    (hrc : ∀ t, ContinuousWithinAt f (Ici t) t) :
    IsCadlag f :=
  fun t => ⟨hrc t, hm.leftLim_exists_nat t⟩

end MonotoneNat
```

**Note on sorry:** `Monotone.leftLim_exists_nat` for `t > 0` requires showing:
1. The range `{f s | s ∈ Iio t}` is bounded above by `f t`
2. The supremum `n` is achieved at some `s₀ < t`
3. For all `s ∈ (s₀, t)`, `f s = n` (since `f` is monotone and ℕ-valued)

This is fully provable but fiddly. Strategy:
- `n := ⨆ s ∈ Iio t, f s` (finite sup since values ≤ f t)
- Find `s₀ < t` with `f s₀ = n` using `Finset.range` or `Nat.find`
- Show `f` is constant on `(s₀, t)` by monotonicity + maximality
- Use `eventually_nhdsWithin_of_forall` + `Filter.Tendsto`

Attempt the full proof. If the `Nat.sSup` / `Finset` path gets too tangled, sorry
this one lemma (adds +1 sorry, still within budget).

**Step 2: Build**

Run: `lake build LeanLevy.Processes.Cadlag`
Expected: Success (with or without sorry on leftLim_exists_nat for t > 0)

**Step 3: Commit**

```
git add LeanLevy/Processes/Cadlag.lean
git commit -m "feat: define càdlàg functions with monotone ℕ-valued lemmas"
```

---

## Task 3: LevyProcess.lean — IsLevyProcess definition

**Files:**
- Create: `LeanLevy/Processes/LevyProcess.lean`

**Step 1: Write the file with the structure and API**

```lean
/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.StochasticProcess
import LeanLevy.Processes.Cadlag
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# Lévy Processes

A *Lévy process* is a stochastic process with stationary independent increments
and càdlàg sample paths. This file defines the predicate `IsLevyProcess` and
provides basic API.

## Main definitions

* `ProbabilityTheory.IsLevyProcess X μ` — predicate asserting `X` is a Lévy
  process w.r.t. measure `μ`.

## Main results

* `IsLevyProcess.indepFun_increment` — non-overlapping increments are independent.
* `IsLevyProcess.identDistrib_increment` — the law of an increment depends only
  on the interval length.
* `IsLevyProcess.charExponent` — the characteristic exponent `ψ` such that
  `φ_{X(t)}(ξ) = exp(t · ψ(ξ))` (definition; the main theorem is sorry'd pending
  infinite divisibility).
-/

open MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {E : Type*}
  [MeasurableSpace Ω] [MeasurableSpace E]
  [TopologicalSpace E] [AddGroup E] [Sub E]

/-- A stochastic process `X : ℝ≥0 → Ω → E` is a **Lévy process** w.r.t. `μ`
if it starts at zero, has independent and stationary increments, and has
càdlàg sample paths almost surely. -/
structure IsLevyProcess (X : ℝ≥0 → Ω → E) (μ : Measure Ω) : Prop where
  /-- The process starts at the identity. -/
  start_zero : X 0 = fun _ => 0
  /-- Consecutive increments along any monotone partition are mutually independent. -/
  indep_increments : HasIndependentIncrements X μ
  /-- The law of an increment depends only on the interval length. -/
  stationary_increments : HasStationaryIncrements X μ
  /-- Sample paths are càdlàg almost surely. -/
  cadlag_ae : ∀ᵐ ω ∂μ, IsCadlag (fun t => X t ω)

namespace IsLevyProcess

variable {X : ℝ≥0 → Ω → E} {μ : Measure Ω} (h : IsLevyProcess X μ)

/-- Non-overlapping increments of a Lévy process are pairwise independent. -/
theorem indepFun_increment {s t u : ℝ≥0} (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun (increment X s t) (increment X t u) μ :=
  h.indep_increments.indepFun_increment hst htu

/-- The law of an increment of a Lévy process depends only on the length. -/
theorem identDistrib_increment (s h : ℝ≥0) :
    IdentDistrib (increment X s (s + h)) (increment X 0 h) μ μ :=
  h.stationary_increments s h

end IsLevyProcess

section CharExponent

variable [BorelSpace E]

/-- The **characteristic exponent** (or Lévy exponent) of a Lévy process,
defined as the log of the characteristic function at time 1:
`ψ(ξ) := log(E[exp(i⟨ξ, X(1)⟩)])`.

For any Lévy process, `E[exp(i⟨ξ, X(t)⟩)] = exp(t · ψ(ξ))`.
The proof of this factorization requires infinite divisibility. -/
noncomputable def IsLevyProcess.charExponent
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (_ : IsLevyProcess X μ) : E → ℂ :=
  fun ξ => Complex.log (charFun (μ.map (X 1)) ξ)

/-- **Lévy–Khintchine factorization** (statement only):
the characteristic function of `X(t)` factors as `exp(t · ψ(ξ))`.

TODO: requires proving infinite divisibility from independent stationary
increments. -/
theorem IsLevyProcess.charFun_eq_exp_mul
    [Inner ℝ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (h : IsLevyProcess X μ) (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ = Complex.exp (↑(t : ℝ) * h.charExponent ξ) := by
  sorry -- Requires infinite divisibility argument

end CharExponent

end ProbabilityTheory
```

**Step 2: Build**

Run: `lake build LeanLevy.Processes.LevyProcess`
Expected: Success (1 sorry in `charFun_eq_exp_mul`)

**Step 3: Commit**

```
git add LeanLevy/Processes/LevyProcess.lean
git commit -m "feat: define Lévy process predicate with characteristic exponent"
```

---

## Task 4: PoissonProcess.lean — IsPoissonProcess definition

**Files:**
- Create: `LeanLevy/Processes/PoissonProcess.lean`

**Step 1: Write the definition and module header**

```lean
/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.LevyProcess
import LeanLevy.Probability.Poisson
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Poisson Process

A *Poisson process* with rate `λ` is an ℕ-valued stochastic process whose
increments are independent and Poisson-distributed.

## Main definitions

* `ProbabilityTheory.IsPoissonProcess N λ μ` — predicate asserting `N` is a
  Poisson process with rate `λ` w.r.t. `μ`.

## Main results

* `IsPoissonProcess.hasStationaryIncrements` — stationarity of ℤ-valued increments.
* `IsPoissonProcess.isLevyProcess` — a Poisson process is a Lévy process (via ℤ).
* `charFun_poissonMeasure_eq` — bridge: `charFun` of `poissonMeasure` equals
  `exp(λ(e^{iξ} − 1))`.
* `IsPoissonProcess.charFun_eq` — characteristic function of `N(t)`.
* `exists_poissonProcess` — existence via Kolmogorov extension (sorry).
-/

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A stochastic process `N : ℝ≥0 → Ω → ℕ` is a **Poisson process** with
rate `λ` w.r.t. measure `μ` if it starts at zero, has independent increments
(in ℤ), and its increments are Poisson-distributed. -/
structure IsPoissonProcess (N : ℝ≥0 → Ω → ℕ) (λ' : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- The process starts at zero. -/
  start_zero : N 0 = fun _ => 0
  /-- Consecutive increments (embedded in ℤ) are mutually independent. -/
  indep_increments : HasIndependentIncrements (fun t ω => (N t ω : ℤ)) μ
  /-- The increment over `[s, s + h]` has Poisson distribution with rate `λ · h`. -/
  increment_poisson : ∀ (s h : ℝ≥0),
    μ.map (fun ω => N (s + h) ω - N s ω) = poissonMeasure (λ' * h)

end ProbabilityTheory
```

**Step 2: Build**

Run: `lake build LeanLevy.Processes.PoissonProcess`
Expected: Success

---

## Task 5: PoissonProcess.lean — Derived lemmas

**Files:**
- Modify: `LeanLevy/Processes/PoissonProcess.lean`

**Step 1: Add stationarity and monotonicity**

Append inside the `ProbabilityTheory` namespace, after the structure definition:

```lean
namespace IsPoissonProcess

variable {N : ℝ≥0 → Ω → ℕ} {λ' : ℝ≥0} {μ : Measure Ω}
  (h : IsPoissonProcess N λ' μ)

/-- The ℤ-valued increments of a Poisson process are stationary: the law
of `N(s+h) - N(s)` (in ℤ) depends only on `h`. -/
theorem hasStationaryIncrements :
    HasStationaryIncrements (fun t ω => (N t ω : ℤ)) μ := by
  intro s k
  -- Both sides map to (poissonMeasure (λ' * k)).map Nat.cast via increment_poisson
  -- Need to show IdentDistrib of ℤ-valued increments
  -- Strategy: show both pushforward measures equal (poissonMeasure (λ' * k)).map Nat.cast
  sorry -- Attempt full proof: connect ℤ increment to ℕ increment via Nat.cast

/-- A Poisson process is a.e. non-decreasing: `N s ω ≤ N (s + h) ω` a.s.
This follows from the increment `N(s+h) - N(s)` being ℕ-valued (hence ≥ 0). -/
theorem monotone_ae :
    ∀ᵐ ω ∂μ, ∀ (s t : ℝ≥0), s ≤ t → N s ω ≤ N t ω := by
  sorry -- Strategy: for each rational pair s < t, the increment is ℕ-valued
        -- (poissonMeasure is supported on ℕ), then extend by density

/-- A Poisson process is a Lévy process (via ℤ embedding). -/
theorem isLevyProcess : IsLevyProcess (fun t ω => (N t ω : ℤ)) μ where
  start_zero := by ext ω; simp [h.start_zero, show N 0 ω = 0 from congr_fun h.start_zero ω]
  indep_increments := h.indep_increments
  stationary_increments := h.hasStationaryIncrements
  cadlag_ae := by
    sorry -- Requires: a.s. monotonicity → a.s. right-continuity (for ℕ-valued)
          -- + Monotone.isCadlag_of_rightContinuous_nat

end IsPoissonProcess
```

**Note on sorries:** Three potential sorries here:
- `hasStationaryIncrements` — connecting ℤ and ℕ increments. Attempt full proof:
  show `IdentDistrib` by proving both pushforward measures equal
  `(poissonMeasure (λ' * k)).map Nat.cast`. Key lemmas: `Measure.map_map`,
  `h.increment_poisson`, and `h.start_zero`.
- `monotone_ae` — provable via countable intersection over rational pairs + the
  fact that `poissonMeasure` is supported on ℕ (non-negative).
- `isLevyProcess.cadlag_ae` — the hardest; requires right-continuity a.s. from
  distributional properties. If the other two are proved, this becomes the sole sorry.

**Target: at most 1 sorry** (in `cadlag_ae`), prove the other two.

**Step 2: Build**

Run: `lake build LeanLevy.Processes.PoissonProcess`
Expected: Success

---

## Task 6: PoissonProcess.lean — charFun bridge lemma

**Files:**
- Modify: `LeanLevy/Processes/PoissonProcess.lean`

**Context:** We need to connect mathlib's `charFun` (defined for `Measure E` with
`Inner ℝ E`) to our `poissonCharFun_eq` (a tsum identity). Since `poissonMeasure`
is `Measure ℕ` and ℕ doesn't have `Inner ℝ ℕ`, we push forward to ℝ via `Nat.cast`.

**Step 1: Add the bridge lemma**

Append before the `IsPoissonProcess` namespace:

```lean
/-- The characteristic function of the Poisson distribution pushed forward to ℝ:
`charFun ((poissonMeasure r).map Nat.cast) ξ = exp(r(e^{iξ} − 1))`.

Proof strategy:
1. `charFun_apply_real` to unfold as `∫ x, exp(ξ * x * I) ∂(...)`.
2. `integral_map` to pull back to `∫ n, exp(ξ * ↑n * I) ∂poissonMeasure r`.
3. `PMF.integral_eq_tsum` to rewrite as `∑' n, pmfReal n • exp(...)`.
4. Match with `poissonCharFun_eq` from `Poisson.lean`.
-/
theorem charFun_poissonMeasure_eq (r : ℝ≥0) (ξ : ℝ) :
    charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) ξ =
    cexp (↑(r : ℝ) * (cexp (↑ξ * I) - 1)) := by
  -- Step 1: unfold charFun as integral, pull back through map
  rw [charFun_apply_real]
  rw [integral_map (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)) (by fun_prop)]
  -- Step 2: rewrite integral over PMF.toMeasure as tsum
  -- poissonMeasure r = (poissonPMF r).toMeasure
  change ∫ n, cexp (↑ξ * ↑(↑n : ℝ) * I) ∂(poissonPMF r).toMeasure = _
  rw [PMF.integral_eq_tsum]
  -- Step 3: simplify pmf weights and match with poissonCharFun
  -- (poissonPMF r n).toReal = poissonPMFReal r n
  -- real smul on ℂ: a • z = ↑a * z
  -- Match with poissonCharFun_eq
  sorry -- Attempt: simp with poissonPMF_toReal, smul_eq_mul, poissonCharFun_eq
  · -- Integrability: norm of integrand ≤ 1 * poissonPMFReal, which is summable
    sorry
```

**Proof strategy details:**
- After `PMF.integral_eq_tsum`, the goal becomes
  `∑' n, (poissonPMF r n).toReal • cexp(ξ * ↑n * I) = cexp(r * (cexp(ξI) - 1))`
- Rewrite `(poissonPMF r n).toReal` to `poissonPMFReal r n` via `poissonPMF_toReal`
- Rewrite `a • z` to `↑a * z` via `smul_eq_mul` / `ofReal_smul` / `real_smul`
- Rearrange to match `poissonCharFun` definition: `∑' n, cexp(...) * ↑(poissonPMFReal ...)`
- Apply `poissonCharFun_eq`

Key mathlib lemmas to use:
- `charFun_apply_real`
- `integral_map`
- `PMF.integral_eq_tsum`
- `poissonPMF_toReal` (from our `Poisson.lean`)
- `Complex.real_smul` or `Complex.ofReal_mul_re`
- `poissonCharFun_eq` (from our `Poisson.lean`)
- `summable_poissonCharFun` (from our `Poisson.lean`) for integrability

**Step 2: Build**

Run: `lake build LeanLevy.Processes.PoissonProcess`
Expected: Success

---

## Task 7: PoissonProcess.lean — Characterization theorem

**Files:**
- Modify: `LeanLevy/Processes/PoissonProcess.lean`

**Step 1: Add the characterization theorem**

Append inside the `IsPoissonProcess` namespace:

```lean
/-- **Poisson process characterization:** the characteristic function of `N(t)`
(pushed to ℝ) is `exp(λt(e^{iξ} − 1))`. -/
theorem charFun_eq (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (fun ω => (N t ω : ℝ))) ξ =
    cexp (↑(λ' * t : ℝ≥0) * (cexp (↑ξ * I) - 1)) := by
  -- N t = N(0 + t) - N 0 (by start_zero, N 0 = 0)
  -- So μ.map (N t : ℝ) = μ.map (N(0+t) - N(0) : ℕ → ℝ)
  -- = (poissonMeasure (λ' * t)).map Nat.cast (by increment_poisson)
  -- Then apply charFun_poissonMeasure_eq
  have h0 : (fun ω => (N t ω : ℝ)) = (fun ω => ((N (0 + t) ω - N 0 ω : ℕ) : ℝ)) := by
    ext ω
    simp [show N 0 ω = 0 from congr_fun h.start_zero ω, show (0 : ℝ≥0) + t = t from zero_add t]
  rw [h0, show (fun ω => ((N (0 + t) ω - N 0 ω : ℕ) : ℝ)) =
    (Nat.cast : ℕ → ℝ) ∘ (fun ω => N (0 + t) ω - N 0 ω) from rfl,
    ← Measure.map_map (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)) (by fun_prop),
    h.increment_poisson 0 t, charFun_poissonMeasure_eq]
```

**Step 2: Build**

Run: `lake build LeanLevy.Processes.PoissonProcess`
Expected: Success (depends on Task 6 being sorry-free)

---

## Task 8: PoissonProcess.lean — Kolmogorov construction (sorry)

**Files:**
- Modify: `LeanLevy/Processes/PoissonProcess.lean`

**Step 1: Add the existence theorem**

Append after the `IsPoissonProcess` namespace:

```lean
section Construction

/-- **Existence of a Poisson process** via Kolmogorov extension.

The finite-dimensional distributions (products of Poisson marginals) form a
projective family; the Kolmogorov extension theorem yields a probability
measure on path space `ℝ≥0 → ℕ` whose marginals are the Poisson fdds. -/
theorem exists_poissonProcess (λ' : ℝ≥0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (N : ℝ≥0 → Ω → ℕ),
      IsPoissonProcess N λ' μ := by
  sorry -- Kolmogorov extension: build projective family from Poisson fdds,
        -- apply extension theorem, verify axioms on the canonical process

end Construction
```

**Step 2: Build**

Run: `lake build LeanLevy.Processes.PoissonProcess`
Expected: Success (1 sorry)

**Step 3: Commit**

```
git add LeanLevy/Processes/PoissonProcess.lean
git commit -m "feat: define Poisson process with characterization theorem"
```

---

## Task 9: Full build + sorry audit

**Step 1: Full project build**

Run: `lake build`
Expected: Success

**Step 2: Audit sorries**

Run: `grep -rn "sorry" LeanLevy/Processes/Cadlag.lean LeanLevy/Processes/LevyProcess.lean LeanLevy/Processes/PoissonProcess.lean`

Expected sorry locations (target ≤ 3-4):

| File | Lemma | Reason |
|------|-------|--------|
| `LevyProcess.lean` | `charFun_eq_exp_mul` | Infinite divisibility |
| `PoissonProcess.lean` | `isLevyProcess.cadlag_ae` | Path regularity |
| `PoissonProcess.lean` | `exists_poissonProcess` | Kolmogorov extension |

Possibly also:
| `Cadlag.lean` | `leftLim_exists_nat` (t > 0 case) | If the Nat.sSup argument is too fiddly |
| `PoissonProcess.lean` | `charFun_poissonMeasure_eq` | If the tsum/smul coercion chain is too deep |

**Step 3: Final commit (if needed)**

```
git add -A LeanLevy/Processes/
git commit -m "feat: add Poisson and Lévy process formalization"
```

---

## Sorry Budget Summary

**Hard sorry (cannot prove without major new infrastructure):**
1. `IsLevyProcess.charFun_eq_exp_mul` — needs infinite divisibility theory
2. `exists_poissonProcess` — needs Kolmogorov extension applied to Poisson fdds

**Soft sorry (provable but may be fiddly):**
3. `IsPoissonProcess.isLevyProcess.cadlag_ae` — needs right-continuity from distributions

**Attempt to prove (may sorry if too deep):**
4. `Monotone.leftLim_exists_nat` — should be provable with Nat.sSup
5. `charFun_poissonMeasure_eq` — should be provable with PMF.integral_eq_tsum
6. `IsPoissonProcess.hasStationaryIncrements` — should be provable via map_map
7. `IsPoissonProcess.monotone_ae` — should be provable via countable intersection

**Target: 3 hard/soft sorries, 0 in the "attempt" category.**

---

## Reference: Key Mathlib Lemmas

| Lemma | Module | Purpose |
|-------|--------|---------|
| `charFun_apply_real` | `CharacteristicFunction` | Unfold charFun for ℝ measures |
| `PMF.integral_eq_tsum` | `ProbabilityMassFunction.Integrals` | Integral over PMF = tsum |
| `Measure.map_map` | `MeasureTheory.Measure.Map` | `(μ.map f).map g = μ.map (g ∘ f)` |
| `integral_map` | `MeasureTheory.Integral.Bochner` | Pull integral through map |
| `poissonPMF_toReal` | `LeanLevy.Probability.Poisson` | PMF value = poissonPMFReal |
| `poissonCharFun_eq` | `LeanLevy.Probability.Poisson` | Closed form char fun |
| `summable_poissonPMFReal` | `LeanLevy.Probability.Poisson` | PMF summability |
| `IdentDistrib` | `Mathlib.Probability.IdentDistrib` | Equal-in-distribution |
| `iIndepFun` | `Mathlib.Probability.Independence.Basic` | Mutual independence |
