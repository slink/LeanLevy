# Weak Convergence & Lévy's Continuity Theorem — Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove Lévy's continuity theorem: a sequence of probability measures on ℝ converges weakly iff their characteristic functions converge pointwise.

**Architecture:** Four layers building bottom-up: (1) auxiliary constructions (`expBCF`), (2) tightness from charfun convergence via Fubini + sinc bounds, (3) Lévy's continuity theorem (both directions + iff), (4) bridge to `TendstoInDistribution`. File: `LeanLevy/Probability/WeakConvergence.lean`.

**Tech Stack:** Lean 4 / mathlib4. Key mathlib modules: `ProbabilityMeasure`, `Portmanteau`, `Tight`, `Prokhorov`, `CharacteristicFunction`, `ConvergenceInDistribution`, `SpecialFunctions.Integrals`.

---

## Task 1: File Skeleton + `CharFunTendsto` Definition

**Files:**
- Create: `LeanLevy/Probability/WeakConvergence.lean`

**Step 1: Create the file with imports and module doc**

```lean
/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
-/
import LeanLevy.Probability.Characteristic
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Weak Convergence and Lévy's Continuity Theorem

This file proves Lévy's continuity theorem: a sequence of probability measures
on ℝ converges weakly if and only if their characteristic functions converge
pointwise.

## Main definitions

* `MeasureTheory.ProbabilityMeasure.CharFunTendsto` — pointwise convergence of
  characteristic functions along a filter.

## Main results

* `MeasureTheory.ProbabilityMeasure.charFunTendsto_of_tendsto` — weak convergence
  implies pointwise convergence of characteristic functions.
* `MeasureTheory.ProbabilityMeasure.isTight_of_charFunTendsto` — pointwise convergence
  of characteristic functions implies tightness of the sequence.
* `MeasureTheory.ProbabilityMeasure.tendsto_of_charFunTendsto` — pointwise convergence
  of characteristic functions implies weak convergence (Lévy's continuity theorem,
  hard direction).
* `MeasureTheory.ProbabilityMeasure.tendsto_iff_charFunTendsto` — the biconditional.
* `MeasureTheory.ProbabilityMeasure.tendstoInDistribution_iff_charFunTendsto` — bridge
  to mathlib's `TendstoInDistribution`.

## References

* [P. Billingsley, *Convergence of Probability Measures*]
-/

open MeasureTheory Complex ComplexConjugate Filter Topology

namespace MeasureTheory.ProbabilityMeasure
```

**Step 2: Define `CharFunTendsto`**

```lean
variable {ι : Type*} {F : Filter ι}

/-- Pointwise convergence of characteristic functions of probability measures
along a filter `F`. This is the natural convergence notion for Lévy's
continuity theorem. -/
def CharFunTendsto (μs : ι → ProbabilityMeasure ℝ) (F : Filter ι)
    (μ : ProbabilityMeasure ℝ) : Prop :=
  ∀ ξ : ℝ, Tendsto (fun i => characteristicFun (μs i) ξ) F (𝓝 (characteristicFun μ ξ))

@[simp]
theorem charFunTendsto_iff {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} :
    CharFunTendsto μs F μ ↔
    ∀ ξ : ℝ, Tendsto (fun i => characteristicFun (μs i) ξ) F (𝓝 (characteristicFun μ ξ)) :=
  Iff.rfl
```

**Step 3: Verify compilation**

Run: `lake build LeanLevy.Probability.WeakConvergence`
Expected: SUCCESS (may take a while on first build as it resolves imports)

Notes:
- If any import fails, grep `.lake/packages/mathlib4/Mathlib/` for the correct module path.
- `Mathlib.MeasureTheory.Measure.Portmanteau` might be `Mathlib.MeasureTheory.Measure.Portmanteau.Basic` or similar — check with `fd Portmanteau .lake/packages/mathlib4/`.

---

## Task 2: Auxiliary Construction + Easy Direction

**Files:**
- Modify: `LeanLevy/Probability/WeakConvergence.lean`

**Step 1: Construct `expBCF` — the exponential character as a `BoundedContinuousFunction`**

This is needed because `tendsto_iff_forall_integral_tendsto` characterizes weak convergence via integrals of bounded continuous functions.

```lean
/-! ## Auxiliary constructions -/

/-- The exponential character `x ↦ exp(iξx)` as a bounded continuous function.
This is the integrand of the characteristic function. -/
noncomputable def expBCF (ξ : ℝ) : ℝ →ᵇ ℂ :=
  .mkOfBound ⟨fun x => exp (↑(ξ * x) * I), by fun_prop⟩ 2
    (fun x y => by
      calc dist (exp (↑(ξ * x) * I)) (exp (↑(ξ * y) * I))
          ≤ ‖exp (↑(ξ * x) * I)‖ + ‖exp (↑(ξ * y) * I)‖ := dist_le_norm_add_norm _ _
        _ = 1 + 1 := by simp [norm_exp_ofReal_mul_I]
        _ = 2 := by ring)

@[simp]
theorem expBCF_apply (ξ x : ℝ) : expBCF ξ x = exp (↑(ξ * x) * I) := rfl

theorem integral_expBCF_eq_characteristicFun (μ : ProbabilityMeasure ℝ) (ξ : ℝ) :
    ∫ x, expBCF ξ x ∂(μ : Measure ℝ) = characteristicFun μ ξ := by
  simp [characteristicFun, charFun_apply_real]
  congr 1; ext x; push_cast; ring
```

**Step 2: Prove the easy direction**

Strategy: Weak convergence means integrals of all bounded continuous functions converge. The characteristic function is the integral of `expBCF ξ`, a bounded continuous function. We use `tendsto_iff_forall_integral_tendsto` (the ℝ-valued version) applied to the real and imaginary parts, or `tendsto_iff_forall_integral_rclike_tendsto` if available for ℂ.

```lean
/-! ## Easy direction: weak convergence ⇒ charfun convergence -/

/-- **Easy direction of Lévy's continuity theorem.** Weak convergence of probability
measures implies pointwise convergence of characteristic functions. -/
theorem charFunTendsto_of_tendsto {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : Tendsto μs F (𝓝 μ)) : CharFunTendsto μs F μ := by
  intro ξ
  -- Rewrite charfuns as integrals of the bounded continuous function expBCF
  simp_rw [← integral_expBCF_eq_characteristicFun]
  -- Apply weak convergence characterization
  exact (tendsto_iff_forall_integral_tendsto F (𝕜 := ℂ)).mp h (expBCF ξ)
```

Notes:
- The exact name might be `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` — check namespace.
- If the ℂ version doesn't exist, decompose into real/imaginary parts:
  - Show `Re (charFun)` converges (using real-valued BCF `Re ∘ expBCF`)
  - Show `Im (charFun)` converges (using real-valued BCF `Im ∘ expBCF`)
  - Combine via `Complex.ext_iff` or `Filter.Tendsto.comp`.
- The `(𝕜 := ℂ)` syntax provides the RCLike instance — try with and without it.

**Step 3: Verify compilation**

Run: `lake build LeanLevy.Probability.WeakConvergence`
Expected: SUCCESS

---

## Task 3: Tightness — Tail Bound via Fubini

**Files:**
- Modify: `LeanLevy/Probability/WeakConvergence.lean`

This is the analytic core. We prove: for a probability measure μ on ℝ,

  `μ({x : |x| > 2/T}) ≤ (2/T) · ∫ t in 0..T, (1 - Re(φ(t))) dt`

where `φ = charFun μ`.

**Step 1: State and prove the sinc estimate**

For `|x| > 2/T` and `T > 0`: `T - sin(Tx)/x ≥ T/2`.

```lean
/-! ## Tightness from characteristic function convergence -/

section Tightness

/-- For |x| > 2/T with T > 0, we have T - sin(Tx)/x ≥ T/2. This is because
|sin(Tx)/x| ≤ 1/|x| < T/2. -/
theorem T_sub_sinc_ge_half {T x : ℝ} (hT : 0 < T) (hx : 2 / T < |x|) :
    T / 2 ≤ T - Real.sin (T * x) / x := by
  have hx_ne : x ≠ 0 := by positivity_ne_zero  -- |x| > 2/T > 0
  have : |Real.sin (T * x) / x| ≤ 1 / |x| := by
    rw [abs_div]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_pos.mpr hx_ne)
  -- 1/|x| < T/2, so |sin(Tx)/x| < T/2, so T - sin(Tx)/x ≥ T - T/2 = T/2
  linarith [abs_le.mp (le_of_lt (lt_of_le_of_lt this (by linarith)))]
```

Notes:
- `positivity_ne_zero` might not exist — use manual proof: `ne_of_gt (lt_trans (by positivity) hx)`.
- `Real.abs_sin_le_one` gives `|sin x| ≤ 1`.
- `div_le_div_of_nonneg_right` needs `0 < |x|` — have this from `hx`.
- This step may need careful linarith/nlinarith work. If stuck, sorry and move on.

**Step 2: State and prove the tail bound**

This is the key inequality connecting measure tails to characteristic functions via Fubini.

```lean
/-- **Tail probability bound via characteristic function.** For any probability measure μ
on ℝ and T > 0:
  `μ({x : |x| > 2/T}) ≤ (2/T) · ∫ t in 0..T, (1 - Re(charFun μ t))`

Proof: swap ∫∫ via Fubini, compute inner integral, estimate. -/
theorem measure_abs_gt_le_integral_charFun (μ : ProbabilityMeasure ℝ) {T : ℝ} (hT : 0 < T) :
    (μ : Measure ℝ) {x | 2 / T < |x|} ≤
    ENNReal.ofReal ((2 / T) * ∫ t in (0 : ℝ)..T, (1 - (charFun (μ : Measure ℝ) t).re)) := by
  sorry
```

Proof outline (attempt each step, sorry sub-goals if blocked):
1. Rewrite `charFun μ t = ∫ x, exp(itx) dμ(x)`, so `Re(charFun μ t) = ∫ x, cos(tx) dμ(x)`.
2. Then `∫ t in 0..T, (1 - Re φ(t)) = ∫ t in 0..T, ∫ x, (1 - cos(tx)) dμ(x)`.
3. By Fubini (`MeasureTheory.integral_integral_swap` or `integral_prod`):
   `= ∫ x, ∫ t in 0..T, (1 - cos(tx)) dμ(x)`.
4. Inner integral: `∫ t in 0..T, (1 - cos(tx)) dt = T - sin(Tx)/x` for `x ≠ 0`.
   Use `intervalIntegral.integral_cos` after substitution.
5. For `|x| > 2/T`: `T - sin(Tx)/x ≥ T/2` (from `T_sub_sinc_ge_half`).
6. Therefore `∫ x, (T - sin(Tx)/x) dμ(x) ≥ (T/2) · μ({|x| > 2/T})`.
7. Rearrange: `μ({|x| > 2/T}) ≤ (2/T) · ∫ t in 0..T, (1 - Re φ(t))`.

Key mathlib lemmas needed:
- `integral_prod` or `integral_integral_swap` — Fubini
- `intervalIntegral.integral_cos` — `∫ t in a..b, cos t = sin b - sin a`
- `intervalIntegral.integral_comp_mul_right` — for substitution `cos(tx)`
- `MeasureTheory.integral_nonneg` — integrand ≥ 0
- `MeasureTheory.setIntegral_le_integral` — restrict to `{|x| > 2/T}`

**Step 3: Verify compilation**

Run: `lake build LeanLevy.Probability.WeakConvergence`
Expected: SUCCESS (with sorry in `measure_abs_gt_le_integral_charFun`)

---

## Task 4: Tightness from CharFun Convergence

**Files:**
- Modify: `LeanLevy/Probability/WeakConvergence.lean`

**Step 1: Prove that charfun convergence implies tightness**

```lean
/-- **Tightness from characteristic function convergence.** If the characteristic
functions of a sequence of probability measures converge pointwise to the
characteristic function of a probability measure μ, then the sequence is tight.

Proof strategy:
1. The limit charfun φ_μ is continuous at 0 with φ_μ(0) = 1.
2. For any ε > 0, choose T small enough that
   (2/T) · ∫ t in 0..T, (1 - Re φ_μ(t)) < ε/2.
3. By dominated convergence (|1 - Re φ_n| ≤ 2), for large n:
   (2/T) · ∫ t in 0..T, (1 - Re φ_n(t)) < ε.
4. By `measure_abs_gt_le_integral_charFun`, μ_n({|x| > 2/T}) < ε for large n.
5. Finitely many remaining n are each tight (single prob measure on Polish space).
6. Take union of compact sets. -/
theorem isTight_of_charFunTendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : CharFunTendsto μs atTop μ) :
    IsTightMeasureSet (Set.range (fun n => (μs n : Measure ℝ))) := by
  sorry
```

Proof outline:
1. Use `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` to reduce to: ∀ ε > 0, ∃ K compact, ∀ n, (μs n) Kᶜ ≤ ε.
2. Fix ε > 0. The function `t ↦ 1 - Re(φ_μ(t))` is continuous and vanishes at 0.
3. By continuity, choose `T > 0` such that `(2/T) · ∫ t in 0..T, (1 - Re φ_μ(t)) < ε/2`.
   - This uses: `Re φ_μ` is continuous (composition of continuous functions).
   - And `Re φ_μ(0) = Re 1 = 1`, so `1 - Re φ_μ(t) → 0` as `t → 0`.
   - Specifically: `(1/T) · ∫ t in 0..T, f(t) → f(0) = 0` as `T → 0⁺` for continuous `f`.
4. By dominated convergence on `[0, T]`:
   `∫ t in 0..T, (1 - Re φ_n(t)) → ∫ t in 0..T, (1 - Re φ_μ(t))`.
   - Domination: `|1 - Re φ_n(t)| ≤ 2` (since `|Re φ| ≤ ‖φ‖ ≤ 1`).
   - Pointwise: `φ_n(t) → φ_μ(t)` for each `t` (hypothesis).
5. So for `n ≥ N`: `(2/T) · ∫ t in 0..T, (1 - Re φ_n(t)) < ε`.
6. By `measure_abs_gt_le_integral_charFun`: `μ_n({|x| > 2/T}) < ε` for `n ≥ N`.
7. For `n < N`: each `μ_n` is tight (single prob measure on ℝ, which is Polish). Choose compact `K_n` with `μ_n(K_nᶜ) < ε`.
8. Set `K = K_0 ∪ ... ∪ K_{N-1} ∪ [-2/T, 2/T]`. This is compact and `μ_n(Kᶜ) < ε` for all `n`.

Key mathlib lemmas:
- `isTightMeasureSet_iff_exists_isCompact_measure_compl_le` — epsilon-delta characterization
- `MeasureTheory.tendsto_integral_of_dominated_convergence` — dominated convergence for integrals
- `isCompact_Icc` — `[-M, M]` is compact in ℝ
- `Finset.isCompact_biUnion` or `IsCompact.union` — finite union of compact sets is compact
- `MeasureTheory.FiniteMeasure.innerRegular` or similar — single measure is tight on Polish space

**Step 2: Verify compilation**

Run: `lake build LeanLevy.Probability.WeakConvergence`
Expected: SUCCESS (with sorry in body)

---

## Task 5: Hard Direction + Iff (Lévy's Continuity Theorem)

**Files:**
- Modify: `LeanLevy/Probability/WeakConvergence.lean`

**Step 1: Prove the hard direction via subsequence extraction**

```lean
end Tightness

/-! ## Lévy's continuity theorem -/

/-- **Lévy's continuity theorem (hard direction).** Pointwise convergence of characteristic
functions of probability measures on ℝ implies weak convergence.

Proof: By tightness (`isTight_of_charFunTendsto`), the sequence is tight. By Prokhorov's
theorem, every subsequence has a further weakly convergent subsequence. By the easy
direction and injectivity of characteristic functions (`Measure.ext_of_charFun`), all
subsequential limits equal μ. By `tendsto_of_subseq_tendsto`, the full sequence converges. -/
theorem tendsto_of_charFunTendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : CharFunTendsto μs atTop μ) : Tendsto μs atTop (𝓝 μ) := by
  -- Use: every subsequence has a further subsequence converging to μ
  apply tendsto_of_subseq_tendsto
  intro ns hns
  -- Step 1: The subsequence μs ∘ ns also has convergent charfuns
  have hsub : CharFunTendsto (μs ∘ ns) atTop μ := fun ξ => (h ξ).comp hns
  -- Step 2: By tightness, the range is tight
  have htight := isTight_of_charFunTendsto hsub
  -- Step 3: By Prokhorov, extract a further convergent subsequence
  -- (tight ⇒ relatively compact ⇒ ∃ convergent subsequence)
  sorry
```

Proof outline for Step 3 onwards:
3. From `htight`, the closure of `{μs (ns n) : n ∈ ℕ}` is compact in `ProbabilityMeasure ℝ`.
   Use Prokhorov's theorem: `isCompact_closure_of_isTightMeasureSet` or similar.
4. Extract a convergent subsequence `ms` with limit `ν`:
   `∃ ms : ℕ → ℕ, StrictMono ms ∧ ∃ ν, Tendsto (μs ∘ ns ∘ ms) atTop (𝓝 ν)`.
   Use `IsCompact.tendsto_subseq` from compact sets in metric spaces.
5. By the easy direction: `CharFunTendsto (μs ∘ ns ∘ ms) atTop ν`.
6. But also `CharFunTendsto (μs ∘ ns ∘ ms) atTop μ` (sub-subsequence of convergent sequence).
7. By uniqueness of limits: `characteristicFun ν = characteristicFun μ` pointwise.
8. This means `charFun (ν : Measure ℝ) = charFun (μ : Measure ℝ)`.
9. By `Measure.ext_of_charFun`: `(ν : Measure ℝ) = (μ : Measure ℝ)`.
10. Lift to `ν = μ` (via `ProbabilityMeasure.ext` or `Subtype.ext`).
11. Return `⟨ms, hconv⟩`.

Key mathlib lemmas:
- `tendsto_of_subseq_tendsto` — `Mathlib.Order.Filter.AtTopBot.CountablyGenerated`
- `IsCompact.tendsto_subseq` — extract convergent subsequence from compact set
- `Measure.ext_of_charFun` — injectivity of characteristic functions
- `ProbabilityMeasure.ext` — extensionality for probability measures

**Step 2: State the iff**

```lean
/-- **Lévy's continuity theorem (biconditional).** A sequence of probability measures
on ℝ converges weakly iff their characteristic functions converge pointwise. -/
theorem tendsto_iff_charFunTendsto
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ} :
    Tendsto μs atTop (𝓝 μ) ↔ CharFunTendsto μs atTop μ :=
  ⟨charFunTendsto_of_tendsto, tendsto_of_charFunTendsto⟩
```

**Step 3: Verify compilation**

Run: `lake build LeanLevy.Probability.WeakConvergence`
Expected: SUCCESS

---

## Task 6: Random Variable Bridge + Cleanup

**Files:**
- Modify: `LeanLevy/Probability/WeakConvergence.lean`

**Step 1: Bridge to `TendstoInDistribution`**

Mathlib defines `TendstoInDistribution X l Z μ` for random variables. We connect this
to our `CharFunTendsto` by going through the induced measures (pushforward measures).

```lean
/-! ## Bridge to convergence in distribution -/

/-- The characteristic function of the law of a random variable X equals
the characteristic function of its pushforward measure. -/
theorem characteristicFun_map {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (ξ : ℝ) :
    charFun (μ.map X) ξ = ∫ ω, exp (↑(ξ * X ω) * I) ∂μ := by
  simp [charFun_apply_real]
  rw [integral_map hX.aestronglyMeasurable]
  · congr 1; ext ω; push_cast; ring
  · fun_prop

/-- **Convergence in distribution via characteristic functions.** A sequence of random
variables converges in distribution iff the characteristic functions of their laws
converge pointwise.

Note: this uses `TendstoInDistribution` from mathlib, which is defined as weak
convergence of the pushforward measures. -/
theorem tendstoInDistribution_iff_charFunTendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xs : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hXs : ∀ n, Measurable (Xs n)) (hX : Measurable X) :
    (∀ ξ : ℝ, Tendsto (fun n => ∫ ω, exp (↑(ξ * Xs n ω) * I) ∂μ) atTop
      (𝓝 (∫ ω, exp (↑(ξ * X ω) * I) ∂μ))) ↔
    TendstoInDistribution Xs atTop X μ := by
  sorry
```

Notes:
- `TendstoInDistribution` may be defined differently in mathlib — check the exact definition.
  It might use `Tendsto (fun n => μ.map (Xs n)) atTop (𝓝 (μ.map X))` or a weaker formulation.
- If `TendstoInDistribution` is defined via bounded continuous functions directly on Ω,
  the bridge is: `TendstoInDistribution ↔ weak convergence of pushforwards ↔ charfun convergence`.
- The pushforward `μ.map X` is a `Measure ℝ`, need to lift to `ProbabilityMeasure ℝ` to use
  our `tendsto_iff_charFunTendsto`. Use `⟨μ.map X, isProbabilityMeasure_map hX.aemeasurable⟩`.

**Step 2: Close the namespace and add the file to the build**

```lean
end MeasureTheory.ProbabilityMeasure
```

Verify the file is picked up by `lake build` (it should be automatic since `LeanLevy` is a `lean_lib`).

**Step 3: Verify full compilation**

Run: `lake build LeanLevy.Probability.WeakConvergence`
Expected: SUCCESS

**Step 4: Commit**

```bash
git add LeanLevy/Probability/WeakConvergence.lean
git commit -m "feat: state Lévy's continuity theorem for probability measures on ℝ"
```

---

## Dependency Graph

```
Task 1 (skeleton + CharFunTendsto)
  ↓
Task 2 (expBCF + easy direction)
  ↓
Task 3 (tail bound inequality)
  ↓
Task 4 (tightness from charfun)
  ↓
Task 5 (hard direction + iff)
  ↓
Task 6 (random variable bridge + commit)
```

All tasks are sequential — each builds on the previous.

## Sorry Budget

Target: minimize sorry usage. Expected sorry locations:
- `measure_abs_gt_le_integral_charFun` — the Fubini + sinc computation (Task 3). Attempt full proof; sorry individual sub-goals (integral computation, Fubini application) only if specific mathlib lemmas are missing.
- `isTight_of_charFunTendsto` — the dominated convergence argument (Task 4). Most of this should be provable; the "single measure is tight on Polish space" step may need sorry if the mathlib API isn't directly available.
- `tendsto_of_charFunTendsto` — the Prokhorov extraction (Task 5). The subsequence extraction from compact sets should work; sorry only if `IsCompact.tendsto_subseq` or equivalent isn't available for `ProbabilityMeasure`.
- `tendstoInDistribution_iff_charFunTendsto` — the random variable bridge (Task 6). May need sorry depending on mathlib's exact `TendstoInDistribution` API.

Each sorry should be documented with a comment explaining what's missing.
