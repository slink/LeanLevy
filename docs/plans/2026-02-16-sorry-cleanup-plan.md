# Sorry Cleanup Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Close the `sorry` in `charFun_eq_exp_mul` (LevyProcess.lean:268) and document roadmap for remaining sorrys.

**Architecture:** Replace the sorry with a two-phase proof: (1) branch-cut argument showing `φ(1/n) = exp(ψ/n)` using `Complex.exp_eq_exp_iff_exists_int` and continuity of log, (2) density argument extending from rationals to all reals via right-continuity and `Nat.ceil`.

**Tech Stack:** Lean 4, mathlib4 v4.28.0-rc1

---

### Task 1: Implement the branch-cut + density proof

**Files:**
- Modify: `LeanLevy/Processes/LevyProcess.lean:268` (replace `sorry`)

**Step 1: Replace the sorry with the full proof**

Replace the `sorry` at line 268 with a proof in two phases:

**Phase 1 — Branch-cut:** Show `φ(1/n) = exp(ψ/n)` for positive n.
- Right-continuity at 0 (`lk_charFun_rightCts h hX 0 ξ`) + `lk_charFun_zero` gives `φ(1/n) → 1`
- `continuousAt_clog one_mem_slitPlane` gives `log(φ(1/n)) → log(1) = 0`
- `hφ_root` gives `(φ(1/n))^n = φ(1) = exp(ψ)`, so `exp(n * log(φ(1/n))) = exp(ψ)`
- `Complex.exp_eq_exp_iff_exists_int` gives integer `k_n` with `n * log(φ(1/n)) = ψ + 2πik_n`
- Size estimate: `log(φ(1/n)) → 0` and `ψ/n → 0` forces `k_n = 0` eventually
- For the finitely many small n, use a direct argument or show k_n is locally constant
- Conclude: `φ(1/n) = exp(ψ/n)` for all positive n

**Phase 2 — Density:** Extend from `{k/n}` to all `t : ℝ≥0`.
- For any `t`, define `s_m := (⌈(t : ℝ) * m⌉₊ : ℕ) / m` for `m ≥ 1`
- `s_m ≥ t` and `s_m → t` from above
- `φ(s_m) = exp(s_m * ψ)` (rational case)
- Right-continuity: `φ(s_m) → φ(t)`, continuity: `exp(s_m * ψ) → exp(t * ψ)`
- `tendsto_nhds_unique` gives `φ(t) = exp(t * ψ)`

Key mathlib lemmas:
- `Complex.exp_log`, `Complex.log_one`, `Complex.continuousAt_clog`
- `Complex.exp_eq_exp_iff_exists_int`
- `Complex.one_mem_slitPlane`, `Complex.slitPlane_ne_zero`
- `Nat.le_ceil` (for `⌈x⌉₊ ≥ x`)
- `tendsto_nhds_unique`

**Step 2: Build and verify**

Run: `lake build LeanLevy.Processes.LevyProcess`
Expected: Success with no sorry warnings

**Step 3: Commit**

```bash
git add LeanLevy/Processes/LevyProcess.lean
git commit -m "feat: close charFun_eq_exp_mul sorry via branch-cut argument"
```

### Task 2: Update sglink.md with roadmap notes

**Files:**
- Modify: `sglink.md`

Add a section documenting the remaining 2 sorrys and their roadmaps per the design doc.
