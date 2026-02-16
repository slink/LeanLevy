# Sorry Cleanup Design

## Status

3 sorrys remain in the project:

| # | File | Theorem | Difficulty |
|---|------|---------|-----------|
| 1 | `LevyProcess.lean:268` | `charFun_eq_exp_mul` | Tractable |
| 2 | `InfiniteDivisible.lean:284` | `levyKhintchine_representation` | Very hard |
| 3 | `PoissonProcess.lean:306` | `exists_poissonProcess` | Medium |

## Part A: Close `charFun_eq_exp_mul` (implement now)

### Context

All helper lemmas are proved:
- `lk_charFun_mul` — multiplicativity
- `lk_charFun_zero` — φ(0) = 1
- `lk_charFun_rat_pow` — φ(k/n) = φ(1/n)^k
- `lk_charFun_rightCts` — right-continuity via DCT
- `lk_charFun_ne_zero` — non-vanishing via halving

The sorry is the final step: extending from rational to real times.

### Proof strategy

**Phase 1 — Branch-cut argument:** Show `φ(1/n) = exp(ψ/n)` for all positive `n`.

1. Right-continuity at 0: `φ(1/n) → φ(0) = 1` as `n → ∞`.
2. Continuity of log near 1: `log(φ(1/n)) → log(1) = 0`.
3. From `φ(1/n)^n = exp(ψ)` and `exp_log`: `exp(n * log(φ(1/n))) = exp(ψ)`.
4. By `exp_eq_exp_iff_exists_int`: `n * log(φ(1/n)) = ψ + 2πi·kₙ` for integer `kₙ`.
5. Dividing by n: `log(φ(1/n)) = ψ/n + 2πi·kₙ/n → 0`.
6. Since `ψ/n → 0`, we get `2πi·kₙ/n → 0`, forcing `kₙ = 0` for large n.
7. Therefore `φ(1/n) = exp(ψ/n)`.

**Phase 2 — Density argument:**

1. From Phase 1: `φ(k/n) = φ(1/n)^k = exp(ψ/n)^k = exp(k·ψ/n)`.
2. Both `φ` and `t ↦ exp(t·ψ)` are right-continuous on ℝ≥0.
3. They agree on `{k/n | k, n ∈ ℕ, n > 0}` which is dense in ℝ≥0.
4. Right-continuous functions agreeing on a dense subset agree everywhere.

### Key mathlib lemmas

- `Complex.exp_log` / `Complex.log_exp`
- `Complex.exp_eq_exp_iff_exists_int`
- `Complex.continuousAt_log`
- `tendsto_nhdsWithin_iff` for right-continuity

## Part B: Roadmap for `levyKhintchine_representation`

**Assessment:** This is a deep analytic theorem requiring:
- Fourier inversion for positive-definite functions
- Construction of the Lévy measure from the characteristic exponent
- Truncated integration `∫ (e^{ixξ} - 1 - ixξ·1_{|x|≤1}) dν(x)`

**Recommendation:** Leave as sorry. The statement is correct and usable as an axiom. This is a multi-month formalization project that would be better suited for a dedicated effort or mathlib contribution.

## Part C: Roadmap for `exists_poissonProcess`

**Assessment:** Medium difficulty. Mathlib v4.28.0-rc1 has:
- `Measure.infinitePi` — Kolmogorov extension for product measures
- `IsProjectiveMeasureFamily` — projective consistency
- Ionescu-Tulcea construction (`Mathlib.Probability.Kernel.IonescuTulcea`)

**Approach sketch:**
1. Define canonical path space `Ω := ℝ≥0 → ℕ`.
2. For each finite set of times `{t₁,...,tₖ}`, define the joint law of
   `(N(t₁), N(t₂)-N(t₁), ..., N(tₖ)-N(tₖ₋₁))` as a product of Poisson measures.
3. Show this family is projective.
4. Apply `infinitePi` or Ionescu-Tulcea to get a measure on `Ω`.
5. Verify the four axioms of `IsPoissonProcess`.

**Main challenges:**
- The canonical path space is `ℝ≥0 → ℕ`, not `ℕ → X`, so the Ionescu-Tulcea approach
  (which is ℕ-indexed) doesn't directly apply.
- Proving càdlàg for the canonical process requires additional work.
- Alternative: use `infinitePi` on a discretized grid, then take a limit.

**Estimated effort:** 200-400 lines, tractable as a follow-up.
