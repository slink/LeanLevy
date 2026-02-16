# Poisson Process & Lévy Process Infrastructure

**Date:** 2026-02-15
**Status:** Approved

## Goal

Define Lévy processes as a predicate, specialize to Poisson processes, prove the
characterization theorem via characteristic functions, and provide a partial
Kolmogorov construction. Target: 2-3 sorries max, all in the construction section.

## Design Decisions

- **State space:** ℕ-valued counting process `N : ℝ≥0 → Ω → ℕ`
- **Time type:** `ℝ≥0`
- **Definition style:** Predicates (`IsLevyProcess`, `IsPoissonProcess`)
- **Càdlàg:** Full definition + basic lemmas (not sorry'd)
- **Lévy first:** `IsLevyProcess` defined before `IsPoissonProcess`
- **Sorry budget:** 2-3, only in Kolmogorov construction section

## File Structure

```
LeanLevy/Processes/
├── StochasticProcess.lean   (existing — increments, independence, filtration)
├── Cadlag.lean              (NEW)
├── LevyProcess.lean         (NEW)
└── PoissonProcess.lean      (NEW)
```

Dependency chain: `StochasticProcess` ← `Cadlag` ← `LevyProcess` ← `PoissonProcess`

## File 1: Cadlag.lean

### Definitions

```
IsCadlagAt f t : Prop
  := ContinuousWithinAt f (Set.Ici t) t
   ∧ ∃ l, Filter.Tendsto f (nhdsWithin t (Set.Iio t)) (nhds l)

IsCadlag f : Prop := ∀ t, IsCadlagAt f t
```

### Lemmas (all sorry-free)

- `IsCadlag.continuousWithinAt_Ici` — extract right-continuity
- `IsCadlag.leftLim_exists` — extract left-limit existence
- `isCadlag_const` — constant functions
- `Monotone.isCadlag_nat` — monotone ℕ-valued functions are càdlàg
  (discrete topology ℕ + monotonicity → locally eventually constant from right,
  left limit = supremum exists by monotonicity)

## File 2: LevyProcess.lean

### Imports

`StochasticProcess.lean`, `Cadlag.lean`

### Definition

```
structure IsLevyProcess [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E] [Sub E] [AddGroup E] [Zero E]
    (X : ℝ≥0 → Ω → E) (μ : Measure Ω) : Prop where
  start_zero : X 0 = fun _ => 0
  indep_increments : HasIndependentIncrements X μ
  stationary_increments : HasStationaryIncrements X μ
  cadlag_ae : ∀ᵐ ω ∂μ, IsCadlag (fun t => X t ω)
```

Note: `HasStationaryIncrements` requires `[AddGroup ι]`. Since `ℝ≥0` is not an
additive group, we either:
(a) relax the existing def to `AddMonoid` + `Sub`, or
(b) define an `ℝ≥0`-specific stationarity predicate.
Decision: option (a) if the change is safe, otherwise (b).

### API Lemmas (sorry-free)

- Projections from structure fields
- `IsLevyProcess.indepFun_increment` — delegate to existing
- `IsLevyProcess.identDistrib_increment` — from stationarity

### Characteristic Exponent (sorry)

```
noncomputable def IsLevyProcess.charExponent ... : ℝ → ℂ := ...
theorem IsLevyProcess.charFun_eq_exp_mul ... :
    charFun (μ.map (X t)) ξ = cexp (↑(t : ℝ) * h.charExponent ξ) := sorry
```

This requires infinite divisibility — sorry with TODO comment.

## File 3: PoissonProcess.lean

### Imports

`LevyProcess.lean`, `Probability/Poisson.lean`

### Definition

```
structure IsPoissonProcess [MeasurableSpace Ω]
    (N : ℝ≥0 → Ω → ℕ) (λ : ℝ≥0) (μ : Measure Ω) : Prop where
  start_zero : N 0 = fun _ => 0
  indep_increments : HasIndependentIncrements (fun t ω => (N t ω : ℤ)) μ
  increment_poisson : ∀ (s h : ℝ≥0),
    μ.map (fun ω => N (s + h) ω - N s ω) = poissonMeasure (λ * h)
```

ℤ embedding for `indep_increments` because ℕ lacks `Sub` (truncated subtraction).
The `increment_poisson` statement keeps ℕ (increment is always ≥ 0 for counting process).

### Derived Lemmas (all sorry-free)

- `IsPoissonProcess.hasStationaryIncrements` — from `increment_poisson` (law depends only on `h`)
- `IsPoissonProcess.monotone` — Poisson increments are ℕ-valued hence ≥ 0
- `IsPoissonProcess.isLevyProcess` — assembles Lévy predicate; càdlàg from `Monotone.isCadlag_nat`
- `IsPoissonProcess.measurable` — each `N t` is measurable

### Bridge Lemma (sorry-free, attempt full proof)

```
theorem charFun_poissonMeasure_eq (r : ℝ≥0) (ξ : ℝ) :
    charFun (poissonMeasure r) ξ = cexp (↑(r : ℝ) * (cexp (↑ξ * I) - 1))
```

Proof strategy: unfold `charFun` as integral over counting measure on ℕ,
rewrite as `tsum`, apply `poissonCharFun_eq`.

### Characterization Theorem (sorry-free)

```
theorem IsPoissonProcess.charFun_eq (h : IsPoissonProcess N λ μ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (N t)) ξ = cexp (↑(λ * t : ℝ≥0) * (cexp (↑ξ * I) - 1))
```

Proof: rewrite `N t` as increment from 0, apply `increment_poisson`,
apply `charFun_poissonMeasure_eq`.

### Expectation & Variance (sorry-free)

- `IsPoissonProcess.expectation` — `E[N(t)] = λt`, delegate to `poissonExpectation_hasSum`
- `IsPoissonProcess.variance` — `Var[N(t)] = λt`, delegate to `poissonVariance`

### Characteristic Exponent

```
theorem IsPoissonProcess.charExponent_eq :
    charExponent = fun ξ => ↑(λ : ℝ) * (cexp (↑ξ * I) - 1)
```

(Only makes sense once `IsLevyProcess.charExponent` is defined; may defer.)

### Kolmogorov Construction (sorry section)

```
theorem poissonProcess_isProjectiveMeasureFamily (λ : ℝ≥0) :
    IsProjectiveMeasureFamily ... := sorry  -- attempt partial proof

theorem exists_poissonProcess (λ : ℝ≥0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (N : ℝ≥0 → Ω → ℕ),
      IsPoissonProcess N λ μ := sorry  -- Kolmogorov extension
```

## Sorry Summary

| Location | Statement | Reason |
|----------|-----------|--------|
| LevyProcess.lean | `charFun_eq_exp_mul` | Requires infinite divisibility |
| PoissonProcess.lean | `poissonProcess_isProjectiveMeasureFamily` | Projective consistency (attempt) |
| PoissonProcess.lean | `exists_poissonProcess` | Kolmogorov extension step |

## Downstream Roadmap

- **Compound Poisson:** `IsCompoundPoissonProcess` extends `IsLevyProcess` with jump distribution
- **Brownian motion:** Another `IsLevyProcess` specialization (Gaussian increments)
- **Lévy-Itô decomposition:** Decomposes `IsLevyProcess` into BM + drift + compound Poisson
- **Lévy-Khintchine:** Characterizes `charExponent` via the Lévy triple `(b, σ², ν)`
- **SGD/ADAM:** Uses filtration + adaptedness + martingale convergence (discrete-time, reuses the increment/independence layer)
