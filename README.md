# LeanLevy

A Lean 4 formalization of Lévy processes, built on top of mathlib.

## What's here

**Fourier analysis** (`LeanLevy/Fourier/`)
- Fourier transform of finite measures on ℝ, with boundedness and continuity

**Characteristic functions** (`LeanLevy/Probability/Characteristic.lean`)
- Characteristic function of probability measures
- Bochner positive semi-definiteness
- Multiplicativity under convolution

**Poisson distribution** (`LeanLevy/Probability/Poisson.lean`)
- Expectation, variance, second factorial moment
- Characteristic function: `φ(ξ) = exp(r(exp(iξ) − 1))`

**Lévy's continuity theorem** (`LeanLevy/Probability/WeakConvergence.lean`)
- Both directions fully proved: weak convergence ⟺ pointwise convergence of characteristic functions
- Tightness from characteristic function convergence

**Stochastic processes** (`LeanLevy/Processes/StochasticProcess.lean`)
- Independent and stationary increments
- Increment independence from the natural filtration

**Càdlàg paths** (`LeanLevy/Processes/Cadlag.lean`)
- Right-continuity with left limits
- Monotone ℕ-valued functions are càdlàg when right-continuous

**Lévy processes** (`LeanLevy/Processes/LevyProcess.lean`)
- Definition: independent increments, stationary increments, càdlàg paths, starts at zero
- Characteristic exponent and supporting lemmas (multiplicativity, non-vanishing, right-continuity)

**Poisson process** (`LeanLevy/Processes/PoissonProcess.lean`)
- Definition as a counting process with independent Poisson-distributed increments
- Shown to be a Lévy process

**Infinite divisibility** (`LeanLevy/Levy/InfiniteDivisible.lean`)
- Iterated convolution, with characteristic function formula
- Poisson distribution is infinitely divisible
- Lévy process marginals are infinitely divisible

## Incomplete

Three results remain sorry'd:

- **`charFun_eq_exp_mul`** — The exponential formula `φ_{X_t}(ξ) = exp(tΨ(ξ))` is proved for rational times but extending to all reals requires a branch-cut argument for complex logarithms that isn't closed yet.
- **`exists_poissonProcess`** — Existence of a Poisson process. Needs the Kolmogorov extension theorem, which isn't in mathlib yet.
- **`levyKhintchine_representation`** — The full Lévy–Khintchine representation theorem. Not yet attempted.

## Building

Requires Lean 4 (v4.28.0-rc1) and mathlib.

```
lake build
```

## Structure

```
LeanLevy/
├── Basic.lean
├── Fourier/
│   └── MeasureFourier.lean
├── Probability/
│   ├── Characteristic.lean
│   ├── Poisson.lean
│   └── WeakConvergence.lean
├── Processes/
│   ├── Cadlag.lean
│   ├── LevyProcess.lean
│   ├── PoissonProcess.lean
│   └── StochasticProcess.lean
└── Levy/
    └── InfiniteDivisible.lean
```
