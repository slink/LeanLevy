# LeanLevy

A Lean 4 formalization of Lévy processes, built on top of mathlib.

## What's here

**Bochner–Gaussian process construction** (`LeanLevy/Representation/BochnerGaussian.lean`)
- Positive semidefinite kernels: `IsPositiveSemidefiniteKernel`, shift kernel `K ψ s t := ψ(s-t)`
- `kernel_from_pd`: a positive definite function induces a PSD kernel
- `gaussianFDD`: Gaussian finite-dimensional distributions (product of i.i.d. N(0,1))
- `gaussianFDD_consistent`: FDD family is consistent under coordinate projection
- `covMatrix`: covariance matrix `ψ(tᵢ - tⱼ)` with `covMatrix_is_psd`
- `gaussianProjectiveFamily` + `gaussian_process_from_pd`: Kolmogorov extension yields a path measure on `ℝ → ℝ`
- `bochner_identity`: for continuous PD ψ with ψ(0)=1, `ψ t = ∫ exp(I·t·x) ∂μ` for the spectral measure μ

**Fourier analysis** (`LeanLevy/Fourier/`)
- Fourier transform of finite measures on ℝ, with boundedness, continuity, and value at zero
- Positive definite functions: definition, Schur product theorem, pointwise closure, characteristic function bridge
- Bochner's theorem: main proof via Gaussian smoothing + Prokhorov + Lévy continuity

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

**Finite-dimensional distributions** (`LeanLevy/Processes/FiniteDimensional.lean`)
- Joint law at finitely many times as a pushforward measure
- Marginalization: restricting to a subset of times recovers the sub-distribution
- Projective consistency (`IsProjectiveMeasureFamily`)

**Projective families** (`LeanLevy/Processes/ProjectiveFamily.lean`)
- Bundled structure: measure family + consistency + probability
- Projection and composition lemmas (functoriality)
- Constructor from stochastic processes

**Càdlàg paths** (`LeanLevy/Processes/Cadlag.lean`)
- Right-continuity with left limits
- Monotone ℕ-valued functions are càdlàg when right-continuous

**Lévy processes** (`LeanLevy/Processes/LevyProcess.lean`)
- Definition: independent increments, stationary increments, càdlàg paths, starts at zero
- Characteristic exponent and supporting lemmas (multiplicativity, non-vanishing, right-continuity)

**Kolmogorov extension theorem** (`LeanLevy/Processes/Kolmogorov.lean`)
- Full proof of existence and uniqueness of the projective limit measure on Polish spaces
- σ-additivity of cylinder content via inner regularity and Tychonoff compactness

**Poisson process** (`LeanLevy/Processes/PoissonProcess.lean`)
- Definition as a counting process with independent Poisson-distributed increments
- Existence via Kolmogorov extension, fully proved (zero sorry)
- Poisson FDD projectivity fully proved (single-step erase via Poisson convolution)
- Shown to be a Lévy process

**Characteristic exponent** (`LeanLevy/Levy/CharacteristicExponent.lean`)
- Local log construction (branch-cut safe) and local-global exponent agreement
- Semigroup API: multiplicativity, power formulas, complex power law `φ_t(ξ) = φ₁(ξ)^t`
- Ceiling-sequence density lemma: right-continuous + continuous functions agreeing on ℕ/ℕ rationals are equal
- Lévy exponential formula `F(t,ξ) = exp(tΨ(ξ))` with full continuity in `t`

**Infinite divisibility** (`LeanLevy/Levy/InfiniteDivisible.lean`)
- Iterated convolution, with characteristic function formula
- Poisson distribution is infinitely divisible
- Lévy process marginals are infinitely divisible

**Lévy measures** (`LeanLevy/Levy/LevyMeasure.lean`)
- `IsLevyMeasure` predicate: `ν({0}) = 0` and `∫ min(1, x²) dν < ∞`
- Finite mass on `{x | ε ≤ |x|}`, σ-finiteness

**Compensated integrand** (`LeanLevy/Levy/CompensatedIntegral.lean`)
- `levyCompensatedIntegrand ξ x = exp(ixξ) − 1 − ixξ·1_{|x|<1}`
- Pointwise norm bound, measurability, Bochner integrability under a Lévy measure

**Lévy–Khintchine representation** (`LeanLevy/Levy/LevyKhintchine.lean`, `LevyKhintchineProof.lean`)
- `LevyKhintchineTriple` structure: drift, Gaussian variance, Lévy measure
- Statement of the representation theorem
- Sub-lemmas 1–3 fully proved: non-vanishing, continuous logarithm, conditional negative definiteness
- Schoenberg helper lemmas, convolution semigroup structure
- Sub-lemma 4: Schoenberg's theorem proved via kernel factorization + spectral decomposition; convolution semigroup construction complete
- Measure differentiation at `t = 0` remains for extracting the Lévy-Khintchine triple

## Incomplete

Six sorry keywords remain across six private declarations in two files:

**`LeanLevy/Fourier/Bochner.lean`** (5 sorries, all private helpers feeding into `bochner`):
- **`re_nonneg_double_integral`** — The PD quadratic form `∫∫ ψ(s-t) e^{-ix(s-t)} ds dt` has non-negative real part. Requires a Riemann-sum argument approximating `∑ᵢ ∑ⱼ c̄ᵢ cⱼ ψ(sᵢ-sⱼ) ≥ 0`.
- **`fejerApproximant_eq_double_integral`** — The Fejér integral equals `(1/N)` times the double integral over `[0,N]²`. Requires change of variables `u = s-t` and Fubini.
- **`fourierTransform_rescaled_eq`** — Convention bridge: `𝓕(ψ(2π·))(y) = ↑(ρ(y))`. Change of variables + Hermitian symmetry.
- **`integrable_inverseFourierDensity`** — The inverse Fourier density `ρ ∈ L¹`. Follows from `ρ ≥ 0` + Gaussian regularization.
- **`charFun_inverseFourierDensity`** — Inner product convention bridge in the Fourier inversion identity.

**`LeanLevy/Levy/LevyKhintchineProof.lean`** (1 sorry):
- **`levyKhintchine_of_cnd`** — Extracting the Lévy-Khintchine triple `(b, σ², ν)` from the convolution semigroup by differentiating at `t = 0`.

## Building

Requires Lean 4 (v4.29.0-rc3) and mathlib.

```
lake build
```

## Structure

```
LeanLevy/
├── Basic.lean
├── Fourier/
│   ├── Bochner.lean
│   ├── MeasureFourier.lean
│   └── PositiveDefinite.lean
├── Probability/
│   ├── Characteristic.lean
│   ├── Poisson.lean
│   └── WeakConvergence.lean
├── Processes/
│   ├── Cadlag.lean
│   ├── FiniteDimensional.lean
│   ├── ProjectiveFamily.lean
│   ├── Kolmogorov.lean
│   ├── LevyProcess.lean
│   ├── PoissonProcess.lean
│   └── StochasticProcess.lean
├── Representation/
│   └── BochnerGaussian.lean
└── Levy/
    ├── CharacteristicExponent.lean
    ├── CompensatedIntegral.lean
    ├── InfiniteDivisible.lean
    ├── LevyKhintchine.lean
    ├── LevyKhintchineProof.lean
    └── LevyMeasure.lean
```
