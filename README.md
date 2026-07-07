# LeanLevy

A Lean 4 formalization of Lévy processes, built on top of mathlib.

## What's here

**Bochner API** (`LeanLevy/Representation/BochnerGaussian.lean`)
- `covMatrix`: covariance matrix `ψ(tᵢ - tⱼ)` of a positive definite function, with `covMatrix_is_psd`
- `bochner_identity`: for continuous PD ψ with ψ(0)=1, `ψ t = ∫ exp(I·t·x) ∂μ` for the spectral measure μ (explicit-integral form of Bochner's theorem)

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

**Lévy–Khintchine representation** (`LeanLevy/Levy/LevyKhintchine.lean`, `LevyKhintchineProof.lean`, `LevyKhintchineUniqueness.lean`)
- `LevyKhintchineTriple` structure: drift, Gaussian variance, Lévy measure
- Statement of the representation theorem
- Sub-lemmas 1–3 fully proved: non-vanishing, continuous logarithm, conditional negative definiteness
- Schoenberg helper lemmas, convolution semigroup structure
- Sub-lemma 4: Schoenberg's theorem proved via kernel factorization + spectral decomposition; convolution semigroup construction complete
- **General representation theorem**: `levyKhintchine_representation` holds for every infinitely divisible probability measure on ℝ, with `ν` an arbitrary Lévy measure (σ-finite, `∫ min(1,x²) dν < ∞`) — no finite-activity or finite-mass hypothesis. This covers infinite-activity cases such as α-stable laws (whose infinite divisibility is not itself formalized here)
- **Proof route (canonical-measure extraction)**: the `min(1,x²)`-tilted scaled measures `tiltedScaledMeasure t` are uniformly bounded and tight with no hypothesis on `μ_t` (`tiltedScaledMeasure_mass_eventually_le`, `tiltedScaledMeasure_largeSet_le`); a single Prokhorov call extracts Khintchine's canonical measure (`exists_canonicalMeasure`), which is untilted into a σ-finite Lévy measure `ν` (`exists_levyMeasure`). The triple `(b, σ², ν)` is then extracted jointly along a single subsequence (`exists_drift_variance_jumpMeasure_along_seq`) and identified at an atom-free split radius (`psi_eq_levyKhintchine_formula`, `psi_decomposition`)
- Analytic limit identification (`psi_eq_levyKhintchine_formula`) fully proved: it identifies `t⁻¹(charFun μ_t − 1) → Ψ(ξ)` by chaining four subsequential limits — the drift term, the small-jump compensated limit (3rd-order Taylor remainder + δ-truncation), and the complex large-jump limit (smooth-cutoff approximation) — against `charFun_scaled_limit` via uniqueness of limits
- The formula is stated at an **extracted atom-free split radius** `r ∈ (1/2, 1]`: the Gaussian variance is `σ² = lim t⁻¹∫_{|x|<r} x² dμ_t − ∫_{|x|<r} x² dν` (subtracting the small-jump second moment that the compensated integral already carries) and the drift is recovered at the ν level as `b + ∫_{r≤|x|<1} x dν`. This normalization is what makes the formula correct — a naive radius-1 statement double-counts the small-jump second moment
- **Converse**: `levyKhintchine_converse` — every Lévy–Khintchine triple `T = (b, σ², ν)` is realised by an infinitely divisible probability measure whose characteristic function is `exp(ψ_T)`, where `ψ_T = LevyKhintchineTriple.exponent T` is fed (continuous, `0`-vanishing, conditionally negative definite, Hermitian) to the Schoenberg + Bochner machinery
- **Uniqueness of the triple**: `LevyKhintchineTriple.ext_of_exponent_eq` — a triple is determined by its exponent. Via Sato's smearing route: the smeared exponent `g(ξ) = ψ_T(ξ) − ½∫_{[-1,1]} ψ_T(ξ+u) du` is the characteristic function of a finite **smeared measure** `smearedMeasure σ² ν` (`smeared_exponent_eq_charFun`) carrying a `σ²/6` atom at `0` and density `1 − sinc` against `ν`; inverting the smearing (`smearedMeasure_inj`) recovers `σ²` and `ν`, and the drift is read off at `ξ = 1`
- **Characterization**: `isInfinitelyDivisible_iff_exists_levyKhintchineTriple` — a probability measure on ℝ is infinitely divisible **iff** its characteristic function is `exp(ψ_T)` for some Lévy–Khintchine triple `T` (backward direction via `Measure.ext_of_charFun`). `existsUnique_levyKhintchineTriple` upgrades this to a *unique* triple, identifying exponents from equal exponentials by a continuous-log argument on the connected line

**Compound Poisson process** (`LeanLevy/Processes/CompoundPoisson.lean`, `CompoundPoissonLaw.lean`)
- **Construction**: `exists_isCompoundPoissonDriver` — for any rate `r > 0` and jump law `ν'`, a driver `(τ, Y)` of i.i.d. exponential interarrival times and i.i.d. `ν'`-marks, jointly independent, on a canonical product space
- **Sample paths**: `compoundPoisson_ae_isCadlag` — the path `t ↦ b·t + ∑_{n ≤ N(t)} Yₙ` is almost surely càdlàg
- **Pathwise Itô formula**: `compoundPoisson_pathwise_ito` — for a `C¹` function `f`, a purely *pathwise* change-of-variables identity `f(Xₜ) − f(X₀) = ∫₀ᵗ f'(Xₛ)·b ds + ∑ jump terms`, valid for these finite-activity paths with no stochastic integral (the drift part is an ordinary Riemann integral, the jumps a finite sum)
- **Jump-count law**: `map_jumpCount_arrival` — the number of jumps by time `t` is Poisson with mean `r·t`, obtained from the Gamma law of the arrival times and telescoping survival probabilities
- **Characteristic function**: `charFun_map_compoundPoisson` — the marginal at time `t` has characteristic function `exp(t·(i b ξ + r·(charFun ν' ξ − 1)))`, by conditioning on the Poisson jump count and summing the generating series
- **Lévy–Khintchine realization**: `compoundPoissonTriple` is the triple `(b + ∫_{|x|<1} x d(r·ν'), 0, r·ν')`; `charFun_map_compoundPoisson_eq_exponent` shows the marginal's characteristic function is `exp(t·ψ_T)` for this triple, so compound Poisson processes realize exactly the finite-activity, zero-Gaussian Lévy–Khintchine triples, and `isInfinitelyDivisible_map_compoundPoisson` records that every marginal is infinitely divisible (via the converse Lévy–Khintchine theorem)

The entire codebase is **sorry-free** (verified by `#print axioms`: the representation theorem, the converse, the `isInfinitelyDivisible_iff_exists_levyKhintchineTriple` / `existsUnique_levyKhintchineTriple` characterization, and the compound Poisson `compoundPoisson_pathwise_ito` / `charFun_map_compoundPoisson_eq_exponent` / `isInfinitelyDivisible_map_compoundPoisson` results depend only on `propext`, `Classical.choice`, `Quot.sound`).

## Building

Requires Lean 4 (v4.29.0-rc3) and mathlib.

```
lake build
```

## Structure

```
LeanLevy/
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
│   ├── CompoundPoisson.lean
│   ├── CompoundPoissonLaw.lean
│   ├── FiniteDimensional.lean
│   ├── ProjectiveFamily.lean
│   ├── Kolmogorov.lean
│   ├── LevyProcess.lean
│   ├── PiecewisePath.lean
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
