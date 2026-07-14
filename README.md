# LeanLevy

A Lean 4 formalization of Lévy processes, built on top of mathlib.

## What's here

**Bochner API** (`LeanLevy/Representation/BochnerGaussian.lean`)
- `covMatrix`: covariance matrix `ψ(tᵢ - tⱼ)` of a positive definite function, with `covMatrix_is_psd`
- `bochner_identity`: for continuous PD ψ with ψ(0)=1, `ψ t = ∫ exp(I·t·x) ∂μ` for the spectral measure μ (explicit-integral form of Bochner's theorem)

**Fourier analysis** (`LeanLevy/Fourier/`)
- Fourier transform of finite measures on ℝ, with boundedness, continuity, and value at zero
- Positive definite functions: definition, Schur product theorem, pointwise closure, characteristic function bridge
- Bochner's theorem, proved via Gaussian smoothing, Prokhorov compactness, and Lévy continuity

**Characteristic functions** (`LeanLevy/Probability/Characteristic.lean`)
- Characteristic function of probability measures
- Bochner positive semi-definiteness
- Multiplicativity under convolution

**Poisson distribution** (`LeanLevy/Probability/Poisson.lean`)
- Expectation, variance, second factorial moment
- Characteristic function: `φ(ξ) = exp(r(exp(iξ) − 1))`

**Lévy's continuity theorem** (`LeanLevy/Probability/WeakConvergence.lean`)
- Weak convergence of probability measures is equivalent to pointwise convergence of characteristic functions
- Tightness from convergence of characteristic functions

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
- Existence and uniqueness of the projective limit measure on Polish spaces
- σ-additivity of the cylinder content via inner regularity and Tychonoff compactness

**Poisson process** (`LeanLevy/Processes/PoissonProcess.lean`)
- Defined as a counting process with independent, Poisson-distributed increments
- Constructed via the Kolmogorov extension theorem from its finite-dimensional distributions, whose projective consistency comes down to the convolution identity for Poisson laws
- Is a Lévy process

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

**Lévy–Khintchine theorem** (`LeanLevy/Levy/LevyKhintchine.lean`, `LevyKhintchineProof.lean`, `LevyKhintchineUniqueness.lean`)
- `LevyKhintchineTriple`: a drift, a Gaussian variance, and a Lévy measure, whose `exponent` is the Lévy–Khintchine formula `ψ_T(ξ) = ibξ − σ²ξ²/2 + ∫ (e^{ixξ} − 1 − ixξ·1_{|x|<1}) dν`
- `levyKhintchine_representation`: every infinitely divisible probability measure on ℝ has characteristic function `exp(ψ_T)` for some triple. The Lévy measure is only required to be σ-finite with `∫ min(1,x²) dν < ∞`, so infinite-activity cases such as α-stable laws are covered (their infinite divisibility is not itself formalized here)
- The proof extracts Khintchine's canonical measure by a single Prokhorov argument applied to the `min(1,x²)`-tilted scaled measures, untilts it into the Lévy measure, and obtains the whole triple along one subsequence. The limit is identified at a split radius `r ∈ (1/2, 1]` chosen so that `ν` has no atom on the sphere; the resulting variance `σ² = lim t⁻¹∫_{|x|<r} x² dμ_t − ∫_{|x|<r} x² dν` keeps the small-jump second moment from being counted both in `σ²` and in the compensated integral
- `levyKhintchine_converse`: conversely, every triple is realised by an infinitely divisible law — `ψ_T` is continuous, vanishes at `0`, is Hermitian and conditionally negative definite, so Schoenberg's theorem and Bochner's theorem produce a convolution semigroup whose time-`1` member has characteristic function `exp(ψ_T)`
- `LevyKhintchineTriple.ext_of_exponent_eq`: the triple is determined by its exponent, via Sato's smearing argument — `ψ_T(ξ) − ½∫_{[-1,1]} ψ_T(ξ+u) du` is the characteristic function of a finite measure with a `σ²/6` atom at the origin and density `1 − sinc` against `ν`, from which `σ²`, `ν`, and then the drift are recovered
- `isInfinitelyDivisible_iff_exists_levyKhintchineTriple` and `existsUnique_levyKhintchineTriple`: a probability measure on ℝ is infinitely divisible iff its characteristic function is `exp(ψ_T)` for a triple `T`, and that triple is unique (equal exponentials force equal exponents by a continuous-logarithm argument on the connected line)

**Compound Poisson process** (`LeanLevy/Processes/CompoundPoisson.lean`, `CompoundPoissonLaw.lean`)
- **Construction**: `exists_isCompoundPoissonDriver` — for any rate `r > 0` and jump law `ν'`, a driver `(τ, Y)` of i.i.d. exponential interarrival times and i.i.d. `ν'`-marks, jointly independent, on a canonical product space
- **Sample paths**: `compoundPoisson_ae_isCadlag` — the path `t ↦ b·t + ∑_{n ≤ N(t)} Yₙ` is almost surely càdlàg
- **Pathwise Itô formula**: `compoundPoisson_pathwise_ito` — for a `C¹` function `f`, a purely *pathwise* change-of-variables identity `f(Xₜ) − f(X₀) = ∫₀ᵗ f'(Xₛ)·b ds + ∑ jump terms`, valid for these finite-activity paths with no stochastic integral (the drift part is an ordinary Riemann integral, the jumps a finite sum)
- **Jump-count law**: `map_jumpCount_arrival` — the number of jumps by time `t` is Poisson with mean `r·t`, obtained from the Gamma law of the arrival times and telescoping survival probabilities
- **Characteristic function**: `charFun_map_compoundPoisson` — the marginal at time `t` has characteristic function `exp(t·(i b ξ + r·(charFun ν' ξ − 1)))`, by conditioning on the Poisson jump count and summing the generating series
- **Lévy–Khintchine realization**: `compoundPoissonTriple` is the triple `(b + ∫_{|x|<1} x d(r·ν'), 0, r·ν')`; `charFun_map_compoundPoisson_eq_exponent` shows the marginal's characteristic function is `exp(t·ψ_T)` for this triple, so compound Poisson processes realize exactly the finite-activity, zero-Gaussian Lévy–Khintchine triples, and `isInfinitelyDivisible_map_compoundPoisson` records that every marginal is infinitely divisible (via the converse Lévy–Khintchine theorem)

**Poisson random measures** (`LeanLevy/RandomMeasure/PoissonPointFamily.lean`, `PoissonRandomMeasure.lean`, `PoissonCompensated.lean`, `TimeSpacePoisson.lean`, `PoissonFiltration.lean`, `PoissonMartingale.lean`)

For a σ-finite intensity measure `m` on a measurable space, the random measure is constructed, rather than axiomatized.
- **Point family**: `prmPiece`, `prmPieceLaw` partition the space into disjoint finite-mass pieces and normalize `m` on each; `IsPoissonPointFamily` bundles a family of piece counts and points, and `exists_isPoissonPointFamily` builds it in one shot with the counts and all points jointly independent, each count Poisson-distributed with the piece mass and each point drawn from the normalized piece law
- **Per-piece identities**: `integral_pieceSum` is Campbell's formula for a piece (`E[∑ g(Xₙ)] = ∫ g dm`), `integral_sq_pieceSum` its second moment, and `integral_pieceProd_eq_exp` the piece probability-generating-function identity `E[∏ w(Xₙ)] = exp(m(piece)·(∫ w dm̂ − 1))`
- **Thinning**: `thinnedCount` counts the points of a piece landing in a set; `map_thinnedCount` shows this count is Poisson with mean `m(piece ∩ A)`, `indepFun_thinnedCount_thinnedCount` gives independence of the counts on two disjoint sets, and `iIndepFun_thinnedCount` gives mutual independence of the counts over a finite pairwise-disjoint family (with `integral_prod_pow_thinnedCount` and `charFunDual_pi_thinnedCount` the joint probability-generating and characteristic functions that factor across the pieces)
- **The random measure**: `poissonRandomMeasure` is a genuine `Measure`-valued random object, a countable sum of Dirac masses at the realized points, with `poissonRandomMeasure_apply` its evaluation and `measurable_poissonRandomMeasure_apply` measurability; `map_poissonRandomMeasure_apply` is the superposition law — the count `N(A)` on a finite-mass set is Poisson with mean `m A` — `indepFun_poissonRandomMeasure_apply` gives independence of the evaluations on two disjoint finite-mass sets, and `iIndepFun_poissonRandomMeasure_apply` gives mutual independence of the evaluations over a finite pairwise-disjoint family of finite-mass sets
- **Compensated integral**: `compensatedPoissonSum` is the centered sum `∑ f(Xₙ) − ∫ f dm`; `integral_compensatedPoissonSum` shows it has mean zero and `integral_sq_compensatedPoissonSum` is Campbell's second formula, the L² isometry `E[Ñ(f)²] = ∫ f² dm` on `L¹ ∩ L²`, with `memLp_two_compensatedPoissonSum` recording square-integrability; `compensatedPoissonIntegral : Lp ℝ 2 m → Lp ℝ 2 μ` extends the map to all of `L²(m)` by density, `eLpNorm_compensatedPoissonIntegral` being the isometry on the whole space, `compensatedPoissonIntegral_eq_sum` its agreement with the explicit sum on `L¹ ∩ L²`, and `integral_compensatedPoissonIntegral` its mean-zero property on all of `L²`
- **Time-indexed random measure**: specializing to the mark space `ℝ × E` under the product intensity `volume.prod m` reads `ℝ` as time; `poissonTimeCount` is the running count of realized marks in `(0, t] × A`, `map_poissonRandomMeasure_band` is the band law (the count in `(s, t] × A` is Poisson with mean `(t − s) · m A`), `map_poissonTimeCount` its running-count specialization, `poissonTimeCount_add` its pathwise additivity over consecutive windows, and `iIndepFun_poissonRandomMeasure_bands` the independent-increments statement — counts over consecutive disjoint time bands are mutually independent
- **Lévy specialization**: with mark space `ℝ` and intensity `volume.prod ν` for a Lévy measure `ν`, `memLp_two_smallJumpFun` shows the small-jump test function `1_{(0,t] × (−1,1)}(s, x) · x` is square-integrable, so `levyCompensatedSmallJump` is a genuine `L²(μ)` element at each time `t`; `integral_levyCompensatedSmallJump` gives it mean zero and `eLpNorm_sq_levyCompensatedSmallJump` its second moment `t · ∫_{(−1,1)} x² dν`, while `map_levyLargeJumpCount` shows the number of large jumps up to time `t` is Poisson with mean `t · ν{|x| ≥ 1}`
- **Evaluation σ-algebras and filtration**: `prmEvalSigma K X m R` is the σ-algebra generated by the finite-mass evaluations of the random measure inside a region `R ⊆ E`, and `indep_prmEvalSigma` records that the random measure is independently scattered — the evaluation σ-algebras of two disjoint regions are independent — resting on `indepFun_poissonRandomMeasure_families`, the independence of two finite families of finite-mass evaluation sets whose disjointness is required only across the families — each set of the first disjoint from each set of the second, with no disjointness needed within a family; reading `ℝ` as time, `prmFiltration` is the natural filtration whose value at time `t` is the evaluation σ-algebra of the prefix region `(−∞, t] × E` (`prmFiltration_apply`)
- **Martingales**: for the natural filtration `prmFiltration` over `ℝ≥0`, `martingale_centeredPoissonTimeCount` shows the centered running count `(poissonTimeCount K X A t).toReal − t · (m A).toReal` of a measurable finite-mass set `A` is a martingale, and `martingale_levyCompensatedSmallJump` shows the compensated small-jump process of a Lévy measure is a martingale — stated for `levyCompensatedSmallJumpVersion`, the `prmFiltration`-adapted representative that `levyCompensatedSmallJumpVersion_ae_eq` places almost everywhere equal to the `L²` element `levyCompensatedSmallJump` at each time; the martingale property is the conditional-expectation form of the independent-increment law and does not assert càdlàg paths, path regularity, or a process-level stochastic integral

The codebase is sorry-free. `#print axioms` on the main results — the Lévy–Khintchine representation, converse, uniqueness, and characterization, the compound Poisson pathwise Itô formula and law identification, and the Poisson random measure superposition law, mutual independence over a finite disjoint family, compensated second-moment isometry and its L² extension, the time-indexed independent increments, the Lévy small-jump isometry and large-jump count law, the independent scattering of the evaluation σ-algebras, and the centered-count and compensated small-jump martingales — reports only `propext`, `Classical.choice`, and `Quot.sound`.

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
├── RandomMeasure/
│   ├── PoissonCompensated.lean
│   ├── PoissonPointFamily.lean
│   ├── PoissonRandomMeasure.lean
│   └── TimeSpacePoisson.lean
├── Representation/
│   └── BochnerGaussian.lean
└── Levy/
    ├── CharacteristicExponent.lean
    ├── CompensatedIntegral.lean
    ├── InfiniteDivisible.lean
    ├── LevyKhintchine.lean
    ├── LevyKhintchineProof.lean
    ├── LevyKhintchineUniqueness.lean
    └── LevyMeasure.lean
```
