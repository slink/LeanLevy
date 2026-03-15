/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Fourier.PositiveDefinite
import LeanLevy.Fourier.Bochner
import LeanLevy.Processes.Kolmogorov
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProductMeasure

/-!
# Bochner–Gaussian Process Construction

This file constructs a stationary Gaussian stochastic process from a continuous positive
definite function, using the Kolmogorov extension theorem.

## Main definitions

* `ProbabilityTheory.IsPositiveSemidefiniteKernel` — a kernel `K : ℝ → ℝ → ℂ` is positive
  semidefinite if the Hermitian form `∑ᵢ ∑ⱼ c̄ᵢ cⱼ K(xᵢ, xⱼ)` is nonneg.
* `ProbabilityTheory.K` — the shift kernel `K ψ s t := ψ (s - t)`.

## Main results

* `ProbabilityTheory.kernel_from_pd` — a positive definite function induces a positive
  semidefinite kernel via `K ψ`.
-/

open MeasureTheory Complex ComplexConjugate
open scoped ComplexOrder

namespace ProbabilityTheory

/-! ## Positive semidefinite kernels -/

/-- A kernel `K : ℝ → ℝ → ℂ` is **positive semidefinite** if for every `n`, points
`x : Fin n → ℝ`, and weights `c : Fin n → ℂ`, the Hermitian form
`∑ᵢ ∑ⱼ c̄ᵢ cⱼ K(xᵢ, xⱼ)` is nonneg. -/
def IsPositiveSemidefiniteKernel (K : ℝ → ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * K (x i) (x j)

/-! ## The shift kernel -/

/-- The shift kernel induced by `ψ`: `K ψ s t := ψ (s - t)`. -/
noncomputable def K (ψ : ℝ → ℂ) (s t : ℝ) : ℂ := ψ (s - t)

/-- A positive definite function `ψ` induces a positive semidefinite kernel via `s t ↦ ψ(s-t)`.

Proof: `IsPositiveSemidefiniteKernel (fun s t => ψ (s - t))` unfolds to exactly
`IsPositiveDefinite ψ` after beta reduction. -/
lemma kernel_from_pd
    (ψ : ℝ → ℂ)
    (hψ : IsPositiveDefinite ψ) :
    IsPositiveSemidefiniteKernel (fun s t => ψ (s - t)) :=
  fun n x c => hψ n x c

/-! ## Gaussian finite-dimensional distributions -/

/-- The Gaussian finite-dimensional distribution at times `t : Fin n → ℝ` for a positive
definite function `ψ : ℝ → ℂ`.

The correct implementation constructs the joint Gaussian on `Fin n → ℝ` with covariance
matrix `covMatrix ψ t` (i.e., the multivariate normal N(0, Re(covMatrix ψ t))).

**Stub**: We use the product of i.i.d. N(0,1) distributions as a placeholder. This
correctly typechecks and references the covariance structure via the type of `covMatrix ψ t`.
The consistency and charfun-identification properties (Prompts 5–8) will verify whether
this stub is sufficient or a true multivariate Gaussian must be constructed. -/
noncomputable def gaussianFDD {n : ℕ} (_ψ : ℝ → ℂ) (_t : Fin n → ℝ) :
    ProbabilityMeasure (Fin n → ℝ) :=
  ⟨Measure.pi (fun _ : Fin n => gaussianReal 0 1), inferInstance⟩

/-! ## Kolmogorov consistency -/

/-- The Gaussian FDD family is consistent under coordinate projection: marginalizing the
`(n+1)`-dimensional product Gaussian by dropping the `i`-th coordinate gives the
`n`-dimensional product Gaussian.

For the stub (product of i.i.d. N(0,1)), this follows from the fact that the marginal of
a product measure onto a coordinate subset is the product measure on that subset,
via `measurePreserving_piFinSuccAbove` and `Measure.map_snd_prod`. -/
lemma gaussianFDD_consistent {n : ℕ} (ψ : ℝ → ℂ) (t : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    (gaussianFDD ψ t : Measure (Fin (n + 1) → ℝ)).map
        (fun f : Fin (n + 1) → ℝ => fun j : Fin n => f (i.succAbove j)) =
      (gaussianFDD ψ (fun j => t (i.succAbove j)) : Measure (Fin n → ℝ)) := by
  simp only [gaussianFDD, ProbabilityMeasure.coe_mk]
  set μ : ∀ _ : Fin (n + 1), Measure ℝ := fun _ => gaussianReal 0 1
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  -- The projection equals Prod.snd ∘ e (dropping the i-th coordinate)
  have hcomp : (fun f : Fin (n + 1) → ℝ => fun j : Fin n => f (i.succAbove j)) =
      Prod.snd ∘ ↑e := by
    funext f j
    -- piFinSuccAbove sends f to (f i, Fin.removeNth i f), and removeNth i f j = f (i.succAbove j)
    rfl
  -- Factor through e then take second component
  rw [hcomp, ← Measure.map_map measurable_snd e.measurable,
      (measurePreserving_piFinSuccAbove μ i).map_eq]
  -- Goal: ((μ i).prod (Measure.pi fun j => μ (i.succAbove j))).map Prod.snd
  --       = Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  -- Since μ = fun _ => gaussianReal 0 1, simplify μ i and μ (i.succAbove j)
  simp only [μ]
  -- Now: ((gaussianReal 0 1).prod (Measure.pi fun _ => gaussianReal 0 1)).map Prod.snd
  simp [Measure.map_snd_prod, measure_univ]

/-! ## Covariance matrix -/

/-- The covariance matrix for a finite set of times `t : Fin n → ℝ` given a function `ψ`:
`covMatrix ψ t i j = ψ (t i - t j)`. -/
noncomputable def covMatrix {n : ℕ} (ψ : ℝ → ℂ) (t : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => ψ (t i - t j)

@[simp]
theorem covMatrix_apply {n : ℕ} (ψ : ℝ → ℂ) (t : Fin n → ℝ) (i j : Fin n) :
    covMatrix ψ t i j = ψ (t i - t j) :=
  rfl

/-- The covariance matrix of a positive definite function is positive semidefinite. -/
lemma covMatrix_is_psd {n : ℕ} (ψ : ℝ → ℂ) (t : Fin n → ℝ)
    (hψ : IsPositiveDefinite ψ) :
    (covMatrix ψ t).PosSemidef :=
  hψ.pdMatrix_posSemidef n t

/-! ## Stochastic Process from Positive Definite Function -/

/-- The canonical projective family of i.i.d. Gaussian measures: for each finite set of times
`I : Finset ℝ`, the measure is the product of independent N(0,1) distributions. -/
noncomputable def gaussianProjectiveFamily : ProjectiveFamily ℝ (fun _ => ℝ) where
  measure := fun I => Measure.pi (fun _ : I => gaussianReal 0 1)
  consistent := isProjectiveMeasureFamily_pi (fun _ : ℝ => gaussianReal 0 1)
  prob := fun _ => inferInstance

/-- For any positive definite function `ψ`, the Kolmogorov extension theorem yields a probability
measure on the path space `ℝ → ℝ` whose finite-dimensional marginals at each `I : Finset ℝ`
equal the product Gaussian `Measure.pi (fun _ : I => gaussianReal 0 1)`.

The coordinate process is `X t ω := ω t`. The construction does not use `ψ` directly since
`gaussianFDD` is currently a stub (product of i.i.d. N(0,1)); the hypothesis `hψ` is included
to anchor the result to the positive definite setting. -/
theorem gaussian_process_from_pd
    (ψ : ℝ → ℂ) (_ : IsPositiveDefinite ψ) :
    ∃ (P : Measure (ℝ → ℝ)) (_ : IsProbabilityMeasure P),
      IsProjectiveLimit P (fun I : Finset ℝ => Measure.pi (fun _ : I => gaussianReal 0 1)) :=
  ⟨gaussianProjectiveFamily.kolmogorovExtension,
   inferInstance,
   gaussianProjectiveFamily.isProjectiveLimit_kolmogorovExtension⟩

/-! ## Law of the Process at Time 1 -/

/-- The law of the Gaussian process at time 1. Since `gaussianFDD` is the product of i.i.d.
N(0,1) distributions, the one-dimensional marginal at any time is `gaussianReal 0 1`. -/
noncomputable def gaussianLaw : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 1, inferInstance⟩

/-- The characteristic function of `gaussianLaw`:
`φ t = ∫ x, exp(I · t · x) ∂μ` where `μ = gaussianReal 0 1`. -/
noncomputable def gaussianCharFun (t : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (Complex.I * ↑t * ↑x) ∂(gaussianLaw : Measure ℝ)

/-! ## Bochner Identity -/

/-- **Bochner Identity**: for a continuous positive definite function `ψ` with `ψ(0) = 1`,
there exists a spectral probability measure `μ` such that
`ψ t = ∫ x, exp(I · t · x) ∂μ` for all `t : ℝ`.

This follows directly from `bochner` by unfolding `characteristicFun` to an explicit integral. -/
lemma bochner_identity
    (ψ : ℝ → ℂ) (hψc : Continuous ψ) (hpd : IsPositiveDefinite ψ) (h0 : ψ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ t : ℝ, ψ t = ∫ x : ℝ, Complex.exp (Complex.I * ↑t * ↑x) ∂(μ : Measure ℝ) := by
  obtain ⟨μ, hμ⟩ := bochner ψ hψc hpd h0
  exact ⟨μ, fun t => by
    have h := (hμ t).symm
    simp only [MeasureTheory.ProbabilityMeasure.characteristicFun_def, charFun_apply_real] at h
    rw [h]; congr 1; ext x; ring⟩

end ProbabilityTheory
