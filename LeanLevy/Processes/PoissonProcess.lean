/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.LevyProcess
import LeanLevy.Probability.Poisson
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.CharacteristicFunction
import LeanLevy.Processes.Kolmogorov

/-!
# Poisson Process

This file defines the Poisson process as a structure predicate and derives key properties:

* `ProbabilityTheory.IsPoissonProcess` — a counting process `N : ℝ≥0 → Ω → ℕ` is a Poisson
  process with rate `r` if it starts at zero, has independent increments (via ℤ embedding),
  each increment `N(s+h) - N(s)` has Poisson(r·h) distribution, and a.e. sample path is càdlàg.

* `ProbabilityTheory.IsPoissonProcess.hasStationaryIncrements` — stationary increments follow
  from the Poisson increment assumption.

* `ProbabilityTheory.IsPoissonProcess.isLevyProcess` — a Poisson process (ℤ-embedded) is a
  Lévy process.

* `ProbabilityTheory.charFun_poissonMeasure_eq` — the characteristic function of
  `(poissonMeasure r).map Nat.cast` equals `exp(r(e^{iξ} − 1))`.

* `ProbabilityTheory.IsPoissonProcess.charFun_eq` — the characteristic function of the
  time-`t` marginal `N(t)` equals `exp(r·t(e^{iξ} − 1))`.

* `ProbabilityTheory.exists_poissonProcess` — existence (sorry'd, requires Kolmogorov
  extension).

## Implementation notes

The independent increments condition uses the ℤ-valued embedding `fun t ω => (N t ω : ℤ)`
because `HasIndependentIncrements` requires `[Sub E]` and ℕ subtraction is truncated.
The `increment_poisson` field uses ℕ subtraction directly since increments of a counting
process are non-negative.
-/

open scoped ENNReal NNReal Nat
open MeasureTheory Real Complex Finset ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Poisson process definition -/

/-- A counting process `N : ℝ≥0 → Ω → ℕ` is a **Poisson process** with rate `rate` if:
1. It starts at zero: `N 0 = 0`.
2. Its ℤ-valued embedding has independent increments.
3. Each increment `N(s+h) - N(s)` has Poisson(`rate * h`) distribution.
4. Almost every sample path (ℤ-embedded) is càdlàg. -/
structure IsPoissonProcess (N : ℝ≥0 → Ω → ℕ) (rate : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- The process starts at zero. -/
  start_zero : N 0 = fun _ => 0
  /-- The ℤ-embedded increments are independent. -/
  indep_increments : HasIndependentIncrements (fun t ω => (N t ω : ℤ)) μ
  /-- Each increment has Poisson distribution. -/
  increment_poisson : ∀ (s h : ℝ≥0),
    μ.map (fun ω => N (s + h) ω - N s ω) = poissonMeasure (rate * h)
  /-- Almost every sample path is càdlàg (right-continuous with left limits). -/
  cadlag_paths : ∀ᵐ ω ∂μ, IsCadlag (fun t => (N t ω : ℤ))

/-! ## Derived lemmas -/

namespace IsPoissonProcess

variable {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}

/-- The ℤ-valued increments of a Poisson process are stationary.

**Strategy:** Both `increment (fun t ω => (N t ω : ℤ)) s (s+h)` and
`increment (fun t ω => (N t ω : ℤ)) 0 h` push forward to
`(poissonMeasure (rate * h)).map Nat.cast` when composed with the natural ℤ → ℤ identity,
since the ℕ increment maps to the same ℤ value. We show the two pushforward measures
agree using `increment_poisson`. -/
theorem hasStationaryIncrements (h : IsPoissonProcess N rate μ) :
    HasStationaryIncrements (fun t ω => (N t ω : ℤ)) μ := by
  intro s k
  -- Notation: Xℤ t ω = (N t ω : ℤ)
  set Xℤ : ℝ≥0 → Ω → ℤ := fun t ω => (N t ω : ℤ) with hXℤ_def
  -- Derive IsProbabilityMeasure μ from increment_poisson
  have hprob : IsProbabilityMeasure μ := by
    have hmapeq : μ.map (fun ω => N (0 + 0) ω - N 0 ω) = poissonMeasure (rate * 0) :=
      h.increment_poisson 0 0
    haveI : IsProbabilityMeasure (μ.map (fun ω => N (0 + 0) ω - N 0 ω)) := hmapeq ▸ inferInstance
    exact Measure.isProbabilityMeasure_of_map (fun ω => N (0 + 0) ω - N 0 ω)
  -- Int.cast : ℤ → ℝ is a MeasurableEmbedding (injective + discrete σ-algebra)
  have hmembed : MeasurableEmbedding (Int.cast : ℤ → ℝ) :=
    ⟨Int.cast_injective, measurable_from_top,
      fun {t} _ => (t.to_countable.image _).measurableSet⟩
  -- N t is AEMeasurable for any t (from increment_poisson giving a probability measure)
  have haem_N : ∀ t : ℝ≥0, AEMeasurable (N t) μ := by
    intro t
    apply AEMeasurable.of_map_ne_zero
    rw [show N t = fun ω => N (0 + t) ω - N 0 ω from by
      ext ω; simp [congr_fun h.start_zero ω]]
    rw [h.increment_poisson 0 t]
    exact IsProbabilityMeasure.ne_zero _
  -- ℝ-valued abbreviations
  set Ns : Ω → ℝ := fun ω => (N s ω : ℝ)
  set Nsk : Ω → ℝ := fun ω => (N (s + k) ω : ℝ)
  set Nk : Ω → ℝ := fun ω => (N k ω : ℝ)
  set diffR : Ω → ℝ := Nsk - Ns
  -- AEMeasurability for ℝ-valued functions
  have haem_Ns : AEMeasurable Ns μ :=
    (measurable_from_top (α := ℕ)).comp_aemeasurable (haem_N s)
  have haem_Nsk : AEMeasurable Nsk μ :=
    (measurable_from_top (α := ℕ)).comp_aemeasurable (haem_N (s + k))
  have haem_Nk : AEMeasurable Nk μ :=
    (measurable_from_top (α := ℕ)).comp_aemeasurable (haem_N k)
  have haem_diffR : AEMeasurable diffR μ := haem_Nsk.sub haem_Ns
  -- AEMeasurability for ℤ-valued increments
  have haem_Xℤ : ∀ t : ℝ≥0, AEMeasurable (Xℤ t) μ := fun t =>
    (measurable_from_top (α := ℕ)).comp_aemeasurable (haem_N t)
  have haem_incr_sk : AEMeasurable (increment Xℤ s (s + k)) μ :=
    (haem_Xℤ (s + k)).sub (haem_Xℤ s)
  have haem_incr_0k : AEMeasurable (increment Xℤ 0 k) μ :=
    (haem_Xℤ k).sub (haem_Xℤ 0)
  -- Step 1: Independence of (Xℤ s) and (increment Xℤ s (s+k)), then compose to ℝ
  have hindep_ℤ : IndepFun (Xℤ s) (increment Xℤ s (s + k)) μ := by
    have h0 : increment Xℤ 0 s = Xℤ s := by
      ext ω; simp [increment_apply, hXℤ_def, congr_fun h.start_zero ω]
    rw [← h0]
    exact h.indep_increments.indepFun_increment (zero_le s) le_self_add
  have hNs_eq : Ns = (Int.cast : ℤ → ℝ) ∘ Xℤ s := by ext ω; simp [Ns, hXℤ_def]
  have hdiffR_eq : diffR = (Int.cast : ℤ → ℝ) ∘ increment Xℤ s (s + k) := by
    ext ω; simp [diffR, Nsk, Ns, increment_apply, hXℤ_def]
  have hindep_ℝ : IndepFun Ns diffR μ := by
    rw [hNs_eq, hdiffR_eq]
    exact hindep_ℤ.comp hmembed.measurable hmembed.measurable
  -- Step 2: Nsk = Ns + diffR
  have hdecomp : Nsk = Ns + diffR := by ext ω; simp [Nsk, Ns, diffR, Pi.add_apply, Pi.sub_apply]
  -- Step 3: CharFun factorization via independence
  have hcf_prod : charFun (μ.map Nsk) = charFun (μ.map Ns) * charFun (μ.map diffR) := by
    rw [hdecomp]; exact hindep_ℝ.charFun_map_add_eq_mul haem_Ns haem_diffR
  -- Step 4: Compute charFun of Nt (inlined from charFun_eq / map_natCast_eq)
  -- First prove the charFun formula for the Poisson measure pushed to ℝ
  have hcf_poisson : ∀ (r : ℝ≥0) (ξ : ℝ),
      charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) ξ =
      cexp (↑(r : ℝ) * (cexp (↑ξ * I) - 1)) := by
    intro r ξ
    rw [charFun_apply_real]
    rw [integral_map (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable
      (by fun_prop : Continuous (fun x : ℝ => cexp (↑ξ * ↑x * I))).aestronglyMeasurable]
    change ∫ n, cexp (↑ξ * ↑(n : ℝ) * I) ∂(poissonPMF r).toMeasure = _
    have hint : Integrable (fun n : ℕ => cexp (↑ξ * ↑(n : ℝ) * I)) (poissonPMF r).toMeasure := by
      apply (integrable_const (1 : ℝ)).mono'
      · exact (by fun_prop : Continuous (fun n : ℕ => cexp (↑ξ * ↑(n : ℝ) * I))).measurable.aestronglyMeasurable
      · filter_upwards with n
        rw [show (↑ξ : ℂ) * ↑(n : ℝ) * I = ↑(ξ * ↑n) * I from by push_cast; ring,
          norm_exp_ofReal_mul_I]
    rw [PMF.integral_eq_tsum _ _ hint]
    simp_rw [poissonPMF_toReal, RCLike.real_smul_eq_coe_mul]
    convert poissonCharFun_eq r ξ using 1
    unfold poissonCharFun
    congr 1; ext n; exact mul_comm _ _
  -- Now prove charFun of N t marginal
  have hcf_Nt : ∀ t : ℝ≥0, ∀ ξ : ℝ,
      charFun (μ.map (fun ω => (N t ω : ℝ))) ξ =
      cexp (↑(rate * t : ℝ≥0) * (cexp (↑ξ * I) - 1)) := by
    intro t ξ
    have hfun : (fun ω => (N t ω : ℝ)) =
        (Nat.cast : ℕ → ℝ) ∘ (fun ω => N (0 + t) ω - N 0 ω) := by
      ext ω
      simp only [zero_add, Function.comp_apply, Nat.cast_inj]
      have : N 0 ω = 0 := congr_fun h.start_zero ω
      omega
    have hae : AEMeasurable (fun ω => N (0 + t) ω - N 0 ω) μ :=
      AEMeasurable.of_map_ne_zero (by
        rw [h.increment_poisson 0 t]; exact IsProbabilityMeasure.ne_zero _)
    rw [hfun, ← AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable hae,
      h.increment_poisson 0 t]
    exact hcf_poisson (rate * t) ξ
  -- Step 5: Show charFun of diffR equals charFun of Nk
  have hcf_diff_eq : charFun (μ.map diffR) = charFun (μ.map Nk) := by
    ext ξ
    have hprod := congr_fun hcf_prod ξ
    rw [Pi.mul_apply, hcf_Nt (s + k) ξ, hcf_Nt s ξ] at hprod
    have hne : cexp (↑(rate * s : ℝ≥0) * (cexp (↑ξ * I) - 1)) ≠ 0 := Complex.exp_ne_zero _
    have hsolve : charFun (μ.map diffR) ξ =
        cexp (↑(rate * k : ℝ≥0) * (cexp (↑ξ * I) - 1)) := by
      have hmul : cexp (↑↑(rate * s) * (cexp (↑ξ * I) - 1)) * charFun (μ.map diffR) ξ =
          cexp (↑↑(rate * s) * (cexp (↑ξ * I) - 1)) *
            cexp (↑↑(rate * k) * (cexp (↑ξ * I) - 1)) := by
        rw [← hprod, ← Complex.exp_add]; congr 1; push_cast; ring
      exact mul_left_cancel₀ hne hmul
    rw [hsolve]
    exact (hcf_Nt k ξ).symm
  -- Step 6: Conclude ℝ-valued measures are equal
  haveI : IsFiniteMeasure (μ.map diffR) := inferInstance
  haveI : IsFiniteMeasure (μ.map Nk) := inferInstance
  have hmap_R : μ.map diffR = μ.map Nk := Measure.ext_of_charFun hcf_diff_eq
  -- Step 7: Lift to ℤ-valued measures
  -- diffR = Int.cast ∘ (increment Xℤ s (s+k)) and Nk = Int.cast ∘ (increment Xℤ 0 k)
  have hNk_eq : Nk = (Int.cast : ℤ → ℝ) ∘ increment Xℤ 0 k := by
    ext ω; simp [Nk, increment_apply, hXℤ_def, congr_fun h.start_zero ω]
  -- Rewrite hmap_R in terms of composed maps
  have hmap_composed : (μ.map (increment Xℤ s (s + k))).map (Int.cast : ℤ → ℝ) =
      (μ.map (increment Xℤ 0 k)).map (Int.cast : ℤ → ℝ) := by
    rw [AEMeasurable.map_map_of_aemeasurable hmembed.measurable.aemeasurable haem_incr_sk,
      AEMeasurable.map_map_of_aemeasurable hmembed.measurable.aemeasurable haem_incr_0k]
    show μ.map ((Int.cast : ℤ → ℝ) ∘ increment Xℤ s (s + k)) =
         μ.map ((Int.cast : ℤ → ℝ) ∘ increment Xℤ 0 k)
    rw [← hdiffR_eq, ← hNk_eq]
    exact hmap_R
  -- Apply MeasurableEmbedding.map_injective to lift to ℤ
  have hmap_Z : μ.map (increment Xℤ s (s + k)) = μ.map (increment Xℤ 0 k) :=
    hmembed.map_injective hmap_composed
  -- Wrap in IdentDistrib
  exact ⟨haem_incr_sk, haem_incr_0k, hmap_Z⟩

/-- A Poisson process (ℤ-embedded) is a Lévy process. -/
theorem isLevyProcess (h : IsPoissonProcess N rate μ) :
    IsLevyProcess (fun t ω => (N t ω : ℤ)) μ where
  start_zero := by
    ext ω
    show (N 0 ω : ℤ) = 0
    rw [show N 0 ω = (fun _ => 0) ω from congr_fun h.start_zero ω]
    simp
  indep_increments := h.indep_increments
  stationary_increments := h.hasStationaryIncrements
  cadlag_ae := h.cadlag_paths

end IsPoissonProcess

/-! ## Characteristic function of the Poisson measure -/

/-- The characteristic function of the Poisson measure pushed forward to ℝ equals
`exp(r(e^{iξ} − 1))`.

**Proof:**
1. Unfold `charFun` via `charFun_apply_real`.
2. Pull through `Measure.map` via `integral_map`.
3. Unfold `poissonMeasure` as `(poissonPMF r).toMeasure`.
4. Apply `PMF.integral_eq_tsum`.
5. Rewrite `smul` to multiplication.
6. Match with `poissonCharFun` and apply `poissonCharFun_eq`. -/
theorem charFun_poissonMeasure_eq (r : ℝ≥0) (ξ : ℝ) :
    charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) ξ =
    cexp (↑(r : ℝ) * (cexp (↑ξ * I) - 1)) := by
  -- Step 1: Unfold charFun to integral
  rw [charFun_apply_real]
  -- Step 2: Pull integral through Measure.map
  rw [integral_map (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable
    (by fun_prop : Continuous (fun x : ℝ => cexp (↑ξ * ↑x * I))).aestronglyMeasurable]
  -- Step 3: Unfold poissonMeasure as PMF.toMeasure
  change ∫ n, cexp (↑ξ * ↑(n : ℝ) * I) ∂(poissonPMF r).toMeasure = _
  -- Step 4: Apply PMF.integral_eq_tsum
  have hint : Integrable (fun n : ℕ => cexp (↑ξ * ↑(n : ℝ) * I)) (poissonPMF r).toMeasure := by
    apply (integrable_const (1 : ℝ)).mono'
    · exact (by fun_prop : Continuous (fun n : ℕ => cexp (↑ξ * ↑(n : ℝ) * I))).measurable.aestronglyMeasurable
    · filter_upwards with n
      rw [show (↑ξ : ℂ) * ↑(n : ℝ) * I = ↑(ξ * ↑n) * I from by push_cast; ring,
        norm_exp_ofReal_mul_I]
  rw [PMF.integral_eq_tsum _ _ hint]
  -- Step 5: Rewrite smul to mul and match poissonCharFun
  simp_rw [poissonPMF_toReal, RCLike.real_smul_eq_coe_mul]
  -- Now: ∑' n, ↑(poissonPMFReal r n) * cexp (↑ξ * ↑(n : ℝ) * I) = ...
  -- Match poissonCharFun (which has the factors in opposite order) via commutativity
  convert poissonCharFun_eq r ξ using 1
  unfold poissonCharFun
  congr 1; ext n; exact mul_comm _ _

/-- The pushforward measure of `N t` (as ℝ) equals `(poissonMeasure (rate * t)).map Nat.cast`. -/
private theorem IsPoissonProcess.map_natCast_eq {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}
    (h : IsPoissonProcess N rate μ) (t : ℝ≥0) :
    μ.map (fun ω => (N t ω : ℝ)) = (poissonMeasure (rate * t)).map (Nat.cast : ℕ → ℝ) := by
  have hfun : (fun ω => (N t ω : ℝ)) =
      (Nat.cast : ℕ → ℝ) ∘ (fun ω => N (0 + t) ω - N 0 ω) := by
    ext ω
    simp only [zero_add, Function.comp_apply, Nat.cast_inj]
    have : N 0 ω = 0 := congr_fun h.start_zero ω
    omega
  rw [hfun]
  have hae : AEMeasurable (fun ω => N (0 + t) ω - N 0 ω) μ :=
    AEMeasurable.of_map_ne_zero (by
      rw [h.increment_poisson 0 t]
      exact IsProbabilityMeasure.ne_zero _)
  rw [← AEMeasurable.map_map_of_aemeasurable
    (by fun_prop : Measurable (Nat.cast : ℕ → ℝ)).aemeasurable hae,
    h.increment_poisson 0 t]

/-- The characteristic function of the time-`t` marginal of a Poisson process equals
`exp(rate · t · (e^{iξ} − 1))`. -/
theorem IsPoissonProcess.charFun_eq {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}
    (h : IsPoissonProcess N rate μ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (fun ω => (N t ω : ℝ))) ξ =
    cexp (↑(rate * t : ℝ≥0) * (cexp (↑ξ * I) - 1)) := by
  rw [h.map_natCast_eq t]
  exact charFun_poissonMeasure_eq (rate * t) ξ

/-! ## Poisson process projective family -/

/-- The finite-dimensional distribution of a Poisson process with rate `rate`
at times `I : Finset ℝ≥0`. For sorted times `t₁ ≤ ⋯ ≤ tₙ`, this is the
pushforward of the product `⨂ₖ poissonMeasure(rate * Δtₖ)` under the
cumulative-sum map from increments to values.

**Dependencies for filling this sorry:**
- `Measure.pi` for the product of independent Poisson measures
- `Finset.sort` to order the times
- A measurable cumulative-sum transformation -/
noncomputable def poissonProcessFDD (rate : ℝ≥0) (I : Finset ℝ≥0) :
    Measure (∀ j : I, ℕ) :=
  sorry

/-- The Poisson FDDs form a projective family: marginalizing from `I` to `J ⊆ I`
recovers the FDD at `J`. Follows from the Poisson convolution property
`Poisson(a) * Poisson(b) = Poisson(a + b)` for independent variables, which lets
us merge adjacent increments when dropping times.

**Dependencies:** `poissonProcessFDD` definition, Poisson convolution. -/
theorem isProjectiveMeasureFamily_poissonProcessFDD (rate : ℝ≥0) :
    IsProjectiveMeasureFamily (α := fun (_ : ℝ≥0) => ℕ) (poissonProcessFDD rate) :=
  sorry

/-- Each Poisson FDD is a probability measure (product of probability measures
pushed forward by a measurable map).

**Dependencies:** `poissonProcessFDD` definition, `isProbabilityMeasure_poissonMeasure`. -/
instance isProbabilityMeasure_poissonProcessFDD (rate : ℝ≥0) (I : Finset ℝ≥0) :
    IsProbabilityMeasure (poissonProcessFDD rate I) :=
  sorry

/-- `ℕ` is a Polish space (closed embedding into `ℝ`, which is Polish). -/
instance : PolishSpace ℕ := Nat.isClosedEmbedding_coe_real.polishSpace

/-- The projective family for a Poisson process with rate `rate`.
Input to `ProjectiveFamily.kolmogorovExtension`. -/
noncomputable def poissonProjectiveFamily (rate : ℝ≥0) :
    ProjectiveFamily ℝ≥0 (fun _ : ℝ≥0 => ℕ) where
  measure := poissonProcessFDD rate
  consistent := isProjectiveMeasureFamily_poissonProcessFDD rate
  prob := isProbabilityMeasure_poissonProcessFDD rate

/-! ## Existence -/

/-- There exists a probability space supporting a Poisson process with any rate.

**Construction:**
- Path space: `Ω := ∀ (_ : ℝ≥0), ℕ`
- Process: `N t ω := if t = 0 then 0 else ω t` (the `if` gives pointwise `N 0 = 0`)
- Measure: `(poissonProjectiveFamily rate).kolmogorovExtension`

**Dependency graph:**
```
poissonProcessFDD ──→ isProjectiveMeasureFamily_poissonProcessFDD
                  ──→ isProbabilityMeasure_poissonProcessFDD
                         │
                         v
                  poissonProjectiveFamily
                         │
                         v
                  kolmogorovExtension
                         │
                         v
              ┌──────────┼──────────┬────────────┐
              v          v          v            v
          start_zero  indep_incr  incr_poisson  cadlag
          (proved!)   (sorry)     (sorry)       (sorry)
```
-/
theorem exists_poissonProcess (rate : ℝ≥0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (N : ℝ≥0 → Ω → ℕ),
      IsPoissonProcess N rate μ := by
  -- Canonical path space with Kolmogorov extension measure
  refine ⟨∀ _ : ℝ≥0, ℕ, inferInstance,
    (poissonProjectiveFamily rate).kolmogorovExtension,
    fun t ω => if t = 0 then 0 else ω t, ?_⟩
  exact {
    start_zero := by ext ω; simp
    indep_increments := by
      sorry
      -- Independent increments of `fun t ω => ((if t = 0 then 0 else ω t : ℕ) : ℤ)`.
      -- Follows from the product structure of poissonProcessFDD and
      -- kolmogorovExtension_apply_cylinder recovering the FDD on cylinder sets.
      -- Dependencies: poissonProcessFDD, kolmogorovExtension_apply_cylinder.
    increment_poisson := by
      sorry
      -- `μ.map (fun ω => N(s+h) ω - N s ω) = poissonMeasure (rate * h)`.
      -- Factor through the projection to {s, s+h}: by kolmogorovExtension_apply_cylinder,
      -- the marginal at {s, s+h} equals poissonProcessFDD rate {s, s+h}, whose
      -- increment marginal is Poisson(rate * h) by construction.
      -- Dependencies: poissonProcessFDD, kolmogorovExtension_apply_cylinder.
    cadlag_paths := by
      sorry
      -- A.e. càdlàg paths for `fun t => ((if t = 0 then 0 else ω t : ℕ) : ℤ)`.
      -- Hardest field. Strategy:
      -- 1. Show a.s. paths are non-decreasing (ℕ-valued increments are non-negative).
      -- 2. Show a.s. right-continuity: P(Poisson(rate·h) ≥ 1) → 0 as h → 0.
      -- 3. Left limits exist by monotonicity + ℤ-valued.
      -- Dependencies: increment_poisson, Poisson tail bounds.
  }

end ProbabilityTheory
