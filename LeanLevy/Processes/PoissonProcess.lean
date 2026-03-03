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

* `ProbabilityTheory.exists_poissonProcess` — existence via Kolmogorov extension.

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
3. Each increment `N(s+h) - N(s)` has Poisson(`rate * h`) distribution. -/
structure IsPoissonProcess (N : ℝ≥0 → Ω → ℕ) (rate : ℝ≥0) (μ : Measure Ω) : Prop where
  /-- The process starts at zero. -/
  start_zero : N 0 = fun _ => 0
  /-- The ℤ-embedded increments are independent. -/
  indep_increments : HasIndependentIncrements (fun t ω => (N t ω : ℤ)) μ
  /-- Each increment has Poisson distribution. -/
  increment_poisson : ∀ (s h : ℝ≥0),
    μ.map (fun ω => N (s + h) ω - N s ω) = poissonMeasure (rate * h)

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
    simp only [poissonPMF_toReal]
    convert poissonCharFun_eq r ξ using 1
    unfold poissonCharFun
    congr 1; ext n; erw [Algebra.smul_def]; exact mul_comm _ _
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

/-- A Poisson process (ℤ-embedded) with càdlàg paths is a Lévy process. -/
theorem isLevyProcess (h : IsPoissonProcess N rate μ)
    (hcadlag : ∀ᵐ ω ∂μ, IsCadlag (fun t => (N t ω : ℤ))) :
    IsLevyProcess (fun t ω => (N t ω : ℤ)) μ where
  start_zero := by
    ext ω
    show (N 0 ω : ℤ) = 0
    rw [show N 0 ω = (fun _ => 0) ω from congr_fun h.start_zero ω]
    simp
  indep_increments := h.indep_increments
  stationary_increments := h.hasStationaryIncrements
  cadlag_ae := hcadlag

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
  simp only [poissonPMF_toReal]
  -- Now: ∑' n, poissonPMFReal r n • cexp (↑ξ * ↑(n : ℝ) * I) = ...
  -- Match poissonCharFun (which has the factors in opposite order) via commutativity
  convert poissonCharFun_eq r ξ using 1
  unfold poissonCharFun
  congr 1; ext n; erw [Algebra.smul_def]; exact mul_comm _ _

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

/-! ## Poisson convolution on ℕ -/

set_option maxHeartbeats 800000 in
/-- Poisson convolution at the ℕ level: pushing forward the product
`poissonMeasure(a) ⊗ poissonMeasure(b)` through addition gives `poissonMeasure(a + b)`.
Derived from the ℝ-level characteristic function identity via Nat.cast injectivity. -/
private theorem poissonMeasure_add_conv (a b : ℝ≥0) :
    ((poissonMeasure a).prod (poissonMeasure b)).map (fun p : ℕ × ℕ => p.1 + p.2) =
    poissonMeasure (a + b) := by
  -- Nat.cast : ℕ → ℝ is a measurable embedding
  have hembed : MeasurableEmbedding (Nat.cast : ℕ → ℝ) :=
    ⟨Nat.cast_injective, measurable_from_top,
      fun {t} _ => (t.to_countable.image _).measurableSet⟩
  -- The ℝ-level convolution: Poisson(a).map cast ∗ Poisson(b).map cast = Poisson(a+b).map cast
  have hR : (poissonMeasure a).map (Nat.cast : ℕ → ℝ) ∗
      (poissonMeasure b).map (Nat.cast : ℕ → ℝ) =
      (poissonMeasure (a + b)).map (Nat.cast : ℕ → ℝ) := by
    apply Measure.ext_of_charFun; funext ξ
    rw [charFun_conv, charFun_poissonMeasure_eq, charFun_poissonMeasure_eq,
      charFun_poissonMeasure_eq, NNReal.coe_add, Complex.ofReal_add, add_mul]
    exact (Complex.exp_add _ _).symm
  -- Key: map Nat.cast of our LHS = convolution on ℝ
  have h_cast_lhs :
      (((poissonMeasure a).prod (poissonMeasure b)).map (fun p : ℕ × ℕ => p.1 + p.2)).map
        (Nat.cast : ℕ → ℝ) =
      (poissonMeasure a).map (Nat.cast : ℕ → ℝ) ∗
      (poissonMeasure b).map (Nat.cast : ℕ → ℝ) := by
    -- Convolution μ ∗ ν = (μ.prod ν).map (+)
    -- LHS = ((prod pa pb).map (+ℕ)).map cast = (prod pa pb).map (cast ∘ +ℕ)
    --     = (prod pa pb).map (+ℝ ∘ Prod.map cast cast)
    --     = ((prod pa pb).map (Prod.map cast cast)).map (+ℝ)
    --     = ((pa.map cast).prod (pb.map cast)).map (+ℝ)
    --     = pa.map cast ∗ pb.map cast
    rw [Measure.map_map hembed.measurable Measurable.of_discrete]
    show ((poissonMeasure a).prod (poissonMeasure b)).map
      ((Nat.cast : ℕ → ℝ) ∘ fun p : ℕ × ℕ => p.1 + p.2) = _
    have hcomp : (Nat.cast : ℕ → ℝ) ∘ (fun p : ℕ × ℕ => p.1 + p.2) =
        (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (Nat.cast : ℕ → ℝ) (Nat.cast : ℕ → ℝ) := by
      ext ⟨x, y⟩; simp [Prod.map]
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
        ← Measure.map_prod_map _ _ hembed.measurable hembed.measurable]
    rfl
  -- Combine: map cast of LHS = conv = map cast of RHS
  exact hembed.map_injective (h_cast_lhs.trans hR)

/-- Singleton-level Poisson convolution: the convolution sum at a single point. -/
private theorem poissonMeasure_conv_singleton (a b : ℝ≥0) (m : ℕ) :
    (∑' n : ℕ, if n ≤ m then poissonMeasure a {n} * poissonMeasure b {m - n} else 0) =
    poissonMeasure (a + b) {m} := by
  have hpc := poissonMeasure_add_conv a b
  -- hpc : (prod).map add = poissonMeasure(a+b)
  -- Evaluate both sides at {m}
  have hpc' : ((poissonMeasure a).prod (poissonMeasure b)).map
      (fun p : ℕ × ℕ => p.1 + p.2) {m} = poissonMeasure (a + b) {m} := by rw [hpc]
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton m)] at hpc'
  rw [← hpc']
  -- LHS of hpc: (prod).{(i,j) | i + j = m}
  -- Express preimage as disjoint union of singletons {(n, m-n)}
  have hfib : (fun p : ℕ × ℕ => p.1 + p.2) ⁻¹' {m} =
      ⋃ n : ℕ, if n ≤ m then {⟨n, m - n⟩} else ∅ := by
    ext ⟨a', b'⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
    constructor
    · intro hab; exact ⟨a', by rw [if_pos (by omega)]; ext <;> simp <;> omega⟩
    · rintro ⟨n, hn⟩
      by_cases hle : n ≤ m
      · rw [if_pos hle] at hn; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hn; omega
      · rw [if_neg hle] at hn; exact absurd hn (by simp)
  rw [hfib, measure_iUnion₀
    (by intro i j hij; simp only [Function.onFun, AEDisjoint]
        by_cases hi : i ≤ m
        · by_cases hj : j ≤ m
          · rw [if_pos hi, if_pos hj]
            exact (Set.disjoint_singleton.mpr (fun h => hij (Prod.mk.inj h).1)).aedisjoint
          · rw [if_neg hj]; simp
        · rw [if_neg hi]; simp)
    (by intro n; by_cases hn : n ≤ m
        · rw [if_pos hn]; exact (measurableSet_singleton _).nullMeasurableSet
        · rw [if_neg hn]; exact MeasurableSet.empty.nullMeasurableSet)]
  congr 1; ext n
  by_cases hn : n ≤ m
  · rw [if_pos hn, if_pos hn,
      show ({⟨n, m - n⟩} : Set (ℕ × ℕ)) = {n} ×ˢ {m - n} from (Set.singleton_prod_singleton).symm,
      Measure.prod_prod]
  · rw [if_neg hn, if_neg hn, measure_empty]

/-! ## Poisson process projective family -/

/-- The time gap (increment) at position `k` in the sorted enumeration of `I`.
For `k = 0` this is `t₀ - 0`; for `k > 0` this is `tₖ - tₖ₋₁`. -/
noncomputable def poissonProcessGap (I : Finset ℝ≥0) (k : Fin I.card) : ℝ≥0 :=
  let e := I.orderIsoOfFin rfl
  (e k : ℝ≥0) - if h : (k : ℕ) = 0 then 0 else (e ⟨k - 1, by omega⟩ : ℝ≥0)

/-- The cumulative sum map: given increments `d : Fin n → ℕ`, compute values
`v k = d 0 + d 1 + ⋯ + d k = ∑ j in Finset.range (k + 1), d ⟨j, ⋯⟩`. -/
noncomputable def poissonProcessCumSum {n : ℕ} (d : Fin n → ℕ) (k : Fin n) : ℕ :=
  ∑ j : Fin (k.val + 1), d ⟨j.val, by omega⟩

/-- The reindexing map from `Fin I.card → ℕ` to `∀ j : I, ℕ`, using the
order-preserving bijection `Finset.orderIsoOfFin`. -/
noncomputable def poissonProcessReindex (I : Finset ℝ≥0) (f : Fin I.card → ℕ) : I → ℕ :=
  fun j => f ((I.orderIsoOfFin rfl).symm j)

/-- The combined map from increment space to value space: cumulative sum
followed by reindexing. -/
noncomputable def poissonProcessIncrToVal (I : Finset ℝ≥0) :
    (Fin I.card → ℕ) → (I → ℕ) :=
  poissonProcessReindex I ∘ poissonProcessCumSum

/-- The finite-dimensional distribution of a Poisson process with rate `rate`
at times `I : Finset ℝ≥0`. For sorted times `0 = t₀ < t₁ ≤ ⋯ ≤ tₙ`, this is
the pushforward of the product `⨂ₖ poissonMeasure(rate * Δtₖ)` under the
cumulative-sum map from increments to values.

The construction proceeds as:
1. Sort `I` via `Finset.orderIsoOfFin` to get `e : Fin n ≃o I`.
2. Compute time gaps `Δtₖ = tₖ - tₖ₋₁` (with `t₋₁ = 0`).
3. Build the product measure `Measure.pi (fun k => poissonMeasure (rate * Δtₖ))`.
4. Push forward through `poissonProcessIncrToVal`, which applies cumulative
   summation and reindexes from `Fin n` to `I`. -/
noncomputable def poissonProcessFDD (rate : ℝ≥0) (I : Finset ℝ≥0) :
    Measure (I → ℕ) :=
  let incrMeasure : Fin I.card → Measure ℕ := fun k => poissonMeasure (rate * poissonProcessGap I k)
  (Measure.pi incrMeasure).map (poissonProcessIncrToVal I)

/-- The sorted enumeration of `I.erase t` is the sorted enumeration of `I` with position `k`
(the sorted position of `t`) removed. Specifically:
`(I.erase t).orderEmbOfFin rfl j = I.orderEmbOfFin rfl (k.succAbove j)` -/
private theorem orderEmbOfFin_erase (I : Finset ℝ≥0) (t : ℝ≥0) (ht : t ∈ I) :
    let J := I.erase t
    let hcard : J.card + 1 = I.card := Finset.card_erase_add_one ht
    let eI := I.orderEmbOfFin rfl
    let k' : Fin (J.card + 1) := Fin.cast hcard.symm ((I.orderIsoOfFin rfl).symm ⟨t, ht⟩)
    ∀ j : Fin J.card, J.orderEmbOfFin rfl j = eI (Fin.cast hcard (k'.succAbove j)) := by
  intro J hcard eI k' j
  -- We use orderEmbOfFin_unique: the composition eI ∘ Fin.cast hcard ∘ k'.succAbove
  -- is the unique strictly monotone map from Fin J.card into J.
  -- The composition is strictly monotone
  have hmono : StrictMono (fun j => eI (Fin.cast hcard (k'.succAbove j))) := by
    intro a b hab
    exact eI.strictMono (Fin.cast_strictMono hcard ((Fin.strictMono_succAbove k') hab))
  -- eI (Fin.cast hcard (k'.succAbove j)) ∈ J for all j
  have hmem : ∀ j : Fin J.card, eI (Fin.cast hcard (k'.succAbove j)) ∈ J := by
    intro j
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.orderEmbOfFin_mem I rfl _⟩
    -- eI (Fin.cast hcard (k'.succAbove j)) ≠ t
    intro h_eq
    -- Show eI (Fin.cast hcard k') = t
    have hk_eq : eI (Fin.cast hcard k') = t := by
      show (I.orderIsoOfFin rfl (Fin.cast hcard (Fin.cast hcard.symm
        ((I.orderIsoOfFin rfl).symm ⟨t, ht⟩)))) = t
      simp
    have hinj := eI.injective (h_eq.trans hk_eq.symm)
    have hval : (k'.succAbove j).val = k'.val := by
      have := Fin.val_eq_of_eq hinj; simp at this; exact this
    exact absurd (Fin.ext hval) (Fin.succAbove_ne k' j)
  -- Apply uniqueness
  have huniq := Finset.orderEmbOfFin_unique (s := J) rfl hmem hmono
  exact congr_fun huniq.symm j

/-- The merge map `ψ` on increment vectors: given `d : Fin (n+1) → ℕ` (increments for `I`),
produce `d' : Fin n → ℕ` (increments for `I.erase t`) by dropping the coordinate at
position `k` (the sorted position of `t` in `I`) and adding it to the appropriate neighbor:
- For `j < k`: `d'(j) = d(j)` (unchanged)
- For `j = k` (when `k < n`): `d'(k) = d(k) + d(k+1)` (merge with next)
- For `j > k`: `d'(j) = d(j+1)` (shift)
When `k = n` (t is the largest element), we simply drop the last coordinate. -/
private noncomputable def poissonProcessMerge (I : Finset ℝ≥0) (t : ℝ≥0) (ht : t ∈ I) :
    (Fin I.card → ℕ) → (Fin (I.erase t).card → ℕ) :=
  have hcard : (I.erase t).card + 1 = I.card := Finset.card_erase_add_one ht
  let k : Fin I.card := (I.orderIsoOfFin rfl).symm ⟨t, ht⟩
  fun d j =>
    if h : j.val < k.val then d ⟨j.val, by omega⟩
    else if j.val = k.val then
      d ⟨k.val, by omega⟩ + d ⟨k.val + 1, by omega⟩
    else -- j.val > k.val
      d ⟨j.val + 1, by omega⟩

private theorem poissonProcessFDD_erase (rate : ℝ≥0) (I : Finset ℝ≥0) (t : ℝ≥0) (ht : t ∈ I) :
    poissonProcessFDD rate (I.erase t) =
      (poissonProcessFDD rate I).map
        (@Finset.restrict₂ _ (fun _ : ℝ≥0 => ℕ) _ _ (Finset.erase_subset t I)) := by
  set J := I.erase t with hJ_def
  have hcard : J.card + 1 = I.card := Finset.card_erase_add_one ht
  -- Set up the merge map ψ
  set ψ := poissonProcessMerge I t ht with hψ_def
  -- The increment measures
  set μ_I : Fin I.card → Measure ℕ := fun k => poissonMeasure (rate * poissonProcessGap I k)
  set μ_J : Fin J.card → Measure ℕ := fun k => poissonMeasure (rate * poissonProcessGap J k)
  -- All functions on discrete spaces are measurable
  have hmeas_ψ : Measurable ψ := Measurable.of_discrete
  have hmeas_incrI : Measurable (poissonProcessIncrToVal I) := Measurable.of_discrete
  have hmeas_incrJ : Measurable (poissonProcessIncrToVal J) := Measurable.of_discrete
  have hmeas_restrict : Measurable (@Finset.restrict₂ _ (fun _ : ℝ≥0 => ℕ) _ _
    (Finset.erase_subset t I)) := Measurable.of_discrete
  -- SigmaFinite for product measures
  have hσI : ∀ k, SigmaFinite (μ_I k) := fun k => inferInstance
  have hσJ : ∀ k, SigmaFinite (μ_J k) := fun k => inferInstance
  -- The sorted position of t in I
  set eI := I.orderIsoOfFin rfl with heI_def
  set k : Fin I.card := eI.symm ⟨t, ht⟩ with hk_def
  -- Helper lemmas (shared by hdiag and hmerge)
  have hk' : k.val = ((Fin.cast hcard.symm k) : Fin (J.card + 1)).val := by simp
  set k' : Fin (J.card + 1) := Fin.cast hcard.symm k with hk'_def
  have herase := orderEmbOfFin_erase I t ht
  have hiso_emb_I : ∀ i : Fin I.card,
      (I.orderIsoOfFin rfl i : ℝ≥0) = I.orderEmbOfFin rfl i := by
    intro i; simp [Finset.coe_orderIsoOfFin_apply]
  have hiso_emb_J : ∀ j : Fin J.card,
      (J.orderIsoOfFin rfl j : ℝ≥0) = J.orderEmbOfFin rfl j := by
    intro j; simp [Finset.coe_orderIsoOfFin_apply]
  have hmono_I : ∀ a b : Fin I.card, a ≤ b →
      (I.orderIsoOfFin rfl a : ℝ≥0) ≤ (I.orderIsoOfFin rfl b : ℝ≥0) :=
    fun a b hab => Subtype.mk_le_mk.mp ((I.orderIsoOfFin rfl).monotone hab)
  have hsa_lt : ∀ (j : Fin J.card), j.val < k'.val →
      (Fin.cast hcard (k'.succAbove j)).val = j.val := by
    intro j hj
    rw [Fin.succAbove_of_castSucc_lt k' j (by rwa [Fin.lt_def, Fin.val_castSucc])]
    simp
  have hsa_ge : ∀ (j : Fin J.card), k'.val ≤ j.val →
      (Fin.cast hcard (k'.succAbove j)).val = j.val + 1 := by
    intro j hj
    rw [Fin.succAbove_of_le_castSucc k' j (by rwa [Fin.le_def, Fin.val_castSucc])]
    simp
  have heJ_val : ∀ j : Fin J.card, (J.orderIsoOfFin rfl j : ℝ≥0) =
      (I.orderIsoOfFin rfl (Fin.cast hcard (k'.succAbove j)) : ℝ≥0) := by
    intro j
    rw [hiso_emb_J, herase j, ← hiso_emb_I]
  -- Step 1: The diagram commutes:
  --   restrict₂ ∘ incrToVal I = incrToVal J ∘ ψ
  have hdiag : @Finset.restrict₂ _ (fun _ : ℝ≥0 => ℕ) _ _ (Finset.erase_subset t I) ∘
      poissonProcessIncrToVal I = poissonProcessIncrToVal J ∘ ψ := by
    funext d ⟨s, hs⟩
    simp only [Function.comp_apply, Finset.restrict₂, poissonProcessIncrToVal,
      poissonProcessReindex, poissonProcessCumSum]
    -- Goal: ∑ j : Fin (posI+1), d ⟨j,_⟩ = ∑ j : Fin (posJ+1), ψ d ⟨j,_⟩
    set posJ := (J.orderIsoOfFin rfl).symm ⟨s, hs⟩
    -- Position relationship
    have hpos : (I.orderIsoOfFin rfl).symm ⟨s, Finset.erase_subset t I hs⟩ =
        Fin.cast hcard (k'.succAbove posJ) := by
      apply eI.injective
      ext
      simp only [eI, OrderIso.apply_symm_apply]
      rw [hiso_emb_I, ← herase, ← hiso_emb_J]
      simp [posJ, OrderIso.apply_symm_apply]
    by_cases hlt : posJ.val < k.val
    · -- Case 1: posJ < k ⟹ posI = posJ, sums match term-by-term
      have hval : ((I.orderIsoOfFin rfl).symm ⟨s, Finset.erase_subset t I hs⟩).val =
          posJ.val := by
        rw [hpos]; exact hsa_lt posJ hlt
      -- Use Fintype.sum_equiv to change sum bounds + show term equality
      have hlen : ((I.orderIsoOfFin rfl).symm ⟨s, Finset.erase_subset t I hs⟩).val + 1 =
          posJ.val + 1 := by omega
      exact Fintype.sum_equiv (finCongr hlen)
        (fun j => d ⟨j.val, by omega⟩)
        (fun j => ψ d ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt posJ.isLt)⟩)
        (fun ⟨j, hj⟩ => by
          show d ⟨j, _⟩ = ψ d ⟨(finCongr hlen ⟨j, hj⟩).val, _⟩
          simp only [finCongr_apply_mk, ψ, poissonProcessMerge, ← heI_def, ← hk_def]
          rw [dif_pos (show j < k.val from by omega)])
    · -- Case 2: posJ ≥ k ⟹ posI = posJ + 1, merge at k
      push_neg at hlt
      have hval : ((I.orderIsoOfFin rfl).symm ⟨s, Finset.erase_subset t I hs⟩).val =
          posJ.val + 1 := by
        rw [hpos]; exact hsa_ge posJ hlt
      -- LHS sums posJ+2 terms, RHS sums posJ+1 terms.
      have hlen : ((I.orderIsoOfFin rfl).symm ⟨s, Finset.erase_subset t I hs⟩).val + 1 =
          posJ.val + 2 := by omega
      have hk_lt : k.val < posJ.val + 2 := by omega
      set kk : Fin (posJ.val + 2) := ⟨k.val, hk_lt⟩ with hkk_def
      -- Step A: Convert LHS from Fin(posI+1) to Fin(posJ+2) and split at kk
      -- LHS = ∑_{Fin(posJ+2)} d j = d(k) + ∑_{Fin(posJ+1)} d(succAbove j)
      have hlhs : (∑ j : Fin (((I.orderIsoOfFin rfl).symm
            ⟨s, Finset.erase_subset t I hs⟩).val + 1), d ⟨j.val, by omega⟩) =
          d ⟨k.val, by omega⟩ +
          ∑ j : Fin (posJ.val + 1),
            d ⟨(kk.succAbove j).val, by exact Nat.lt_of_lt_of_le (kk.succAbove j).isLt (by omega)⟩ := by
        rw [show (∑ j : Fin (((I.orderIsoOfFin rfl).symm
              ⟨s, Finset.erase_subset t I hs⟩).val + 1), d ⟨j.val, by omega⟩) =
            ∑ j : Fin (posJ.val + 2), d ⟨j.val, by omega⟩ from
          Fintype.sum_equiv (finCongr hlen)
            (fun j => d ⟨j.val, by omega⟩) (fun j => d ⟨j.val, by omega⟩)
            (fun j => by simp [finCongr_apply_mk])]
        exact Fin.sum_univ_succAbove (fun j : Fin (posJ.val + 2) => d ⟨j.val, by omega⟩) kk
      rw [hlhs]
      -- Goal: d(k) + ∑ d(succAbove j) = ∑ ψ d j
      -- Step B: Show ψ d j = d(succAbove j) + (if j = kJ then d(k) else 0)
      set kJ : Fin (posJ.val + 1) := ⟨k.val, by omega⟩ with hkJ_def
      -- Bound for succAbove values in I.card
      have hsa_bound : ∀ j : Fin (posJ.val + 1), (kk.succAbove j).val < I.card :=
        fun j => Nat.lt_of_lt_of_le (kk.succAbove j).isLt
          (hcard ▸ Nat.succ_le_succ (Nat.succ_le_of_lt posJ.isLt))
      -- Compute succAbove values
      have hsa_val : ∀ j : Fin (posJ.val + 1),
          (kk.succAbove j).val = if j.val < k.val then j.val else j.val + 1 := by
        intro ⟨j, hj⟩
        by_cases hjk : j < k.val
        · rw [if_pos hjk,
            Fin.succAbove_of_castSucc_lt kk ⟨j, hj⟩ (by rwa [Fin.lt_def, Fin.val_castSucc])]
          simp
        · have hle : kk ≤ Fin.castSucc ⟨j, hj⟩ := by
            rw [Fin.le_def, Fin.val_castSucc]; exact Nat.not_lt.mp hjk
          rw [if_neg hjk, Fin.succAbove_of_le_castSucc kk ⟨j, hj⟩ hle]
          simp
      have hψ_decomp : ∀ j : Fin (posJ.val + 1),
          ψ d ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt posJ.isLt)⟩ =
          d ⟨(kk.succAbove j).val, hsa_bound j⟩ +
          if j = kJ then d ⟨k.val, by omega⟩ else 0 := by
        intro ⟨j, hj⟩
        simp only [ψ, poissonProcessMerge, ← heI_def, ← hk_def]
        by_cases hjk : j < k.val
        · -- j < k: ψ d j = d j, succAbove j = j
          have hne : (⟨j, hj⟩ : Fin _) ≠ kJ := Fin.ne_of_val_ne (Nat.ne_of_lt hjk)
          rw [dif_pos hjk, if_neg hne, add_zero]
          exact congr_arg d (Fin.ext (by rw [hsa_val]; simp [hjk]))
        · push_neg at hjk
          by_cases hjk2 : j = k.val
          · -- j = k: ψ d j = d(k) + d(k+1), succAbove j = j+1
            subst hjk2
            rw [dif_neg (lt_irrefl _), if_pos rfl, if_pos (show (⟨k.val, hj⟩ : Fin _) = kJ from rfl)]
            have hsa_eq : (kk.succAbove ⟨k.val, hj⟩).val = k.val + 1 := by
              rw [hsa_val]; simp [lt_irrefl k.val]
            rw [show d ⟨(kk.succAbove ⟨k.val, hj⟩).val, hsa_bound ⟨k.val, hj⟩⟩ =
              d ⟨k.val + 1, by omega⟩ from congr_arg d (Fin.ext hsa_eq)]
            exact add_comm _ _
          · -- j > k: ψ d j = d(j+1), succAbove j = j+1
            have hne : (⟨j, hj⟩ : Fin _) ≠ kJ := Fin.ne_of_val_ne hjk2
            rw [dif_neg (not_lt.mpr hjk), if_neg hjk2, if_neg hne, add_zero]
            exact congr_arg d (Fin.ext (by rw [hsa_val]; simp [not_lt.mpr hjk]))
      -- Step C: Sum the decomposition
      simp_rw [hψ_decomp]
      rw [Finset.sum_add_distrib]
      -- Goal: d(k) + ∑ d(succAbove j) = ∑ d(succAbove j) + ∑ (if j = kJ then d(k) else 0)
      rw [Finset.sum_ite_eq' Finset.univ kJ (fun _ => d ⟨k.val, by omega⟩)]
      simp [add_comm]
  -- Step 2: The merge map pushes the product measure correctly
  -- Helper: eJ(j) in terms of eI using the erase lemma
  have heJ_val : ∀ j : Fin J.card, (J.orderIsoOfFin rfl j : ℝ≥0) =
      (I.orderIsoOfFin rfl (Fin.cast hcard (k'.succAbove j)) : ℝ≥0) := by
    intro j
    rw [hiso_emb_J, herase j, ← hiso_emb_I]
  -- Gap identities
  have hgap_lt : ∀ j : Fin J.card, j.val < k.val →
      poissonProcessGap J j = poissonProcessGap I ⟨j.val, by omega⟩ := by
    intro j hj
    simp only [poissonProcessGap]
    -- eJ(j) = eI(j) (since j < k)
    have hsa_j := hsa_lt j (by simp [k']; exact hj)
    have hkk_j : Fin.cast hcard (k'.succAbove j) = ⟨j.val, by omega⟩ := Fin.ext hsa_j
    rw [heJ_val j, hkk_j]
    -- Both have the same dite condition (j.val = 0), so we just need predecessor equality
    by_cases hj0 : j.val = 0
    · -- j = 0: both sides are eI(0) - 0
      simp [hj0]
    · -- j > 0: need eJ(j-1) = eI(j-1), which holds since j-1 < j < k
      rw [dif_neg hj0, dif_neg hj0]
      -- eJ(j-1) = eI(j-1) since j-1 < k
      have hsa_pred := hsa_lt ⟨j.val - 1, by omega⟩ (by simp [k']; omega)
      have hkk_pred : Fin.cast hcard (k'.succAbove ⟨j.val - 1, by omega⟩) =
          ⟨j.val - 1, by omega⟩ := Fin.ext hsa_pred
      rw [heJ_val ⟨j.val - 1, by omega⟩, hkk_pred]
  have hgap_eq : (hkn : k.val < J.card) →
      poissonProcessGap J ⟨k.val, hkn⟩ =
      poissonProcessGap I k + poissonProcessGap I ⟨k.val + 1, by omega⟩ := by
    intro hkn
    simp only [poissonProcessGap]
    -- eJ(k) = eI(k+1)
    have hkk1 : Fin.cast hcard (k'.succAbove ⟨k.val, hkn⟩) = ⟨k.val + 1, by omega⟩ :=
      Fin.ext (hsa_ge ⟨k.val, hkn⟩ (by simp [k']))
    rw [heJ_val ⟨k.val, hkn⟩, hkk1]
    by_cases hk0 : (k : ℕ) = 0
    · -- k = 0
      have hkn0 : (⟨k.val, hkn⟩ : Fin J.card).val = 0 := hk0
      rw [dif_pos hkn0, dif_pos hk0, tsub_zero, tsub_zero]
      have hne : ¬ ((⟨k.val + 1, (by omega : k.val + 1 < I.card)⟩ : Fin I.card).val = 0) := by
        simp
      rw [dif_neg hne]
      have hfin_sub : (⟨(⟨k.val + 1, (by omega : k.val + 1 < I.card)⟩ : Fin I.card).val - 1,
          (by simp)⟩ : Fin I.card) = ⟨k.val, by omega⟩ := Fin.ext (by simp)
      rw [hfin_sub]
      have hkk : (⟨k.val, (by omega : k.val < I.card)⟩ : Fin I.card) = k := Fin.ext rfl
      rw [hkk, add_tsub_cancel_of_le]
      exact hmono_I k ⟨k.val + 1, by omega⟩ (by simp [Fin.le_def])
    · -- k > 0
      have hkn0 : ¬ ((⟨k.val, hkn⟩ : Fin J.card).val = 0) := hk0
      rw [dif_neg hkn0, dif_neg hk0]
      have hne : ¬ ((⟨k.val + 1, (by omega : k.val + 1 < I.card)⟩ : Fin I.card).val = 0) := by
        simp
      rw [dif_neg hne]
      have hkk_pred : Fin.cast hcard (k'.succAbove ⟨k.val - 1, by omega⟩) =
          ⟨k.val - 1, by omega⟩ :=
        Fin.ext (hsa_lt ⟨k.val - 1, by omega⟩ (by simp [k']; omega))
      rw [heJ_val ⟨k.val - 1, by omega⟩, hkk_pred]
      have hfin_sub : (⟨(⟨k.val + 1, (by omega : k.val + 1 < I.card)⟩ : Fin I.card).val - 1,
          (by simp)⟩ : Fin I.card) = k := Fin.ext (by simp)
      rw [hfin_sub]
      have hle1 : k ≤ (⟨k.val + 1, by omega⟩ : Fin I.card) := Nat.le_succ _
      have hle2 : (⟨k.val - 1, by omega⟩ : Fin I.card) ≤ k := Nat.sub_le _ _
      have hcancel := tsub_add_tsub_cancel (hmono_I _ _ hle1) (hmono_I _ _ hle2)
      rw [add_comm] at hcancel; exact hcancel.symm
  have hgap_gt : ∀ j : Fin J.card, j.val > k.val →
      poissonProcessGap J j = poissonProcessGap I ⟨j.val + 1, by omega⟩ := by
    intro j hj
    simp only [poissonProcessGap]
    -- eJ(j) = eI(j+1)
    have hkk_j : Fin.cast hcard (k'.succAbove j) = ⟨j.val + 1, by omega⟩ :=
      Fin.ext (hsa_ge j (by simp [k']; omega))
    rw [heJ_val j, hkk_j]
    -- Both j and j+1 are > 0
    have hj0 : ¬ ((j : ℕ) = 0) := by omega
    have hj10 : ¬ ((⟨j.val + 1, (by omega : j.val + 1 < I.card)⟩ : Fin I.card).val = 0) := by
      simp
    rw [dif_neg hj0, dif_neg hj10]
    -- eJ(j-1): since j-1 ≥ k, succAbove gives (j-1)+1 = j
    have hkk_pred : Fin.cast hcard (k'.succAbove ⟨j.val - 1, by omega⟩) =
        ⟨j.val, by omega⟩ := by
      apply Fin.ext
      have h := hsa_ge ⟨j.val - 1, by omega⟩ (by simp [k']; omega)
      simp at h ⊢; omega
    rw [heJ_val ⟨j.val - 1, by omega⟩, hkk_pred]
    -- Both sides are eI(j+1) - eI(j), just need ⟨j, _⟩ = ⟨j+1-1, _⟩
    congr 1
  -- Bound: k.val ≤ J.card (since k : Fin I.card and J.card + 1 = I.card)
  have hk_le : k.val ≤ J.card := by have := k.isLt; omega
  have hmerge : (Measure.pi μ_I).map ψ = Measure.pi μ_J := by
    apply Measure.ext_of_singleton; intro f
    rw [Measure.map_apply hmeas_ψ (measurableSet_singleton f), Measure.pi_singleton]
    -- Goal: (Measure.pi μ_I) (ψ ⁻¹' {f}) = ∏ i : Fin J.card, μ_J i {f i}
    -- Define lift: given n (value at coord k), build the preimage element
    let lift : ℕ → (Fin I.card → ℕ) := fun n i =>
      if h1 : i.val < k.val then f ⟨i.val, Nat.lt_of_lt_of_le h1 hk_le⟩
      else if h2 : i.val = k.val then n
      else if h3 : i.val = k.val + 1 ∧ k.val < J.card then f ⟨k.val, h3.2⟩ - n
      else f ⟨i.val - 1, by
        have : (I.erase t).card + 1 = I.card := Finset.card_erase_add_one ht
        have : i.val < I.card := i.isLt
        have : ¬(i.val < k.val) := h1; have : ¬(i.val = k.val) := h2
        omega⟩
    -- lift is injective (determined by value at coord k)
    have hlift_inj : Function.Injective lift := by
      intro m n hmn
      have := congr_fun hmn ⟨k.val, k.isLt⟩
      change (if _ : _ then _ else if _ : _ then _ else _) =
        (if _ : _ then _ else if _ : _ then _ else _) at this
      rw [dif_neg (lt_irrefl _), dif_pos rfl, dif_neg (lt_irrefl _), dif_pos rfl] at this
      exact this
    -- Evaluate lift at k → n
    have hlift_at_k : ∀ n, lift n ⟨k.val, k.isLt⟩ = n := by
      intro n
      change (if _ : _ then _ else if _ : _ then _ else _) = _
      rw [dif_neg (lt_irrefl _), dif_pos rfl]
    -- Evaluate lift at k+1 (merge case) → f(k) - n
    have hlift_at_k1 : ∀ (hkJ : k.val < J.card) n,
        lift n ⟨k.val + 1, by omega⟩ = f ⟨k.val, hkJ⟩ - n := by
      intro hkJ n
      change (if _ : _ then _ else if _ : _ then _ else if _ : _ then _ else _) = _
      rw [dif_neg (by omega : ¬(k.val + 1 < k.val)),
          dif_neg (by omega : ¬(k.val + 1 = k.val)),
          dif_pos (show k.val + 1 = k.val + 1 ∧ k.val < J.card from ⟨rfl, hkJ⟩)]
    -- Evaluate lift at i > k (not k+1 merge): gives f(i-1)
    have hlift_at_gt : ∀ n (i : Fin I.card) (hki : k.val < i.val)
        (hni : ¬(i.val = k.val + 1 ∧ k.val < J.card)) (hb : i.val - 1 < J.card),
        lift n i = f ⟨i.val - 1, hb⟩ := by
      intro n i hki hni hb
      change (if _ : _ then _ else if _ : _ then _ else if _ : _ then _ else _) = _
      rw [dif_neg (by omega), dif_neg (by omega), dif_neg hni]
    -- ψ (lift n) = f when n ≤ f(k) (if k < J.card) or always (if k ≥ J.card)
    have hlift_ψ : ∀ n, (∀ hkJ : k.val < J.card, n ≤ f ⟨k.val, hkJ⟩) → ψ (lift n) = f := by
      intro n hn; ext ⟨j, hj⟩
      simp only [ψ, poissonProcessMerge, ← heI_def, ← hk_def]
      have hIJ : (I.erase t).card + 1 = I.card := Finset.card_erase_add_one ht
      by_cases hjk : j < k.val
      · -- j < k
        rw [dif_pos hjk]
        change lift n ⟨j, _⟩ = _
        change (if _ : _ then _ else _) = _
        rw [dif_pos hjk]
      · push_neg at hjk
        rw [dif_neg (not_lt.mpr hjk)]
        by_cases hjk2 : j = k.val
        · -- j = k: n + (f(k) - n) = f(k)
          subst hjk2; rw [if_pos rfl]
          change lift n ⟨k.val, k.isLt⟩ + lift n ⟨k.val + 1, _⟩ = f ⟨k.val, hj⟩
          rw [hlift_at_k, hlift_at_k1 hj]
          exact Nat.add_sub_cancel' (hn hj)
        · -- j > k
          rw [if_neg hjk2]
          change lift n ⟨j + 1, _⟩ = _
          have hjk3 : k.val < j := Nat.lt_of_le_of_ne hjk (Ne.symm hjk2)
          have hj1_lt : j + 1 < I.card := by omega
          have hb : (⟨j + 1, hj1_lt⟩ : Fin I.card).val - 1 < J.card := hj
          rw [hlift_at_gt n ⟨j + 1, hj1_lt⟩ (Nat.lt_succ_of_lt hjk3)
              (by intro ⟨h, _⟩; simp at h; omega) hb]
          exact congr_arg f (Fin.ext (by simp))
    -- Converse: every element of ψ⁻¹'{f} is of the form lift n
    have hlift_surj : ∀ d, ψ d = f → d = lift (d ⟨k.val, k.isLt⟩) := by
      intro d hd; ext ⟨i, hi⟩
      set m := d ⟨k.val, k.isLt⟩
      -- Use hd to extract info about d from ψ d = f
      have hd' : ∀ j : Fin J.card, ψ d j = f j := congr_fun hd
      by_cases hi1 : i < k.val
      · -- i < k: d(i) = ψ(d)(i) = f(i) = lift(m)(i)
        have hψi := hd' ⟨i, Nat.lt_of_lt_of_le hi1 hk_le⟩
        simp only [ψ, poissonProcessMerge, ← heI_def, ← hk_def, dif_pos hi1] at hψi
        show d ⟨i, hi⟩ = (if _ : _ then _ else _)
        rw [dif_pos hi1, ← hψi]
      · push_neg at hi1
        by_cases hi2 : i = k.val
        · -- i = k: d(k) = m = lift(m)(k)
          subst hi2; exact (hlift_at_k m).symm
        · -- i > k
          have hik : k.val < i := Nat.lt_of_le_of_ne hi1 (Ne.symm hi2)
          by_cases hi3 : i = k.val + 1 ∧ k.val < J.card
          · -- i = k+1, k < J.card: d(k+1) = f(k) - d(k)
            have hi_eq : i = k.val + 1 := hi3.1
            subst hi_eq
            have hψk := hd' ⟨k.val, hi3.2⟩
            simp only [ψ, poissonProcessMerge, ← heI_def, ← hk_def,
              dif_neg (lt_irrefl _)] at hψk
            simp only [if_true] at hψk
            -- hψk : d(k) + d(k+1) = f(k)
            show d ⟨k.val + 1, hi⟩ = lift m ⟨k.val + 1, hi⟩
            rw [hlift_at_k1 hi3.2]; omega
          · -- i > k, not merge: d(i) = f(i-1)
            have hib : i - 1 < J.card := by
              have := Finset.card_erase_add_one ht; omega
            rw [hlift_at_gt m ⟨i, hi⟩ hik hi3 hib]
            have hψi := hd' ⟨i - 1, hib⟩
            simp only [ψ, poissonProcessMerge, ← heI_def, ← hk_def] at hψi
            rw [dif_neg (by omega : ¬(i - 1 < k.val)),
                if_neg (by omega : ¬((i - 1 : ℕ) = k.val))] at hψi
            simp only [show i - 1 + 1 = i from by omega] at hψi
            exact hψi
    -- Split into merge case (k < J.card) and drop-last case (k = J.card)
    by_cases hkJ : k.val < J.card
    · -- MERGE CASE: k < J.card, ψ merges coordinates k and k+1
      set m := f ⟨k.val, hkJ⟩ with hm_def
      -- Helper: ψ d at position k gives d(k) + d(k+1)
      have hψ_at_k : ∀ d, ψ d ⟨k.val, hkJ⟩ = d ⟨k.val, k.isLt⟩ + d ⟨k.val + 1, by omega⟩ := by
        intro d
        simp only [ψ, poissonProcessMerge, ← heI_def, ← hk_def,
          dif_neg (lt_irrefl _), ite_true]
      -- Preimage: ψ⁻¹'{f} = ⋃ n ≤ m, {lift n}
      have hpreimage : ψ ⁻¹' {f} =
          ⋃ n : ℕ, if n ≤ m then {lift n} else ∅ := by
        ext d; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
        constructor
        · intro hd
          have hdk_le : d ⟨k.val, k.isLt⟩ ≤ m := by
            have := congr_fun hd ⟨k.val, hkJ⟩; rw [hψ_at_k] at this; omega
          refine ⟨d ⟨k.val, k.isLt⟩, ?_⟩
          rw [if_pos hdk_le]; exact Set.mem_singleton_iff.mpr (hlift_surj d hd)
        · rintro ⟨n, hn⟩
          by_cases hle : n ≤ m
          · rw [if_pos hle, Set.mem_singleton_iff] at hn; rw [hn]
            exact hlift_ψ n (fun _ => hle)
          · rw [if_neg hle] at hn; exact absurd hn (by simp)
      rw [hpreimage, measure_iUnion₀
        (by intro i j hij
            show AEDisjoint _ (if i ≤ m then {lift i} else ∅) (if j ≤ m then {lift j} else ∅)
            by_cases hi : i ≤ m
            · by_cases hj : j ≤ m
              · rw [if_pos hi, if_pos hj]
                exact (Set.disjoint_singleton.mpr fun h => hij (hlift_inj h)).aedisjoint
              · rw [if_neg hj]; exact disjoint_bot_right.aedisjoint
            · rw [if_neg hi]; exact disjoint_bot_left.aedisjoint)
        (by intro n; by_cases h : n ≤ m
            · rw [if_pos h]; exact (measurableSet_singleton _).nullMeasurableSet
            · rw [if_neg h]; exact MeasurableSet.empty.nullMeasurableSet)]
      simp only [show ∀ n, (Measure.pi μ_I) (if n ≤ m then ({lift n} : Set _) else ∅) =
          if n ≤ m then (Measure.pi μ_I) {lift n} else 0 from fun n => by
        by_cases h : n ≤ m
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h, measure_empty]]
      simp only [Measure.pi_singleton]
      -- Product identity: split the n-dependent terms from the constant
      set kJ := (⟨k.val, hkJ⟩ : Fin J.card)
      let C := (Finset.univ.erase kJ).prod (fun j => μ_J j {f j})
      -- Helper: lift n at positions j < k gives f j
      have hlift_lt : ∀ n (j : Fin J.card), j.val < k.val →
          lift n ⟨j.val, by omega⟩ = f j := by
        intro n j hj
        change (if _ : _ then _ else _) = _
        rw [dif_pos hj]
      have hprod_merge : ∀ n, ∏ i : Fin I.card, μ_I i {lift n i} =
          μ_I k {n} * μ_I ⟨k.val + 1, by omega⟩ {m - n} * C := by
        intro n
        -- Reindex from Fin I.card to Fin (J.card + 1)
        rw [Fintype.prod_equiv (finCongr hcard.symm)
          (fun i => μ_I i {lift n i})
          (fun j => μ_I (finCongr hcard j) {lift n (finCongr hcard j)})
          (fun x => by simp [finCongr])]
        -- Split at k' to extract the k-th term
        rw [Fin.prod_univ_succAbove _ k']
        have hk'_eq : finCongr hcard k' = k := Fin.ext (by simp [k', finCongr])
        rw [hk'_eq, hlift_at_k, mul_assoc]
        congr 1
        -- Extract kJ from inner product via mul_prod_erase
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ kJ)]
        -- The kJ-th term = μ_I ⟨k+1⟩ {m - n}
        have hk'_le_kJ : k'.val ≤ kJ.val := le_refl _
        have hfin_kJ : finCongr hcard (k'.succAbove kJ) = ⟨k.val + 1, by omega⟩ :=
          Fin.ext (hsa_ge kJ hk'_le_kJ)
        congr 1
        · rw [hfin_kJ, hlift_at_k1 hkJ]
        · -- Remaining product = C
          apply Finset.prod_congr rfl
          intro j hj
          rw [Finset.mem_erase] at hj
          have hne : j.val ≠ k.val := fun h => hj.1 (Fin.ext h)
          by_cases hjk : j.val < k.val
          · -- j < k: succAbove j = j, lift gives f j, gap identity
            have hfin_j : finCongr hcard (k'.succAbove j) = ⟨j.val, by omega⟩ :=
              Fin.ext (hsa_lt j (by simp [k']; exact hjk))
            rw [hfin_j, hlift_lt n j hjk]
            show poissonMeasure (rate * poissonProcessGap I ⟨j.val, _⟩) {f j} =
              poissonMeasure (rate * poissonProcessGap J j) {f j}
            congr 2; congr 1; exact (hgap_lt j hjk).symm
          · -- j > k: succAbove j = j+1, lift gives f j, gap identity
            push_neg at hjk
            have hjk_gt : j.val > k.val := Nat.lt_of_le_of_ne hjk (Ne.symm hne)
            have hk'_le_j : k'.val ≤ j.val := by simp [k']; omega
            have hj1_lt_I : j.val + 1 < I.card := by omega
            have hk_lt_j1 : k.val < j.val + 1 := by omega
            have hni : ¬(j.val + 1 = k.val + 1 ∧ k.val < J.card) := by
              intro ⟨h, _⟩; omega
            have hfin_j : finCongr hcard (k'.succAbove j) = ⟨j.val + 1, hj1_lt_I⟩ :=
              Fin.ext (hsa_ge j hk'_le_j)
            have hlift_val : lift n (finCongr hcard (k'.succAbove j)) = f j := by
              rw [hfin_j]
              exact hlift_at_gt n ⟨j.val + 1, hj1_lt_I⟩ hk_lt_j1 hni j.isLt
            rw [hlift_val, hfin_j]
            show poissonMeasure (rate * poissonProcessGap I ⟨j.val + 1, _⟩) {f j} =
              poissonMeasure (rate * poissonProcessGap J j) {f j}
            congr 2; congr 1; exact (hgap_gt j hjk_gt).symm
      -- Factor out the n-independent constant and apply Poisson convolution
      simp_rw [show ∀ n, (if n ≤ m then ∏ i, μ_I i {lift n i} else 0) =
          (if n ≤ m then μ_I k {n} * μ_I ⟨k.val + 1, by omega⟩ {m - n} else 0) * C
          from fun n => by
        by_cases h : n ≤ m
        · rw [if_pos h, if_pos h, hprod_merge]
        · simp [if_neg h]]
      rw [ENNReal.tsum_mul_right, poissonMeasure_conv_singleton _ _ m,
        show rate * poissonProcessGap I k + rate * poissonProcessGap I ⟨k.val + 1, by omega⟩ =
          rate * poissonProcessGap J kJ from by rw [← mul_add, hgap_eq hkJ]]
      -- Reassemble: μ_J kJ {m} * C = ∏ j, μ_J j {f j}
      change μ_J kJ {m} * C = ∏ i, μ_J i {f i}
      rw [hm_def]
      exact Finset.mul_prod_erase Finset.univ (fun j => μ_J j {f j})
        (Finset.mem_univ kJ)
    · -- DROP-LAST CASE: k = J.card, ψ just drops the last coordinate
      have hkJ_eq : k.val = J.card := Nat.le_antisymm hk_le (Nat.not_lt.mp hkJ)
      -- Preimage: every n gives a valid lift
      have hpreimage : ψ ⁻¹' {f} = ⋃ n : ℕ, {lift n} := by
        ext d; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
        constructor
        · intro hd; exact ⟨d ⟨k.val, k.isLt⟩, hlift_surj d hd⟩
        · rintro ⟨n, rfl⟩; exact hlift_ψ n (fun hkJ' => absurd hkJ' (by omega))
      rw [hpreimage, measure_iUnion₀
        (by intro i j hij
            exact (Set.disjoint_singleton.mpr (fun h => hij (hlift_inj h))).aedisjoint)
        (by intro n; exact (measurableSet_singleton _).nullMeasurableSet)]
      simp_rw [Measure.pi_singleton]
      -- Product split: ∏ i, μ_I i {lift n i} = (∏ j, μ_J j {f j}) * μ_I k {n}
      have hlift_lt : ∀ n (j : Fin J.card),
          lift n ⟨j.val, by omega⟩ = f j := by
        intro n j
        change (if _ : _ then _ else _) = _
        rw [dif_pos (show j.val < k.val by omega)]
      have hprod : ∀ n, ∏ i : Fin I.card, μ_I i {lift n i} =
          (∏ j : Fin J.card, μ_J j {f j}) * μ_I k {n} := by
        intro n
        rw [Fintype.prod_equiv (finCongr hcard.symm)
          (fun i => μ_I i {lift n i})
          (fun j => μ_I (finCongr hcard j) {lift n (finCongr hcard j)})
          (fun x => by simp [finCongr])]
        rw [Fin.prod_univ_castSucc]
        congr 1
        · -- castSucc product = ∏ j, μ_J j {f j}
          apply Finset.prod_congr rfl; intro j _
          have hfin : finCongr hcard (Fin.castSucc j) = ⟨j.val, by omega⟩ :=
            Fin.ext (by simp [finCongr])
          rw [hfin, hlift_lt n j]
          show poissonMeasure (rate * poissonProcessGap I ⟨j.val, _⟩) {f j} =
               poissonMeasure (rate * poissonProcessGap J j) {f j}
          congr 2; congr 1; exact (hgap_lt j (by omega)).symm
        · -- last term = μ_I k {n}
          have hfin : finCongr hcard (Fin.last J.card) = k :=
            Fin.ext (by simp [finCongr, Fin.last, hkJ_eq])
          rw [hfin, hlift_at_k]
      simp_rw [hprod, ENNReal.tsum_mul_left]
      rw [show ∑' n, μ_I k {n} = 1 from by
        calc ∑' n, μ_I k {n}
            = μ_I k (⋃ n, {n}) := (measure_iUnion
              (fun i j hij => Set.disjoint_singleton.mpr fun h => hij h)
              (fun n => measurableSet_singleton n)).symm
          _ = μ_I k Set.univ := by congr 1; ext x; simp
          _ = 1 := measure_univ, mul_one]
  -- Step 3: Chain the equalities
  show (Measure.pi μ_J).map (poissonProcessIncrToVal J) =
    ((Measure.pi μ_I).map (poissonProcessIncrToVal I)).map
      (@Finset.restrict₂ _ (fun _ : ℝ≥0 => ℕ) _ _ (Finset.erase_subset t I))
  rw [Measure.map_map hmeas_restrict hmeas_incrI, hdiag,
      ← Measure.map_map hmeas_incrJ hmeas_ψ, hmerge]

/-- For `J ⊆ I`, the poissonProcessFDD at `J` agrees with the projection of the
poissonProcessFDD at `I`. This is the projective consistency property.

**Proof strategy:** Strong induction on `|I \ J|`. Base case: `J = I`, identity.
Step: pick `t ∈ I \ J`, let `I' = I.erase t`. By Poisson convolution,
`Poisson(a) * Poisson(b) = Poisson(a+b)`, the FDD at `I` projects to `I'`.
By IH the FDD at `I'` projects to `J`. Compose the two. -/
theorem isProjectiveMeasureFamily_poissonProcessFDD (rate : ℝ≥0) :
    IsProjectiveMeasureFamily (α := fun (_ : ℝ≥0) => ℕ) (poissonProcessFDD rate) := by
  -- Unfold: for all J ⊆ I, poissonProcessFDD rate J =
  --   (poissonProcessFDD rate I).map (Finset.restrict₂ hJI)
  intro I J hJI
  -- Strong induction on |I \ J|
  induction h_card : (I \ J).card using Nat.strongRecOn generalizing I J with
  | _ n ih =>
  by_cases hIJ : I = J
  · -- Base case: I = J, projection is identity
    subst hIJ; simp [Finset.restrict₂_def]
  · -- Inductive step: pick t ∈ I \ J
    have hne : (I \ J).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
      exact fun h => hIJ (Finset.Subset.antisymm h hJI)
    obtain ⟨t, ht⟩ := hne
    rw [Finset.mem_sdiff] at ht
    set I' := I.erase t with hI'_def
    have hJI' : J ⊆ I' := by
      intro x hx
      rw [Finset.mem_erase]
      exact ⟨fun h => ht.2 (h ▸ hx), hJI hx⟩
    have hI'I : I' ⊆ I := Finset.erase_subset t I
    -- Show |I' \ J| < |I \ J| for IH
    have h_sub : I' \ J ⊆ I \ J := fun x hx => by
      rw [Finset.mem_sdiff] at hx ⊢; exact ⟨hI'I hx.1, hx.2⟩
    have h_not_sub : ¬ I \ J ⊆ I' \ J := by
      intro h
      have := h (Finset.mem_sdiff.mpr ht)
      rw [Finset.mem_sdiff, Finset.mem_erase] at this
      exact this.1.1 rfl
    have h_card_lt' : (I' \ J).card < n :=
      h_card ▸ Finset.card_lt_card ⟨h_sub, h_not_sub⟩
    -- IH: poissonProcessFDD rate I' projects to J
    have ih_step := ih _ h_card_lt' I' J hJI' rfl
    -- Single-step: poissonProcessFDD rate I projects to I'
    have erase_step := poissonProcessFDD_erase rate I t ht.1
    -- Compose the two projections
    rw [ih_step, erase_step,
      Measure.map_map (Finset.measurable_restrict₂ hJI') (Finset.measurable_restrict₂ hI'I),
      Finset.restrict₂_comp_restrict₂]

/-- Each Poisson FDD is a probability measure (product of probability measures
pushed forward by a measurable map).

**Dependencies:** `poissonProcessFDD` definition, `isProbabilityMeasure_poissonMeasure`. -/
instance isProbabilityMeasure_poissonProcessFDD (rate : ℝ≥0) (I : Finset ℝ≥0) :
    IsProbabilityMeasure (poissonProcessFDD rate I) := by
  unfold poissonProcessFDD
  exact Measure.isProbabilityMeasure_map (Measurable.of_discrete).aemeasurable

/-- `ℕ` is a Polish space (closed embedding into `ℝ`, which is Polish). -/
instance : PolishSpace ℕ := Nat.isClosedEmbedding_coe_real.polishSpace

/-- The projective family for a Poisson process with rate `rate`.
Input to `ProjectiveFamily.kolmogorovExtension`. -/
noncomputable def poissonProjectiveFamily (rate : ℝ≥0) :
    ProjectiveFamily ℝ≥0 (fun _ : ℝ≥0 => ℕ) where
  measure := poissonProcessFDD rate
  consistent := isProjectiveMeasureFamily_poissonProcessFDD rate
  prob := isProbabilityMeasure_poissonProcessFDD rate

/-! ## Singleton marginal of the FDD -/

/-- Evaluating the poissonProcessFDD at a singleton `{t}` and projecting to the unique
coordinate recovers `poissonMeasure (rate * t)`. -/
private theorem poissonProcessFDD_singleton_eval (rate : ℝ≥0) (t : ℝ≥0) :
    (poissonProcessFDD rate {t}).map
      (fun f : ({t} : Finset ℝ≥0) → ℕ => f ⟨t, Finset.mem_singleton_self t⟩) =
    poissonMeasure (rate * t) := by
  -- {t}.card = 1
  have hcard : ({t} : Finset ℝ≥0).card = 1 := Finset.card_singleton t
  -- The gap at position 0 in {t} is t - 0 = t
  have hgap : poissonProcessGap {t} ⟨0, by rw [hcard]; omega⟩ = t := by
    simp [poissonProcessGap]
    exact Finset.mem_singleton.mp
      (({t} : Finset ℝ≥0).orderEmbOfFin_mem rfl ⟨0, by omega⟩)
  -- Unfold: FDD = (Measure.pi incrMeasure).map incrToVal
  -- Compose: eval ∘ incrToVal = fun d => d 0
  -- Because incrToVal sends d to (fun ⟨t, _⟩ => cumsum(d)(orderIso⁻¹(⟨t,_⟩))) = (fun _ => d 0)
  have hcomp : (fun f : ({t} : Finset ℝ≥0) → ℕ => f ⟨t, Finset.mem_singleton_self t⟩) ∘
      poissonProcessIncrToVal {t} =
      (fun d : Fin ({t} : Finset ℝ≥0).card → ℕ => d ⟨0, by rw [hcard]; omega⟩) := by
    ext d
    simp only [Function.comp_apply, poissonProcessIncrToVal, poissonProcessReindex]
    -- cumsum at orderIso⁻¹(⟨t,_⟩) = d 0, since #{t} = 1 means the position is ⟨0, _⟩
    haveI : Subsingleton (Fin ({t} : Finset ℝ≥0).card) := by rw [hcard]; infer_instance
    rw [show (({t} : Finset ℝ≥0).orderIsoOfFin rfl).symm
        ⟨t, Finset.mem_singleton_self t⟩ = ⟨0, by rw [hcard]; omega⟩ from
      Subsingleton.elim _ _]
    simp [poissonProcessCumSum]
  -- poissonProcessFDD rate {t} = (Measure.pi incrMeasure).map incrToVal
  -- So (FDD.map eval) = (Measure.pi incrMeasure).map (eval ∘ incrToVal)
  --                    = (Measure.pi incrMeasure).map (fun d => d 0)
  unfold poissonProcessFDD
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete, hcomp]
  -- Now: (Measure.pi incrMeasure).map (fun d => d 0) = incrMeasure 0 = poissonMeasure (rate * t)
  -- Prove by ext_of_singleton
  apply Measure.ext_of_singleton; intro n
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton n)]
  -- LHS: (Measure.pi incrMeasure) {d | d 0 = n}
  -- = (Measure.pi incrMeasure) (Set.pi univ (fun i => if i = ⟨0, _⟩ then {n} else univ))
  -- But on Fin 1, this simplifies to {fun _ => n}
  have hpreimage : (fun d : Fin ({t} : Finset ℝ≥0).card → ℕ =>
      d ⟨0, by rw [hcard]; omega⟩) ⁻¹' {n} =
      {fun i : Fin ({t} : Finset ℝ≥0).card => n} := by
    ext d; simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hd; ext ⟨j, hj⟩; have hj0 : j = 0 := by omega
      subst hj0; exact hd
    · intro hd; exact congr_fun hd _
  rw [hpreimage, Measure.pi_singleton]
  -- Beta-reduce the product and collapse (#{t} = 1 so Fin #{t} ≅ Fin 1)
  change ∏ i : Fin ({t} : Finset ℝ≥0).card,
      poissonMeasure (rate * poissonProcessGap {t} i) {n} = _
  -- Collapse product over Fin 1 using Subsingleton
  haveI : Subsingleton (Fin ({t} : Finset ℝ≥0).card) := by rw [hcard]; infer_instance
  rw [Fintype.prod_subsingleton _ ⟨0, by rw [hcard]; omega⟩, hgap]

/-- The Kolmogorov extension measure projected to a single coordinate `t`
gives `poissonMeasure (rate * t)`. -/
private theorem kolmogorovExtension_map_coord (rate : ℝ≥0) (t : ℝ≥0) :
    (poissonProjectiveFamily rate).kolmogorovExtension.map (fun ω : ∀ _ : ℝ≥0, ℕ => ω t) =
    poissonMeasure (rate * t) := by
  set μ := (poissonProjectiveFamily rate).kolmogorovExtension
  -- Factor: (fun ω => ω t) = eval_t ∘ {t}.restrict
  have hfactor : (fun ω : ∀ _ : ℝ≥0, ℕ => ω t) =
      (fun f : ({t} : Finset ℝ≥0) → ℕ => f ⟨t, Finset.mem_singleton_self t⟩) ∘
      Finset.restrict {t} := by
    ext ω; simp [Finset.restrict]
  -- μ.map ({t}.restrict) = poissonProcessFDD rate {t}
  have hmarg : μ.map (Finset.restrict {t}) = poissonProcessFDD rate {t} :=
    (poissonProjectiveFamily rate).isProjectiveLimit_kolmogorovExtension {t}
  rw [hfactor]
  have h_decomp : μ.map ((fun f : ({t} : Finset ℝ≥0) → ℕ =>
      f ⟨t, Finset.mem_singleton_self t⟩) ∘ Finset.restrict {t}) =
      (μ.map (Finset.restrict {t})).map
        (fun f : ({t} : Finset ℝ≥0) → ℕ => f ⟨t, Finset.mem_singleton_self t⟩) :=
    (Measure.map_map Measurable.of_discrete
      (Finset.measurable_restrict (X := fun _ : ℝ≥0 => ℕ) {t})).symm
  rw [h_decomp, hmarg]
  exact poissonProcessFDD_singleton_eval rate t

/-! ## 2-point increment marginal -/

/-- The Kolmogorov extension projected through the difference
`ω(s+h) - ω(s)` gives `poissonMeasure (rate * h)`, for `s ≠ 0` and `h ≠ 0`. -/
private theorem kolmogorovExtension_map_diff (rate : ℝ≥0) (s h : ℝ≥0) (hh : h ≠ 0) :
    (poissonProjectiveFamily rate).kolmogorovExtension.map
      (fun ω : ∀ _ : ℝ≥0, ℕ => ω (s + h) - ω s) =
    poissonMeasure (rate * h) := by
  set μ := (poissonProjectiveFamily rate).kolmogorovExtension
  -- s < s + h since h ≠ 0
  have hlt : s < s + h := lt_add_of_pos_right s (pos_iff_ne_zero.mpr hh)
  have hne : s ≠ s + h := ne_of_lt hlt
  have hsh_ne : s + h ≠ s := hne.symm
  -- Factor through {s, s+h}.restrict
  set I := ({s, s + h} : Finset ℝ≥0) with hI_def
  have hs_mem : s ∈ I := Finset.mem_insert.mpr (Or.inl rfl)
  have hsh_mem : s + h ∈ I := Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))
  -- The difference function factors through the restriction
  have hfactor : (fun ω : ∀ _ : ℝ≥0, ℕ => ω (s + h) - ω s) =
      (fun f : I → ℕ => f ⟨s + h, hsh_mem⟩ - f ⟨s, hs_mem⟩) ∘ Finset.restrict I := by
    ext ω; simp [Finset.restrict]
  -- μ.map (I.restrict) = poissonProcessFDD rate I
  have hmarg : μ.map (Finset.restrict I) = poissonProcessFDD rate I :=
    (poissonProjectiveFamily rate).isProjectiveLimit_kolmogorovExtension I
  rw [hfactor]
  have h_decomp : μ.map ((fun f : I → ℕ =>
      f ⟨s + h, hsh_mem⟩ - f ⟨s, hs_mem⟩) ∘ Finset.restrict I) =
      (μ.map (Finset.restrict I)).map
        (fun f : I → ℕ => f ⟨s + h, hsh_mem⟩ - f ⟨s, hs_mem⟩) :=
    (Measure.map_map Measurable.of_discrete
      (Finset.measurable_restrict (X := fun _ : ℝ≥0 => ℕ) I)).symm
  rw [h_decomp, hmarg]
  -- Now prove: (poissonProcessFDD rate I).map (fun f => f(s+h) - f(s)) = poissonMeasure(rate * h)
  -- Unfold poissonProcessFDD and compute
  -- I has 2 elements: {s, s+h}, card = 2
  have hcard : I.card = 2 := by
    rw [hI_def, Finset.card_insert_of_notMem
      (Finset.notMem_singleton.mpr hne), Finset.card_singleton]
  -- The order iso sends 0 ↦ s, 1 ↦ s+h (since s < s+h)
  set e := I.orderIsoOfFin rfl with he_def
  -- Gaps: gap 0 = s, gap 1 = h
  -- incrToVal sends d to cumsum reindexed:
  --   at s: d(0)
  --   at s+h: d(0) + d(1)
  -- So f(s+h) - f(s) = d(1)
  -- Therefore (FDD.map diff) = (pi incr).map (fun d => d 1) = poissonMeasure(rate * h)
  -- Prove the composition identity
  have hcomp : (fun f : I → ℕ => f ⟨s + h, hsh_mem⟩ - f ⟨s, hs_mem⟩) ∘
      poissonProcessIncrToVal I =
      fun d : Fin I.card → ℕ => d ⟨1, by rw [hcard]; omega⟩ := by
    ext d
    simp only [Function.comp_apply, poissonProcessIncrToVal, poissonProcessReindex,
      poissonProcessCumSum]
    set pos_s := e.symm ⟨s, hs_mem⟩
    set pos_sh := e.symm ⟨s + h, hsh_mem⟩
    -- pos_s and pos_sh are distinct because s ≠ s + h
    have hne_pos : pos_s ≠ pos_sh := by
      intro heq
      have := congr_arg (fun x => (e x : ℝ≥0)) heq
      simp only [pos_s, pos_sh, OrderIso.apply_symm_apply, Subtype.coe_mk] at this
      exact hne this
    -- pos_s.val = 0: by contradiction via ordering
    have hps_lt := pos_s.isLt   -- pos_s.val < I.card
    have hpsh_lt := pos_sh.isLt -- pos_sh.val < I.card
    have hne_val : pos_s.val ≠ pos_sh.val := fun hv => hne_pos (Fin.ext hv)
    have hpos_s : pos_s.val = 0 := by
      by_contra h0
      have h1 : pos_s.val = 1 := by omega
      have hpsh0 : pos_sh.val = 0 := by omega
      -- pos_sh < pos_s in Fin order, so e(pos_sh) < e(pos_s), i.e. s+h < s — contradiction
      have hlt_fin : pos_sh < pos_s := show pos_sh.val < pos_s.val by omega
      have : (e pos_sh : ℝ≥0) < (e pos_s : ℝ≥0) :=
        Subtype.mk_lt_mk.mp (e.strictMono hlt_fin)
      simp only [pos_s, pos_sh, OrderIso.apply_symm_apply, Subtype.coe_mk] at this
      exact not_lt.mpr (le_of_lt hlt) this
    have hpos_sh : pos_sh.val = 1 := by omega
    -- cumsum at pos_sh = d(0) + d(1), cumsum at pos_s = d(0)
    have hsum_sh : (∑ j : Fin (pos_sh.val + 1), d ⟨j.val, by omega⟩) =
        d ⟨0, by omega⟩ + d ⟨1, by omega⟩ :=
      calc ∑ j : Fin (pos_sh.val + 1), d ⟨j.val, by omega⟩
          = ∑ j : Fin 2, d ⟨j.val, by omega⟩ :=
            Fintype.sum_equiv (finCongr (by omega : pos_sh.val + 1 = 2)) _ _ (fun j => rfl)
        _ = d ⟨0, by omega⟩ + d ⟨1, by omega⟩ := Fin.sum_univ_two _
    have hsum_s : (∑ j : Fin (pos_s.val + 1), d ⟨j.val, by omega⟩) =
        d ⟨0, by omega⟩ :=
      calc ∑ j : Fin (pos_s.val + 1), d ⟨j.val, by omega⟩
          = ∑ j : Fin 1, d ⟨j.val, by omega⟩ :=
            Fintype.sum_equiv (finCongr (by omega : pos_s.val + 1 = 1)) _ _ (fun j => rfl)
        _ = d ⟨0, by omega⟩ := Fin.sum_univ_one _
    -- The sums in the goal match pos_sh and pos_s
    change (∑ j : Fin (pos_sh.val + 1), d ⟨j.val, _⟩) -
        (∑ j : Fin (pos_s.val + 1), d ⟨j.val, _⟩) = _
    rw [hsum_sh, hsum_s]
    omega
  -- Now: (FDD rate I).map diff = (pi incr).map (fun d => d 1)
  unfold poissonProcessFDD
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete, hcomp]
  -- Need: (Measure.pi incrMeasure).map (fun d => d 1) = poissonMeasure (rate * h)
  -- where incrMeasure 1 = poissonMeasure (rate * gap 1) = poissonMeasure (rate * h)
  -- This is the marginal of the product measure at coordinate 1
  -- Prove gap 1 = h
  have hgap1 : poissonProcessGap I ⟨1, by rw [hcard]; omega⟩ = h := by
    -- Helper: e(0) and e(1) are elements of I = {s, s+h}
    set fin0 : Fin I.card := ⟨0, by omega⟩
    set fin1 : Fin I.card := ⟨1, by rw [hcard]; omega⟩
    have he0_mem := (e fin0).prop
    have he1_mem := (e fin1).prop
    -- e is strictly monotone, so e(0) < e(1)
    have hlt_01 : (e fin0 : ℝ≥0) < (e fin1 : ℝ≥0) :=
      Subtype.mk_lt_mk.mp (e.strictMono (show fin0 < fin1 from
        Fin.mk_lt_mk.mpr (by omega)))
    -- Membership gives: e(0), e(1) ∈ {s, s+h}
    simp only [hI_def, Finset.mem_insert, Finset.mem_singleton] at he0_mem he1_mem
    -- e(0) = s (the smaller) and e(1) = s+h (the larger)
    have he0 : (e fin0 : ℝ≥0) = s := by
      rcases he0_mem with h0s | h0sh
      · exact h0s
      · -- if e(0) = s+h then e(1) ∈ {s, s+h} with e(0) < e(1) gives contradiction
        rcases he1_mem with h1s | h1sh
        · rw [h0sh, h1s] at hlt_01; exact absurd hlt_01 (not_lt.mpr (le_of_lt hlt))
        · rw [h0sh, h1sh] at hlt_01; exact absurd hlt_01 (lt_irrefl _)
    have he1 : (e fin1 : ℝ≥0) = s + h := by
      rcases he1_mem with h1s | h1sh
      · rw [he0, h1s] at hlt_01; exact absurd hlt_01 (lt_irrefl _)
      · exact h1sh
    -- Unfold poissonProcessGap: for k = 1, gap = e(1) - e(0)
    simp only [poissonProcessGap]
    rw [dif_neg (show (fin1.val : ℕ) ≠ 0 by simp [fin1])]
    -- ⟨fin1.val - 1, _⟩ = fin0
    have hfin0 : (⟨fin1.val - 1, by omega⟩ : Fin I.card) = fin0 :=
      Fin.ext (by simp [fin0, fin1])
    rw [he1, hfin0, he0]
    exact add_tsub_cancel_left s h
  -- Remaining computation: ext_of_singleton, preimage, product split, tsum
  apply Measure.ext_of_singleton; intro n
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton n)]
  -- Preimage: d ↦ d(1) lands in {n} iff d = (fun i => if i = 0 then m else n) for some m
  set a : Fin I.card := ⟨0, by omega⟩
  set b : Fin I.card := ⟨1, by rw [hcard]; omega⟩
  have hab : a ≠ b := Fin.ne_of_val_ne (show (0 : ℕ) ≠ 1 by omega)
  have hpreimage : (fun d : Fin I.card → ℕ => d b) ⁻¹' {n} =
      ⋃ m : ℕ, {fun i : Fin I.card => if i = a then m else n} := by
    ext d; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
    constructor
    · intro hd
      refine ⟨d a, funext fun ⟨i, hi⟩ => ?_⟩
      by_cases h0 : i = 0
      · subst h0; simp [a]
      · simp only [show (⟨i, hi⟩ : Fin I.card) ≠ a from Fin.ne_of_val_ne h0, ite_false]
        have hi2 : i < 2 := hcard ▸ hi
        have hi1 : i = 1 := by omega
        subst hi1; exact hd
    · rintro ⟨m, rfl⟩
      simp [show b ≠ a from hab.symm]
  rw [hpreimage, measure_iUnion₀
    (fun i j hij => (Set.disjoint_singleton.mpr (fun h => hij (by
      have := congr_fun h a; simp [a] at this; exact this))).aedisjoint)
    (fun m => (measurableSet_singleton _).nullMeasurableSet)]
  simp_rw [Measure.pi_singleton]
  -- Product split: ∏ over Fin I.card with I.card = 2
  have huniv : (Finset.univ : Finset (Fin I.card)) = {a, b} := by
    ext ⟨i, hi⟩
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    have hi2 : i < 2 := hcard ▸ hi
    by_cases h : i = 0
    · left; exact Fin.ext h
    · right; exact Fin.ext (show i = 1 by omega)
  have hprod : ∀ m, ∏ i : Fin I.card,
      poissonMeasure (rate * poissonProcessGap I i) {if i = a then m else n} =
      poissonMeasure (rate * poissonProcessGap I a) {m} *
      poissonMeasure (rate * poissonProcessGap I b) {n} := by
    intro m
    change Finset.univ.prod _ = _
    rw [huniv, Finset.prod_pair hab, if_pos rfl, if_neg hab.symm]
  simp_rw [hprod, ENNReal.tsum_mul_right]
  -- ∑' m, poissonMeasure(rate * gap 0) {m} = 1 (total mass of probability measure)
  rw [show ∑' m, poissonMeasure (rate * poissonProcessGap I a) {m} = 1 from by
    calc ∑' m, poissonMeasure (rate * poissonProcessGap I a) {m}
        = poissonMeasure (rate * poissonProcessGap I a) (⋃ m, {m}) := (measure_iUnion
          (fun i j hij => Set.disjoint_singleton.mpr fun h => hij h)
          (fun m => measurableSet_singleton m)).symm
      _ = poissonMeasure (rate * poissonProcessGap I a) Set.univ := by congr 1; ext x; simp
      _ = 1 := measure_univ, one_mul, hgap1]

/-! ## Independent increments from the Kolmogorov extension -/

/-- The cumulative sum at position `j+1` minus position `j` equals `d(j+1)`.
This is the telescoping property of partial sums. -/
private theorem poissonProcessCumSum_succ_sub {m : ℕ} (d : Fin m → ℕ) (j : Fin m)
    (hj : j.val + 1 < m) :
    poissonProcessCumSum d ⟨j.val + 1, hj⟩ = poissonProcessCumSum d j + d ⟨j.val + 1, hj⟩ := by
  simp only [poissonProcessCumSum]
  -- Goal involves ∑ i : Fin (⟨j.val+1, hj⟩.val+1) and ∑ i : Fin (j.val+1)
  -- Use Fin.sum_univ_castSucc to split the last term
  have hsplit := Fin.sum_univ_castSucc (n := j.val + 1)
    (f := fun (i : Fin (j.val + 1 + 1)) => d ⟨i.val, by omega⟩)
  simp only [Fin.val_castSucc, Fin.val_last] at hsplit
  convert hsplit using 2

/-- For monotone `t : Fin (n+1) → ℝ≥0`, the sorted positions of consecutive values
`t k.castSucc` and `t k.succ` in `I = image t univ` are consecutive in `Fin I.card`
when `t k.castSucc < t k.succ`. -/
private theorem orderIsoOfFin_symm_succ_of_lt (n : ℕ) (t : Fin (n + 1) → ℝ≥0)
    (hmono : Monotone t) (k : Fin n) (hlt : t k.castSucc < t k.succ) :
    let I := Finset.image t Finset.univ
    let e := I.orderIsoOfFin rfl
    (e.symm ⟨t k.succ, Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩⟩).val =
    (e.symm ⟨t k.castSucc, Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩⟩).val + 1 := by
  intro I e
  -- Use abbreviations for readability, but `let` to avoid opaqueness from `set`
  let p := e.symm ⟨t k.castSucc, Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩⟩
  let q := e.symm ⟨t k.succ, Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩⟩
  -- p < q since e is order-preserving and t k.castSucc < t k.succ
  have hpq : p < q := e.symm.strictMono hlt
  show q.val = p.val + 1
  -- No element of Fin I.card is strictly between p and q
  -- because any such element would correspond to a value strictly between
  -- t k.castSucc and t k.succ in I = image t univ.
  -- But there's no Fin (n+1) index strictly between k.castSucc and k.succ.
  by_contra h
  -- q.val ≠ p.val + 1, and p.val < q.val, so q.val ≥ p.val + 2
  have hpq_val : p.val < q.val := hpq
  have hgap : p.val + 2 ≤ q.val := by omega
  -- There exists j : Fin I.card with p < j < q
  let j : Fin I.card := ⟨p.val + 1, by omega⟩
  have hpj : p < j := by show p.val < j.val; dsimp [j]; omega
  have hjq : j < q := by show j.val < q.val; dsimp [j]; omega
  -- e j is in I and satisfies t k.castSucc < e j < t k.succ
  have h1 : t k.castSucc < (e j : ℝ≥0) := by
    have := e.strictMono hpj; simp [p, OrderIso.apply_symm_apply] at this; exact this
  have h2 : (e j : ℝ≥0) < t k.succ := by
    have := e.strictMono hjq; simp [q, OrderIso.apply_symm_apply] at this; exact this
  -- e j ∈ I = image t univ, so e j = t m for some m
  have hej_mem : (e j : ℝ≥0) ∈ I := (e j).2
  rw [Finset.mem_image] at hej_mem
  obtain ⟨m, _, hm_eq⟩ := hej_mem
  rw [← hm_eq] at h1 h2
  -- h1 : t k.castSucc < t m, h2 : t m < t k.succ
  -- By monotonicity: k.castSucc < m < k.succ (as Fin (n+1) values)
  -- But k.castSucc.val = k.val and k.succ.val = k.val + 1, so no m exists
  have hlt1 : k.val < m.val := by
    by_contra hle; push_neg at hle
    exact absurd (hmono (Fin.le_iff_val_le_val.mpr (by simp [Fin.val_castSucc]; exact hle)))
      (not_le.mpr h1)
  have hlt2 : m.val < k.val + 1 := by
    by_contra hle; push_neg at hle
    exact absurd (hmono (Fin.le_iff_val_le_val.mpr (by simp [Fin.val_succ]; exact hle)))
      (not_le.mpr h2)
  omega

/-- Under the Kolmogorov extension, `ω 0 = 0` almost everywhere. This follows from the
FDD at `{0}` being `poissonMeasure(rate * 0) = Dirac(0)` via `poissonProcessGap`. -/
private theorem kolmogorovExtension_coord_zero_ae (rate : ℝ≥0) :
    ∀ᵐ ω ∂(poissonProjectiveFamily rate).kolmogorovExtension, ω 0 = 0 := by
  set μ := (poissonProjectiveFamily rate).kolmogorovExtension
  -- Show μ {ω | ω 0 ≠ 0} = 0 via the FDD at {0}
  rw [ae_iff (μ := μ)]
  -- Goal: μ { a | ¬a 0 = 0 } = 0
  -- This set equals (fun ω => ω 0) ⁻¹' ({0}ᶜ)
  have hset : { ω : ∀ _ : ℝ≥0, ℕ | ¬ω 0 = 0 } = (fun ω => ω 0) ⁻¹' ({0} : Set ℕ)ᶜ := by
    ext ω; simp
  rw [hset]
  -- μ ((fun ω => ω 0) ⁻¹' {0}ᶜ) = (μ.map (fun ω => ω 0)) {0}ᶜ
  rw [← Measure.map_apply (measurable_pi_apply 0) (MeasurableSet.compl (measurableSet_singleton 0))]
  rw [kolmogorovExtension_map_coord rate 0, mul_zero]
  -- poissonMeasure 0 {0}ᶜ = 0 because poissonMeasure 0 = Dirac 0
  -- poissonMeasure 0 = (poissonPMF 0).toMeasure, and poissonPMF 0 0 = 1 (by definition with 0^0/0! = 1)
  -- poissonMeasure 0 {0}ᶜ = 1 - poissonMeasure 0 {0} = 1 - 1 = 0
  rw [measure_compl (measurableSet_singleton 0) (measure_ne_top _ _),
    measure_univ, show poissonMeasure 0 {0} = 1 from ?_, tsub_self]
  -- poissonMeasure 0 {0} = (poissonPMF 0).toMeasure {0} = poissonPMF 0 0 = 1
  change (poissonPMF 0).toMeasure {0} = 1
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton 0)]
  -- Goal: (poissonPMF 0) 0 = 1
  -- poissonPMF 0 0 = ENNReal.ofReal (poissonPMFReal 0 0) = ENNReal.ofReal (exp(-0) * 0^0 / 0!) = 1
  show ENNReal.ofReal (poissonPMFReal 0 0) = 1
  simp [poissonPMFReal, Nat.factorial]

/-- The ℤ-valued increments `ω(t(k+1)) - ω(t(k))` are mutually independent under
the Kolmogorov extension of the Poisson projective family, for any monotone
`t : Fin (n+1) → ℝ≥0`. This is the core independence property needed for `exists_poissonProcess`.

The proof uses `iIndepFun_iff_measure_inter_preimage_eq_mul`: for any `S : Finset (Fin n)` and
measurable sets `A_k ⊆ ℤ`, the product formula
`μ (⋂ k ∈ S, incr_k ⁻¹' A_k) = ∏ k ∈ S, μ (incr_k ⁻¹' A_k)`
holds because the intersection is a cylinder set at `I = image t univ`, and the FDD
`poissonProcessFDD rate I` is a product measure pushed through a cumulative sum. -/
private theorem kolmogorovExtension_indep_increments (rate : ℝ≥0) (n : ℕ)
    (t : Fin (n + 1) → ℝ≥0) (hmono : Monotone t) :
    iIndepFun (fun k : Fin n => fun ω : ∀ _ : ℝ≥0, ℕ =>
        (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ))
        (poissonProjectiveFamily rate).kolmogorovExtension := by
  set μ := (poissonProjectiveFamily rate).kolmogorovExtension
  -- Each increment fun ω => (ω(t(k+1)) : ℤ) - (ω(t(k)) : ℤ) is measurable
  have hmeas_incr : ∀ k : Fin n, Measurable (fun ω : ∀ _ : ℝ≥0, ℕ =>
      (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)) := by
    intro k
    exact (Measurable.of_discrete.comp (measurable_pi_apply _)).sub
      (Measurable.of_discrete.comp (measurable_pi_apply _))
  -- Use the product formula characterization
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _hmeas_sets
  -- Reduce to showing: the joint distribution μ.map fI is a product measure.
  -- The combined function extracts all n increments at once.
  set fI : (∀ _ : ℝ≥0, ℕ) → (Fin n → ℤ) :=
    fun ω k => (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ) with hfI_def
  -- fI is measurable
  have hmeas_fI : Measurable fI := measurable_pi_lambda _ hmeas_incr
  -- The intersection and each preimage factor through fI
  have hinter_eq : ⋂ k ∈ S, (fun ω : ∀ _ : ℝ≥0, ℕ =>
      (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)) ⁻¹' sets k =
      fI ⁻¹' (⋂ k ∈ S, (fun z : Fin n → ℤ => z k) ⁻¹' sets k) := by
    ext ω; simp only [Set.mem_iInter, Set.mem_preimage, fI]
  have hindiv_eq : ∀ k : Fin n,
      (fun ω : ∀ _ : ℝ≥0, ℕ => (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)) ⁻¹' sets k =
      fI ⁻¹' ((fun z : Fin n → ℤ => z k) ⁻¹' sets k) := by
    intro k; ext ω; simp only [Set.mem_preimage, fI]
  rw [hinter_eq]; simp_rw [hindiv_eq]
  -- Goal: μ (fI ⁻¹' (⋂ k ∈ S, ..)) = ∏ k ∈ S, μ (fI ⁻¹' (..))
  -- = (μ.map fI) (⋂ k ∈ S, ..) = ∏ k ∈ S, (μ.map fI) (..)
  -- It suffices to show μ.map fI is a product measure, i.e.,
  -- iIndepFun (fun k z => z k) (μ.map fI)
  -- because then the product formula follows from iIndepFun_pi.
  -- Equivalently, show μ.map fI = Measure.pi (fun k => (μ.map fI).map (fun z => z k)).
  --
  -- Step 1: Compute μ.map fI by factoring through restrict I.
  set I := Finset.image t Finset.univ
  -- fI factors through restrict I
  have hfI_factor : fI = (fun f : (i : ↥I) → ℕ => fun k : Fin n =>
      (f ⟨t k.succ, Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩⟩ : ℤ) -
      (f ⟨t k.castSucc, Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩⟩ : ℤ))
      ∘ Finset.restrict I := by
    ext ω k; simp [fI, Finset.restrict]
  -- μ.map (restrict I) = FDD = (Measure.pi incrMeasure).map incrToVal
  have hmarg : μ.map (Finset.restrict I) = poissonProcessFDD rate I :=
    (poissonProjectiveFamily rate).isProjectiveLimit_kolmogorovExtension I
  -- Step 2: Convert to μ.map fI and show it's a product measure.
  haveI : MeasurableSingletonClass (Fin n → ℤ) :=
    Pi.instMeasurableSingletonClass
  haveI : DiscreteMeasurableSpace (Fin n → ℤ) :=
    MeasurableSingletonClass.toDiscreteMeasurableSpace
  rw [← Measure.map_apply hmeas_fI MeasurableSet.of_discrete]
  simp_rw [← Measure.map_apply hmeas_fI MeasurableSet.of_discrete]
  -- Goal: (μ.map fI) (⋂ k ∈ S, ..) = ∏ k ∈ S, (μ.map fI) (..)
  -- It suffices to show μ.map fI is a product measure, then use the iIndepFun
  -- criterion for coordinate projections.
  -- Show iIndepFun of coordinate projections on μ.map fI:
  suffices h_indep : iIndepFun (fun k (z : Fin n → ℤ) => z k) (μ.map fI) from
    h_indep.measure_inter_preimage_eq_mul S (fun k _ => _hmeas_sets k ‹_›)
  -- It suffices to show μ.map fI = Measure.pi (fun k => (μ.map fI).map (fun z => z k))
  -- Use iIndepFun_iff_map_fun_eq_pi_map
  haveI : IsProbabilityMeasure (μ.map fI) :=
    Measure.isProbabilityMeasure_map hmeas_fI.aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun k => (measurable_pi_apply k).aemeasurable)]
  -- Goal: (μ.map fI).map (fun z k => z k) = Measure.pi (fun k => (μ.map fI).map (fun z => z k))
  -- Simplify: (fun z k => z k) = id
  have hid : (fun z : Fin n → ℤ => fun k => z k) = id := by ext z k; rfl
  rw [hid, Measure.map_id]
  -- Goal: μ.map fI = Measure.pi (fun k => (μ.map fI).map (fun z => z k))
  -- = Measure.pi (fun k => μ.map (fun ω => (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)))
  -- Simplify RHS marginals: (μ.map fI).map (fun z => z k) = μ.map (fI_k)
  have hmarg_k : ∀ k : Fin n,
      (μ.map fI).map (fun z : Fin n → ℤ => z k) =
      μ.map (fun ω => (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)) := by
    intro k
    rw [Measure.map_map (measurable_pi_apply k) hmeas_fI]
    rfl
  simp_rw [hmarg_k]
  -- Goal: μ.map fI = Measure.pi (fun k => μ.map (fun ω => (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)))
  -- Show the joint distribution is a product measure.
  -- Key: μ.map fI factors through the FDD, which is a product measure map.
  -- Compute μ.map fI via the factorization fI = gI ∘ restrict I.
  have hmap_fI : μ.map fI = (poissonProcessFDD rate I).map (fun f : (i : ↥I) → ℕ =>
      fun k : Fin n =>
        (f ⟨t k.succ, Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩⟩ : ℤ) -
        (f ⟨t k.castSucc, Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩⟩ : ℤ)) := by
    rw [hfI_factor]
    rw [← Measure.map_map Measurable.of_discrete
      (Finset.measurable_restrict (X := fun _ : ℝ≥0 => ℕ) I)]
    rw [hmarg]
  -- Now use the FDD = (Measure.pi incrMeasure).map incrToVal structure.
  -- The composition extracts differences of cumulative sums, which are sums over
  -- disjoint coordinate blocks. This means μ.map fI is a product measure.
  -- We show equality with Measure.pi on singletons.
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply hmeas_fI (measurableSet_singleton z)]
  rw [Measure.pi_singleton]
  simp_rw [Measure.map_apply (hmeas_incr _) (measurableSet_singleton (z _))]
  -- Goal: μ (fI ⁻¹' {z}) = ∏ k : Fin n, μ (incr_k ⁻¹' {z k})
  -- Both sides factor through the FDD.
  -- Use hmap_fI to express LHS through the FDD
  have hLHS : μ (fI ⁻¹' {z}) = (μ.map fI) {z} :=
    (Measure.map_apply hmeas_fI (measurableSet_singleton z)).symm
  rw [hLHS, hmap_fI]
  -- LHS: ((FDD).map gI) {z}
  -- For each k in the product, factor through FDD too
  have hRHS_k : ∀ k : Fin n,
      μ ((fun ω : ∀ _ : ℝ≥0, ℕ => (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)) ⁻¹' {z k}) =
      (poissonProcessFDD rate I).map (fun f : (i : ↥I) → ℕ =>
        (f ⟨t k.succ, Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩⟩ : ℤ) -
        (f ⟨t k.castSucc, Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩⟩ : ℤ))
        {z k} := by
    intro k
    have hcomp : (fun ω : ∀ _ : ℝ≥0, ℕ => (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)) =
        (fun f : (i : ↥I) → ℕ =>
          (f ⟨t k.succ, Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩⟩ : ℤ) -
          (f ⟨t k.castSucc, Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩⟩ : ℤ)) ∘
        Finset.restrict I := by
      ext ω; simp [Finset.restrict]
    rw [hcomp, Set.preimage_comp]
    rw [← Measure.map_apply
      (Finset.measurable_restrict (X := fun _ : ℝ≥0 => ℕ) I) MeasurableSet.of_discrete]
    -- Goal: (μ.map I.restrict) (g ⁻¹' {z k}) = (FDD.map g) {z k}
    -- = ((μ.map I.restrict).map g) {z k} using Measure.map_apply
    rw [← Measure.map_apply Measurable.of_discrete (measurableSet_singleton (z k))]
    -- Goal: ((μ.map I.restrict).map g) {z k} = (FDD.map g) {z k}
    rw [hmarg]
  simp_rw [hRHS_k]
  -- Now both sides are expressed through poissonProcessFDD rate I.
  -- Unfold FDD as product measure map.
  unfold poissonProcessFDD
  haveI : DiscreteMeasurableSpace (Fin I.card → ℕ) :=
    MeasurableSingletonClass.toDiscreteMeasurableSpace
  -- LHS: ((Measure.pi incrMeasure).map incrToVal).map gI_all {z}
  --     = (Measure.pi incrMeasure).map (gI_all ∘ incrToVal) {z}
  --     = (Measure.pi incrMeasure) ((gI_all ∘ incrToVal) ⁻¹' {z})
  rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton z)]
  -- RHS: ∏ k, ((Measure.pi incrMeasure).map incrToVal).map gI_k {z k}
  --     = ∏ k, (Measure.pi incrMeasure).map (gI_k ∘ incrToVal) {z k}
  --     = ∏ k, (Measure.pi incrMeasure) ((gI_k ∘ incrToVal) ⁻¹' {z k})
  simp_rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete,
    Measure.map_apply Measurable.of_discrete (measurableSet_singleton (z _))]
  -- Goal: (Measure.pi incrMeasure) (h ⁻¹' {z}) = ∏ k, (Measure.pi incrMeasure) (h_k ⁻¹' {z k})
  -- where h = gI_all ∘ incrToVal and h_k = gI_k ∘ incrToVal
  -- Strategy: reduce to iIndepFun of ℤ-cast coordinate projections on product measure.
  -- Abbreviations for readability (using let to avoid unfolding issues)
  let incrMeasure' : Fin I.card → Measure ℕ :=
    fun k => poissonMeasure (rate * poissonProcessGap I k)
  let πμ := Measure.pi incrMeasure'
  let e := I.orderIsoOfFin rfl
  -- F_k k d = the k-th increment computed from increment vector d
  let F_k : Fin n → (Fin I.card → ℕ) → ℤ := fun k d =>
    ((fun f : (i : ↥I) → ℕ => fun j : Fin n =>
      (f ⟨t j.succ, Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, rfl⟩⟩ : ℤ) -
      (f ⟨t j.castSucc, Finset.mem_image.mpr ⟨j.castSucc, Finset.mem_univ _, rfl⟩⟩ : ℤ))
      (poissonProcessIncrToVal I d)) k
  -- q k = position of t k.succ in sorted enumeration
  let q : Fin n → Fin I.card :=
    fun k => e.symm ⟨t k.succ, Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩⟩
  -- Step 1: Show F_k k d = (d (q k) : ℤ) when t k.castSucc < t k.succ
  have hF_k_eq : ∀ k : Fin n, t k.castSucc < t k.succ →
      ∀ d : Fin I.card → ℕ, F_k k d = (d (q k) : ℤ) := by
    intro k hlt d
    show (poissonProcessIncrToVal I d ⟨t k.succ, _⟩ : ℤ) -
         (poissonProcessIncrToVal I d ⟨t k.castSucc, _⟩ : ℤ) = (d (q k) : ℤ)
    unfold poissonProcessIncrToVal poissonProcessReindex
    simp only [Function.comp_apply]
    set p := e.symm ⟨t k.castSucc, Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩⟩
    have hqp := orderIsoOfFin_symm_succ_of_lt n t hmono k hlt
    have hcum : poissonProcessCumSum d (q k) =
        poissonProcessCumSum d p + d (q k) := by
      have hqval : (q k).val = p.val + 1 := hqp
      -- q k = ⟨p.val + 1, _⟩ and we need CumSum(q k) = CumSum(p) + d(q k)
      -- This is poissonProcessCumSum_succ_sub d p (p.val + 1 < I.card)
      have hp_lt : p.val + 1 < I.card := by omega
      have := poissonProcessCumSum_succ_sub d p hp_lt
      -- this : poissonProcessCumSum d ⟨p.val + 1, hp_lt⟩ = ...
      -- We need to show that ⟨p.val + 1, hp_lt⟩ = q k
      have hq_eq_fin : q k = ⟨p.val + 1, hp_lt⟩ := Fin.ext hqval
      rwa [hq_eq_fin]
    rw [hcum]; push_cast; ring
  -- Step 2: Show F_k k d = 0 when t k.castSucc = t k.succ
  have hF_k_const : ∀ k : Fin n, t k.castSucc = t k.succ →
      ∀ d : Fin I.card → ℕ, F_k k d = 0 := by
    intro k heq d
    show (poissonProcessIncrToVal I d ⟨t k.succ, _⟩ : ℤ) -
         (poissonProcessIncrToVal I d ⟨t k.castSucc, _⟩ : ℤ) = 0
    -- Since t k.castSucc = t k.succ, the two terms are equal
    suffices heq' : poissonProcessIncrToVal I d
        ⟨t k.succ, Finset.mem_image.mpr ⟨k.succ, Finset.mem_univ _, rfl⟩⟩ =
      poissonProcessIncrToVal I d
        ⟨t k.castSucc, Finset.mem_image.mpr ⟨k.castSucc, Finset.mem_univ _, rfl⟩⟩ by
      simp [heq']
    congr 1; exact Subtype.ext heq.symm
  -- Step 3: q is injective on non-constant k's
  have hq_inj : ∀ k₁ k₂ : Fin n, t k₁.castSucc < t k₁.succ →
      t k₂.castSucc < t k₂.succ → q k₁ = q k₂ → k₁ = k₂ := by
    intro k₁ k₂ hlt₁ hlt₂ hq_eq
    have : (⟨t k₁.succ, _⟩ : ↥I) = ⟨t k₂.succ, _⟩ := e.symm.injective hq_eq
    have ht_eq : t k₁.succ = t k₂.succ := Subtype.ext_iff.mp this
    by_contra hne
    -- WLOG k₁ < k₂ (without using wlog tactic to avoid type issues)
    rcases lt_or_gt_of_ne hne with h12 | h21
    · -- k₁ < k₂ : then t k₁.succ ≤ t k₂.castSucc < t k₂.succ = t k₁.succ, contradiction
      have hle' : t k₁.succ ≤ t k₂.castSucc := hmono (by
        exact Fin.le_iff_val_le_val.mpr (by simp [Fin.val_succ]; omega))
      exact absurd (lt_of_le_of_lt (ht_eq ▸ hle') hlt₂) (lt_irrefl _)
    · -- k₂ < k₁ : symmetric
      have hle' : t k₂.succ ≤ t k₁.castSucc := hmono (by
        exact Fin.le_iff_val_le_val.mpr (by simp [Fin.val_succ]; omega))
      exact absurd (lt_of_le_of_lt (ht_eq.symm ▸ hle') hlt₁) (lt_irrefl _)
  -- The goal's LHS and RHS involve the same functions as F_k, just written differently.
  -- Show the combined preimage equals intersection of component preimages.
  -- Then rewrite the product's terms to use F_k.
  -- The preimage of {z} under the combined function = ⋂ k, F_k k ⁻¹' {z k}
  -- and the RHS products are definitionally equal to the F_k versions.
  -- So we just need to prove the independence product formula for F_k.
  suffices h : πμ (⋂ k : Fin n, F_k k ⁻¹' {z k}) = ∏ k : Fin n, πμ (F_k k ⁻¹' {z k}) by
    -- LHS: preimage of {z} = ⋂ k, F_k k ⁻¹' {z k}
    have hLHS_set : ((fun (f : (i : ↥I) → ℕ) (j : Fin n) =>
        (f ⟨t j.succ, Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, rfl⟩⟩ : ℤ) -
        (f ⟨t j.castSucc, Finset.mem_image.mpr ⟨j.castSucc, Finset.mem_univ _, rfl⟩⟩ : ℤ))
      ∘ poissonProcessIncrToVal I) ⁻¹' {z} = ⋂ k : Fin n, F_k k ⁻¹' {z k} := by
      ext d; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
        Function.comp_apply]
      exact ⟨fun h k => by rw [← h], fun h => funext h⟩
    rw [hLHS_set]; exact h
  -- Goal: πμ (⋂ k, F_k k ⁻¹' {z k}) = ∏ k, πμ (F_k k ⁻¹' {z k})
  -- Step 4: Split into constant and non-constant cases.
  by_cases h_const_empty : ∃ k : Fin n, t k.castSucc = t k.succ ∧ z k ≠ 0
  · -- Some constant k has z k ≠ 0, so F_k k ⁻¹' {z k} = ∅
    obtain ⟨k₀, hk₀_const, hk₀_ne⟩ := h_const_empty
    have hempty : F_k k₀ ⁻¹' {z k₀} = ∅ := by
      ext d; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]; exact fun h => hk₀_ne (h ▸ hF_k_const k₀ hk₀_const d)
    rw [show ⋂ k, F_k k ⁻¹' {z k} = ∅ from by
      rw [Set.eq_empty_iff_forall_notMem]
      intro d hd
      have : d ∈ F_k k₀ ⁻¹' {z k₀} := Set.mem_iInter.mp hd k₀
      rw [hempty] at this; exact this]
    rw [measure_empty]
    exact (Finset.prod_eq_zero (Finset.mem_univ k₀) (by rw [hempty, measure_empty])).symm
  · push_neg at h_const_empty
    -- All constant k have z k = 0
    have hconst_univ : ∀ k : Fin n, t k.castSucc = t k.succ → F_k k ⁻¹' {z k} = Set.univ := by
      intro k hk_const
      ext d; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rw [hF_k_const k hk_const d]; exact (h_const_empty k hk_const).symm
    -- Filter to non-constant indices
    set S' := Finset.univ.filter (fun k : Fin n => t k.castSucc < t k.succ)
    -- Intersection over univ = intersection over S'
    have hinter_eq : ⋂ k, F_k k ⁻¹' {z k} = ⋂ k ∈ S', F_k k ⁻¹' {z k} := by
      ext d; constructor
      · intro hd; exact Set.mem_iInter₂.mpr (fun k _ => Set.mem_iInter.mp hd k)
      · intro hd; apply Set.mem_iInter.mpr; intro k
        by_cases hlt : t k.castSucc < t k.succ
        · exact Set.mem_iInter₂.mp hd k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hlt⟩)
        · rw [hconst_univ k (le_antisymm (hmono (Fin.castSucc_le_succ k)) (not_lt.mp hlt))]
          exact Set.mem_univ d
    rw [hinter_eq]
    -- Product over univ = product over S'
    have hprod_eq : ∏ k, πμ (F_k k ⁻¹' {z k}) = ∏ k ∈ S', πμ (F_k k ⁻¹' {z k}) := by
      have hcompl : ∏ k ∈ Finset.univ.filter (fun (k : Fin n) => ¬t k.castSucc < t k.succ),
          πμ (F_k k ⁻¹' {z k}) = 1 := by
        apply Finset.prod_eq_one
        intro k hk; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
        rw [hconst_univ k (le_antisymm (hmono (Fin.castSucc_le_succ k)) hk), measure_univ]
      have h_split := Finset.prod_filter_mul_prod_filter_not Finset.univ
        (fun (k : Fin n) => t k.castSucc < t k.succ) (fun k => πμ (F_k k ⁻¹' {z k}))
      -- h_split : (∏ k with ..., ...) * (∏ k with ¬..., ...) = ∏ k ∈ univ, ...
      rw [hcompl, mul_one] at h_split
      -- h_split : ∏ k with ..., ... = ∏ k ∈ univ, ...
      exact h_split.symm
    rw [hprod_eq]
    -- Now both sides involve only non-constant k's.
    -- Rewrite preimages using hF_k_eq
    have hpre_cast : ∀ k ∈ S', F_k k ⁻¹' {z k} =
        (fun d : Fin I.card → ℕ => (d (q k) : ℤ)) ⁻¹' {z k} := by
      intro k hk
      have hlt : t k.castSucc < t k.succ := (Finset.mem_filter.mp hk).2
      ext d; simp only [Set.mem_preimage, Set.mem_singleton_iff]; rw [hF_k_eq k hlt d]
    -- coordinate projections are iIndepFun under Measure.pi:
    haveI : ∀ i, IsProbabilityMeasure (incrMeasure' i) := fun i => inferInstance
    have hcast_indep : iIndepFun (fun i (d : Fin I.card → ℕ) => (d i : ℤ)) πμ :=
      (iIndepFun_pi (fun i => aemeasurable_id)).comp
        (fun _ => Nat.cast) (fun _ => Measurable.of_discrete)
    -- q is injective on S'
    have hq_injOn : Set.InjOn q ↑S' := by
      intro k₁ hk₁ k₂ hk₂ hq_eq
      exact hq_inj k₁ k₂ (Finset.mem_coe.mp hk₁ |> Finset.mem_filter.mp |>.2)
        (Finset.mem_coe.mp hk₂ |> Finset.mem_filter.mp |>.2) hq_eq
    -- Define T = S'.image q ⊆ Fin I.card, and sets' extending sets from q(S')
    set T := S'.image q
    classical
    let sets' : Fin I.card → Set ℤ :=
      Function.extend (fun k : ↥S' => q k.val) (fun k : ↥S' => {z k.val}) (fun _ => Set.univ)
    have hinj_sub : Function.Injective (fun k : ↥S' => q k.val) := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ h; exact Subtype.ext (hq_injOn ha hb h)
    have hsets'_apply : ∀ k ∈ S', sets' (q k) = {z k} := by
      intro k hk
      exact hinj_sub.extend_apply (fun k : ↥S' => {z k.val}) (fun _ => Set.univ) ⟨k, hk⟩
    -- Product formula from hcast_indep on T
    have hindep_T := hcast_indep.measure_inter_preimage_eq_mul T
      (fun (i : Fin I.card) _ => MeasurableSet.of_discrete (s := sets' i))
    -- LHS: rewrite intersection
    have hLHS : ⋂ k ∈ S', F_k k ⁻¹' {z k} =
        ⋂ i ∈ T, (fun d : Fin I.card → ℕ => (d i : ℤ)) ⁻¹' sets' i := by
      rw [show ⋂ k ∈ S', F_k k ⁻¹' {z k} =
          ⋂ k ∈ S', (fun d : Fin I.card → ℕ => (d (q k) : ℤ)) ⁻¹' sets' (q k) from by
        apply Set.iInter₂_congr; intro k hk
        rw [hpre_cast k hk, hsets'_apply k hk]]
      -- ⋂ k ∈ S', g (q k) = ⋂ i ∈ S'.image q, g i
      let g : Fin I.card → Set (Fin I.card → ℕ) :=
        fun i => (fun d : Fin I.card → ℕ => (d i : ℤ)) ⁻¹' sets' i
      show ⋂ k ∈ S', g (q k) = ⋂ i ∈ T, g i
      exact (Finset.set_biInter_finset_image).symm
    -- RHS: rewrite product
    have hRHS : ∏ k ∈ S', πμ (F_k k ⁻¹' {z k}) =
        ∏ i ∈ T, πμ ((fun d : Fin I.card → ℕ => (d i : ℤ)) ⁻¹' sets' i) := by
      -- Step 1: rewrite each summand using hpre_cast and hsets'_apply
      have h1 : ∀ k ∈ S', πμ (F_k k ⁻¹' {z k}) =
          πμ ((fun d : Fin I.card → ℕ => (d (q k) : ℤ)) ⁻¹' sets' (q k)) := by
        intro k hk; rw [hpre_cast k hk, hsets'_apply k hk]
      rw [Finset.prod_congr rfl h1]
      -- Step 2: apply Finset.prod_image
      let g : Fin I.card → ℝ≥0∞ :=
        fun i => πμ ((fun d : Fin I.card → ℕ => (d i : ℤ)) ⁻¹' sets' i)
      show ∏ k ∈ S', g (q k) = ∏ i ∈ T, g i
      exact (Finset.prod_image hq_injOn).symm
    rw [hLHS, hRHS]
    exact hindep_T

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
              ┌──────────┼──────────┐
              v          v          v
          start_zero  indep_incr  incr_poisson
          (proved!)   (proved!)   (proved!)
```
-/
theorem exists_poissonProcess (rate : ℝ≥0) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (N : ℝ≥0 → Ω → ℕ),
      IsPoissonProcess N rate μ := by
  -- Canonical path space with Kolmogorov extension measure
  refine ⟨∀ _ : ℝ≥0, ℕ, inferInstance,
    (poissonProjectiveFamily rate).kolmogorovExtension,
    fun t ω => if t = 0 then 0 else ω t, ?_⟩
  set μ := (poissonProjectiveFamily rate).kolmogorovExtension
  constructor
  · -- start_zero
    ext ω; simp
  · -- indep_increments
    -- Goal: HasIndependentIncrements (fun t ω => (↑(if t = 0 then 0 else ω t) : ℤ)) μ
    intro n t hmono
    -- Step 1: Use a.e. equality to replace ↑(if t=0 then 0 else ω t) with ↑(ω t)
    -- Since ω 0 = 0 μ-a.e., the two formulations agree a.e.
    have hzero_ae := kolmogorovExtension_coord_zero_ae rate
    -- For each k, the k-th increment agrees a.e. with the simpler expression
    have hae : ∀ k : Fin n,
        increment (fun (s : ℝ≥0) (ω : ∀ _ : ℝ≥0, ℕ) => (↑(if s = 0 then 0 else ω s) : ℤ))
          (t k.castSucc) (t k.succ) =ᵐ[μ]
        (fun ω => (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)) := by
      intro k
      filter_upwards [hzero_ae] with ω hω0
      simp only [increment_apply]
      congr 1
      · by_cases h : t k.succ = 0 <;> simp [h, hω0]
      · by_cases h : t k.castSucc = 0 <;> simp [h, hω0]
    -- Use iIndepFun_congr to reduce to simpler form
    suffices h : iIndepFun (fun k : Fin n => fun ω : ∀ _ : ℝ≥0, ℕ =>
        (ω (t k.succ) : ℤ) - (ω (t k.castSucc) : ℤ)) μ from
      (iIndepFun_congr hae).mpr h
    -- Step 2: Prove iIndepFun of (fun k ω => (ω(t(k+1)) : ℤ) - (ω(t(k)) : ℤ))
    -- Use the FDD product structure: the Kolmogorov extension restricted to any finite
    -- set of times I is a product measure (Measure.pi of Poisson marginals) pushed through
    -- a cumulative sum bijection. Increments of the process correspond to coordinate
    -- projections on the product measure, so they're independent.
    exact kolmogorovExtension_indep_increments rate n t hmono
  · -- increment_poisson
    intro s h
    -- Goal: μ.map (fun ω => (if s+h = 0 then 0 else ω (s+h)) - (if s = 0 then 0 else ω s))
    --     = poissonMeasure (rate * h)
    by_cases hh : h = 0
    · -- Case h = 0: difference is always 0
      -- The function is fun ω => N(s+0)(ω) - N(s)(ω) = 0 for all ω
      have hconst : (fun ω : ∀ _ : ℝ≥0, ℕ =>
          (if s + h = 0 then 0 else ω (s + h)) - (if s = 0 then 0 else ω s)) =
          fun _ => (0 : ℕ) := by subst hh; ext ω; simp
      rw [hconst, hh, mul_zero]
      -- μ.map (fun _ => 0) = poissonMeasure 0
      -- Use kolmogorovExtension_map_coord for t = 0
      -- poissonMeasure (rate * 0) = poissonMeasure 0
      -- μ.map (fun _ => 0) = μ.map (fun ω => ω 0) composed with (fun _ => 0)
      -- Actually, just use map_const + show poissonMeasure 0 = Dirac 0
      rw [Measure.map_const _ (0 : ℕ), measure_univ, one_smul]
      -- Dirac 0 = poissonMeasure 0
      -- Both are probability measures; agree on singletons
      symm; apply Measure.ext_of_singleton; intro n
      rw [show poissonMeasure 0 = (poissonPMF 0).toMeasure from rfl,
        PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
      rw [Measure.dirac_apply' 0 (measurableSet_singleton n)]
      -- Goal: poissonPMF 0 n = Set.indicator {0} 1 n
      -- poissonPMF 0 n = ENNReal.ofReal (poissonPMFReal 0 n) definitionally
      change ENNReal.ofReal (poissonPMFReal 0 n) = _
      by_cases hn : n = 0
      · subst hn; simp [poissonPMFReal]
      · simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
        simp [poissonPMFReal, zero_pow (by omega : n ≠ 0)]
        exact fun h => hn h.symm
    · -- Case h ≠ 0
      by_cases hs : s = 0
      · -- Subcase s = 0: N(0+h) ω - N(0) ω = ω h - 0 = ω h
        -- Show the function equals fun ω => ω h
        have hfun : (fun ω : ∀ _ : ℝ≥0, ℕ =>
            (if s + h = 0 then 0 else ω (s + h)) - (if s = 0 then 0 else ω s)) =
            fun ω => ω h := by
          ext ω; simp [hs, hh]
        rw [hfun]
        exact kolmogorovExtension_map_coord rate h
      · -- Subcase s ≠ 0, h ≠ 0: N(s+h) ω - N s ω = ω(s+h) - ω s
        have hsh_ne : s + h ≠ 0 := by positivity
        have hfun : (fun ω : ∀ _ : ℝ≥0, ℕ =>
            (if s + h = 0 then 0 else ω (s + h)) - (if s = 0 then 0 else ω s)) =
            fun ω => ω (s + h) - ω s := by
          ext ω; simp [hs, hsh_ne]
        rw [hfun]
        exact kolmogorovExtension_map_diff rate s h hh

end ProbabilityTheory
