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
          (proved!)   (sorry)     (sorry)
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
  }

end ProbabilityTheory
