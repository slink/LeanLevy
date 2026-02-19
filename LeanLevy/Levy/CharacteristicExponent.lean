/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.LevyProcess
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Local Characteristic Exponent

The characteristic exponent of a Lévy process requires taking `Complex.log` of the characteristic
function. Since `Complex.log` has a branch cut on the negative real axis, we construct the
exponent locally near `ξ = 0` where the characteristic function is near 1 (and hence in mathlib's
`slitPlane`).

## Design

We use a **general framework + Lévy specialisation**:

1. `LocalLog` defines the local log construction for any continuous function `φ` with `φ(0) = 1`.
2. `ProbabilityTheory.IsLevyProcess` applies it to the time-1 characteristic function.

## Main definitions

* `LocalLog.goodDomain` — the preimage of `slitPlane` under `φ`, where `Complex.log ∘ φ` is
  well-defined and continuous.
* `LocalLog.localCharExponent` — `Complex.log ∘ φ`.
* `IsLevyProcess.levyGoodDomain` — the good domain for the time-1 characteristic function.
* `IsLevyProcess.levyLocalCharExponent` — the local characteristic exponent.

## Main results

* `LocalLog.continuousOn_localCharExponent` — `log ∘ φ` is continuous on the good domain.
* `LocalLog.exists_ball_subset_goodDomain` — an open ball around 0 lies in the good domain.
* `IsLevyProcess.continuousOn_levyLocalCharExponent` — continuity of the local exponent.
-/

open MeasureTheory Complex Filter Topology
open scoped NNReal

set_option linter.unusedSectionVars false

/-! ### Continuity of the characteristic function -/

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {ν : Measure E} [IsFiniteMeasure ν]

/-- The characteristic function of a finite measure is continuous. -/
theorem continuous_charFun : Continuous (charFun ν) := by
  show Continuous (fun ξ => ∫ x, cexp (↑(@inner ℝ E _ x ξ) * I) ∂ν)
  apply continuous_of_dominated
  · intro ξ
    exact (by fun_prop : Measurable (fun x => cexp (↑(@inner ℝ E _ x ξ) * I))).aestronglyMeasurable
  · intro ξ; apply Eventually.of_forall; intro x
    simp only [Complex.norm_exp_ofReal_mul_I]; exact le_refl _
  · exact integrable_const 1
  · apply Eventually.of_forall; intro x
    exact (by fun_prop : Continuous (fun ξ => cexp (↑(@inner ℝ E _ x ξ) * I)))

end MeasureTheory

/-! ### General LocalLog framework -/

namespace LocalLog

variable {E : Type*} [TopologicalSpace E] [Zero E]

/-- The good domain where `φ` lands in the slit plane (avoids the branch cut). -/
def goodDomain (φ : E → ℂ) : Set E := φ ⁻¹' Complex.slitPlane

theorem mem_goodDomain_zero {φ : E → ℂ} (hφ_zero : φ 0 = 1) :
    (0 : E) ∈ goodDomain φ := by
  simp [goodDomain, Set.mem_preimage, hφ_zero, Complex.one_mem_slitPlane]

theorem isOpen_goodDomain {φ : E → ℂ} (hφ_cont : Continuous φ) :
    IsOpen (goodDomain φ) :=
  Complex.isOpen_slitPlane.preimage hφ_cont

/-- The local characteristic exponent: `Complex.log ∘ φ`. -/
noncomputable def localCharExponent (φ : E → ℂ) (ξ : E) : ℂ :=
  Complex.log (φ ξ)

theorem continuousOn_localCharExponent {φ : E → ℂ} (hφ_cont : Continuous φ) :
    ContinuousOn (localCharExponent φ) (goodDomain φ) :=
  hφ_cont.continuousOn.clog (fun _ hx => hx)

section MetricBall
variable {E : Type*} [SeminormedAddCommGroup E]

theorem charFun_near_one {φ : E → ℂ} (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    Tendsto φ (𝓝 0) (𝓝 1) := by
  rw [← hφ_zero]; exact hφ_cont.continuousAt.tendsto

theorem exists_ball_subset_goodDomain {φ : E → ℂ}
    (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    ∃ ε > 0, Metric.ball (0 : E) ε ⊆ goodDomain φ :=
  Metric.isOpen_iff.mp (isOpen_goodDomain hφ_cont) 0 (mem_goodDomain_zero hφ_zero)

end MetricBall

end LocalLog

/-! ### Density extension from rationals to reals

A general-purpose ceiling-sequence construction and density lemma for extending
equality from ℕ/ℕ rationals in `ℝ≥0` to all of `ℝ≥0`, given right-continuity
on one side and continuity on the other. Independent of Lévy processes. -/

namespace DensityExtension

open Filter Topology

/-- Ceiling approximation from above: `ceilApprox t m = ⌈t * (m+1)⌉₊ / (m+1)` as `ℝ≥0`.
This gives a sequence of ℕ/ℕ rationals converging to `t` from above. -/
noncomputable def ceilApprox (t : ℝ≥0) (m : ℕ) : ℝ≥0 :=
  (⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)

/-- The ceiling approximation is always `≥ t`. -/
theorem ceilApprox_ge (t : ℝ≥0) (m : ℕ) : t ≤ ceilApprox t m :=
  NNReal.coe_le_coe.mp (by
    show (t : ℝ) ≤ _
    simp only [ceilApprox]
    rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < ↑(m + 1))).mpr (Nat.le_ceil _))

/-- Real coercion of `ceilApprox`. -/
theorem ceilApprox_coe (t : ℝ≥0) (m : ℕ) :
    (ceilApprox t m : ℝ) = ↑⌈(t : ℝ) * ↑(m + 1)⌉₊ / ↑(m + 1) := by
  show NNReal.toReal _ = _
  simp only [ceilApprox]
  rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]

/-- The ceiling approximation converges to `t`. -/
theorem tendsto_ceilApprox (t : ℝ≥0) :
    Tendsto (ceilApprox t) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have hf_ge : ∀ m : ℕ, (t : ℝ) ≤ (ceilApprox t m : ℝ) :=
    fun m => NNReal.coe_le_coe.mpr (ceilApprox_ge t m)
  have hf_le : ∀ m : ℕ, (ceilApprox t m : ℝ) ≤ (t : ℝ) + 1 / ↑(m + 1) := fun m => by
    rw [ceilApprox_coe]
    have hm_pos : (0 : ℝ) < ↑(m + 1) := by positivity
    calc (↑⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ) / ↑(m + 1)
        ≤ ((t : ℝ) * ↑(m + 1) + 1) / ↑(m + 1) :=
          div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hm_pos.le
      _ = (t : ℝ) + 1 / ↑(m + 1) := by
          rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hm_pos)]
  have h_upper : Tendsto (fun m : ℕ => (t : ℝ) + 1 / ↑(m + 1)) atTop (𝓝 (t : ℝ)) := by
    have h0 : Tendsto (fun m : ℕ => (1 : ℝ) / (↑(m + 1) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    have := (tendsto_const_nhds (x := (t : ℝ))).add h0
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper hf_ge hf_le

/-- The ceiling approximation converges to `t` within `𝓝[≥] t`. -/
theorem tendsto_ceilApprox_nhdsWithin_Ici (t : ℝ≥0) :
    Tendsto (ceilApprox t) atTop (𝓝[≥] t) :=
  tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_ceilApprox t, Eventually.of_forall fun m => ceilApprox_ge t m⟩

/-- Each `ceilApprox t m` is a ratio of natural numbers with positive denominator. -/
theorem ceilApprox_isRat (t : ℝ≥0) (m : ℕ) :
    ceilApprox t m = (⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0) :=
  rfl

set_option maxHeartbeats 800000 in
/-- If `f` is right-continuous, `g` is continuous, both from `ℝ≥0` to a T₂ space, and
they agree on all ℕ/ℕ rationals `k/(n+1)`, then `f = g` everywhere. -/
theorem eq_of_rightCts_of_continuous_of_eqOn_ratNNReal {β : Type*}
    [TopologicalSpace β] [T2Space β]
    {f g : ℝ≥0 → β}
    (hf : ∀ t, ContinuousWithinAt f (Set.Ici t) t)
    (hg : Continuous g)
    (heq : ∀ (k n : ℕ), f ((k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)) =
      g ((k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0))) :
    f = g := by
  ext t
  -- ceilApprox gives a sequence of k/(m+1) rationals ≥ t converging to t
  have htends_within := tendsto_ceilApprox_nhdsWithin_Ici t
  have htends := tendsto_ceilApprox t
  have hf_lim : Tendsto (f ∘ ceilApprox t) atTop (𝓝 (f t)) :=
    Filter.Tendsto.comp (hf t) htends_within
  have hg_lim : Tendsto (g ∘ ceilApprox t) atTop (𝓝 (g t)) :=
    Filter.Tendsto.comp (hg.continuousAt (x := t)) htends
  have heq_seq : f ∘ ceilApprox t = g ∘ ceilApprox t := by
    ext m; exact heq ⌈(t : ℝ) * ↑(m + 1)⌉₊ m
  rw [heq_seq] at hf_lim
  exact tendsto_nhds_unique hf_lim hg_lim

end DensityExtension

/-! ### Lévy process specialisation -/

namespace ProbabilityTheory.IsLevyProcess

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The time-1 characteristic function is continuous. -/
theorem continuous_charFun_one (_hX : ∀ t, Measurable (X t)) :
    Continuous (fun ξ => charFun (μ.map (X 1)) ξ) := by
  haveI : IsFiniteMeasure (μ.map (X 1)) := Measure.isFiniteMeasure_map μ (X 1)
  exact MeasureTheory.continuous_charFun

/-- The time-1 characteristic function equals 1 at `ξ = 0`. -/
theorem charFun_one_zero (_h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    charFun (μ.map (X 1)) (0 : E) = 1 := by
  haveI : IsProbabilityMeasure (μ.map (X 1)) :=
    Measure.isProbabilityMeasure_map (hX 1).aemeasurable
  simp [charFun_zero]

/-- `Tendsto (charFun(μ.map(X 1))) (𝓝 0) (𝓝 1)`. -/
theorem charFun_one_near_one (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    Tendsto (fun ξ => charFun (μ.map (X 1)) ξ) (𝓝 0) (𝓝 1) :=
  LocalLog.charFun_near_one (continuous_charFun_one hX) (charFun_one_zero h hX)

/-- The good domain for the time-1 characteristic function. -/
def levyGoodDomain (_h : IsLevyProcess X μ) (_hX : ∀ t, Measurable (X t)) : Set E :=
  LocalLog.goodDomain (fun ξ => charFun (μ.map (X 1)) ξ)

theorem mem_levyGoodDomain_zero (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    (0 : E) ∈ h.levyGoodDomain hX :=
  LocalLog.mem_goodDomain_zero (charFun_one_zero h hX)

theorem isOpen_levyGoodDomain (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    IsOpen (h.levyGoodDomain hX) :=
  LocalLog.isOpen_goodDomain (continuous_charFun_one hX)

/-- The local characteristic exponent of the Lévy process. -/
noncomputable def levyLocalCharExponent
    (_h : IsLevyProcess X μ) (_hX : ∀ t, Measurable (X t)) : E → ℂ :=
  LocalLog.localCharExponent (fun ξ => charFun (μ.map (X 1)) ξ)

theorem continuousOn_levyLocalCharExponent (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    ContinuousOn (h.levyLocalCharExponent hX) (h.levyGoodDomain hX) :=
  LocalLog.continuousOn_localCharExponent (continuous_charFun_one hX)

/-! ### Semigroup properties

All derived as short corollaries of `charFun_eq_exp_mul`. -/

section Semigroup

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Multiplicativity of the characteristic function: `φ(s+t)(ξ) = φ(s)(ξ) · φ(t)(ξ)`. -/
theorem charFun_marginal_mul (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (s t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X (s + t))) ξ =
      charFun (μ.map (X s)) ξ * charFun (μ.map (X t)) ξ := by
  rw [h.charFun_eq_exp_mul hX (s + t) ξ, h.charFun_eq_exp_mul hX s ξ,
      h.charFun_eq_exp_mul hX t ξ, ← exp_add]
  congr 1; push_cast [NNReal.coe_add]; ring

/-- Power formula: `φ(n)(ξ) = φ(1)(ξ)^n`. -/
@[simp]
theorem charFun_marginal_pow' (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (n : ℕ) (ξ : E) :
    charFun (μ.map (X (n : ℝ≥0))) ξ = (charFun (μ.map (X 1)) ξ) ^ n := by
  rw [h.charFun_eq_exp_mul hX n ξ, h.charFun_eq_exp_mul hX 1 ξ, ← exp_nat_mul]
  congr 1; push_cast; ring

/-- Natural multiplication formula: `φ(n·s)(ξ) = φ(s)(ξ)^n`. -/
theorem charFun_marginal_nat_mul (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (n : ℕ) (s : ℝ≥0) (ξ : E) :
    charFun (μ.map (X ((n : ℝ≥0) * s))) ξ = (charFun (μ.map (X s)) ξ) ^ n := by
  rw [h.charFun_eq_exp_mul hX ((n : ℝ≥0) * s) ξ, h.charFun_eq_exp_mul hX s ξ, ← exp_nat_mul]
  congr 1; push_cast; ring

/-- Rational power formula: `φ(k/n)(ξ) = φ(1/n)(ξ)^k`. -/
theorem charFun_marginal_rat_pow (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (k n : ℕ) (ξ : E) :
    charFun (μ.map (X ((k : ℝ≥0) / (n : ℝ≥0)))) ξ =
      (charFun (μ.map (X ((1 : ℝ≥0) / (n : ℝ≥0)))) ξ) ^ k := by
  rw [h.charFun_eq_exp_mul hX _ ξ, h.charFun_eq_exp_mul hX _ ξ, ← exp_nat_mul]
  congr 1; push_cast; ring

/-! ### Characteristic exponent at origin -/

/-- The characteristic exponent vanishes at `ξ = 0`. -/
theorem charExponent_zero (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    h.charExponent (0 : E) = 0 := by
  simp only [charExponent]
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have : charFun (μ.map (X t)) (0 : E) = 1 := by
    haveI : IsProbabilityMeasure (μ.map (X t)) :=
      Measure.isProbabilityMeasure_map (hX t).aemeasurable
    simp [charFun_zero]
  rw [this, Complex.log_one, zero_div]

/-! ### Local-global exponent connection -/

set_option maxHeartbeats 400000 in
/-- On a ball around the origin, the local characteristic exponent (via `Complex.log`)
agrees with the characteristic exponent (defined as a limit). The proof uses a power-of-2
induction with a connectedness argument: at each step, a continuous square root on a
connected domain that equals 1 at the origin must be identically 1. -/
theorem levyLocalCharExponent_eq_charExponent
    (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε,
      h.levyLocalCharExponent hX ξ = h.charExponent ξ := by
  obtain ⟨ε, hε_pos, hball⟩ := LocalLog.exists_ball_subset_goodDomain
    (continuous_charFun_one hX) (charFun_one_zero h hX)
  refine ⟨ε, hε_pos, fun ξ hξ => ?_⟩
  set ψ := h.levyLocalCharExponent hX
  set B := Metric.ball (0 : E) ε
  set G := h.levyGoodDomain hX
  have hψ_cont : ContinuousOn ψ G := h.continuousOn_levyLocalCharExponent hX
  have hG_open : IsOpen G := h.isOpen_levyGoodDomain hX
  have hB_preconn : IsPreconnected B := Metric.isPreconnected_ball
  have h0B : (0 : E) ∈ B := Metric.mem_ball_self hε_pos
  have hψ0 : ψ 0 = 0 := by
    show Complex.log (charFun (μ.map (X 1)) 0) = 0
    rw [charFun_one_zero h hX, Complex.log_one]
  -- Key claim by induction: charFun(X(1/2^n))(ξ') = exp(ψ(ξ')/2^n) on the ball
  suffices key : ∀ n : ℕ, ∀ ξ' ∈ B,
      charFun (μ.map (X ((1 : ℝ≥0) / (2 : ℝ≥0) ^ n))) ξ' =
        exp (ψ ξ' / (2 : ℂ) ^ n) by
    -- From key + charFun_eq_exp_mul: exp((Ψ(ξ)-ψ(ξ))/2^n) = 1 for all n
    have hexp_eq : ∀ n : ℕ,
        exp ((h.charExponent ξ - ψ ξ) / (2 : ℂ) ^ n) = 1 := by
      intro n
      have h1 := key n ξ hξ
      have h2 := h.charFun_eq_exp_mul hX ((1 : ℝ≥0) / (2 : ℝ≥0) ^ n) ξ
      rw [h1] at h2
      rw [sub_div, exp_sub, div_eq_one_iff_eq (exp_ne_zero _)]
      convert h2.symm using 2; push_cast; ring
    -- d/2^n ∈ 2πiℤ for all n ⟹ 2^n ∣ k₀ for all n ⟹ k₀ = 0
    set d := h.charExponent ξ - ψ ξ
    obtain ⟨k₀, hk₀⟩ := Complex.exp_eq_one_iff.mp (hexp_eq 0)
    simp only [pow_zero, div_one] at hk₀
    -- hk₀ : d = ↑k₀ * (2 * ↑Real.pi * I)
    have hpow_dvd : ∀ n : ℕ, (2 : ℤ) ^ n ∣ k₀ := by
      intro n
      obtain ⟨m_n, hm_n⟩ := Complex.exp_eq_one_iff.mp (hexp_eq n)
      have h2piI_ne : (2 * ↑Real.pi * I : ℂ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
      have h2n_ne : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
      have hcast : (↑k₀ : ℂ) = ↑m_n * (2 : ℂ) ^ n := by
        apply mul_right_cancel₀ h2piI_ne
        calc (↑k₀ : ℂ) * (2 * ↑Real.pi * I)
            = d := hk₀.symm
          _ = d / (2 : ℂ) ^ n * (2 : ℂ) ^ n := (div_mul_cancel₀ d h2n_ne).symm
          _ = ↑m_n * (2 * ↑Real.pi * I) * (2 : ℂ) ^ n := by rw [hm_n]
          _ = ↑m_n * (2 : ℂ) ^ n * (2 * ↑Real.pi * I) := by ring
      refine ⟨m_n, ?_⟩
      have : k₀ = m_n * (2 : ℤ) ^ n := by
        have : (↑k₀ : ℂ) = (↑(m_n * (2 : ℤ) ^ n) : ℂ) := by push_cast; exact hcast
        exact_mod_cast this
      linarith [mul_comm m_n ((2 : ℤ) ^ n)]
    have hk₀_zero : k₀ = 0 := by
      by_contra hne
      have hpos : 0 < k₀.natAbs := Int.natAbs_pos.mpr hne
      have hnat_dvd : 2 ^ k₀.natAbs ∣ k₀.natAbs := by
        have h := Int.natAbs_dvd_natAbs.mpr (hpow_dvd k₀.natAbs)
        simp only [Int.natAbs_pow] at h
        exact h
      exact absurd (Nat.le_of_dvd hpos hnat_dvd) (not_le.mpr k₀.natAbs.lt_two_pow_self)
    have hd_zero : h.charExponent ξ - ψ ξ = 0 := by
      show d = 0; rw [hk₀, hk₀_zero, Int.cast_zero, zero_mul]
    exact (sub_eq_zero.mp hd_zero).symm
  -- Prove key claim by induction on n
  intro n
  induction n with
  | zero =>
    intro ξ' hξ'
    simp only [pow_zero, div_one]
    exact (Complex.exp_log (charFun_marginal_ne_zero h hX 1 ξ')).symm
  | succ n ih =>
    intro ξ' hξ'
    -- Define f(η) = charFun(X(1/2^{n+1}))(η) * exp(-ψ(η)/2^{n+1}), show f²=1, f(0)=1
    set f : E → ℂ := fun η =>
      charFun (μ.map (X ((1 : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1)))) η *
        exp (-(ψ η / (2 : ℂ) ^ (n + 1)))
    -- f is continuous on G
    have hf_cont : ContinuousOn f G := by
      apply ContinuousOn.mul
      · exact (MeasureTheory.continuous_charFun (ν :=
            μ.map (X ((1 : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1))))).continuousOn.mono
          (Set.subset_univ _)
      · exact (hψ_cont.div_const _).neg.cexp
    -- f² = 1 on B (using charFun_marginal_mul and ih)
    have hf_sq : ∀ η ∈ B, f η ^ 2 = 1 := by
      intro η hη
      have h_sq_cf : charFun (μ.map (X ((1 : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1)))) η ^ 2 =
          charFun (μ.map (X ((1 : ℝ≥0) / (2 : ℝ≥0) ^ n))) η := by
        rw [h.charFun_eq_exp_mul hX _ η, h.charFun_eq_exp_mul hX _ η, sq, ← exp_add]
        congr 1; push_cast; ring
      simp only [f, mul_pow, ← exp_nat_mul]
      rw [h_sq_cf, ih η hη]
      have : (2 : ℕ) * -(ψ η / (2 : ℂ) ^ (n + 1)) = -(ψ η / (2 : ℂ) ^ n) := by
        rw [show (2 : ℂ) ^ (n + 1) = 2 * (2 : ℂ) ^ n from by ring]; field_simp; ring
      rw [this, exp_neg, mul_inv_cancel₀ (exp_ne_zero _)]
    -- f(0) = 1
    set t_half := (1 : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1) with ht_half_def
    have hf_zero : f 0 = 1 := by
      simp only [f, hψ0, zero_div, neg_zero, exp_zero, mul_one]
      change charFun (μ.map (X t_half)) 0 = 1
      haveI : IsProbabilityMeasure (μ.map (X t_half)) :=
        Measure.isProbabilityMeasure_map (hX t_half).aemeasurable
      simp [charFun_zero]
    -- Connectedness: f ∈ {1,-1}, continuous on B ⊆ G (open), connected → f ≡ 1
    suffices hf1 : f ξ' = 1 by
      have hmul : charFun (μ.map (X ((1 : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1)))) ξ' *
          exp (-(ψ ξ' / (2 : ℂ) ^ (n + 1))) = 1 := hf1
      have : charFun (μ.map (X ((1 : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1)))) ξ' =
          charFun (μ.map (X ((1 : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1)))) ξ' *
          (exp (-(ψ ξ' / (2 : ℂ) ^ (n + 1))) * exp (ψ ξ' / (2 : ℂ) ^ (n + 1))) := by
        rw [← exp_add, neg_add_cancel, exp_zero, mul_one]
      rw [this, ← mul_assoc, hmul, one_mul]
    by_contra hne
    have hf_val : f ξ' = -1 := by
      have hfact : (f ξ' - 1) * (f ξ' + 1) = 0 := by
        have : (f ξ' - 1) * (f ξ' + 1) = f ξ' ^ 2 - 1 := by ring
        rw [this, hf_sq ξ' hξ', sub_self]
      exact (mul_eq_zero.mp hfact).resolve_left (sub_ne_zero.mpr hne) |>
        eq_neg_of_add_eq_zero_left
    -- Use IsPreconnected of B with open sets U = f⁻¹(B(1,1)) ∩ G, V = f⁻¹(B(-1,1)) ∩ G
    set U := G ∩ f ⁻¹' Metric.ball (1 : ℂ) 1
    set V := G ∩ f ⁻¹' Metric.ball (-1 : ℂ) 1
    have hU_open : IsOpen U := hf_cont.isOpen_inter_preimage hG_open Metric.isOpen_ball
    have hV_open : IsOpen V := hf_cont.isOpen_inter_preimage hG_open Metric.isOpen_ball
    have hBUV : B ⊆ U ∪ V := by
      intro η hη
      have hηG := hball hη
      have hη_sq := hf_sq η hη
      have hfact : (f η - 1) * (f η + 1) = 0 := by
        have : (f η - 1) * (f η + 1) = f η ^ 2 - 1 := by ring
        rw [this, hη_sq, sub_self]
      rcases mul_eq_zero.mp hfact with h1 | h2
      · left; exact ⟨hηG, by rw [Set.mem_preimage, sub_eq_zero.mp h1]; exact Metric.mem_ball_self one_pos⟩
      · right; exact ⟨hηG, by rw [Set.mem_preimage, eq_neg_of_add_eq_zero_left h2]; simp [Metric.mem_ball]⟩
    have hBU : (B ∩ U).Nonempty :=
      ⟨0, h0B, hball h0B, by rw [Set.mem_preimage, hf_zero]; exact Metric.mem_ball_self one_pos⟩
    have hBV : (B ∩ V).Nonempty :=
      ⟨ξ', hξ', hball hξ', by rw [Set.mem_preimage, hf_val]; simp [Metric.mem_ball]⟩
    obtain ⟨z, hzB, hzU, hzV⟩ := hB_preconn U V hU_open hV_open hBUV hBU hBV
    -- B(1,1) ∩ B(-1,1) = ∅ by triangle inequality: contradiction
    have hz1 : dist (f z) 1 < 1 := hzU.2
    have hz2 : dist (f z) (-1) < 1 := hzV.2
    linarith [dist_triangle_left (1 : ℂ) (-1) (f z),
      show dist (1 : ℂ) (-1) = 2 from by simp [dist_eq_norm]; norm_num]

/-! ### Complex power formulation -/

/-- On a ball around the origin, the characteristic function satisfies the complex power law:
`φ_t(ξ) = φ₁(ξ) ^ (↑t : ℂ)` for all `t : ℝ≥0`. -/
theorem charFun_marginal_cpow (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε, ∀ t : ℝ≥0,
      charFun (μ.map (X t)) ξ = (charFun (μ.map (X 1)) ξ) ^ (↑(t : ℝ) : ℂ) := by
  obtain ⟨ε, hε, hball⟩ := h.levyLocalCharExponent_eq_charExponent hX
  refine ⟨ε, hε, fun ξ hξ t => ?_⟩
  have hne : charFun (μ.map (X 1)) ξ ≠ 0 := charFun_marginal_ne_zero h hX 1 ξ
  rw [Complex.cpow_def_of_ne_zero hne, h.charFun_eq_exp_mul hX t ξ]
  congr 1
  -- levyLocalCharExponent ξ = log(φ₁(ξ)) by definition, and equals charExponent ξ on the ball
  have hψ_eq := hball ξ hξ
  simp only [levyLocalCharExponent, LocalLog.localCharExponent] at hψ_eq
  rw [← hψ_eq]; ring

end Semigroup

/-! ### Lévy exponential formula

The function `F(t, ξ) := exp(t · Ψ(ξ))` packaged as a named definition,
with continuity in `t` and the equivalence with the characteristic function. -/

section LevyExpFormula

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableAdd₂ E]
  {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Lévy exponential formula: `F(t, ξ) := exp(t · Ψ(ξ))` where `Ψ` is the
characteristic exponent. -/
noncomputable def levyExpFormula (h : IsLevyProcess X μ)
    (_hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (ξ : E) : ℂ :=
  exp (↑(t : ℝ) * h.charExponent ξ)

/-- The characteristic function of the time-`t` marginal equals the Lévy exponential
formula. This is a clean restatement of `charFun_eq_exp_mul`. -/
theorem charFun_eq_levyExpFormula (h : IsLevyProcess X μ) (hX : ∀ t, Measurable (X t))
    (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ = h.levyExpFormula hX t ξ :=
  h.charFun_eq_exp_mul hX t ξ

end LevyExpFormula

end ProbabilityTheory.IsLevyProcess
