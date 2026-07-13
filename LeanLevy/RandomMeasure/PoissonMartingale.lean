/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import LeanLevy.RandomMeasure.PoissonFiltration
import LeanLevy.RandomMeasure.TimeSpacePoisson

/-!
# The centered count martingale of a Poisson random measure

For the time-indexed Poisson random measure on `ℝ × E` with intensity `volume.prod m`, the natural
filtration `prmFiltration` records at time `t` the information carried by the evaluations of
finite-mass sets inside the time-prefix region `(-∞, t] × E`. With respect to this filtration the
**centered running count** `(poissonTimeCount K X A t).toReal - t · (m A)` is a martingale: each
increment over a band `(s, t] × A` is independent of the past and has mean exactly `(t - s) · m A`,
which is precisely the compensator that is subtracted.

## Main definitions

* `ProbabilityTheory.prmFiltration` — the natural filtration of the time-indexed Poisson random
  measure.

## Main results

* `ProbabilityTheory.prmFiltration_apply` — the value of the filtration at time `t` is the evaluation
  sigma-algebra of the prefix region `(-∞, t] × E`.
* `ProbabilityTheory.martingale_centeredPoissonTimeCount` — **the centered count process
  `(poissonTimeCount K X A t).toReal - t · (m A).toReal` is a martingale** for the natural filtration.

The martingale property is the conditional-expectation form of the independent-increment law: the
band increment is measurable with respect to the disjoint band region, hence independent of the past
(`indep_prmEvalSigma`), so its conditional expectation collapses to its mean `(t - s) · m A`, which
cancels the centering.
-/

open MeasureTheory Filter

open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {E : Type} [MeasurableSpace E] {m : Measure E} [SigmaFinite m] {A : Set E}

/-- Each space-time band has finite `volume.prod m`-mass whenever the mark set has finite mass. -/
private lemma measure_prod_Ioc_lt_top (hfin : m A < ⊤) (a b : ℝ) :
    (volume.prod m) (Set.Ioc a b ×ˢ A) < ⊤ := by
  rw [Measure.prod_prod, Real.volume_Ioc]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The real mass of a space-time band factorizes as time-length times mark mass. -/
private lemma measure_prod_Ioc_toReal {a b : ℝ} (hab : a ≤ b) :
    ((volume.prod m) (Set.Ioc a b ×ˢ A)).toReal = (b - a) * (m A).toReal := by
  rw [Measure.prod_prod, Real.volume_Ioc, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]

variable {Ω : Type} [MeasurableSpace Ω] [Nonempty E] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × E}
  {μ : Measure Ω} {hK : ∀ k, Measurable (K k)} {hX : ∀ k n, Measurable (X k n)}

/-- The natural filtration of the time-indexed Poisson random measure: at time `t`, the evaluations
of finite-mass sets inside the time-prefix region `(-∞, t] × E`. -/
noncomputable def prmFiltration (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E) (m : Measure E)
    [SigmaFinite m] (hK : ∀ k, Measurable (K k)) (hX : ∀ k n, Measurable (X k n)) :
    MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq t := prmEvalSigma K X (volume.prod m) (Set.Iic (t : ℝ) ×ˢ Set.univ)
  mono' s t hst :=
    prmEvalSigma_mono (Set.prod_mono (Set.Iic_subset_Iic.mpr (by exact_mod_cast hst)) (subset_refl _))
  le' _ := prmEvalSigma_le hK hX _

omit [Nonempty E] in
@[simp] theorem prmFiltration_apply (t : ℝ≥0) :
    prmFiltration K X m hK hX t
      = prmEvalSigma K X (volume.prod m) (Set.Iic (t : ℝ) ×ˢ Set.univ) :=
  rfl

omit [MeasurableSpace Ω] [Nonempty E] in
/-- The centered running count is strongly measurable with respect to the prefix-region evaluation
sigma-algebra. -/
private lemma stronglyMeasurable_centeredTimeCount {u : ℝ≥0} (hA : MeasurableSet A) (hfin : m A < ⊤) :
    StronglyMeasurable[prmEvalSigma K X (volume.prod m) (Set.Iic (u : ℝ) ×ˢ Set.univ)]
      (fun ω => (poissonTimeCount K X A (u : ℝ) ω).toReal - (u : ℝ) * (m A).toReal) :=
  (((measurable_prmEvalSigma_apply (measurableSet_Ioc.prod hA)
    (Set.prod_mono Set.Ioc_subset_Iic_self (Set.subset_univ A))
    (measure_prod_Ioc_lt_top hfin 0 (u : ℝ))).ennreal_toReal).stronglyMeasurable).sub
    stronglyMeasurable_const

/-- The centered running count is integrable at each time. -/
private lemma integrable_centeredTimeCount [IsProbabilityMeasure μ] {u : ℝ≥0}
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    Integrable (fun ω => (poissonTimeCount K X A (u : ℝ) ω).toReal - (u : ℝ) * (m A).toReal) μ :=
  (integrable_toReal_poissonRandomMeasure_apply hd (measurableSet_Ioc.prod hA)
    (measure_prod_Ioc_lt_top hfin 0 (u : ℝ))).sub (integrable_const _)

/-- **The centered count process is a martingale.** For the natural filtration `prmFiltration`, the
centered running count `(poissonTimeCount K X A t).toReal - t · (m A).toReal` is a martingale: the
band increment over `(s, t] × A` is independent of the past and has mean `(t - s) · m A`, cancelling
the centering. -/
theorem martingale_centeredPoissonTimeCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A) (hfin : m A < ⊤) :
    MeasureTheory.Martingale
      (fun (t : ℝ≥0) ω => (poissonTimeCount K X A (t : ℝ) ω).toReal - (t : ℝ) * (m A).toReal)
      (prmFiltration K X m hd.measurable_count hd.measurable_point) μ := by
  refine ⟨fun u => ?_, fun s t hst => ?_⟩
  · -- adaptedness at time `u`
    simpa only [prmFiltration_apply] using
      stronglyMeasurable_centeredTimeCount (K := K) (X := X) (u := u) hA hfin
  -- the conditional-expectation identity for `s ≤ t`
  simp only [prmFiltration_apply]
  set fs := fun ω => (poissonTimeCount K X A (s : ℝ) ω).toReal - (s : ℝ) * (m A).toReal with hfs
  set cb := fun ω => (poissonRandomMeasure K X ω (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ A)).toReal
    - ((t : ℝ) - (s : ℝ)) * (m A).toReal with hcb
  -- the increment identity `f t = f s + centered band` (a.e.)
  have hincr : (fun ω => (poissonTimeCount K X A (t : ℝ) ω).toReal - (t : ℝ) * (m A).toReal)
      =ᵐ[μ] fs + cb := by
    filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd (measurableSet_Ioc.prod hA)
        (measure_prod_Ioc_lt_top hfin 0 (s : ℝ)),
      ae_poissonRandomMeasure_apply_lt_top hd (measurableSet_Ioc.prod hA)
        (measure_prod_Ioc_lt_top hfin (s : ℝ) (t : ℝ))] with ω hωs hωband
    simp only [hfs, hcb, Pi.add_apply]
    rw [poissonTimeCount_add hA (NNReal.coe_nonneg s) (by exact_mod_cast hst) ω]
    simp only [poissonTimeCount]
    rw [ENNReal.toReal_add hωs.ne hωband.ne]
    ring
  -- region sub-sigma-algebras and their finiteness for the conditional expectation
  have hle_s := prmEvalSigma_le (m := volume.prod m) hd.measurable_count hd.measurable_point
    (Set.Iic (s : ℝ) ×ˢ Set.univ)
  have hle_band := prmEvalSigma_le (m := volume.prod m) hd.measurable_count hd.measurable_point
    (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ)
  haveI : IsFiniteMeasure (μ.trim hle_s) := isFiniteMeasure_trim hle_s
  -- the band increment is measurable in the disjoint band region, hence independent of the past
  have hcbsm : StronglyMeasurable[prmEvalSigma K X (volume.prod m)
      (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ)] cb := by
    rw [hcb]
    exact (((measurable_prmEvalSigma_apply (measurableSet_Ioc.prod hA)
      (Set.prod_mono (subset_refl _) (Set.subset_univ A))
      (measure_prod_Ioc_lt_top hfin (s : ℝ) (t : ℝ))).ennreal_toReal).stronglyMeasurable).sub
      stronglyMeasurable_const
  have hindep : Indep (prmEvalSigma K X (volume.prod m) (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ Set.univ))
      (prmEvalSigma K X (volume.prod m) (Set.Iic (s : ℝ) ×ˢ Set.univ)) μ :=
    indep_prmEvalSigma hd
      (Set.Disjoint.set_prod_left (Set.Iic_disjoint_Ioc (le_refl (s : ℝ))).symm Set.univ Set.univ)
  have hcb_int : Integrable cb μ := by
    rw [hcb]
    exact (integrable_toReal_poissonRandomMeasure_apply hd (measurableSet_Ioc.prod hA)
      (measure_prod_Ioc_lt_top hfin (s : ℝ) (t : ℝ))).sub (integrable_const _)
  -- the band increment has mean zero
  have hmean : (∫ ω, cb ω ∂μ) = 0 := by
    rw [hcb, integral_sub (integrable_toReal_poissonRandomMeasure_apply hd
        (measurableSet_Ioc.prod hA) (measure_prod_Ioc_lt_top hfin (s : ℝ) (t : ℝ)))
        (integrable_const _),
      integral_toReal_poissonRandomMeasure_apply hd (measurableSet_Ioc.prod hA)
        (measure_prod_Ioc_lt_top hfin (s : ℝ) (t : ℝ)),
      integral_const, measure_prod_Ioc_toReal (show (s : ℝ) ≤ (t : ℝ) by exact_mod_cast hst)]
    simp
  -- the conditional expectation of the increment collapses to its (zero) mean
  have hcb0 : μ[cb | prmEvalSigma K X (volume.prod m) (Set.Iic (s : ℝ) ×ˢ Set.univ)] =ᵐ[μ] 0 := by
    have hkey := condExp_indep_eq hle_band hle_s hcbsm hindep
    simp only [hmean] at hkey
    simpa using hkey
  -- assemble: `f t = f s + increment`, and both pieces resolve
  refine (condExp_congr_ae hincr).trans ?_
  refine (condExp_add (integrable_centeredTimeCount hd hA hfin) hcb_int _).trans ?_
  rw [condExp_of_stronglyMeasurable hle_s (stronglyMeasurable_centeredTimeCount hA hfin)
    (integrable_centeredTimeCount hd hA hfin)]
  calc fs + μ[cb | prmEvalSigma K X (volume.prod m) (Set.Iic (s : ℝ) ×ˢ Set.univ)]
      =ᵐ[μ] fs + (0 : Ω → ℝ) := EventuallyEq.add EventuallyEq.rfl hcb0
    _ = fs := add_zero fs

end ProbabilityTheory
