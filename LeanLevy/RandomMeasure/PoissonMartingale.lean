/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
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
* `ProbabilityTheory.compensatedPoissonSum_indicator_ae_eq` — the compensated Poisson sum of a
  finite-mass indicator is, almost everywhere, the centered evaluation of the random measure.
* `ProbabilityTheory.aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma` — **locality:**
  the compensated Poisson integral of a test function supported in a region `R` is measurable with
  respect to the evaluation sigma-algebra of `R`.

The martingale property is the conditional-expectation form of the independent-increment law: the
band increment is measurable with respect to the disjoint band region, hence independent of the past
(`indep_prmEvalSigma`), so its conditional expectation collapses to its mean `(t - s) · m A`, which
cancels the centering.
-/

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

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

/-! ### Locality of the compensated Poisson integral

For a general mark space `E` and intensity `m`, the compensated Poisson integral of a test function
supported inside a region `R` carries no information beyond the evaluation sigma-algebra
`prmEvalSigma K X m R` of that region. We prove this by approximating the test function in `L²(m)`
by simple functions supported in `R`, whose compensated integrals are explicit finite combinations
of centered evaluations of finite-mass subsets of `R` — manifestly measurable in `prmEvalSigma R` —
and then passing to the `L²(μ)` limit inside the closed subspace of functions almost everywhere
strongly measurable with respect to `prmEvalSigma R`. -/

section EvalSigmaSupport

variable {E Ω : Type} [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → E} {m : Measure E} [SigmaFinite m] {μ : Measure Ω}

omit [Nonempty E] in
/-- The pieces of the intensity partition intersected with a measurable set exhaust its mass. -/
private lemma tsum_measure_prmPiece_inter {D : Set E} (hD : MeasurableSet D) :
    ∑' k, m (prmPiece m k ∩ D) = m D := by
  rw [← measure_iUnion (fun i j hij =>
        (pairwise_disjoint_prmPiece hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun k => measurableSet_prmPiece.inter hD),
    ← Set.iUnion_inter, iUnion_prmPiece, Set.univ_inter]

omit [Nonempty E] [SigmaFinite m] in
/-- A finite-mass indicator is measurable. -/
private lemma measurable_indicatorConst {D : Set E} (hD : MeasurableSet D) (c : ℝ) :
    Measurable (D.indicator (fun _ => c)) :=
  measurable_const.indicator hD

omit [Nonempty E] [SigmaFinite m] in
/-- A finite-mass indicator is integrable against a finite-mass region. -/
private lemma integrable_indicatorConst {D : Set E} (hD : MeasurableSet D) (hfin : m D < ⊤)
    (c : ℝ) : Integrable (D.indicator (fun _ => c)) m :=
  memLp_one_iff_integrable.mp (memLp_indicator_const 1 hD c (Or.inr hfin.ne))

omit [Nonempty E] [SigmaFinite m] in
/-- A finite-mass indicator lies in `L²`. -/
private lemma memLp_two_indicatorConst {D : Set E} (hD : MeasurableSet D) (hfin : m D < ⊤)
    (c : ℝ) : MemLp (D.indicator (fun _ => c)) 2 m :=
  memLp_indicator_const 2 hD c (Or.inr hfin.ne)

/-- **The compensated sum of a finite-mass indicator is the centered evaluation.** -/
theorem compensatedPoissonSum_indicator_ae_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {D : Set E} (hD : MeasurableSet D) (hfin : m D < ⊤)
    (c : ℝ) :
    compensatedPoissonSum K X (D.indicator fun _ => c) m
      =ᵐ[μ] fun ω => c * ((poissonRandomMeasure K X ω D).toReal - (m D).toReal) := by
  classical
  -- per-piece identity
  have hpiece : ∀ ω k, compensatedPieceSum K X (D.indicator fun _ => c) m k ω
      = c * ((thinnedCount K X D k ω : ℝ) - (m (prmPiece m k ∩ D)).toReal) := by
    intro ω k
    have hsum : pieceSum K X (D.indicator fun _ => c) k ω = c * (thinnedCount K X D k ω : ℝ) := by
      simp only [pieceSum, thinnedCount]
      rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hx : X k n ω ∈ D
      · rw [Set.indicator_of_mem hx, if_pos hx, Nat.cast_one, mul_one]
      · rw [Set.indicator_of_notMem hx, if_neg hx, Nat.cast_zero, mul_zero]
    have hint : ∫ x in prmPiece m k, (D.indicator fun _ => c) x ∂m
        = c * (m (prmPiece m k ∩ D)).toReal := by
      rw [setIntegral_indicator hD]
      simp only [setIntegral_const, smul_eq_mul, measureReal_def]
      ring
    rw [compensatedPieceSum, hsum, hint, ← mul_sub]
  -- the mark-mass series
  have hb_ne : ∀ k, m (prmPiece m k ∩ D) ≠ ⊤ :=
    fun k => (lt_of_le_of_lt (measure_mono Set.inter_subset_right) hfin).ne
  have hb_summable : Summable (fun k => (m (prmPiece m k ∩ D)).toReal) :=
    ENNReal.summable_toReal (by rw [tsum_measure_prmPiece_inter hD]; exact hfin.ne)
  have hb_tsum : ∑' k, (m (prmPiece m k ∩ D)).toReal = (m D).toReal := by
    rw [← ENNReal.tsum_toReal_eq hb_ne, tsum_measure_prmPiece_inter hD]
  filter_upwards [ae_poissonRandomMeasure_apply_lt_top hd hD hfin] with ω hω
  -- the count series
  have ha_ne : ∀ k, (thinnedCount K X D k ω : ℝ≥0∞) ≠ ⊤ := fun k => ENNReal.natCast_ne_top _
  have ha_fin : ∑' k, (thinnedCount K X D k ω : ℝ≥0∞) ≠ ⊤ := by
    rw [← poissonRandomMeasure_apply hD]; exact hω.ne
  have ha_summable : Summable (fun k => (thinnedCount K X D k ω : ℝ)) := by
    simpa only [ENNReal.toReal_natCast] using ENNReal.summable_toReal ha_fin
  have ha_tsum : ∑' k, (thinnedCount K X D k ω : ℝ) = (poissonRandomMeasure K X ω D).toReal := by
    rw [poissonRandomMeasure_apply hD, ENNReal.tsum_toReal_eq ha_ne]
    simp only [ENNReal.toReal_natCast]
  show compensatedPoissonSum K X (D.indicator fun _ => c) m ω = _
  simp only [compensatedPoissonSum]
  rw [tsum_congr (hpiece ω), tsum_mul_left,
    (ha_summable.hasSum.sub hb_summable.hasSum).tsum_eq, ha_tsum, hb_tsum]

omit [Nonempty E] [SigmaFinite m] in
/-- A finite sum of finite-mass indicators is measurable. -/
private lemma measurable_finsetSumIndicatorConst {ι : Type*} (p : Finset ι) (c : ι → ℝ)
    (D : ι → Set E) (hDm : ∀ i ∈ p, MeasurableSet (D i)) :
    Measurable (fun x => ∑ i ∈ p, (D i).indicator (fun _ => c i) x) :=
  Finset.measurable_sum p fun i hi => measurable_indicatorConst (hDm i hi) (c i)

omit [Nonempty E] [SigmaFinite m] in
/-- A finite sum of finite-mass indicators is integrable. -/
private lemma integrable_finsetSumIndicatorConst {ι : Type*} (p : Finset ι) (c : ι → ℝ)
    (D : ι → Set E) (hDm : ∀ i ∈ p, MeasurableSet (D i)) (hDfin : ∀ i ∈ p, m (D i) < ⊤) :
    Integrable (fun x => ∑ i ∈ p, (D i).indicator (fun _ => c i) x) m :=
  integrable_finset_sum p fun i hi => integrable_indicatorConst (hDm i hi) (hDfin i hi) (c i)

omit [Nonempty E] [SigmaFinite m] in
/-- A finite sum of finite-mass indicators lies in `L²`. -/
private lemma memLp_two_finsetSumIndicatorConst {ι : Type*} (p : Finset ι) (c : ι → ℝ)
    (D : ι → Set E) (hDm : ∀ i ∈ p, MeasurableSet (D i)) (hDfin : ∀ i ∈ p, m (D i) < ⊤) :
    MemLp (fun x => ∑ i ∈ p, (D i).indicator (fun _ => c i) x) 2 m :=
  memLp_finset_sum p fun i hi => memLp_two_indicatorConst (hDm i hi) (hDfin i hi) (c i)

/-- The compensated sum of a finite combination of finite-mass indicators is the corresponding
finite combination of centered evaluations. -/
private theorem compensatedPoissonSum_finsetSumIndicatorConst_ae_eq [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {ι : Type*} (p : Finset ι) (c : ι → ℝ) (D : ι → Set E)
    (hDm : ∀ i ∈ p, MeasurableSet (D i)) (hDfin : ∀ i ∈ p, m (D i) < ⊤) :
    compensatedPoissonSum K X (fun x => ∑ i ∈ p, (D i).indicator (fun _ => c i) x) m
      =ᵐ[μ] fun ω => ∑ i ∈ p, c i * ((poissonRandomMeasure K X ω (D i)).toReal
        - (m (D i)).toReal) := by
  classical
  revert hDm hDfin
  induction p using Finset.induction with
  | empty =>
    intro _ _
    filter_upwards with ω
    simp [compensatedPoissonSum, compensatedPieceSum, pieceSum]
  | insert i p hip ih =>
    intro hDm hDfin
    have hi_m : MeasurableSet (D i) := hDm i (Finset.mem_insert_self i p)
    have hi_fin : m (D i) < ⊤ := hDfin i (Finset.mem_insert_self i p)
    have hDm' : ∀ j ∈ p, MeasurableSet (D j) := fun j hj => hDm j (Finset.mem_insert_of_mem hj)
    have hDfin' : ∀ j ∈ p, m (D j) < ⊤ := fun j hj => hDfin j (Finset.mem_insert_of_mem hj)
    have hadd := compensatedPoissonSum_add hd
      (measurable_indicatorConst hi_m (c i))
      (integrable_indicatorConst hi_m hi_fin (c i))
      (memLp_two_indicatorConst hi_m hi_fin (c i))
      (measurable_finsetSumIndicatorConst p c D hDm')
      (integrable_finsetSumIndicatorConst p c D hDm' hDfin')
      (memLp_two_finsetSumIndicatorConst p c D hDm' hDfin')
    have hone := compensatedPoissonSum_indicator_ae_eq hd hi_m hi_fin (c i)
    filter_upwards [hadd, hone, ih hDm' hDfin'] with ω hadd' hone' ih'
    have hfeq : (fun x => ∑ j ∈ insert i p, (D j).indicator (fun _ => c j) x)
        = fun x => (D i).indicator (fun _ => c i) x
            + ∑ j ∈ p, (D j).indicator (fun _ => c j) x :=
      funext fun x => Finset.sum_insert hip
    calc compensatedPoissonSum K X
            (fun x => ∑ j ∈ insert i p, (D j).indicator (fun _ => c j) x) m ω
        = compensatedPoissonSum K X (fun x => (D i).indicator (fun _ => c i) x
            + ∑ j ∈ p, (D j).indicator (fun _ => c j) x) m ω := by rw [hfeq]
      _ = compensatedPoissonSum K X ((D i).indicator (fun _ => c i)) m ω
            + compensatedPoissonSum K X
              (fun x => ∑ j ∈ p, (D j).indicator (fun _ => c j) x) m ω := hadd'
      _ = c i * ((poissonRandomMeasure K X ω (D i)).toReal - (m (D i)).toReal)
            + ∑ j ∈ p, c j * ((poissonRandomMeasure K X ω (D j)).toReal - (m (D j)).toReal) := by
          rw [hone', ih']
      _ = ∑ j ∈ insert i p, c j
            * ((poissonRandomMeasure K X ω (D j)).toReal - (m (D j)).toReal) := by
          rw [Finset.sum_insert hip]

/-- **Locality of the compensated Poisson integral.** If a test function `f ∈ L²(m)` vanishes
almost everywhere outside a measurable region `R`, then its compensated Poisson integral is
measurable with respect to the evaluation sigma-algebra `prmEvalSigma K X m R` of that region. -/
theorem aestronglyMeasurable_compensatedPoissonIntegral_prmEvalSigma [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) {R : Set E} (hR : MeasurableSet R) {f : Lp ℝ 2 m}
    (hf : ∀ᵐ x ∂m, x ∉ R → f x = 0) :
    AEStronglyMeasurable[prmEvalSigma K X m R] (compensatedPoissonIntegral hd f) μ := by
  classical
  have hm' : prmEvalSigma K X m R ≤ (inferInstance : MeasurableSpace Ω) :=
    prmEvalSigma_le hd.measurable_count hd.measurable_point R
  have hSclosed : IsClosed {g : Lp ℝ 2 μ | AEStronglyMeasurable[prmEvalSigma K X m R] (⇑g) μ} :=
    isClosed_aestronglyMeasurable hm'
  -- simple-function approximants of `f` in `L²(m)`
  have happrox : ∀ n : ℕ, ∃ φ : SimpleFunc E ℝ,
      eLpNorm (⇑f - ⇑φ) 2 m < ENNReal.ofReal (1 / (n + 1)) ∧ MemLp (⇑φ) 2 m :=
    fun n => (Lp.memLp f).exists_simpleFunc_eLpNorm_sub_lt (by norm_num)
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  choose φ hφ_lt hφ_memLp using happrox
  -- properties of the `R`-restricted approximants `R.indicator (φ n)`
  have hind_meas : ∀ n, Measurable (R.indicator (⇑(φ n))) :=
    fun n => (φ n).measurable.indicator hR
  have hind_memLp : ∀ n, MemLp (R.indicator (⇑(φ n))) 2 m :=
    fun n => (hφ_memLp n).indicator hR
  have hind_int : ∀ n, Integrable (R.indicator (⇑(φ n))) m :=
    fun n => ((SimpleFunc.memLp_iff_integrable two_ne_zero (by norm_num)).mp
      (hφ_memLp n)).indicator hR
  -- fiber-sum representation of `R.indicator (φ n)`
  have hg_eq : ∀ n,
      (fun x => ∑ z ∈ (φ n).range \ {0}, (R ∩ (φ n) ⁻¹' {z}).indicator (fun _ => z) x)
      = R.indicator (⇑(φ n)) := by
    intro n
    funext x
    by_cases hxR : x ∈ R
    · rw [Set.indicator_of_mem hxR, Finset.sum_eq_single (φ n x)]
      · have hmem : x ∈ R ∩ (φ n) ⁻¹' {φ n x} := ⟨hxR, rfl⟩
        rw [Set.indicator_of_mem hmem]
      · intro z _ hz
        apply Set.indicator_of_notMem
        rintro ⟨-, hzx⟩
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hzx
        exact hz hzx.symm
      · intro hns
        have hzero : φ n x = 0 := by
          by_contra h0
          exact hns (Finset.mem_sdiff.mpr
            ⟨(φ n).mem_range_self x, Finset.notMem_singleton.mpr h0⟩)
        rw [hzero]; simp
    · rw [Set.indicator_of_notMem hxR]
      refine Finset.sum_eq_zero fun z _ => ?_
      apply Set.indicator_of_notMem
      exact fun hmem => hxR hmem.1
  -- the compensated images in `L²(μ)`
  set y : ℕ → Lp ℝ 2 μ :=
    fun n => compensatedPoissonIntegral hd ((hind_memLp n).toLp (R.indicator (⇑(φ n)))) with hydef
  -- each image lives in the closed subspace
  have hyS : ∀ n, AEStronglyMeasurable[prmEvalSigma K X m R] (⇑(y n)) μ := by
    intro n
    have hHmeas : StronglyMeasurable[prmEvalSigma K X m R] (fun ω => ∑ z ∈ (φ n).range \ {0},
        z * ((poissonRandomMeasure K X ω (R ∩ (φ n) ⁻¹' {z})).toReal
          - (m (R ∩ (φ n) ⁻¹' {z})).toReal)) := by
      refine Finset.stronglyMeasurable_fun_sum _ fun z hz => ?_
      have hz0 : z ≠ 0 := Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hz).2
      have hzfin : m (R ∩ (φ n) ⁻¹' {z}) < ⊤ :=
        lt_of_le_of_lt (measure_mono Set.inter_subset_right)
          (SimpleFunc.measure_preimage_lt_top_of_memLp two_ne_zero (by norm_num) (φ n)
            (hφ_memLp n) z hz0)
      exact ((((measurable_prmEvalSigma_apply (hR.inter ((φ n).measurableSet_fiber z))
        Set.inter_subset_left hzfin).ennreal_toReal).sub measurable_const).const_mul z).stronglyMeasurable
    have hcombo : compensatedPoissonSum K X
          (fun x => ∑ z ∈ (φ n).range \ {0}, (R ∩ (φ n) ⁻¹' {z}).indicator (fun _ => z) x) m
        =ᵐ[μ] fun ω => ∑ z ∈ (φ n).range \ {0},
          z * ((poissonRandomMeasure K X ω (R ∩ (φ n) ⁻¹' {z})).toReal
            - (m (R ∩ (φ n) ⁻¹' {z})).toReal) :=
      compensatedPoissonSum_finsetSumIndicatorConst_ae_eq hd ((φ n).range \ {0}) (fun z => z)
        (fun z => R ∩ (φ n) ⁻¹' {z})
        (fun z _ => hR.inter ((φ n).measurableSet_fiber z))
        (fun z hz => lt_of_le_of_lt (measure_mono Set.inter_subset_right)
          (SimpleFunc.measure_preimage_lt_top_of_memLp two_ne_zero (by norm_num) (φ n)
            (hφ_memLp n) z (Finset.notMem_singleton.mp (Finset.mem_sdiff.mp hz).2)))
    have heqsum : ⇑(y n) =ᵐ[μ] compensatedPoissonSum K X (R.indicator (⇑(φ n))) m := by
      simp only [hydef]
      exact compensatedPoissonIntegral_eq_sum hd (hind_meas n) (hind_int n) (hind_memLp n)
    refine ⟨_, hHmeas, heqsum.trans ?_⟩
    rw [← hg_eq n]
    exact hcombo
  -- the images converge to `compensatedPoissonIntegral hd f`
  have hnorm_eq : ∀ n, ‖y n - compensatedPoissonIntegral hd f‖
      = (eLpNorm (⇑f - R.indicator (⇑(φ n))) 2 m).toReal := by
    intro n
    have h1 : y n - compensatedPoissonIntegral hd f
        = compensatedPoissonIntegral hd ((hind_memLp n).toLp (R.indicator (⇑(φ n))) - f) := by
      simp only [hydef]
      rw [← compensatedPoissonIntegral_sub]
    rw [h1, norm_compensatedPoissonIntegral, Lp.norm_def]
    congr 1
    have hcoe : ⇑((hind_memLp n).toLp (R.indicator (⇑(φ n))) - f)
        =ᵐ[m] (R.indicator (⇑(φ n)) - ⇑f) := by
      filter_upwards [Lp.coeFn_sub ((hind_memLp n).toLp (R.indicator (⇑(φ n)))) f,
        MemLp.coeFn_toLp (hind_memLp n)] with x hx1 hx2
      simp only [Pi.sub_apply] at hx1 ⊢
      rw [hx1, hx2]
    rw [eLpNorm_congr_ae hcoe, eLpNorm_sub_comm]
  have hbound : ∀ n, (eLpNorm (⇑f - R.indicator (⇑(φ n))) 2 m).toReal ≤ 1 / (n + 1) := by
    intro n
    have hRindic : (⇑f - R.indicator (⇑(φ n))) =ᵐ[m] R.indicator (⇑f - ⇑(φ n)) := by
      filter_upwards [hf] with x hx
      by_cases hxR : x ∈ R
      · simp only [Pi.sub_apply, Set.indicator_of_mem hxR]
      · simp only [Pi.sub_apply, Set.indicator_of_notMem hxR, sub_zero, hx hxR]
    have hle : eLpNorm (⇑f - R.indicator (⇑(φ n))) 2 m ≤ ENNReal.ofReal (1 / (n + 1)) :=
      calc eLpNorm (⇑f - R.indicator (⇑(φ n))) 2 m
          = eLpNorm (R.indicator (⇑f - ⇑(φ n))) 2 m := eLpNorm_congr_ae hRindic
        _ ≤ eLpNorm (⇑f - ⇑(φ n)) 2 m := eLpNorm_indicator_le _
        _ ≤ ENNReal.ofReal (1 / (n + 1)) := (hφ_lt n).le
    calc (eLpNorm (⇑f - R.indicator (⇑(φ n))) 2 m).toReal
        ≤ (ENNReal.ofReal (1 / (n + 1))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = 1 / (n + 1) := ENNReal.toReal_ofReal (by positivity)
  have hconv : Tendsto y atTop (𝓝 (compensatedPoissonIntegral hd f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [hnorm_eq]
    exact squeeze_zero (fun n => ENNReal.toReal_nonneg) hbound
      tendsto_one_div_add_atTop_nhds_zero_nat
  exact hSclosed.mem_of_tendsto hconv (Filter.Eventually.of_forall hyS)

end EvalSigmaSupport

end ProbabilityTheory
