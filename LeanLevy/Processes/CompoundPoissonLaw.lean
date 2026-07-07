/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.CompoundPoisson
import LeanLevy.Probability.Poisson
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The jump-count law of a compound Poisson process is Poisson

For a compound Poisson driver with interarrival rate `r`, the arrival times
`arrival τ n ω = ∑_{i ≤ n} τ i ω` are the partial sums of the i.i.d. exponential interarrival
times. This file identifies the law of the associated *jump count*
`jumpCount (arrival τ · ω) t = #{n : arrival τ n ω ≤ t}` as a Poisson law with mean `r · t`.

The mathematical core is the classical fact that the sum of `n + 1` i.i.d. exponential rate `r`
variables has the Gamma density `r^{n+1} s^n e^{-rs} / n!` on `(0, ∞)`. We prove this by induction
on `n`: the base case is the exponential density, and the induction step convolves with one more
exponential — computed here from scratch as `withDensity ∗ withDensity = withDensity` of the density
convolution, since mathlib has no sum-of-exponentials-is-Gamma. The survival function of the arrival
time is then a finite interval integral, evaluated by the fundamental theorem of calculus, and the
Poisson jump-count law follows by telescoping the survival probabilities.

## Main results

* `ProbabilityTheory.arrival_survival` — `P(arrival τ n > t) = e^{-rt} ∑_{k ≤ n} (rt)^k / k!`.
* `ProbabilityTheory.map_jumpCount_arrival` — the law of the jump count at time `t` is
  `poissonMeasure (r · t)`.
-/

open MeasureTheory Filter Finset
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ}
  {μ : Measure Ω}

/-! ## The Gamma density of the arrival times -/

/-- The real-valued Gamma`(n + 1, R)` density: `R^{n+1} s^n e^{-Rs} / n!`. -/
private noncomputable def arrivalDensityReal (R : ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  R ^ (n + 1) * s ^ n * Real.exp (-(R * s)) / n.factorial

/-- The Gamma`(n + 1, R)` density as an `ℝ≥0∞`-valued function, supported on `[0, ∞)`. -/
private noncomputable def arrivalDensity (R : ℝ) (n : ℕ) (s : ℝ) : ℝ≥0∞ :=
  (Set.Ici 0).indicator (fun s => ENNReal.ofReal (arrivalDensityReal R n s)) s

private lemma arrivalDensityReal_nonneg {R : ℝ} (hR : 0 ≤ R) {s : ℝ} (hs : 0 ≤ s) (n : ℕ) :
    0 ≤ arrivalDensityReal R n s :=
  div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hR _) (pow_nonneg hs _)) (Real.exp_pos _).le)
    (Nat.cast_nonneg _)

private lemma arrivalDensityReal_zero (R : ℝ) (w : ℝ) :
    arrivalDensityReal R 0 w = R * Real.exp (-(R * w)) := by
  simp [arrivalDensityReal]

private lemma continuous_arrivalDensityReal (R : ℝ) (n : ℕ) :
    Continuous (arrivalDensityReal R n) := by
  unfold arrivalDensityReal; fun_prop

private lemma measurable_arrivalDensity (R : ℝ) (n : ℕ) : Measurable (arrivalDensity R n) := by
  refine Measurable.indicator ?_ measurableSet_Ici
  exact ENNReal.measurable_ofReal.comp (continuous_arrivalDensityReal R n).measurable

/-- The survival polynomial `e^{-Rt} ∑_{k ≤ n} (Rt)^k / k!`. -/
private noncomputable def survivalPoly (R : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(R * t)) * ∑ k ∈ Finset.range (n + 1), (R * t) ^ k / (k.factorial : ℝ)

private lemma survivalPoly_nonneg {R : ℝ} (hR : 0 ≤ R) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ survivalPoly R n t :=
  mul_nonneg (Real.exp_pos _).le (Finset.sum_nonneg fun _ _ =>
    div_nonneg (pow_nonneg (mul_nonneg hR ht) _) (Nat.cast_nonneg _))

/-! ## Base case: the exponential density -/

private lemma expMeasure_eq_withDensity_arrivalDensity (R : ℝ) :
    expMeasure R = volume.withDensity (arrivalDensity R 0) := by
  have hpdf : arrivalDensity R 0 = exponentialPDF R := by
    funext x
    simp only [arrivalDensity, Set.indicator_apply, Set.mem_Ici, exponentialPDF_eq,
      arrivalDensityReal_zero]
    by_cases hx : (0 : ℝ) ≤ x <;> simp [hx]
  have hg : gammaPDF 1 R = exponentialPDF R := by
    funext x; rw [gammaPDF, exponentialPDF, exponentialPDFReal]
  rw [hpdf, show expMeasure R = gammaMeasure 1 R from rfl, gammaMeasure, hg]

/-! ## Convolution of densities -/

/-- Convolution of two `withDensity` measures against Lebesgue measure has the convolution density.
This is the elementary translation-invariance computation that mathlib lacks in this form. -/
private lemma withDensity_conv_withDensity {f g : ℝ → ℝ≥0∞}
    [SFinite (volume.withDensity g)] (hf : Measurable f) (hg : Measurable g) :
    (volume.withDensity f) ∗ (volume.withDensity g)
      = volume.withDensity (fun z => ∫⁻ x, f x * g (z - x)) := by
  refine Measure.ext fun A hA => ?_
  have hind : Measurable (A.indicator (1 : ℝ → ℝ≥0∞)) := measurable_one.indicator hA
  -- inner integral: peel the density `g` and translate.
  have hinner : ∀ x : ℝ,
      ∫⁻ y, A.indicator (1 : ℝ → ℝ≥0∞) (x + y) ∂(volume.withDensity g)
        = ∫⁻ z in A, g (z - x) := by
    intro x
    have hmul : Measurable (fun y => A.indicator (1 : ℝ → ℝ≥0∞) (x + y)) := by fun_prop
    rw [lintegral_withDensity_eq_lintegral_mul volume hg
      (g := fun y => A.indicator (1 : ℝ → ℝ≥0∞) (x + y)) hmul]
    have hF : Measurable (fun z => g (z - x) * A.indicator (1 : ℝ → ℝ≥0∞) z) :=
      (hg.comp (measurable_id.sub_const x)).mul hind
    have hmp := (measurePreserving_add_left volume x).lintegral_comp
      (f := fun z => g (z - x) * A.indicator (1 : ℝ → ℝ≥0∞) z) hF
    simp only [add_sub_cancel_left] at hmp
    simp only [Pi.mul_apply]
    rw [hmp, ← lintegral_indicator hA]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ A <;> simp [hz]
  rw [withDensity_apply _ hA, ← lintegral_indicator_one hA, Measure.lintegral_conv hind,
    lintegral_congr hinner]
  -- outer integral: peel the density `f`, pull the constant, and swap.
  have houter : Measurable fun x => ∫⁻ z in A, g (z - x) :=
    (hg.comp (measurable_snd.sub measurable_fst)).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul volume hf houter]
  have hswap : ∀ x : ℝ,
      (f * fun x => ∫⁻ z in A, g (z - x)) x = ∫⁻ z in A, f x * g (z - x) := by
    intro x
    rw [Pi.mul_apply]
    exact (lintegral_const_mul (f x) (hg.comp (by fun_prop : Measurable fun z : ℝ => z - x))).symm
  rw [lintegral_congr hswap]
  exact lintegral_lintegral_swap
    ((hf.comp measurable_fst).mul (hg.comp (measurable_snd.sub measurable_fst))).aemeasurable

/-- The convolution of the Gamma`(n + 1, R)` density with one more exponential density is the
Gamma`(n + 2, R)` density. -/
private lemma arrivalDensity_conv {R : ℝ} (hR : 0 < R) (n : ℕ) (z : ℝ) :
    ∫⁻ x, arrivalDensity R n x * arrivalDensity R 0 (z - x) = arrivalDensity R (n + 1) z := by
  -- The integrand is supported on `Icc 0 z`.
  have hprod : (fun x => arrivalDensity R n x * arrivalDensity R 0 (z - x))
      = (Set.Icc 0 z).indicator
          (fun x => ENNReal.ofReal (arrivalDensityReal R n x * arrivalDensityReal R 0 (z - x))) := by
    funext x
    simp only [arrivalDensity, Set.indicator_apply, Set.mem_Ici, Set.mem_Icc]
    by_cases hx0 : (0 : ℝ) ≤ x
    · by_cases hxz : (0 : ℝ) ≤ z - x
      · have hxleqz : x ≤ z := by linarith
        rw [if_pos hx0, if_pos hxz, if_pos ⟨hx0, hxleqz⟩,
          ENNReal.ofReal_mul (arrivalDensityReal_nonneg hR.le hx0 n)]
      · have hne : ¬ (0 ≤ x ∧ x ≤ z) := fun h => hxz (by linarith [h.2])
        rw [if_pos hx0, if_neg hxz, if_neg hne, mul_zero]
    · have hne : ¬ (0 ≤ x ∧ x ≤ z) := fun h => hx0 h.1
      rw [if_neg hx0, if_neg hne, zero_mul]
  rw [hprod, lintegral_indicator measurableSet_Icc]
  by_cases hz : (0 : ℝ) ≤ z
  · -- `z ≥ 0`: convert to a Bochner integral and evaluate by `∫ x^n`.
    have hcongr : ∀ x ∈ Set.Icc (0 : ℝ) z,
        arrivalDensityReal R n x * arrivalDensityReal R 0 (z - x)
          = R ^ (n + 2) * Real.exp (-(R * z)) / n.factorial * x ^ n := by
      intro x _
      have hexp : Real.exp (-(R * x)) * Real.exp (-(R * (z - x))) = Real.exp (-(R * z)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [arrivalDensityReal, arrivalDensityReal_zero,
        show R ^ (n + 1) * x ^ n * Real.exp (-(R * x)) / (n.factorial : ℝ)
            * (R * Real.exp (-(R * (z - x))))
          = R ^ (n + 2) * (Real.exp (-(R * x)) * Real.exp (-(R * (z - x)))) / n.factorial * x ^ n
          from by ring, hexp]
    have hint : IntegrableOn
        (fun x => R ^ (n + 2) * Real.exp (-(R * z)) / n.factorial * x ^ n) (Set.Icc 0 z) :=
      (by fun_prop : Continuous fun x : ℝ =>
        R ^ (n + 2) * Real.exp (-(R * z)) / n.factorial * x ^ n).integrableOn_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc 0 z)]
        fun x => R ^ (n + 2) * Real.exp (-(R * z)) / n.factorial * x ^ n :=
      (ae_restrict_mem measurableSet_Icc).mono fun x hx =>
        mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg hR.le _) (Real.exp_pos _).le)
          (Nat.cast_nonneg _)) (pow_nonneg hx.1 _)
    rw [setLIntegral_congr_fun measurableSet_Icc (fun x hx => by rw [hcongr x hx]),
      ← ofReal_integral_eq_lintegral_ofReal hint hnn,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz,
      intervalIntegral.integral_const_mul, integral_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
    rw [arrivalDensity, Set.indicator_of_mem (Set.mem_Ici.mpr hz), arrivalDensityReal,
      Nat.factorial_succ]
    push_cast
    congr 1
    have h1 : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
    field_simp
  · -- `z < 0`: both sides vanish.
    have hz' : z < 0 := not_le.mp hz
    rw [Set.Icc_eq_empty (by linarith), setLIntegral_empty]
    symm
    rw [arrivalDensity, Set.indicator_of_notMem (by simp only [Set.mem_Ici, not_le]; exact hz')]

/-! ## The Gamma law of the arrival times -/

/-- The law of the `n`-th arrival time is the Gamma`(n + 1, r)` law. -/
private lemma map_arrival_eq [IsProbabilityMeasure μ]
    (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (n : ℕ) :
    μ.map (arrival τ n) = volume.withDensity (arrivalDensity (r : ℝ) n) := by
  have hR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  haveI : IsProbabilityMeasure (expMeasure (r : ℝ)) := isProbabilityMeasure_expMeasure hR
  induction n with
  | zero =>
    have h0 : arrival τ 0 = τ 0 := by funext ω; exact arrival_zero τ ω
    rw [h0, (hd.law_interarrival 0).map_eq, expMeasure_eq_withDensity_arrivalDensity]
  | succ n ih =>
    have hτ : iIndepFun τ μ := by
      have := hd.indep.precomp (g := Sum.inl) Sum.inl_injective
      simpa [Function.comp] using this
    have harr_eq : arrival τ n = ∑ j ∈ Finset.range (n + 1), τ j := by
      funext ω; simp [arrival, Finset.sum_apply]
    have hindep : IndepFun (arrival τ n) (τ (n + 1)) μ := by
      rw [harr_eq]; exact hτ.indepFun_sum_range_succ hd.measurable_interarrival (n + 1)
    have hlawA : HasLaw (arrival τ n) (volume.withDensity (arrivalDensity (r : ℝ) n)) μ :=
      ⟨(hd.measurable_arrival n).aemeasurable, ih⟩
    have hlawT : HasLaw (τ (n + 1)) (expMeasure (r : ℝ)) μ := hd.law_interarrival (n + 1)
    haveI : SigmaFinite (volume.withDensity (arrivalDensity (r : ℝ) n)) := by
      rw [← ih]
      haveI : IsProbabilityMeasure (μ.map (arrival τ n)) :=
        Measure.isProbabilityMeasure_map (hd.measurable_arrival n).aemeasurable
      infer_instance
    have hsum := hindep.hasLaw_add hlawA hlawT
    have hsucc : arrival τ (n + 1) = arrival τ n + τ (n + 1) := by
      funext ω; exact arrival_succ τ n ω
    rw [hsucc, hsum.map_eq, expMeasure_eq_withDensity_arrivalDensity]
    haveI : SFinite (volume.withDensity (arrivalDensity (r : ℝ) 0)) := by
      rw [← expMeasure_eq_withDensity_arrivalDensity]; infer_instance
    rw [withDensity_conv_withDensity (measurable_arrivalDensity _ _)
      (measurable_arrivalDensity _ _)]
    exact congrArg _ (funext fun z => arrivalDensity_conv hR n z)

/-! ## Survival function -/

private lemma hasDerivAt_survivalPoly (R : ℝ) (n : ℕ) (s : ℝ) :
    HasDerivAt (survivalPoly R n) (-(arrivalDensityReal R n s)) s := by
  induction n with
  | zero =>
    have hfun : survivalPoly R 0 = fun s => Real.exp (-(R * s)) := by
      funext s; simp [survivalPoly]
    rw [hfun]
    have h1 : HasDerivAt (fun s => Real.exp (-(R * s))) (Real.exp (-(R * s)) * -(R * 1)) s :=
      (((hasDerivAt_id s).const_mul R).neg).exp
    convert h1 using 1
    rw [arrivalDensityReal]; ring
  | succ n ih =>
    have hsplit : survivalPoly R (n + 1)
        = fun s => survivalPoly R n s
            + Real.exp (-(R * s)) * ((R * s) ^ (n + 1) / ((n + 1).factorial : ℝ)) := by
      funext s; simp only [survivalPoly, Finset.sum_range_succ, mul_add]
    rw [hsplit]
    have hE : HasDerivAt (fun s => Real.exp (-(R * s))) (Real.exp (-(R * s)) * -(R * 1)) s :=
      (((hasDerivAt_id s).const_mul R).neg).exp
    have hP : HasDerivAt (fun s => (R * s) ^ (n + 1))
        ((n + 1 : ℕ) * (R * s) ^ (n + 1 - 1) * (R * 1)) s :=
      ((hasDerivAt_id s).const_mul R).pow (n + 1)
    have hg := hE.mul (hP.div_const ((n + 1).factorial : ℝ))
    convert ih.add hg using 1
    rw [arrivalDensityReal, arrivalDensityReal, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The interval integral of the Gamma density is `1 - survivalPoly`. -/
private lemma integral_arrivalDensityReal {R : ℝ} (n : ℕ) {t : ℝ} :
    ∫ s in (0 : ℝ)..t, arrivalDensityReal R n s = 1 - survivalPoly R n t := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s => -survivalPoly R n s) (arrivalDensityReal R n s) s := by
    intro s _
    simpa using (hasDerivAt_survivalPoly R n s).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_arrivalDensityReal R n).intervalIntegrable _ _)]
  have h0 : survivalPoly R n 0 = 1 := by
    simp only [survivalPoly, mul_zero, neg_zero, Real.exp_zero, one_mul]
    rw [Finset.sum_eq_single 0 (fun b _ hb => by rw [zero_pow hb, zero_div])
      (fun hb => absurd (Finset.mem_range.mpr n.succ_pos) hb)]
    simp
  simp only [h0]
  ring

private lemma withDensity_arrivalDensity_Iic {R : ℝ} (hR : 0 < R) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (volume.withDensity (arrivalDensity R n)) (Set.Iic t)
      = ENNReal.ofReal (1 - survivalPoly R n t) := by
  rw [withDensity_apply _ measurableSet_Iic]
  have hInt : ∫⁻ s in Set.Iic t, arrivalDensity R n s
      = ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (arrivalDensityReal R n s) := by
    rw [← lintegral_indicator measurableSet_Iic, ← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun s => ?_
    rw [show (arrivalDensity R n) = (Set.Ici 0).indicator
        (fun s => ENNReal.ofReal (arrivalDensityReal R n s)) from rfl,
      Set.indicator_indicator, Set.inter_comm, Set.Ici_inter_Iic]
  rw [hInt, ← ofReal_integral_eq_lintegral_ofReal
    ((continuous_arrivalDensityReal R n).integrableOn_Icc)
    ((ae_restrict_mem measurableSet_Icc).mono fun s hs => arrivalDensityReal_nonneg hR.le hs.1 n),
    MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
    integral_arrivalDensityReal]

private lemma survival_ennreal [IsProbabilityMeasure μ]
    (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < arrival τ n ω} = ENNReal.ofReal (survivalPoly (r : ℝ) n t) := by
  have hR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hmap := map_arrival_eq hd hr n
  have hset : {ω | t < arrival τ n ω} = arrival τ n ⁻¹' Set.Ioi t := by
    ext ω; simp [Set.mem_Ioi]
  rw [hset, ← Measure.map_apply (hd.measurable_arrival n) measurableSet_Ioi, hmap]
  haveI : IsProbabilityMeasure (volume.withDensity (arrivalDensity (r : ℝ) n)) := by
    rw [← hmap]; exact Measure.isProbabilityMeasure_map (hd.measurable_arrival n).aemeasurable
  have hone : (0 : ℝ) ≤ 1 - survivalPoly (r : ℝ) n t := by
    rw [← integral_arrivalDensityReal (R := (r : ℝ)) n (t := t)]
    exact intervalIntegral.integral_nonneg ht fun s hs =>
      arrivalDensityReal_nonneg hR.le hs.1 n
  rw [show Set.Ioi t = (Set.Iic t)ᶜ from (Set.compl_Iic).symm,
    measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    withDensity_arrivalDensity_Iic hR n ht, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ hone]
  congr 1
  ring

/-- **Survival function of the arrival times.** The probability that fewer than `n + 1` arrivals
have occurred by time `t` is `e^{-rt} ∑_{k ≤ n} (rt)^k / k!`. -/
theorem arrival_survival [IsProbabilityMeasure μ]
    (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (μ {ω | t < arrival τ n ω}).toReal
      = Real.exp (-(r * t)) * ∑ k ∈ Finset.range (n + 1), (r * t) ^ k / k.factorial := by
  have hR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  rw [survival_ennreal hd hr n ht, ENNReal.toReal_ofReal (survivalPoly_nonneg hR.le ht n)]
  rfl

/-! ## The jump count is Poisson -/

/-- **The jump count of a compound Poisson process is Poisson.** At time `t`, the number of arrivals
that have occurred is Poisson distributed with mean `r · t`. -/
theorem map_jumpCount_arrival [IsProbabilityMeasure μ]
    (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (t : ℝ≥0) :
    μ.map (fun ω => jumpCount (fun n => arrival τ n ω) (t : ℝ)) = poissonMeasure (r * t) := by
  have hR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
  set jc : Ω → ℕ := fun ω => jumpCount (fun n => arrival τ n ω) (t : ℝ) with hjc
  have hmeas_jc : Measurable jc := measurable_jumpCount_arrival hd.measurable_interarrival _
  have hmeas_le : ∀ j, MeasurableSet {ω | jc ω ≤ j} := fun j => hmeas_jc measurableSet_Iic
  -- The jump-count CDF from the arrival survival function, via a.e. decoding.
  have hle : ∀ k, μ {ω | jc ω ≤ k} = ENNReal.ofReal (survivalPoly (r : ℝ) k (t : ℝ)) := by
    intro k
    have hae : {ω | jc ω ≤ k} =ᵐ[μ] {ω | (t : ℝ) < arrival τ k ω} := by
      filter_upwards [hd.ae_strictMono_arrival hr, hd.ae_tendsto_arrival hr] with ω hmono htop
      show (jumpCount (fun n => arrival τ n ω) (t : ℝ) ≤ k) = ((t : ℝ) < arrival τ k ω)
      rw [eq_iff_iff, ← not_lt, lt_jumpCount_iff hmono htop, not_le]
    rw [measure_congr hae, survival_ennreal hd hr k ht]
  refine Measure.ext_of_singleton fun k => ?_
  rw [Measure.map_apply hmeas_jc (measurableSet_singleton k)]
  have hpoisson : poissonMeasure (r * t) {k} = ENNReal.ofReal (poissonPMFReal (r * t) k) := by
    rw [poissonMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k)]; rfl
  rw [hpoisson, show jc ⁻¹' {k} = {ω | jc ω = k} from rfl]
  cases k with
  | zero =>
    rw [show {ω | jc ω = 0} = {ω | jc ω ≤ 0} from by ext ω; simp, hle 0]
    congr 1
    simp only [survivalPoly, poissonPMFReal, zero_add, Finset.sum_range_one, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one, mul_one, NNReal.coe_mul]
  | succ m =>
    have hsub : {ω | jc ω ≤ m} ⊆ {ω | jc ω ≤ m + 1} := fun ω h => le_trans h (Nat.le_succ m)
    rw [show {ω | jc ω = m + 1} = {ω | jc ω ≤ m + 1} \ {ω | jc ω ≤ m} from by
        ext ω; simp only [Set.mem_setOf_eq, Set.mem_diff]; omega,
      measure_diff hsub (hmeas_le m).nullMeasurableSet (measure_ne_top _ _),
      hle (m + 1), hle m, ← ENNReal.ofReal_sub _ (survivalPoly_nonneg hR.le ht m)]
    congr 1
    simp only [survivalPoly, poissonPMFReal, Finset.sum_range_succ, NNReal.coe_mul]
    field_simp
    ring

end ProbabilityTheory
