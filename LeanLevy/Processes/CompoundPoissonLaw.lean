/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.CompoundPoisson
import LeanLevy.Probability.Poisson
import LeanLevy.Levy.LevyKhintchineUniqueness
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process

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
* `ProbabilityTheory.charFun_map_compoundPoisson` — the characteristic function of the
  compound-Poisson-with-drift marginal at time `t` is
  `exp(t · (i b ξ + r · (charFun ν' ξ − 1)))`.
* `ProbabilityTheory.compoundPoissonTriple` — the Lévy–Khintchine triple `(b', 0, r · ν')` of a
  compound Poisson process with drift `b`, jump rate `r`, and jump law `ν'`.
* `ProbabilityTheory.charFun_map_compoundPoisson_eq_exponent` — the marginal's characteristic
  function is `exp(t · ψ_T)` for `T = compoundPoissonTriple b r ν'`, realizing the finite-activity,
  zero-Gaussian Lévy–Khintchine triples.
* `ProbabilityTheory.isInfinitelyDivisible_map_compoundPoisson` — every marginal is infinitely
  divisible.
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

/-! ## The characteristic function of the compound Poisson marginal -/

/-- **Poisson probability-generating function.** For any complex `w`, the power series
`∑ₖ P(N = k) · wᵏ` of a Poisson`(λ)` count sums to `exp(λ · (w − 1))`. This is the analytic
identity behind the compound-Poisson characteristic function; it is proved exactly like
`poissonCharFun_eq`, by pulling the normalising constant `e^{−λ}` out of the exponential series. -/
private lemma tsum_poissonPMFReal_mul_pow (lam : ℝ≥0) (w : ℂ) :
    ∑' k : ℕ, (poissonPMFReal lam k : ℂ) * w ^ k = Complex.exp ((lam : ℝ) * (w - 1)) := by
  have hterm : ∀ k : ℕ, (poissonPMFReal lam k : ℂ) * w ^ k
      = (Real.exp (-(lam : ℝ)) : ℂ) * (((lam : ℝ) * w) ^ k / (Nat.factorial k : ℂ)) := by
    intro k
    simp only [poissonPMFReal]
    push_cast
    rw [mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hsum := NormedSpace.expSeries_div_hasSum_exp (((lam : ℝ) : ℂ) * w)
  rw [hsum.tsum_eq, ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {b : ℝ}

/-- **The interarrival family is independent of the mark family.** The joint driver independence
`iIndepFun (Sum.elim τ Y)` over `ℕ ⊕ ℕ` restricts, via the process-independence criterion, to
independence of the two whole `ℕ → ℝ`-valued blocks. This is the pi-block independence that lets a
functional of *all* interarrival times (such as the jump count) be treated as independent of the
marks. -/
private lemma indepFun_interarrival_mark (hd : IsCompoundPoissonDriver τ Y r ν' μ) :
    IndepFun (fun ω n => τ n ω) (fun ω n => Y n ω) μ := by
  haveI := hd.isProbabilityMeasure
  have hmeas : ∀ i, Measurable (Sum.elim τ Y i) := by
    rintro (n | n)
    · exact hd.measurable_interarrival n
    · exact hd.measurable_mark n
  refine IndepFun.process_indepFun_process hd.measurable_interarrival hd.measurable_mark ?_
  intro I J
  classical
  set eL : ℕ ↪ ℕ ⊕ ℕ := ⟨Sum.inl, Sum.inl_injective⟩ with heL
  set eR : ℕ ↪ ℕ ⊕ ℕ := ⟨Sum.inr, Sum.inr_injective⟩ with heR
  have hdisj : Disjoint (I.map eL) (J.map eR) := by
    rw [Finset.disjoint_left]
    rintro x hxL hxR
    rw [Finset.mem_map] at hxL hxR
    obtain ⟨a, -, rfl⟩ := hxL
    obtain ⟨c, -, hc⟩ := hxR
    exact Sum.inr_ne_inl hc
  have key := hd.indep.indepFun_finset (I.map eL) (J.map eR) hdisj hmeas
  have φmeas : Measurable
      (fun (g : (I.map eL) → ℝ) (i : I) => g ⟨Sum.inl (i : ℕ), Finset.mem_map_of_mem eL i.2⟩) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  have ψmeas : Measurable
      (fun (g : (J.map eR) → ℝ) (j : J) => g ⟨Sum.inr (j : ℕ), Finset.mem_map_of_mem eR j.2⟩) :=
    measurable_pi_lambda _ fun _ => measurable_pi_apply _
  exact key.comp φmeas ψmeas

/-- **iid marks contribute a power of the mark characteristic function.** The partial sum of the
first `k` marks has characteristic function `(charFun ν' ξ)ᵏ`, since the marks are i.i.d. with law
`ν'`. Proved through mathlib's `iIndepFun.charFun_map_fun_sum_eq_prod`. -/
private lemma charFun_finset_sum_marks (hd : IsCompoundPoissonDriver τ Y r ν' μ)
    (k : ℕ) (ξ : ℝ) :
    charFun (μ.map (fun ω => ∑ n ∈ Finset.range k, Y n ω)) ξ = (charFun ν' ξ) ^ k := by
  haveI := hd.isProbabilityMeasure
  have hY : iIndepFun Y μ := by
    have := hd.indep.precomp (g := Sum.inr) Sum.inr_injective
    simpa [Function.comp] using this
  have hZ : iIndepFun (fun i : Fin k => Y (i : ℕ)) μ := hY.precomp Fin.val_injective
  have hfun : (fun ω => ∑ n ∈ Finset.range k, Y n ω) = (fun ω => ∑ i : Fin k, Y (i : ℕ) ω) := by
    funext ω
    exact (Fin.sum_univ_eq_sum_range (fun n => Y n ω) k).symm
  rw [hfun, iIndepFun.charFun_map_fun_sum_eq_prod
      (fun (i : Fin k) => (hd.measurable_mark (i : ℕ)).aemeasurable) hZ,
    Finset.prod_apply]
  rw [Finset.prod_congr rfl fun i _ => by rw [(hd.law_mark (i : ℕ)).map_eq]]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The characteristic function of the compound Poisson marginal.** At each fixed time `t ≥ 0`,
the compound-Poisson-with-drift random variable `Xₜ = b·t + ∑_{n ≤ N(t)} Yₙ` has characteristic
function

`E[e^{iξ Xₜ}] = exp(t · (i b ξ + r · (charFun ν' ξ − 1)))`,

the classical Lévy–Khintchine form of a compound Poisson process with drift `b`, jump rate `r`, and
jump law `ν'`. The proof conditions on the Poisson jump count `N(t)`: on `{N(t) = k}` the jump sum is
a sum of `k` i.i.d. marks, contributing `(charFun ν' ξ)ᵏ`, and `∑ₖ P(N(t) = k)·(charFun ν' ξ)ᵏ`
sums to the Poisson generating function `exp(r t · (charFun ν' ξ − 1))`. -/
theorem charFun_map_compoundPoisson [IsProbabilityMeasure μ]
    (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (compoundPoisson b τ Y (t : ℝ))) ξ
      = Complex.exp ((t : ℝ) * (Complex.I * b * ξ + r * (charFun ν' ξ - 1))) := by
  classical
  set jc : Ω → ℕ := fun ω => jumpCount (fun n => arrival τ n ω) (t : ℝ) with hjc
  have hjc_meas : Measurable jc := measurable_jumpCount_arrival hd.measurable_interarrival _
  set w : ℂ := charFun ν' ξ with hw
  have hXmeas : Measurable (compoundPoisson b τ Y (t : ℝ)) :=
    measurable_compoundPoisson hd.measurable_interarrival hd.measurable_mark _
  -- Independence of the jump count (a functional of all interarrival times) from the marks.
  have hblock : IndepFun (fun ω n => τ n ω) (fun ω n => Y n ω) μ := indepFun_interarrival_mark hd
  have hφ : Measurable (fun g : ℕ → ℝ =>
      jumpCount (fun n => arrival (fun m ω' => ω' m) n g) (t : ℝ)) :=
    measurable_jumpCount_arrival (fun m => measurable_pi_apply m) (t : ℝ)
  have hNY : IndepFun jc (fun ω n => Y n ω) μ := hblock.comp hφ measurable_id
  have hYbar_ae : AEMeasurable (fun ω n => Y n ω) μ :=
    (measurable_pi_lambda _ fun n => hd.measurable_mark n).aemeasurable
  -- The value of the jump-sum integral: the Poisson generating function.
  have hA : (∫ ω, Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I) ∂μ)
      = Complex.exp (((r * t : ℝ≥0) : ℝ) * (w - 1)) := by
    set F : Ω → ℂ := fun ω => Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I)
      with hF
    set s : ℕ → Set Ω := fun k => {ω | jc ω = k} with hs
    have hs_meas : ∀ k, MeasurableSet (s k) := fun k => hjc_meas (measurableSet_singleton k)
    have hs_disj : Pairwise (fun i j => Disjoint (s i) (s j)) := by
      intro k k' hkk'
      simp only [Set.disjoint_left, hs, Set.mem_setOf_eq]
      intro ω h1 h2
      exact hkk' (h1.symm.trans h2)
    have hunion : (⋃ k, s k) = Set.univ :=
      Set.eq_univ_of_forall fun ω => Set.mem_iUnion.2 ⟨jc ω, rfl⟩
    have hSum : Measurable (fun ω => ∑ n ∈ Finset.range (jc ω), Y n ω) := by
      have hP : Measurable (fun p : Ω × ℕ => ∑ n ∈ Finset.range p.2, Y n p.1) :=
        measurable_from_prod_countable_left fun m =>
          Finset.measurable_sum (Finset.range m) fun n _ => hd.measurable_mark n
      exact hP.comp (measurable_id.prodMk hjc_meas)
    have hFmeas : Measurable F := by
      show Measurable (fun ω => Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I))
      exact (by fun_prop : Measurable fun z : ℝ => Complex.exp (↑ξ * ↑z * Complex.I)).comp hSum
    have hFbound : ∀ ω, ‖F ω‖ ≤ 1 := by
      intro ω
      show ‖Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I)‖ ≤ 1
      rw [show (↑ξ * ↑(∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I : ℂ)
          = ↑(ξ * ∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I from by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hF_int : Integrable F μ :=
      (integrable_const (1 : ℝ)).mono' hFmeas.aestronglyMeasurable
        (ae_of_all _ fun ω => by simpa using hFbound ω)
    have hpart := hasSum_integral_iUnion hs_meas hs_disj (by rw [hunion]; exact hF_int.integrableOn)
    rw [hunion, setIntegral_univ] at hpart
    have hterm : ∀ k, (∫ ω in s k, F ω ∂μ) = (poissonPMFReal (r * t) k : ℂ) * w ^ k := by
      intro k
      -- On `{jc = k}` the jump sum is the sum of the first `k` marks.
      have hFcong : Set.EqOn F
          (fun ω => Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range k, Y n ω) * Complex.I)) (s k) := by
        intro ω hω
        have hk : jc ω = k := hω
        show Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I) = _
        rw [hk]
      have hGeq :
          (s k).indicator (fun ω => Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range k, Y n ω) * Complex.I))
            = fun ω => (if jc ω = k then (1 : ℂ) else 0)
                * Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range k, Y n ω) * Complex.I) := by
        funext ω
        simp only [Set.indicator_apply, hs, Set.mem_setOf_eq]
        by_cases h : jc ω = k <;> simp [h]
      -- Measurability of the two factor maps.
      have hf_aesm : AEStronglyMeasurable (fun m : ℕ => if m = k then (1 : ℂ) else 0) (μ.map jc) :=
        (measurable_of_countable _).aestronglyMeasurable
      have hg_aesm : AEStronglyMeasurable
          (fun y : ℕ → ℝ => Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range k, y n) * Complex.I))
          (μ.map (fun ω n => Y n ω)) := by
        have : Measurable
            (fun y : ℕ → ℝ => Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range k, y n) * Complex.I)) := by
          fun_prop
        exact this.aestronglyMeasurable
      -- Factorisation of the `k`-th term by independence of the count and the marks.
      have hprod : (∫ ω, (if jc ω = k then (1 : ℂ) else 0)
            * Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range k, Y n ω) * Complex.I) ∂μ)
          = (∫ ω, (if jc ω = k then (1 : ℂ) else 0) ∂μ)
            * ∫ ω, Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range k, Y n ω) * Complex.I) ∂μ :=
        hNY.integral_fun_comp_mul_comp (f := fun m : ℕ => if m = k then (1 : ℂ) else 0)
          (g := fun y : ℕ → ℝ => Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range k, y n) * Complex.I))
          hjc_meas.aemeasurable hYbar_ae hf_aesm hg_aesm
      -- Identify the probability of `{jc = k}` with the Poisson pmf.
      have hμreal : μ.real (s k) = poissonPMFReal (r * t) k := by
        have h1 : μ (s k) = poissonMeasure (r * t) {k} := by
          have hmap : μ.map jc = poissonMeasure (r * t) := map_jumpCount_arrival hd hr t
          rw [show s k = jc ⁻¹' {k} from rfl,
            ← Measure.map_apply hjc_meas (measurableSet_singleton k), hmap]
        rw [measureReal_def, h1, show poissonMeasure (r * t) {k}
            = ENNReal.ofReal (poissonPMFReal (r * t) k) from by
              rw [poissonMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k)]; rfl,
          ENNReal.toReal_ofReal poissonPMFReal_nonneg]
      -- The indicator factor integrates to the probability of `{jc = k}`.
      have hf_int : (∫ ω, (if jc ω = k then (1 : ℂ) else 0) ∂μ)
          = (poissonPMFReal (r * t) k : ℂ) := by
        have heq : (fun ω => if jc ω = k then (1 : ℂ) else 0) = (s k).indicator fun _ => (1 : ℂ) := by
          funext ω
          simp only [Set.indicator_apply, hs, Set.mem_setOf_eq]
        rw [heq, integral_indicator_const (1 : ℂ) (hs_meas k), hμreal]
        exact Complex.real_smul.trans (mul_one _)
      -- The mark factor is the `k`-th power of the mark characteristic function.
      have hg_int : (∫ ω, Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range k, Y n ω) * Complex.I) ∂μ)
          = w ^ k := by
        have hmapmeas : Measurable (fun ω => ∑ n ∈ Finset.range k, Y n ω) :=
          Finset.measurable_sum _ fun n _ => hd.measurable_mark n
        rw [hw, ← charFun_finset_sum_marks hd k ξ, charFun_apply_real,
          integral_map hmapmeas.aemeasurable
            ((by fun_prop : Continuous fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I))
              |>.aestronglyMeasurable)]
      rw [setIntegral_congr_fun (hs_meas k) hFcong, ← integral_indicator (hs_meas k)]
      simp only [hGeq]
      rw [hprod, hf_int, hg_int]
    -- Sum the Poisson generating series.
    have hHS : HasSum (fun k => (poissonPMFReal (r * t) k : ℂ) * w ^ k) (∫ ω, F ω ∂μ) := by
      have hfun : (fun k => ∫ ω in s k, F ω ∂μ)
          = fun k => (poissonPMFReal (r * t) k : ℂ) * w ^ k := funext hterm
      rwa [hfun] at hpart
    rw [← hHS.tsum_eq, tsum_poissonPMFReal_mul_pow]
  -- Peel off the drift and assemble.
  have hint_eq : ∀ ω, Complex.exp (↑ξ * ↑(compoundPoisson b τ Y (t : ℝ) ω) * Complex.I)
      = Complex.exp (↑ξ * ↑b * ↑(t : ℝ) * Complex.I)
        * Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I) := by
    intro ω
    rw [show compoundPoisson b τ Y (t : ℝ) ω
        = 0 + b * (t : ℝ) + ∑ n ∈ Finset.range (jc ω), Y n ω from rfl, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [charFun_apply_real,
    integral_map hXmeas.aemeasurable
      ((by fun_prop : Continuous fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I))
        |>.aestronglyMeasurable)]
  simp_rw [hint_eq]
  calc ∫ ω, Complex.exp (↑ξ * ↑b * ↑(t : ℝ) * Complex.I)
          * Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I) ∂μ
        = Complex.exp (↑ξ * ↑b * ↑(t : ℝ) * Complex.I)
          * ∫ ω, Complex.exp (↑ξ * ↑(∑ n ∈ Finset.range (jc ω), Y n ω) * Complex.I) ∂μ :=
        MeasureTheory.integral_const_mul _ _
    _ = Complex.exp ((t : ℝ) * (Complex.I * b * ξ + r * (charFun ν' ξ - 1))) := by
        rw [hA, ← Complex.exp_add]
        congr 1
        push_cast
        ring

/-! ## The Lévy–Khintchine triple of the compound Poisson marginal -/

/-- **The Lévy–Khintchine triple of a compound Poisson process** with drift `b`, jump rate `r`,
and (probability) jump law `ν'`. The Gaussian part vanishes, the Lévy measure is the finite measure
`r · ν'`, and the drift is corrected by the small-jump compensator `∫_{|x| < 1} x d(r · ν')` so that
the compensated Lévy–Khintchine exponent reproduces the compound-Poisson characteristic exponent
`i b ξ + r (charFun ν' ξ − 1)` (see `exponent_compoundPoissonTriple`). By uniqueness of the triple
of an infinitely divisible law (`existsUnique_levyKhintchineTriple`) this is *the* Lévy–Khintchine
triple of the time-`1` marginal. -/
noncomputable def compoundPoissonTriple (b : ℝ) (r : ℝ≥0) (ν' : Measure ℝ)
    [IsProbabilityMeasure ν'] (hν' : ν' {0} = 0) : LevyKhintchineTriple where
  drift := b + ∫ x in {x : ℝ | |x| < 1}, x ∂((r : ℝ≥0∞) • ν')
  gaussianVariance := 0
  levyMeasure := (r : ℝ≥0∞) • ν'
  levyMeasure_isLevyMeasure := by
    haveI : IsFiniteMeasure ((r : ℝ≥0∞) • ν') := Measure.smul_finite ν' ENNReal.coe_ne_top
    refine IsLevyMeasure.of_isFiniteMeasure ?_
    rw [Measure.smul_apply, hν', smul_zero]

/-- **The compound-Poisson exponent identity.** The Lévy–Khintchine exponent of
`compoundPoissonTriple b r ν'` equals the compound-Poisson characteristic exponent
`i b ξ + r (charFun ν' ξ − 1)`. The small-jump drift correction inside the triple exactly cancels
the imaginary compensator `∫ i x ξ · 1_{|x| < 1} d(r · ν')`, and `∫ (e^{i x ξ} − 1) d(r · ν')`
evaluates to `r (charFun ν' ξ − 1)` because `ν'` is a probability measure. -/
private lemma exponent_compoundPoissonTriple (b : ℝ) (r : ℝ≥0) (ν' : Measure ℝ)
    [IsProbabilityMeasure ν'] (hν' : ν' {0} = 0) (ξ : ℝ) :
    (compoundPoissonTriple b r ν' hν').exponent ξ
      = Complex.I * b * ξ + r * (charFun ν' ξ - 1) := by
  have hSmeas : MeasurableSet {x : ℝ | |x| < 1} :=
    measurableSet_lt continuous_abs.measurable measurable_const
  -- Integrability of the pieces against the finite probability measure `ν'`.
  have hexpint : Integrable (fun x => Complex.exp (↑x * ↑ξ * Complex.I)) ν' := by
    apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
    refine ae_of_all _ fun x => ?_
    have hn : ‖Complex.exp (↑x * ↑ξ * Complex.I)‖ = 1 := by
      rw [show (↑x * ↑ξ * Complex.I : ℂ) = ↑(x * ξ) * Complex.I from by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    exact le_of_eq hn
  have hmeas_g2 : Measurable
      (fun x : ℝ => (↑x : ℂ) * ↑ξ * Complex.I * (if |x| < 1 then (1 : ℂ) else 0)) :=
    (((Complex.continuous_ofReal.measurable).mul measurable_const).mul measurable_const).mul
      (Measurable.ite hSmeas measurable_const measurable_const)
  have hg2int : Integrable
      (fun x : ℝ => (↑x : ℂ) * ↑ξ * Complex.I * (if |x| < 1 then (1 : ℂ) else 0)) ν' := by
    apply (integrable_const |ξ|).mono' hmeas_g2.aestronglyMeasurable
    refine ae_of_all _ fun x => ?_
    by_cases hx : |x| < 1
    · simp only [hx, if_true, mul_one]
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      calc |x| * |ξ| ≤ 1 * |ξ| := mul_le_mul_of_nonneg_right hx.le (abs_nonneg _)
        _ = |ξ| := one_mul _
    · simp only [hx, if_false, mul_zero, norm_zero]; exact abs_nonneg ξ
  -- `∫ (e^{i x ξ} − 1) dν' = charFun ν' ξ − 1`.
  have hE : ∫ x, (Complex.exp (↑x * ↑ξ * Complex.I) - 1) ∂ν' = charFun ν' ξ - 1 := by
    rw [integral_sub hexpint (integrable_const 1)]
    have h1 : (∫ _ : ℝ, (1 : ℂ) ∂ν') = 1 := by simp
    rw [h1]
    congr 1
    rw [charFun_apply_real]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact congrArg Complex.exp (by ring)
  -- The imaginary compensator integral, bridged to the real small-jump integral.
  have hg2 : ∫ x, (↑x : ℂ) * ↑ξ * Complex.I * (if |x| < 1 then (1 : ℂ) else 0) ∂ν'
      = ↑ξ * Complex.I * ↑(∫ x in {x : ℝ | |x| < 1}, x ∂ν') := by
    have hpt : ∀ x : ℝ, (↑x : ℂ) * ↑ξ * Complex.I * (if |x| < 1 then (1 : ℂ) else 0)
        = (↑ξ * Complex.I) * ((({x : ℝ | |x| < 1}).indicator (fun y => y) x : ℝ) : ℂ) := by
      intro x
      rw [Set.indicator_apply]
      by_cases hx : x ∈ {x : ℝ | |x| < 1}
      · have hlt : |x| < 1 := hx
        rw [if_pos hlt, if_pos hx]; ring
      · have hlt : ¬ |x| < 1 := hx
        rw [if_neg hlt, if_neg hx]; push_cast; ring
    calc ∫ x, (↑x : ℂ) * ↑ξ * Complex.I * (if |x| < 1 then (1 : ℂ) else 0) ∂ν'
        = ∫ x, (↑ξ * Complex.I) *
            ((({x : ℝ | |x| < 1}).indicator (fun y => y) x : ℝ) : ℂ) ∂ν' :=
          integral_congr_ae (ae_of_all _ hpt)
      _ = (↑ξ * Complex.I) *
            ∫ x, ((({x : ℝ | |x| < 1}).indicator (fun y => y) x : ℝ) : ℂ) ∂ν' :=
          integral_const_mul _ _
      _ = (↑ξ * Complex.I) * ↑(∫ x, ({x : ℝ | |x| < 1}).indicator (fun y => y) x ∂ν') :=
          congrArg _ integral_complex_ofReal
      _ = ↑ξ * Complex.I * ↑(∫ x in {x : ℝ | |x| < 1}, x ∂ν') := by
          rw [integral_indicator hSmeas]
  -- Split the compensated integral against `ν'`.
  have hCsplit : ∫ x, levyCompensatedIntegrand ξ x ∂ν'
      = (charFun ν' ξ - 1) - ↑ξ * Complex.I * ↑(∫ x in {x : ℝ | |x| < 1}, x ∂ν') := by
    simp only [levyCompensatedIntegrand_def]
    have hsub : ∫ x, (Complex.exp (↑x * ↑ξ * Complex.I) - 1
          - ↑x * ↑ξ * Complex.I * (if |x| < 1 then (1 : ℂ) else 0)) ∂ν'
        = (∫ x, (Complex.exp (↑x * ↑ξ * Complex.I) - 1) ∂ν')
          - ∫ x, (↑x : ℂ) * ↑ξ * Complex.I * (if |x| < 1 then (1 : ℂ) else 0) ∂ν' :=
      integral_sub (hexpint.sub (integrable_const 1)) hg2int
    rw [hsub, hE, hg2]
  -- Pull the scalar `r` through both the compensated and the small-jump integral.
  have hCscale : ∫ x, levyCompensatedIntegrand ξ x ∂((r : ℝ≥0∞) • ν')
      = (r : ℂ) * ((charFun ν' ξ - 1)
          - ↑ξ * Complex.I * ↑(∫ x in {x : ℝ | |x| < 1}, x ∂ν')) := by
    rw [integral_smul_measure, ENNReal.coe_toReal, hCsplit]
    exact Complex.real_smul
  have hDscale : (∫ x in {x : ℝ | |x| < 1}, x ∂((r : ℝ≥0∞) • ν'))
      = (r : ℝ) * ∫ x in {x : ℝ | |x| < 1}, x ∂ν' := by
    rw [Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
  -- Reduce the triple's slots and finish by algebra.
  have hdrift : (compoundPoissonTriple b r ν' hν').drift
      = b + ∫ x in {x : ℝ | |x| < 1}, x ∂((r : ℝ≥0∞) • ν') := rfl
  have hgauss : (compoundPoissonTriple b r ν' hν').gaussianVariance = 0 := rfl
  have hmeasure : (compoundPoissonTriple b r ν' hν').levyMeasure = (r : ℝ≥0∞) • ν' := rfl
  rw [LevyKhintchineTriple.exponent_def, hdrift, hgauss, hmeasure, hCscale, hDscale]
  push_cast
  ring

/-- **Scaling the compound-Poisson exponent in time.** Scaling the exponent by `t` is the same as
scaling the triple's drift and jump rate by `t`; this identifies the time-`t` marginal's exponent
with the exponent of a genuine Lévy–Khintchine triple, which is what the infinite-divisibility
criterion consumes. -/
private lemma exponent_smul_compoundPoissonTriple (b : ℝ) (r : ℝ≥0) (ν' : Measure ℝ)
    [IsProbabilityMeasure ν'] (hν' : ν' {0} = 0) (t : ℝ≥0) (ξ : ℝ) :
    (t : ℝ) * (compoundPoissonTriple b r ν' hν').exponent ξ
      = (compoundPoissonTriple (t * b) (t * r) ν' hν').exponent ξ := by
  rw [exponent_compoundPoissonTriple, exponent_compoundPoissonTriple]
  push_cast
  ring

/-- **The compound Poisson marginal realizes its Lévy–Khintchine triple.** At each time `t`, the
characteristic function of the compound-Poisson-with-drift marginal `Xₜ` is the exponential of `t`
times the Lévy–Khintchine exponent of `compoundPoissonTriple b r ν'`, i.e. the marginal is the
infinitely divisible law of the finite-activity, zero-Gaussian triple with drift `b`, jump rate `r`,
and jump law `ν'`. -/
theorem charFun_map_compoundPoisson_eq_exponent [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν'] (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r)
    (hν' : ν' {0} = 0) (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (compoundPoisson b τ Y (t : ℝ))) ξ
      = Complex.exp ((t : ℝ) * (compoundPoissonTriple b r ν' hν').exponent ξ) := by
  rw [exponent_compoundPoissonTriple b r ν' hν' ξ, charFun_map_compoundPoisson hd hr b t ξ]

/-- **The compound Poisson marginal is infinitely divisible.** Each marginal `Xₜ` of the
compound-Poisson-with-drift process is an infinitely divisible law on `ℝ`: its characteristic
function is `exp` of a Lévy–Khintchine exponent (the `t`-scaled triple
`compoundPoissonTriple (t · b) (t · r) ν'`), so the converse Lévy–Khintchine theorem applies. -/
theorem isInfinitelyDivisible_map_compoundPoisson [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν'] (hd : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r)
    (hν' : ν' {0} = 0) (b : ℝ) (t : ℝ≥0) :
    IsInfinitelyDivisible (μ.map (compoundPoisson b τ Y (t : ℝ))) := by
  have hXmeas : Measurable (compoundPoisson b τ Y (t : ℝ)) :=
    measurable_compoundPoisson hd.measurable_interarrival hd.measurable_mark _
  haveI : IsProbabilityMeasure (μ.map (compoundPoisson b τ Y (t : ℝ))) :=
    Measure.isProbabilityMeasure_map hXmeas.aemeasurable
  refine isInfinitelyDivisible_iff_exists_levyKhintchineTriple.mpr
    ⟨compoundPoissonTriple (t * b) (t * r) ν' hν', fun ξ => ?_⟩
  rw [charFun_map_compoundPoisson_eq_exponent hd hr hν' b t ξ,
    exponent_smul_compoundPoissonTriple b r ν' hν' t ξ]

end ProbabilityTheory
