/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.Real.ConjExponents
import LeanLevy.RandomMeasure.PoissonPointFamily

/-!
# The compensated Poisson integral and its isometry

For a σ-finite intensity `m` on `E`, the Poisson point family `(K, X)` of `PoissonPointFamily`
attaches to each partition piece `k` the *piece sum* `pieceSum K X f k`, a random Poisson sum of a
test function `f`.  This file introduces the **compensated** piece sum
`compensatedPieceSum K X f m k = pieceSum K X f k - ∫_{piece k} f dm` and its countable aggregate
`compensatedPoissonSum K X f m = ∑' k, compensatedPieceSum K X f m k`, the pathwise value of the
compensated Poisson integral `∫ f d(N - m)`.

The main result is the **L² isometry** (Campbell's second formula)
`∫ (compensatedPoissonSum K X f m)² dμ = ∫ f² dm` for `f ∈ L¹(m) ∩ L²(m)`, together with the
supporting facts that the compensated integral is centered, is itself an `L²(μ)` random variable,
and is additive / homogeneous in `f`.  These are the inputs for extending the compensated integral
to all of `L²(m)` by density.

## Main definitions

* `ProbabilityTheory.compensatedPieceSum` — the centered piece sum on a single piece.
* `ProbabilityTheory.compensatedPoissonSum` — the aggregate compensated Poisson integral.

## Main results

* `ProbabilityTheory.integral_compensatedPoissonSum` — the compensated integral has mean zero.
* `ProbabilityTheory.integral_sq_compensatedPoissonSum` — the **isometry** `E[(∫ f dÑ)²] = ∫ f² dm`.
* `ProbabilityTheory.memLp_two_compensatedPoissonSum` — the compensated integral lies in `L²(μ)`.
* `ProbabilityTheory.compensatedPoissonSum_add`, `ProbabilityTheory.compensatedPoissonSum_const_mul`
  — linearity of the compensated integral in the test function.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

section Compensated

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {f g : E → ℝ} {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω} {k : ℕ}

/-- The **compensated piece sum**: the piece sum with its mean subtracted, so it is centered. -/
noncomputable def compensatedPieceSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (f : E → ℝ)
    (m : Measure E) [SigmaFinite m] (k : ℕ) (ω : Ω) : ℝ :=
  pieceSum K X f k ω - ∫ x in prmPiece m k, f x ∂m

/-- The **compensated Poisson integral**: the sum of the compensated piece sums over all pieces. -/
noncomputable def compensatedPoissonSum (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (f : E → ℝ)
    (m : Measure E) [SigmaFinite m] (ω : Ω) : ℝ :=
  ∑' k, compensatedPieceSum K X f m k ω

/-! ### Per-piece facts -/

/-- On a probability space the piece sum of an `L¹ ∩ L²` function is integrable. -/
private theorem integrable_pieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    Integrable (pieceSum K X f k) μ :=
  ((memLp_two_iff_integrable_sq
    (measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf).aestronglyMeasurable).mpr
      (integrable_sq_pieceSum hd hf hf1.integrableOn hf2.integrable_sq.integrableOn)).integrable
    one_le_two

/-- The compensated piece sum is measurable. -/
theorem measurable_compensatedPieceSum (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) :
    Measurable (compensatedPieceSum K X f m k) :=
  (measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf).sub_const _

/-- The compensated piece sum is integrable. -/
theorem integrable_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    Integrable (compensatedPieceSum K X f m k) μ :=
  (integrable_pieceSum (k := k) hd hf hf1 hf2).sub (integrable_const _)

/-- The compensated piece sum lies in `L²(μ)`. -/
theorem memLp_two_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    MemLp (compensatedPieceSum K X f m k) 2 μ :=
  ((memLp_two_iff_integrable_sq
    (measurable_pieceSum (hd.measurable_count k) (hd.measurable_point k) hf).aestronglyMeasurable).mpr
      (integrable_sq_pieceSum hd hf hf1.integrableOn hf2.integrable_sq.integrableOn)).sub
    (memLp_const _)

/-- The compensated piece sum is centered: its mean is zero. -/
theorem integral_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∫ ω, compensatedPieceSum K X f m k ω ∂μ = 0 := by
  simp only [compensatedPieceSum]
  rw [integral_sub (integrable_pieceSum (k := k) hd hf hf1 hf2) (integrable_const _),
    integral_pieceSum hd hf hf1.integrableOn, integral_const, probReal_univ, one_smul, sub_self]

/-- The second moment of the compensated piece sum equals the `L²`-mass of the piece. -/
theorem integral_sq_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∫ ω, (compensatedPieceSum K X f m k ω) ^ 2 ∂μ = ∫ x in prmPiece m k, f x ^ 2 ∂m := by
  have hSint := integrable_pieceSum (k := k) hd hf hf1 hf2
  have hS2int := integrable_sq_pieceSum (k := k) hd hf hf1.integrableOn hf2.integrable_sq.integrableOn
  set C := ∫ x in prmPiece m k, f x ∂m with hC
  calc ∫ ω, (compensatedPieceSum K X f m k ω) ^ 2 ∂μ
      = ∫ ω, ((pieceSum K X f k ω) ^ 2 + (-(2 * C)) * pieceSum K X f k ω + C ^ 2) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [compensatedPieceSum]; ring
    _ = (∫ ω, (pieceSum K X f k ω) ^ 2 ∂μ) + (-(2 * C)) * (∫ ω, pieceSum K X f k ω ∂μ) + C ^ 2 := by
        have e1 : ∫ ω, ((pieceSum K X f k ω) ^ 2 + (-(2 * C)) * pieceSum K X f k ω + C ^ 2) ∂μ
            = (∫ ω, ((pieceSum K X f k ω) ^ 2 + (-(2 * C)) * pieceSum K X f k ω) ∂μ)
              + ∫ _ω, C ^ 2 ∂μ :=
          integral_add (hS2int.add (hSint.const_mul _)) (integrable_const _)
        have e2 : ∫ ω, ((pieceSum K X f k ω) ^ 2 + (-(2 * C)) * pieceSum K X f k ω) ∂μ
            = (∫ ω, (pieceSum K X f k ω) ^ 2 ∂μ) + ∫ ω, (-(2 * C)) * pieceSum K X f k ω ∂μ :=
          integral_add hS2int (hSint.const_mul _)
        rw [e1, e2, integral_const_mul, integral_const, probReal_univ, one_smul]
    _ = ∫ x in prmPiece m k, f x ^ 2 ∂m := by
        rw [integral_sq_pieceSum hd hf hf1.integrableOn hf2.integrable_sq.integrableOn,
          integral_pieceSum hd hf hf1.integrableOn]
        ring

/-- Compensated piece sums of distinct pieces are independent. -/
theorem indepFun_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hg : Measurable g) {j k : ℕ} (hjk : j ≠ k) :
    IndepFun (compensatedPieceSum K X f m j) (compensatedPieceSum K X g m k) μ :=
  (indepFun_pieceSum_pieceSum hd hf hg hjk).comp
    (φ := fun x => x - ∫ x in prmPiece m j, f x ∂m)
    (ψ := fun x => x - ∫ x in prmPiece m k, g x ∂m)
    (measurable_id.sub_const _) (measurable_id.sub_const _)

/-- **Bienaymé's identity** for a finite family of pieces: because the compensated piece sums are
centered and pairwise independent, the second moment of their sum is the sum of the piece
`L²`-masses. -/
theorem integral_sq_finsetSum_compensatedPieceSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) (s : Finset ℕ) :
    ∫ ω, (∑ k ∈ s, compensatedPieceSum K X f m k ω) ^ 2 ∂μ
      = ∑ k ∈ s, ∫ x in prmPiece m k, f x ^ 2 ∂m := by
  have hcenter : ∀ k, ∫ ω, compensatedPieceSum K X f m k ω ∂μ = 0 :=
    fun k => integral_compensatedPieceSum hd hf hf1 hf2
  have hfun_eq : (∑ k ∈ s, compensatedPieceSum K X f m k)
      = fun ω => ∑ k ∈ s, compensatedPieceSum K X f m k ω := by funext ω; rw [Finset.sum_apply]
  have hAEmeas : AEMeasurable (fun ω => ∑ k ∈ s, compensatedPieceSum K X f m k ω) μ :=
    (Finset.measurable_sum s fun k _ => measurable_compensatedPieceSum hd hf).aemeasurable
  have hSint0 : ∫ ω, (∑ k ∈ s, compensatedPieceSum K X f m k ω) ∂μ = 0 := by
    rw [integral_finset_sum s fun k _ => integrable_compensatedPieceSum hd hf hf1 hf2]
    simp [hcenter]
  calc ∫ ω, (∑ k ∈ s, compensatedPieceSum K X f m k ω) ^ 2 ∂μ
      = variance (fun ω => ∑ k ∈ s, compensatedPieceSum K X f m k ω) μ :=
        (variance_of_integral_eq_zero hAEmeas hSint0).symm
    _ = variance (∑ k ∈ s, compensatedPieceSum K X f m k) μ := by rw [hfun_eq]
    _ = ∑ k ∈ s, variance (compensatedPieceSum K X f m k) μ :=
        IndepFun.variance_sum (fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2)
          (fun i _ j _ hij => indepFun_compensatedPieceSum hd hf hf hij)
    _ = ∑ k ∈ s, ∫ x in prmPiece m k, f x ^ 2 ∂m := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [variance_of_integral_eq_zero (measurable_compensatedPieceSum hd hf).aemeasurable
          (hcenter k)]
        exact integral_sq_compensatedPieceSum hd hf hf1 hf2

/-! ### Analytic helpers -/

omit [Nonempty E] in
/-- The piece integrals of an integrable function over the pieces sum to its total integral. -/
private theorem hasSum_setIntegral_prmPiece {φ : E → ℝ} (hφ : Integrable φ m) :
    HasSum (fun k => ∫ x in prmPiece m k, φ x ∂m) (∫ x, φ x ∂m) := by
  have hunion : IntegrableOn φ (⋃ k, prmPiece m k) m := by
    rw [iUnion_prmPiece]; exact hφ.integrableOn
  have h := hasSum_integral_iUnion (fun k => measurableSet_prmPiece) pairwise_disjoint_prmPiece hunion
  rwa [iUnion_prmPiece, setIntegral_univ] at h

/-- Cauchy–Schwarz for real integrals against a probability measure. -/
private theorem abs_integral_mul_le_sqrt {a b : Ω → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    |∫ ω, a ω * b ω ∂μ| ≤ Real.sqrt (∫ ω, (a ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (b ω) ^ 2 ∂μ) := by
  have ha' : MemLp (fun ω => |a ω|) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; simpa [Real.norm_eq_abs] using ha.norm
  have hb' : MemLp (fun ω => |b ω|) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]; simpa [Real.norm_eq_abs] using hb.norm
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun ω => abs_nonneg (a ω)) (Eventually.of_forall fun ω => abs_nonneg (b ω))
    ha' hb'
  have hrw : ∀ h : Ω → ℝ, (∫ ω, |h ω| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
      = Real.sqrt (∫ ω, (h ω) ^ 2 ∂μ) := by
    intro h
    rw [← Real.sqrt_eq_rpow]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only []
    rw [← sq_abs (h ω), ← Real.rpow_natCast |h ω| 2]
    norm_num
  calc |∫ ω, a ω * b ω ∂μ|
      ≤ ∫ ω, |a ω * b ω| ∂μ := abs_integral_le_integral_abs
    _ = ∫ ω, |a ω| * |b ω| ∂μ := by simp_rw [abs_mul]
    _ ≤ (∫ ω, |a ω| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) * (∫ ω, |b ω| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hCS
    _ = Real.sqrt (∫ ω, (a ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (b ω) ^ 2 ∂μ) := by rw [hrw, hrw]

/-- **Fatou lower-semicontinuity of the second moment.** If `gseq n → G` a.e. and the second
moments of `gseq n` are bounded by `C ≥ 0`, then `G` is square-integrable with second moment at
most `C`. -/
private theorem fatou_sq_bound {gseq : ℕ → Ω → ℝ} {G : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ n, Measurable (gseq n)) (hG : AEStronglyMeasurable G μ)
    (hint : ∀ n, Integrable (fun ω => (gseq n ω) ^ 2) μ)
    (htend : ∀ᵐ ω ∂μ, Tendsto (fun n => gseq n ω) atTop (𝓝 (G ω)))
    (hbnd : ∀ n, ∫ ω, (gseq n ω) ^ 2 ∂μ ≤ C) :
    Integrable (fun ω => (G ω) ^ 2) μ ∧ ∫ ω, (G ω) ^ 2 ∂μ ≤ C := by
  set F : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal ((gseq n ω) ^ 2) with hF
  have hFmeas : ∀ n, Measurable (F n) := fun n => ((hg n).pow_const 2).ennreal_ofReal
  have hFint : ∀ n, ∫⁻ ω, F n ω ∂μ = ENNReal.ofReal (∫ ω, (gseq n ω) ^ 2 ∂μ) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hint n) (Eventually.of_forall fun ω => by positivity)).symm
  have hliminf : ∀ᵐ ω ∂μ, ENNReal.ofReal ((G ω) ^ 2) = liminf (fun n => F n ω) atTop := by
    filter_upwards [htend] with ω hω
    have : Tendsto (fun n => F n ω) atTop (𝓝 (ENNReal.ofReal ((G ω) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (hω.pow 2)
    exact this.liminf_eq.symm
  have hfatou : ∫⁻ ω, ENNReal.ofReal ((G ω) ^ 2) ∂μ ≤ liminf (fun n => ∫⁻ ω, F n ω ∂μ) atTop := by
    rw [lintegral_congr_ae hliminf]
    exact lintegral_liminf_le hFmeas
  have hle : liminf (fun n => ∫⁻ ω, F n ω ∂μ) atTop ≤ ENNReal.ofReal C := by
    refine (Filter.liminf_le_liminf (Eventually.of_forall fun n => ?_)).trans (by rw [liminf_const])
    rw [hFint n]; exact ENNReal.ofReal_le_ofReal (hbnd n)
  have hbnd2 : ∫⁻ ω, ENNReal.ofReal ((G ω) ^ 2) ∂μ ≤ ENNReal.ofReal C := hfatou.trans hle
  have hGsq_aesm : AEStronglyMeasurable (fun ω => (G ω) ^ 2) μ := hG.pow 2
  have henorm : ∀ ω, ‖(G ω) ^ 2‖ₑ = ENNReal.ofReal ((G ω) ^ 2) := fun ω =>
    Real.enorm_of_nonneg (by positivity)
  refine ⟨⟨hGsq_aesm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_enorm]
    simp_rw [henorm]
    exact lt_of_le_of_lt hbnd2 ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => by positivity) hGsq_aesm]
    calc (∫⁻ ω, ENNReal.ofReal ((G ω) ^ 2) ∂μ).toReal
        ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbnd2
      _ = C := ENNReal.toReal_ofReal hC

/-! ### Absolute convergence and mean zero -/

/-- The mean absolute size of a compensated piece sum is controlled by the piece `L¹`-mass. -/
private theorem integral_norm_compensatedPieceSum_le [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ∫ ω, ‖compensatedPieceSum K X f m k ω‖ ∂μ ≤ 2 * ∫ x in prmPiece m k, ‖f x‖ ∂m := by
  set C := ∫ x in prmPiece m k, f x ∂m with hC
  have hSnInt : Integrable (pieceSum K X (fun x => ‖f x‖) k) μ :=
    integrable_pieceSum (k := k) hd hf.norm hf1.norm hf2.norm
  have hcompInt : Integrable (compensatedPieceSum K X f m k) μ :=
    integrable_compensatedPieceSum (k := k) hd hf hf1 hf2
  have hle : ∀ ω, ‖compensatedPieceSum K X f m k ω‖ ≤ pieceSum K X (fun x => ‖f x‖) k ω + ‖C‖ := by
    intro ω
    have h1 : ‖compensatedPieceSum K X f m k ω‖ ≤ ‖pieceSum K X f k ω‖ + ‖C‖ := by
      simp only [compensatedPieceSum]; exact norm_sub_le _ _
    have h2 : ‖pieceSum K X f k ω‖ ≤ pieceSum K X (fun x => ‖f x‖) k ω := by
      simp only [pieceSum]
      exact norm_sum_le _ _
    linarith
  calc ∫ ω, ‖compensatedPieceSum K X f m k ω‖ ∂μ
      ≤ ∫ ω, (pieceSum K X (fun x => ‖f x‖) k ω + ‖C‖) ∂μ :=
        integral_mono hcompInt.norm (hSnInt.add (integrable_const _)) hle
    _ = (∫ ω, pieceSum K X (fun x => ‖f x‖) k ω ∂μ) + ‖C‖ := by
        rw [integral_add hSnInt (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ 2 * ∫ x in prmPiece m k, ‖f x‖ ∂m := by
        rw [integral_pieceSum hd hf.norm hf1.norm.integrableOn]
        have hCnorm : ‖C‖ ≤ ∫ x in prmPiece m k, ‖f x‖ ∂m := by
          rw [hC]; exact norm_integral_le_integral_norm _
        linarith

/-- The mean absolute sizes of the compensated piece sums are summable (they are controlled by the
`L¹`-mass of `f`), so the compensated Poisson series converges absolutely almost surely. -/
private theorem tsum_lintegral_enorm_compensatedPieceSum_ne_top [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ∑' k, ∫⁻ ω, ‖compensatedPieceSum K X f m k ω‖ₑ ∂μ ≠ ⊤ := by
  have hbound : ∀ k, ∫⁻ ω, ‖compensatedPieceSum K X f m k ω‖ₑ ∂μ
      ≤ ENNReal.ofReal (2 * ∫ x in prmPiece m k, ‖f x‖ ∂m) := by
    intro k
    rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_compensatedPieceSum hd hf hf1 hf2)]
    exact ENNReal.ofReal_le_ofReal (integral_norm_compensatedPieceSum_le hd hf hf1 hf2)
  have hsum : Summable (fun k => 2 * ∫ x in prmPiece m k, ‖f x‖ ∂m) :=
    ((hasSum_setIntegral_prmPiece hf1.norm).mul_left 2).summable
  exact ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hbound)

/-- The compensated Poisson series converges absolutely almost surely. -/
theorem ae_summable_compensatedPieceSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∀ᵐ ω ∂μ, Summable (fun k => compensatedPieceSum K X f m k ω) := by
  have hmeas : ∀ k, AEMeasurable (fun ω => ‖compensatedPieceSum K X f m k ω‖ₑ) μ :=
    fun k => (measurable_compensatedPieceSum hd hf).enorm.aemeasurable
  have hfin : ∫⁻ ω, ∑' k, ‖compensatedPieceSum K X f m k ω‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    exact tsum_lintegral_enorm_compensatedPieceSum_ne_top hd hf hf1 hf2
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) hfin
  filter_upwards [hae] with ω hω
  have hsc : Summable (fun k => ‖compensatedPieceSum K X f m k ω‖₊) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa only [enorm_eq_nnnorm] using hω.ne
  have hsr : Summable (fun k => ‖compensatedPieceSum K X f m k ω‖) := by
    simpa only [coe_nnnorm] using NNReal.summable_coe.mpr hsc
  exact hsr.of_norm

/-- The compensated Poisson integral is almost-everywhere strongly measurable. -/
theorem aestronglyMeasurable_compensatedPoissonSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) : AEStronglyMeasurable (compensatedPoissonSum K X f m) μ := by
  have htend : ∀ᵐ ω ∂μ, Tendsto (fun n => ∑ k ∈ Finset.range n, compensatedPieceSum K X f m k ω)
      atTop (𝓝 (compensatedPoissonSum K X f m ω)) := by
    filter_upwards [ae_summable_compensatedPieceSum hd hf hf1 hf2] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  exact aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (Finset.measurable_sum _ fun k _ =>
      measurable_compensatedPieceSum hd hf).aestronglyMeasurable) htend

/-- The compensated Poisson integral has mean zero. -/
theorem integral_compensatedPoissonSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    ∫ ω, compensatedPoissonSum K X f m ω ∂μ = 0 := by
  simp only [compensatedPoissonSum]
  rw [integral_tsum (fun k => (measurable_compensatedPieceSum hd hf).aestronglyMeasurable)
    (tsum_lintegral_enorm_compensatedPieceSum_ne_top hd hf hf1 hf2)]
  simp [integral_compensatedPieceSum hd hf hf1 hf2]

/-! ### The isometry -/

/-- The compensated Poisson integral is square-integrable, with second moment at most `∫ f² dm`. -/
private theorem memLp_two_and_integral_sq_le [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    MemLp (compensatedPoissonSum K X f m) 2 μ
      ∧ ∫ ω, (compensatedPoissonSum K X f m ω) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂m := by
  set v : ℕ → ℝ := fun k => ∫ x in prmPiece m k, f x ^ 2 ∂m with hv
  have hv_nonneg : ∀ k, 0 ≤ v k := fun k => integral_nonneg fun x => sq_nonneg (f x)
  have hv_hasSum : HasSum v (∫ x, f x ^ 2 ∂m) := hasSum_setIntegral_prmPiece hf2.integrable_sq
  set Tn : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, compensatedPieceSum K X f m k ω with hTn
  have hTnmeas : ∀ n, Measurable (Tn n) :=
    fun n => Finset.measurable_sum _ fun k _ => measurable_compensatedPieceSum hd hf
  have hTnint : ∀ n, Integrable (fun ω => (Tn n ω) ^ 2) μ :=
    fun n => (memLp_finset_sum _ fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2).integrable_sq
  have hTnle : ∀ n, ∫ ω, (Tn n ω) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂m := by
    intro n
    rw [integral_sq_finsetSum_compensatedPieceSum hd hf hf1 hf2 (Finset.range n)]
    exact sum_le_hasSum _ (fun i _ => hv_nonneg i) hv_hasSum
  have htend : ∀ᵐ ω ∂μ, Tendsto (fun n => Tn n ω) atTop (𝓝 (compensatedPoissonSum K X f m ω)) := by
    filter_upwards [ae_summable_compensatedPieceSum hd hf hf1 hf2] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  obtain ⟨hTsq_int, hTsq_le⟩ := fatou_sq_bound (integral_nonneg fun x => sq_nonneg (f x)) hTnmeas
    (aestronglyMeasurable_compensatedPoissonSum hd hf hf1 hf2) hTnint htend hTnle
  exact ⟨(memLp_two_iff_integrable_sq
    (aestronglyMeasurable_compensatedPoissonSum hd hf hf1 hf2)).mpr hTsq_int, hTsq_le⟩

/-- The compensated Poisson integral lies in `L²(μ)`. -/
theorem memLp_two_compensatedPoissonSum [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) :
    MemLp (compensatedPoissonSum K X f m) 2 μ :=
  (memLp_two_and_integral_sq_le hd hf hf1 hf2).1

/-- **The compensated Poisson integral isometry (Campbell's second formula).** For an `L¹ ∩ L²`
test function, the second moment of the compensated Poisson integral equals the `L²`-mass of the
function against the intensity. -/
theorem integral_sq_compensatedPoissonSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ) (hf : Measurable f) (hf1 : Integrable f m)
    (hf2 : MemLp f 2 m) :
    ∫ ω, (compensatedPoissonSum K X f m ω) ^ 2 ∂μ = ∫ x, f x ^ 2 ∂m := by
  obtain ⟨hTmemlp, hTsq_le⟩ := memLp_two_and_integral_sq_le hd hf hf1 hf2
  have hTsq_int : Integrable (fun ω => (compensatedPoissonSum K X f m ω) ^ 2) μ :=
    hTmemlp.integrable_sq
  set T := compensatedPoissonSum K X f m with hTdef
  set v : ℕ → ℝ := fun k => ∫ x in prmPiece m k, f x ^ 2 ∂m with hv
  have hv_nonneg : ∀ k, 0 ≤ v k := fun k => integral_nonneg fun x => sq_nonneg (f x)
  have hv_hasSum : HasSum v (∫ x, f x ^ 2 ∂m) := hasSum_setIntegral_prmPiece hf2.integrable_sq
  set Tn : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, compensatedPieceSum K X f m k ω with hTn
  have hTnmemlp : ∀ n, MemLp (Tn n) 2 μ :=
    fun n => memLp_finset_sum _ fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2
  have hTnint : ∀ n, Integrable (fun ω => (Tn n ω) ^ 2) μ := fun n => (hTnmemlp n).integrable_sq
  have hTnsq : ∀ n, ∫ ω, (Tn n ω) ^ 2 ∂μ = ∑ k ∈ Finset.range n, v k :=
    fun n => integral_sq_finsetSum_compensatedPieceSum hd hf hf1 hf2 (Finset.range n)
  have hTnle : ∀ n, ∫ ω, (Tn n ω) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂m := by
    intro n; rw [hTnsq]; exact sum_le_hasSum _ (fun i _ => hv_nonneg i) hv_hasSum
  have htend : ∀ᵐ ω ∂μ, Tendsto (fun n => Tn n ω) atTop (𝓝 (T ω)) := by
    filter_upwards [ae_summable_compensatedPieceSum hd hf hf1 hf2] with ω hω
    exact hω.hasSum.tendsto_sum_nat
  -- tail control of the partial sums
  set Sv : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, v k with hSv
  have hSv_tend : Tendsto Sv atTop (𝓝 (∫ x, f x ^ 2 ∂m)) := hv_hasSum.tendsto_sum_nat
  set r : ℕ → ℝ := fun n => (∫ x, f x ^ 2 ∂m) - Sv n with hr
  have hr_tend : Tendsto r atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => ∫ x, f x ^ 2 ∂m) atTop (𝓝 (∫ x, f x ^ 2 ∂m)) :=
      tendsto_const_nhds
    simpa [hr] using hc.sub hSv_tend
  have hr_nonneg : ∀ n, 0 ≤ r n := fun n => by
    rw [hr]; exact sub_nonneg.mpr (sum_le_hasSum _ (fun i _ => hv_nonneg i) hv_hasSum)
  have hdiff_le : ∀ n, ∫ ω, (T ω - Tn n ω) ^ 2 ∂μ ≤ r n := by
    intro n
    set gseq : ℕ → Ω → ℝ :=
      fun N ω => (∑ k ∈ Finset.range (N + n), compensatedPieceSum K X f m k ω)
        - ∑ k ∈ Finset.range n, compensatedPieceSum K X f m k ω with hgseq
    have hgmeas : ∀ N, Measurable (gseq N) := fun N =>
      (Finset.measurable_sum _ fun k _ => measurable_compensatedPieceSum hd hf).sub
        (Finset.measurable_sum _ fun k _ => measurable_compensatedPieceSum hd hf)
    have hgIco : ∀ N ω,
        gseq N ω = ∑ k ∈ Finset.Ico n (N + n), compensatedPieceSum K X f m k ω := fun N ω =>
      (Finset.sum_Ico_eq_sub _ (Nat.le_add_left n N)).symm
    have hgsq : ∀ N, ∫ ω, (gseq N ω) ^ 2 ∂μ = ∑ k ∈ Finset.Ico n (N + n), v k := by
      intro N
      rw [show (fun ω => (gseq N ω) ^ 2)
        = fun ω => (∑ k ∈ Finset.Ico n (N + n), compensatedPieceSum K X f m k ω) ^ 2 from
          funext fun ω => by rw [hgIco]]
      exact integral_sq_finsetSum_compensatedPieceSum hd hf hf1 hf2 (Finset.Ico n (N + n))
    have hgle : ∀ N, ∫ ω, (gseq N ω) ^ 2 ∂μ ≤ r n := by
      intro N
      rw [hgsq, Finset.sum_Ico_eq_sub _ (Nat.le_add_left n N), hr]
      have hbnd := sum_le_hasSum (Finset.range (N + n)) (fun i _ => hv_nonneg i) hv_hasSum
      simp only [hSv]; linarith
    have hgint : ∀ N, Integrable (fun ω => (gseq N ω) ^ 2) μ := fun N =>
      ((memLp_finset_sum _ fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2).sub
        (memLp_finset_sum _ fun k _ => memLp_two_compensatedPieceSum hd hf hf1 hf2)).integrable_sq
    have hgtend : ∀ᵐ ω ∂μ, Tendsto (fun N => gseq N ω) atTop (𝓝 (T ω - Tn n ω)) := by
      filter_upwards [htend] with ω hω
      exact (hω.comp (tendsto_add_atTop_nat n)).sub_const _
    exact (fatou_sq_bound (hr_nonneg n) hgmeas (hTmemlp.1.sub (hTnmemlp n).1) hgint hgtend hgle).2
  -- closing: ∫ Tn² converges to both ∫ T² and ∫ f²
  have hclose : Tendsto (fun n => ∫ ω, (Tn n ω) ^ 2 ∂μ) atTop (𝓝 (∫ ω, (T ω) ^ 2 ∂μ)) := by
    have hbound : ∀ n, |(∫ ω, (T ω) ^ 2 ∂μ) - ∫ ω, (Tn n ω) ^ 2 ∂μ|
        ≤ 2 * Real.sqrt (∫ x, f x ^ 2 ∂m) * Real.sqrt (r n) := by
      intro n
      have haMemLp : MemLp (fun ω => T ω - Tn n ω) 2 μ := hTmemlp.sub (hTnmemlp n)
      have hbMemLp : MemLp (fun ω => T ω + Tn n ω) 2 μ := hTmemlp.add (hTnmemlp n)
      have hdiffsq : (∫ ω, (T ω) ^ 2 ∂μ) - ∫ ω, (Tn n ω) ^ 2 ∂μ
          = ∫ ω, (T ω - Tn n ω) * (T ω + Tn n ω) ∂μ := by
        rw [← integral_sub hTsq_int (hTnint n)]
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_); ring
      have hsum_le : ∫ ω, (T ω + Tn n ω) ^ 2 ∂μ ≤ 4 * ∫ x, f x ^ 2 ∂m := by
        have hpt : ∀ ω, (T ω + Tn n ω) ^ 2 ≤ 2 * (T ω) ^ 2 + 2 * (Tn n ω) ^ 2 :=
          fun ω => by nlinarith [sq_nonneg (T ω - Tn n ω)]
        calc ∫ ω, (T ω + Tn n ω) ^ 2 ∂μ
            ≤ ∫ ω, (2 * (T ω) ^ 2 + 2 * (Tn n ω) ^ 2) ∂μ :=
              integral_mono hbMemLp.integrable_sq
                ((hTsq_int.const_mul 2).add ((hTnint n).const_mul 2)) hpt
          _ = 2 * (∫ ω, (T ω) ^ 2 ∂μ) + 2 * ∫ ω, (Tn n ω) ^ 2 ∂μ := by
              rw [integral_add (hTsq_int.const_mul 2) ((hTnint n).const_mul 2), integral_const_mul,
                integral_const_mul]
          _ ≤ 4 * ∫ x, f x ^ 2 ∂m := by nlinarith [hTsq_le, hTnle n]
      rw [hdiffsq]
      calc |∫ ω, (T ω - Tn n ω) * (T ω + Tn n ω) ∂μ|
          ≤ Real.sqrt (∫ ω, (T ω - Tn n ω) ^ 2 ∂μ) * Real.sqrt (∫ ω, (T ω + Tn n ω) ^ 2 ∂μ) :=
            abs_integral_mul_le_sqrt haMemLp hbMemLp
        _ ≤ Real.sqrt (r n) * (2 * Real.sqrt (∫ x, f x ^ 2 ∂m)) := by
            refine mul_le_mul (Real.sqrt_le_sqrt (hdiff_le n)) ?_ (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)
            rw [show (2 : ℝ) * Real.sqrt (∫ x, f x ^ 2 ∂m) = Real.sqrt (4 * ∫ x, f x ^ 2 ∂m) by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
                Real.sqrt_sq (by norm_num)]]
            exact Real.sqrt_le_sqrt hsum_le
        _ = 2 * Real.sqrt (∫ x, f x ^ 2 ∂m) * Real.sqrt (r n) := by ring
    have hbtend : Tendsto (fun n => 2 * Real.sqrt (∫ x, f x ^ 2 ∂m) * Real.sqrt (r n)) atTop
        (𝓝 0) := by
      have hsqrt : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
        simpa using hr_tend.sqrt
      simpa using hsqrt.const_mul (2 * Real.sqrt (∫ x, f x ^ 2 ∂m))
    have hzero : Tendsto (fun n => (∫ ω, (T ω) ^ 2 ∂μ) - ∫ ω, (Tn n ω) ^ 2 ∂μ) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hbound n) hbtend
    have hcT : Tendsto (fun _ : ℕ => ∫ ω, (T ω) ^ 2 ∂μ) atTop (𝓝 (∫ ω, (T ω) ^ 2 ∂μ)) :=
      tendsto_const_nhds
    simpa using hcT.sub hzero
  have hclose2 : Tendsto (fun n => ∫ ω, (Tn n ω) ^ 2 ∂μ) atTop (𝓝 (∫ x, f x ^ 2 ∂m)) := by
    simp_rw [hTnsq]; exact hSv_tend
  exact tendsto_nhds_unique hclose hclose2

/-! ### Linearity -/

omit [MeasurableSpace Ω] [Nonempty E] in
/-- The compensated piece sum is additive in the test function. -/
theorem compensatedPieceSum_add (hf1 : Integrable f (m.restrict (prmPiece m k)))
    (hg1 : Integrable g (m.restrict (prmPiece m k))) (ω : Ω) :
    compensatedPieceSum K X (fun x => f x + g x) m k ω
      = compensatedPieceSum K X f m k ω + compensatedPieceSum K X g m k ω := by
  simp only [compensatedPieceSum, pieceSum]
  rw [Finset.sum_add_distrib, integral_add hf1 hg1]
  ring

omit [MeasurableSpace Ω] [Nonempty E] in
/-- The compensated piece sum is homogeneous in the test function. -/
theorem compensatedPieceSum_const_mul (c : ℝ) (ω : Ω) :
    compensatedPieceSum K X (fun x => c * f x) m k ω = c * compensatedPieceSum K X f m k ω := by
  simp only [compensatedPieceSum, pieceSum]
  rw [← Finset.mul_sum, integral_const_mul]
  ring

/-- The compensated Poisson integral is additive in the test function (almost everywhere). -/
theorem compensatedPoissonSum_add [IsProbabilityMeasure μ] (hd : IsPoissonPointFamily K X m μ)
    (hf : Measurable f) (hf1 : Integrable f m) (hf2 : MemLp f 2 m) (hg : Measurable g)
    (hg1 : Integrable g m) (hg2 : MemLp g 2 m) :
    ∀ᵐ ω ∂μ, compensatedPoissonSum K X (fun x => f x + g x) m ω
      = compensatedPoissonSum K X f m ω + compensatedPoissonSum K X g m ω := by
  filter_upwards [ae_summable_compensatedPieceSum hd hf hf1 hf2,
    ae_summable_compensatedPieceSum hd hg hg1 hg2] with ω hsf hsg
  simp only [compensatedPoissonSum]
  rw [← (hsf.hasSum.add hsg.hasSum).tsum_eq]
  exact tsum_congr fun k => compensatedPieceSum_add hf1.integrableOn hg1.integrableOn ω

omit [MeasurableSpace Ω] [Nonempty E] in
/-- The compensated Poisson integral is homogeneous in the test function. -/
theorem compensatedPoissonSum_const_mul (c : ℝ) (ω : Ω) :
    compensatedPoissonSum K X (fun x => c * f x) m ω = c * compensatedPoissonSum K X f m ω := by
  simp only [compensatedPoissonSum]
  rw [← tsum_mul_left]
  exact tsum_congr fun k => compensatedPieceSum_const_mul c ω

end Compensated

end ProbabilityTheory
