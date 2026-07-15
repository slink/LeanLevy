/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.RandomMeasure.PoissonMartingale
import LeanLevy.Levy.LevyKhintchineUniqueness

/-!
# The assembled jump law

This file combines the two jump components of a Lévy process — the compound-Poisson large-jump
sum and the compensated small-jump integral — with a constant drift, and identifies the
characteristic function of their sum at a fixed time `t`.

The large-jump sum and the compensated small jumps are supported on the disjoint mark bands
`{|x| ≥ 1}` and `(-1, 1)`, so they are independent; their characteristic functions multiply.
Each factor is a compound-Poisson / compensated exponential of a band integral against the Lévy
measure `ν`, and the two band integrals reassemble the Lévy–Khintchine jump integral at split
radius `1`. Adding the deterministic drift `b · t` supplies the linear term, giving the
characteristic function `exp (t · ψ(ξ))` where `ψ` is the Lévy–Khintchine exponent of the triple
`(b, 0, ν)` — a triple with **zero Gaussian variance**, as befits a pure-jump process.

## Main results

* `ProbabilityTheory.charFun_map_levyJumpSum_eq_exponent` — **the assembled jump law**: for
  `0 ≤ t`, the fixed-time marginal law of `b · t + (large-jump sum) + (compensated small jumps)`
  has characteristic function `exp (t · (b, 0, ν).exponent ξ)`.
* `ProbabilityTheory.isInfinitelyDivisible_map_levyJumpSum` — for `0 ≤ t`, that same fixed-time
  marginal law is **infinitely divisible**: it is the Lévy–Khintchine law of the `t`-scaled triple
  `(t · b, 0, ENNReal.ofReal t • ν)`.
* `ProbabilityTheory.levyJumpProcess` — the **jump process** indexed by `ℝ≥0`: drift plus large-jump
  sum plus compensated small jumps. Only its law-level Lévy structure is established; no path
  regularity is claimed.
* `ProbabilityTheory.hasIndependentIncrements_levyJumpProcess` — **the jump process has independent
  increments** over any monotone time grid.
-/

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type} [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → ℝ × ℝ}
  {ν : Measure ℝ} [SigmaFinite ν] {μ : Measure Ω}

/-- **The assembled jump law**: drift plus large-jump sum plus compensated small jumps
realizes the Lévy–Khintchine exponent of the triple `(b, 0, ν)` at time `t`. -/
theorem charFun_map_levyJumpSum_eq_exponent [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    charFun (μ.map (fun ω => b * t + levyLargeJumpSum K X t ω
        + levyCompensatedSmallJump hd hν t ω)) ξ
      = Complex.exp ((t : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ) := by
  set L := levyLargeJumpSum K X t with hLdef
  set S := fun ω => levyCompensatedSmallJump hd hν t ω with hSdef
  have hL : Measurable L :=
    measurable_levyLargeJumpSum hd.measurable_count hd.measurable_point
  have hS : AEMeasurable S μ := (Lp.aestronglyMeasurable _).aemeasurable
  have hcont : Continuous fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I) := by fun_prop
  -- Independence factorizes the characteristic function of the sum of the two jump components.
  have hLS : charFun (μ.map (fun ω => L ω + S ω)) ξ
      = charFun (μ.map L) ξ * charFun (μ.map S) ξ := by
    have h := (indepFun_levyLargeJumpSum_levyCompensatedSmallJump hd hν ht).charFun_map_fun_add_eq_mul
      hL.aemeasurable hS
    simpa [Pi.mul_apply] using congrFun h ξ
  -- Rewrite the summand to peel off the deterministic drift.
  have hmap_eq : (fun ω => b * t + L ω + S ω) = fun ω => b * t + (L ω + S ω) := by
    funext ω; ring
  rw [hmap_eq]
  have hgae : AEMeasurable (fun ω => b * t + (L ω + S ω)) μ :=
    aemeasurable_const.add (hL.aemeasurable.add hS)
  rw [charFun_apply_real, integral_map hgae hcont.aestronglyMeasurable]
  -- Peel the drift exponential off the integrand.
  have hpeel : ∀ ω, Complex.exp (↑ξ * ↑(b * t + (L ω + S ω)) * Complex.I)
      = Complex.exp (↑ξ * ↑(b * t) * Complex.I)
        * Complex.exp (↑ξ * ↑(L ω + S ω) * Complex.I) := by
    intro ω; rw [← Complex.exp_add]; congr 1; push_cast; ring
  simp_rw [hpeel]
  rw [integral_const_mul]
  -- Reassemble the remaining integral as the characteristic function of the two jump components.
  rw [show (∫ ω, Complex.exp (↑ξ * ↑(L ω + S ω) * Complex.I) ∂μ)
        = charFun (μ.map (fun ω => L ω + S ω)) ξ from by
      rw [charFun_apply_real, integral_map
        (show AEMeasurable (fun ω => L ω + S ω) μ from hL.aemeasurable.add hS)
        hcont.aestronglyMeasurable]]
  rw [hLS, charFun_map_levyLargeJumpSum hd hν ht ξ,
    charFun_map_levyCompensatedSmallJump hd hν ht ξ]
  -- Combine the three exponentials and match the Lévy–Khintchine exponent via the radius-1 split.
  rw [← Complex.exp_add, ← Complex.exp_add, LevyKhintchineTriple.exponent_def,
    integral_levyCompensatedIntegrand_eq_small_add_large hν ξ]
  congr 1
  push_cast
  ring

/-- Scaling the time `t` through the Lévy–Khintchine exponent of the pure-jump triple `(b, 0, ν)`
is the exponent of the `t`-scaled triple `(t · b, 0, ENNReal.ofReal t • ν)`: the drift and the Lévy
measure both scale linearly in `t`, while the zero Gaussian variance is preserved. -/
private lemma ofReal_smul_exponent_mk {ν : Measure ℝ} (hν : IsLevyMeasure ν) (b : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ξ : ℝ) :
    (t : ℂ) * (LevyKhintchineTriple.mk b 0 ν hν).exponent ξ
      = (LevyKhintchineTriple.mk (t * b) 0 (ENNReal.ofReal t • ν)
          (hν.smul ENNReal.ofReal_ne_top)).exponent ξ := by
  rw [LevyKhintchineTriple.exponent_def, LevyKhintchineTriple.exponent_def,
    integral_smul_measure, ENNReal.toReal_ofReal ht, Complex.real_smul]
  push_cast
  ring

/-- **The jump-law marginal is infinitely divisible.** For `0 ≤ t`, the fixed-time marginal law of
`b · t + (large-jump sum) + (compensated small jumps)` is an infinitely divisible law on `ℝ`: its
characteristic function is `exp` of the Lévy–Khintchine exponent of the `t`-scaled pure-jump triple
`(t · b, 0, ENNReal.ofReal t • ν)`, so the converse Lévy–Khintchine theorem applies. -/
theorem isInfinitelyDivisible_map_levyJumpSum [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IsInfinitelyDivisible (μ.map (fun ω => b * t + levyLargeJumpSum K X t ω
        + levyCompensatedSmallJump hd hν t ω)) := by
  have hL : Measurable (levyLargeJumpSum K X t) :=
    measurable_levyLargeJumpSum hd.measurable_count hd.measurable_point
  have hS : AEMeasurable (fun ω => levyCompensatedSmallJump hd hν t ω) μ :=
    (Lp.aestronglyMeasurable _).aemeasurable
  have hmeas : AEMeasurable (fun ω => b * t + levyLargeJumpSum K X t ω
      + levyCompensatedSmallJump hd hν t ω) μ :=
    (aemeasurable_const.add hL.aemeasurable).add hS
  haveI : IsProbabilityMeasure (μ.map (fun ω => b * t + levyLargeJumpSum K X t ω
      + levyCompensatedSmallJump hd hν t ω)) := Measure.isProbabilityMeasure_map hmeas
  refine isInfinitelyDivisible_iff_exists_levyKhintchineTriple.mpr
    ⟨LevyKhintchineTriple.mk (t * b) 0 (ENNReal.ofReal t • ν) (hν.smul ENNReal.ofReal_ne_top),
      fun ξ => ?_⟩
  rw [charFun_map_levyJumpSum_eq_exponent hd hν b ht ξ, ofReal_smul_exponent_mk hν b ht ξ]

/-! ### The jump process and its independent increments

The three jump ingredients — a constant drift, the compound-Poisson large-jump sum, and the
compensated small-jump integral — are assembled into a single process indexed by `ℝ≥0`. Over a time
step `(s, t]` each ingredient reads only the marks of the Poisson random measure inside the band
`(s, t] × ℝ`, and consecutive bands over a monotone grid are pairwise disjoint. Since the evaluation
sigma-algebras of disjoint regions are mutually independent (`iIndep_prmEvalSigma`), the increments
over such a grid are mutually independent. -/

/-- The **jump process** of a Lévy measure: drift plus large-jump sum plus compensated
small jumps, indexed by `ℝ≥0`. Its law-level Lévy structure (independent and stationary
increments, increment charFun `exp((t−s)·ψ)`) is proved below; NO path regularity is claimed. -/
noncomputable def levyJumpProcess [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  b * (t : ℝ) + levyLargeJumpSum K X (t : ℝ) ω + levyCompensatedSmallJump hd hν (t : ℝ) ω

/-- **Independent increments of the jump process** over any monotone time grid. -/
theorem hasIndependentIncrements_levyJumpProcess [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X ((volume : Measure ℝ).prod ν) μ) (hν : IsLevyMeasure ν)
    (b : ℝ) :
    HasIndependentIncrements (levyJumpProcess hd hν b) μ := by
  intro n τ hτmono
  -- the consecutive time bands over the grid, extended over all marks
  set R : Fin n → Set (ℝ × ℝ) :=
    fun k => Set.Ioc ((τ k.castSucc : ℝ)) ((τ k.succ : ℝ)) ×ˢ (Set.univ : Set ℝ) with hRdef
  -- coercion facts: the grid is monotone and nonnegative in ℝ≥0
  have hcoe_le : ∀ k : Fin n, (τ k.castSucc : ℝ) ≤ (τ k.succ : ℝ) := fun k => by
    exact_mod_cast hτmono (Fin.castSucc_le_succ k)
  have hcoe_nonneg : ∀ k : Fin n, (0 : ℝ) ≤ (τ k.castSucc : ℝ) := fun _ => NNReal.coe_nonneg _
  -- the bands are pairwise disjoint
  have hRdisj : Pairwise (Function.onFun Disjoint R) := by
    have hcore : ∀ i j : Fin n, i < j → Disjoint (R i) (R j) := by
      intro i j hij
      refine Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le ?_) _ _
      have hle : i.succ ≤ j.castSucc := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        have : (i : ℕ) < (j : ℕ) := hij
        omega
      exact_mod_cast hτmono hle
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hcore i j h
    · exact (hcore j i h).symm
  -- an honest per-band representative of each increment, measurable in that band's σ-algebra
  have hdata : ∀ k : Fin n, ∃ W : Ω → ℝ,
      Measurable[prmEvalSigma K X (volume.prod ν) (R k)] W ∧
      increment (levyJumpProcess hd hν b) (τ k.castSucc) (τ k.succ) =ᵐ[μ] W := by
    intro k
    obtain ⟨WL, hWL_sm, hWL_ae⟩ :=
      aestronglyMeasurable_levyLargeJumpSum_sub_prmEvalSigma hd hν (hcoe_nonneg k) (hcoe_le k)
    obtain ⟨WS, hWS_sm, hWS_ae⟩ :=
      aestronglyMeasurable_levyCompensatedSmallJump_band hd hν (τ k.castSucc : ℝ) (τ k.succ : ℝ)
    -- lift the large-jump representative from its `{|x| ≥ 1}` band to the full band `R k`
    have hsub : Set.Ioc ((τ k.castSucc : ℝ)) ((τ k.succ : ℝ)) ×ˢ {x : ℝ | 1 ≤ |x|} ⊆ R k :=
      Set.prod_mono le_rfl (Set.subset_univ _)
    have hWL_sm_R : StronglyMeasurable[prmEvalSigma K X (volume.prod ν) (R k)] WL :=
      hWL_sm.mono (prmEvalSigma_mono hsub)
    refine ⟨fun ω => b * ((τ k.succ : ℝ) - (τ k.castSucc : ℝ)) + WL ω + WS ω,
      ((stronglyMeasurable_const.add hWL_sm_R).add hWS_sm).measurable, ?_⟩
    -- the small increment is the coeFn of the band compensated integral, a.e.
    have hcoeFnSub := Lp.coeFn_sub (levyCompensatedSmallJump hd hν (τ k.succ : ℝ))
      (levyCompensatedSmallJump hd hν (τ k.castSucc : ℝ))
    rw [levyCompensatedSmallJump_sub hd hν (hcoe_nonneg k) (hcoe_le k)] at hcoeFnSub
    filter_upwards [hWL_ae, hWS_ae, hcoeFnSub] with ω hWLω hWSω hsubω
    simp only [Pi.sub_apply] at hsubω
    have hWSeq : WS ω = levyCompensatedSmallJump hd hν (τ k.succ : ℝ) ω
        - levyCompensatedSmallJump hd hν (τ k.castSucc : ℝ) ω := hWSω.symm.trans hsubω
    rw [increment_apply]
    simp only [levyJumpProcess]
    rw [← hWLω, hWSeq]
    ring
  choose W hW_meas hW_ae using hdata
  -- disjoint bands give independent evaluation σ-algebras, hence independent representatives
  have hiIndepW : iIndep (fun k => MeasurableSpace.comap (W k) inferInstance) μ :=
    iIndep_of_iIndep_of_le (iIndep_prmEvalSigma hd hRdisj) (fun k => (hW_meas k).comap_le)
  -- transfer independence from the representatives back to the increments
  exact (iIndepFun_congr fun k => hW_ae k).mpr ((iIndepFun_iff_iIndep _ W μ).mpr hiIndepW)

end ProbabilityTheory
