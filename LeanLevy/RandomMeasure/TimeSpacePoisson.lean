/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.RandomMeasure.PoissonRandomMeasure

/-!
# Time-indexed Poisson random measures

Specialize the abstract Poisson random measure to the product space `ℝ × E`, with `ℝ` read as time
and `E` as the mark space, under the product intensity `volume.prod m`. The evaluation on a
space-time band `(s, t] × A` is the number of realized marks in `A` occurring during the time
window `(s, t]`; the running count `poissonTimeCount K X A t` is its value on the initial window
`(0, t]`.

## Main definitions

* `ProbabilityTheory.poissonTimeCount` — the running count of realized points in `(0, t] × A`.

## Main results

* `ProbabilityTheory.measurable_poissonTimeCount` — the running count is a measurable function of the
  sample point.
* `ProbabilityTheory.map_poissonRandomMeasure_band` — the count in a band `(s, t] × A` is Poisson with
  mean `(t - s) · m A`.
* `ProbabilityTheory.map_poissonTimeCount` — the running count `poissonTimeCount K X A t` is Poisson
  with mean `t · m A`.
* `ProbabilityTheory.poissonTimeCount_add` — the running count is pathwise additive over consecutive
  time windows.
* `ProbabilityTheory.iIndepFun_poissonRandomMeasure_bands` — **independent increments**: the counts
  over consecutive disjoint time bands are mutually independent.

Every statement is read off the abstract superposition and disjoint-family independence laws of
`poissonRandomMeasure` on `ℝ × E`; the band mass factorizes as `volume (Ioc s t) * m A` through
`Measure.prod_prod`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] [Nonempty E] {K : ℕ → Ω → ℕ}
  {X : ℕ → ℕ → Ω → ℝ × E} {m : Measure E} [SigmaFinite m] {μ : Measure Ω} {A : Set E} {s t : ℝ}

omit [Nonempty E] in
/-- The `volume.prod m`-mass of a space-time band factorizes: `(volume.prod m) ((s, t] ×ˢ A)` is the
time length `t - s` times the mark mass `m A`. -/
private lemma volume_prod_Ioc_prod (s t : ℝ) (A : Set E) :
    (volume.prod m) (Set.Ioc s t ×ˢ A) = ENNReal.ofReal (t - s) * m A := by
  rw [Measure.prod_prod, Real.volume_Ioc]

omit [Nonempty E] in
/-- Each space-time band has finite `volume.prod m`-mass whenever the mark set has finite mass. -/
private lemma volume_prod_Ioc_prod_lt_top (hfin : m A < ⊤) :
    (volume.prod m) (Set.Ioc s t ×ˢ A) < ⊤ := by
  rw [volume_prod_Ioc_prod]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- The running count of points of the time-space random measure: realized points in `(0, t] × A`. -/
noncomputable def poissonTimeCount (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (A : Set E) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  poissonRandomMeasure K X ω (Set.Ioc 0 t ×ˢ A)

omit [Nonempty E] [SigmaFinite m] in
/-- The running count is a measurable function of the sample point. -/
theorem measurable_poissonTimeCount (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) (hA : MeasurableSet A) :
    Measurable (poissonTimeCount K X A t) :=
  measurable_poissonRandomMeasure_apply hK hX (measurableSet_Ioc.prod hA)

/-- Band evaluation law: the count in `(s, t] × A` is Poisson with mean `(t - s) · m A`. -/
theorem map_poissonRandomMeasure_band [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A)
    (hfin : m A < ⊤) (_hst : s ≤ t) :
    μ.map (fun ω => poissonRandomMeasure K X ω (Set.Ioc s t ×ˢ A))
      = (poissonMeasure (ENNReal.ofReal (t - s) * m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  rw [map_poissonRandomMeasure_apply hd (measurableSet_Ioc.prod hA)
    (volume_prod_Ioc_prod_lt_top hfin), volume_prod_Ioc_prod]

/-- The running count `poissonTimeCount K X A t` is Poisson with mean `t · m A`. -/
theorem map_poissonTimeCount [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A)
    (hfin : m A < ⊤) (ht : 0 ≤ t) :
    μ.map (poissonTimeCount K X A t)
      = (poissonMeasure (ENNReal.ofReal t * m A).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞) := by
  have h := map_poissonRandomMeasure_band (s := 0) hd hA hfin ht
  rwa [sub_zero] at h

omit [Nonempty E] [SigmaFinite m] [MeasurableSpace Ω] in
/-- Pathwise additivity of the running count over consecutive time bands. -/
theorem poissonTimeCount_add (hA : MeasurableSet A) (h0s : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    poissonTimeCount K X A t ω
      = poissonTimeCount K X A s ω + poissonRandomMeasure K X ω (Set.Ioc s t ×ˢ A) := by
  unfold poissonTimeCount
  rw [← Set.Ioc_union_Ioc_eq_Ioc h0s hst, Set.union_prod,
    measure_union (Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le le_rfl) A A)
      (measurableSet_Ioc.prod hA)]

omit [Nonempty E] [SigmaFinite m] [MeasurableSpace E] in
/-- Two time bands over disjoint windows (ordered `i < j`) evaluate on disjoint space-time sets. -/
private lemma disjoint_band {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t) (A : Set E)
    {i j : Fin n} (hij : i < j) :
    Disjoint (Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A)
      (Set.Ioc (t j.castSucc) (t j.succ) ×ˢ A) := by
  refine Set.Disjoint.set_prod_left (Set.Ioc_disjoint_Ioc_of_le (ht ?_)) A A
  have hv : (i : ℕ) < (j : ℕ) := hij
  rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
  omega

/-- **Independent increments.** Counts over disjoint consecutive time bands are mutually
independent. -/
theorem iIndepFun_poissonRandomMeasure_bands [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X (volume.prod m) μ) (hA : MeasurableSet A)
    (hfin : m A < ⊤) {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t) :
    iIndepFun (fun (i : Fin n) ω =>
      poissonRandomMeasure K X ω (Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A)) μ := by
  refine iIndepFun_poissonRandomMeasure_apply hd (fun i => measurableSet_Ioc.prod hA)
    (fun i => volume_prod_Ioc_prod_lt_top hfin) ?_
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact disjoint_band ht A h
  · exact (disjoint_band ht A h).symm

end ProbabilityTheory
