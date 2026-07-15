/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Order.Preorder.Finite
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Monoid

/-!
# Càdlàg Functions

A function is **càdlàg** (continue à droite, limite à gauche) if it is right-continuous
and has left limits at every point. This is the standard regularity condition for sample
paths of Lévy processes and many other stochastic processes.

## Main definitions

* `ProbabilityTheory.IsCadlagAt f t` — `f` is right-continuous at `t` and has a left limit at `t`.
* `ProbabilityTheory.IsCadlag f` — `f` is càdlàg everywhere.

## Main results

* `ProbabilityTheory.isCadlag_const` — constant functions are càdlàg.
* `Monotone.leftLim_exists_nat` — a monotone function `f : ℝ≥0 → ℕ` has left limits.
* `Monotone.isCadlag_of_rightContinuous_nat` — a monotone, right-continuous, ℕ-valued function
  is càdlàg.
-/

open Filter Set Topology
open scoped NNReal

namespace ProbabilityTheory

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]

/-- A function `f` is **càdlàg at** `t` if it is right-continuous at `t` (i.e., continuous
within `[t, ∞)`) and has a left limit at `t` (i.e., `f` converges along the filter of
points strictly less than `t`). -/
def IsCadlagAt (f : α → β) (t : α) : Prop :=
  ContinuousWithinAt f (Ici t) t ∧ ∃ l, Tendsto f (𝓝[Iio t] t) (𝓝 l)

/-- A function `f` is **càdlàg** if it is càdlàg at every point. -/
def IsCadlag (f : α → β) : Prop :=
  ∀ t, IsCadlagAt f t

/-- A càdlàg function is right-continuous at every point. -/
theorem IsCadlag.rightContinuous {f : α → β} (hf : IsCadlag f) (t : α) :
    ContinuousWithinAt f (Ici t) t :=
  (hf t).1

/-- A càdlàg function has a left limit at every point. -/
theorem IsCadlag.leftLim_exists {f : α → β} (hf : IsCadlag f) (t : α) :
    ∃ l, Tendsto f (𝓝[Iio t] t) (𝓝 l) :=
  (hf t).2

/-- Constant functions are càdlàg. -/
theorem isCadlag_const {c : β} : IsCadlag (fun _ : α => c) :=
  fun _ => ⟨continuousWithinAt_const, ⟨c, tendsto_const_nhds⟩⟩

end ProbabilityTheory

/-! ### Monotone ℕ-valued functions on ℝ≥0

A monotone function `f : ℝ≥0 → ℕ` has left limits at every point. The key observation is
that the image of `Iio t` under `f` is a bounded (by `f t`) subset of `ℕ`, hence finite.
A finite nonempty subset of `ℕ` has a maximum, and by monotonicity `f` is eventually
constant near `t` from the left. -/

/-- A monotone function `f : ℝ≥0 → ℕ` has a left limit at every point.

At `t = 0`, the set `Iio 0` is empty in `ℝ≥0`, so the filter `𝓝[Iio 0] 0 = ⊥` and any
value works. At `t > 0`, the image `f '' Iio t` is a nonempty bounded subset of `ℕ`,
hence has a maximum achieved at some `s₀ < t`. By monotonicity, `f` is constantly equal
to this maximum on `(s₀, t)`, which is a neighborhood of `t` in `𝓝[<] t`. -/
theorem Monotone.leftLim_exists_nat {f : ℝ≥0 → ℕ} (hf : Monotone f) (t : ℝ≥0) :
    ∃ l, Tendsto f (𝓝[Iio t] t) (𝓝 l) := by
  -- Case 1: t = 0. Then Iio 0 = ∅ in ℝ≥0, so nhdsWithin is ⊥.
  by_cases ht : t = 0
  · subst ht
    refine ⟨f 0, ?_⟩
    have h_empty : (Iio (0 : ℝ≥0)) = ∅ := by
      ext x; simp
    rw [h_empty, nhdsWithin_empty]
    exact tendsto_bot
  -- Case 2: t > 0. Find the maximum of f on Iio t.
  · have ht_pos : (0 : ℝ≥0) < t := pos_iff_ne_zero.mpr ht
    -- The image f '' Iio t is a subset of Iic (f t), which is finite in ℕ.
    have hS_finite : (f '' Iio t).Finite :=
      (finite_Iic (f t)).subset (image_subset_iff.mpr fun s hs => hf (le_of_lt hs))
    -- Iio t is nonempty since 0 < t.
    have hS_nonempty : (Iio t).Nonempty := ⟨0, ht_pos⟩
    -- Get a maximal element: s₀ < t with f s₀ maximal among {f s | s < t}.
    obtain ⟨s₀, hs₀_mem, hs₀_max⟩ := hS_finite.exists_maximalFor' f (Iio t) hS_nonempty
    -- Unpack: s₀ < t
    have hs₀_lt : s₀ < t := hs₀_mem
    -- For all s < t, f s ≤ f s₀ (maximality in a linear order)
    have hmax : ∀ s, s < t → f s ≤ f s₀ := by
      intro s hs
      by_contra h
      push Not at h
      exact absurd (hs₀_max hs (le_of_lt h)) (not_le.mpr h)
    -- For all s ∈ (s₀, t), f s = f s₀
    have hf_eq : ∀ s, s ∈ Ioo s₀ t → f s = f s₀ := by
      intro s ⟨hs₀s, hst⟩
      exact le_antisymm (hmax s hst) (hf (le_of_lt hs₀s))
    -- Since ℕ has discrete topology, Tendsto f F (nhds n) ↔ ∀ᶠ s in F, f s = n.
    refine ⟨f s₀, ?_⟩
    rw [nhds_discrete, tendsto_pure]
    filter_upwards [Ioo_mem_nhdsLT hs₀_lt] with s hs
    exact hf_eq s hs

/-- A monotone, right-continuous, ℕ-valued function on `ℝ≥0` is càdlàg. -/
theorem Monotone.isCadlag_of_rightContinuous_nat {f : ℝ≥0 → ℕ}
    (hf : Monotone f) (hrc : ∀ t, ContinuousWithinAt f (Ici t) t) :
    ProbabilityTheory.IsCadlag f :=
  fun t => ⟨hrc t, hf.leftLim_exists_nat t⟩

/-! ### Closure properties of càdlàg functions

The càdlàg condition is preserved under equality along `𝓝 t`, continuous functions are
càdlàg, and pointwise finite sums of càdlàg functions are càdlàg. The final result of this
section, `ProbabilityTheory.isCadlag_of_tendstoUniformlyOn`, shows that a uniform-on-`Iic T`
limit of càdlàg functions `ℝ → ℝ` is again càdlàg. -/

namespace ProbabilityTheory

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]

/-- Being càdlàg at a point depends only on the germ of the function at `𝓝 t`: if `f` and `g`
agree on a neighborhood of `t`, then `f` càdlàg at `t` implies `g` càdlàg at `t`. -/
theorem IsCadlagAt.congr {f g : α → β} {t : α} (hf : IsCadlagAt f t) (h : f =ᶠ[𝓝 t] g) :
    IsCadlagAt g t := by
  obtain ⟨hc, l, hl⟩ := hf
  refine ⟨?_, l, ?_⟩
  · exact hc.congr_of_eventuallyEq (h.filter_mono nhdsWithin_le_nhds).symm h.eq_of_nhds.symm
  · exact hl.congr' (h.filter_mono nhdsWithin_le_nhds)

/-- A pointwise sum of two functions that are càdlàg at `t` is càdlàg at `t`. -/
theorem IsCadlagAt.add {β : Type*} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    {f g : α → β} {t : α} (hf : IsCadlagAt f t) (hg : IsCadlagAt g t) :
    IsCadlagAt (fun s => f s + g s) t := by
  obtain ⟨hfc, lf, hlf⟩ := hf
  obtain ⟨hgc, lg, hlg⟩ := hg
  exact ⟨hfc.add hgc, lf + lg, hlf.add hlg⟩

/-- A pointwise sum of two càdlàg functions is càdlàg. -/
theorem IsCadlag.add {β : Type*} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    {f g : α → β} (hf : IsCadlag f) (hg : IsCadlag g) : IsCadlag (fun s => f s + g s) :=
  fun t => (hf t).add (hg t)

/-- A pointwise finite sum of càdlàg functions is càdlàg. -/
theorem IsCadlag.finsetSum {β : Type*} [TopologicalSpace β] [AddCommMonoid β] [ContinuousAdd β]
    {ι : Type*} (s : Finset ι) {f : ι → α → β} (h : ∀ i ∈ s, IsCadlag (f i)) :
    IsCadlag (fun t => ∑ i ∈ s, f i t) := by
  classical
  intro t
  refine ⟨tendsto_finsetSum s (fun i hi => (h i hi t).1), ?_⟩
  choose! l hl using fun i (hi : i ∈ s) => (h i hi t).2
  exact ⟨∑ i ∈ s, l i, tendsto_finsetSum s (fun i hi => hl i hi)⟩

/-- The right-continuous step function `t ↦ if c ≤ t then y else 0` is càdlàg. It is constant
away from `c`, right-continuous at `c` (its value there is `y`), and has left limit `0` at `c`. -/
theorem isCadlag_stepIndicator {c y : ℝ} :
    IsCadlag (fun t : ℝ => if c ≤ t then y else 0) := by
  intro t
  constructor
  · rcases lt_or_ge t c with ht | ht
    · have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Ici t] t] fun _ => (0 : ℝ) := by
        filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
        simp only [if_neg (not_le.mpr (Set.mem_Iio.mp hs))]
      refine continuousWithinAt_const.congr_of_eventuallyEq heq ?_
      simp only [if_neg (not_le.mpr ht)]
    · have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Ici t] t] fun _ => y := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [if_pos (le_trans ht hs)]
      refine continuousWithinAt_const.congr_of_eventuallyEq heq ?_
      simp only [if_pos ht]
  · rcases le_or_gt t c with ht | ht
    · refine ⟨0, ?_⟩
      have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Iio t] t] fun _ => (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [if_neg (not_le.mpr (lt_of_lt_of_le hs ht))]
      exact tendsto_const_nhds.congr' heq.symm
    · refine ⟨y, ?_⟩
      have heq : (fun s : ℝ => if c ≤ s then y else 0) =ᶠ[𝓝[Iio t] t] fun _ => y := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with s hs
        simp only [if_pos (le_of_lt (Set.mem_Ioi.mp hs))]
      exact tendsto_const_nhds.congr' heq.symm

/-- A uniform-on-`Iic T` limit of càdlàg functions `ℝ → ℝ` is càdlàg. The uniform convergence
on `Iic (t + 1)` transfers right-continuity at `t` via a `3ε` estimate, and makes the left-limit
witnesses of the approximants a Cauchy sequence, whose limit is the left limit of `f`. -/
theorem isCadlag_of_tendstoUniformlyOn {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, IsCadlag (F n)) (h : ∀ T : ℝ, TendstoUniformlyOn F f atTop (Set.Iic T)) :
    IsCadlag f := by
  intro t
  have hunif : ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ Set.Iic (t + 1), dist (f x) (F n x) < ε :=
    fun ε hε => (Metric.tendstoUniformlyOn_iff.mp (h (t + 1))) ε hε
  constructor
  · -- Right-continuity at `t`.
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := (hunif (ε / 3) (by positivity)).exists
    obtain ⟨δ', hδ'pos, hδ'⟩ :=
      Metric.continuousWithinAt_iff.mp (hF n t).1 (ε / 3) (by positivity)
    refine ⟨min δ' 1, lt_min hδ'pos one_pos, ?_⟩
    intro s hs hsdist
    have hsd' : dist s t < δ' := lt_of_lt_of_le hsdist (min_le_left _ _)
    have hs1 : s ∈ Set.Iic (t + 1) := by
      have hlt1 : dist s t < 1 := lt_of_lt_of_le hsdist (min_le_right _ _)
      rw [Real.dist_eq, abs_lt] at hlt1
      simp only [Set.mem_Iic]; linarith [hlt1.2]
    have ht1 : t ∈ Set.Iic (t + 1) := by simp
    have T : dist (f s) (f t) ≤
        dist (f s) (F n s) + dist (F n s) (F n t) + dist (F n t) (f t) := dist_triangle4 _ _ _ _
    have B1 : dist (f s) (F n s) < ε / 3 := hn s hs1
    have B2 : dist (F n s) (F n t) < ε / 3 := hδ' hs hsd'
    have B3 : dist (F n t) (f t) < ε / 3 := by rw [dist_comm]; exact hn t ht1
    linarith [T, B1, B2, B3]
  · -- Existence of the left limit at `t`.
    choose l hl using fun n => (hF n t).2
    have hcauchy : CauchySeq l := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hunif (ε / 4) (by positivity))
      refine ⟨N, fun m hm n hn => ?_⟩
      obtain ⟨δm, hδmpos, hδm⟩ :=
        Metric.tendsto_nhdsWithin_nhds.mp (hl m) (ε / 4) (by positivity)
      obtain ⟨δn, hδnpos, hδn⟩ :=
        Metric.tendsto_nhdsWithin_nhds.mp (hl n) (ε / 4) (by positivity)
      set δ := min δm δn with hδdef
      have hδpos : 0 < δ := lt_min hδmpos hδnpos
      set s := t - δ / 2 with hsdef
      have hslt : s ∈ Set.Iio t := by
        simp only [Set.mem_Iio, hsdef]; linarith
      have hsdist : dist s t < δ := by
        rw [Real.dist_eq, hsdef, abs_of_nonpos (by linarith)]; linarith
      have hs1 : s ∈ Set.Iic (t + 1) := by
        simp only [Set.mem_Iic, hsdef]; linarith
      have hb1 : dist (l m) (F m s) < ε / 4 := by
        rw [dist_comm]; exact hδm hslt (lt_of_lt_of_le hsdist (min_le_left _ _))
      have hb2 : dist (F m s) (f s) < ε / 4 := by
        rw [dist_comm]; exact hN m hm s hs1
      have hb3 : dist (f s) (F n s) < ε / 4 := hN n hn s hs1
      have hb4 : dist (F n s) (l n) < ε / 4 := hδn hslt (lt_of_lt_of_le hsdist (min_le_right _ _))
      have T1 : dist (l m) (l n) ≤ dist (l m) (f s) + dist (f s) (l n) := dist_triangle _ _ _
      have T2 : dist (l m) (f s) ≤ dist (l m) (F m s) + dist (F m s) (f s) := dist_triangle _ _ _
      have T3 : dist (f s) (l n) ≤ dist (f s) (F n s) + dist (F n s) (l n) := dist_triangle _ _ _
      linarith [T1, T2, T3, hb1, hb2, hb3, hb4]
    obtain ⟨L, hLtend⟩ := cauchySeq_tendsto_of_complete hcauchy
    refine ⟨L, ?_⟩
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hLev : ∀ᶠ n in atTop, dist (l n) L < ε / 3 :=
      Metric.tendsto_nhds.mp hLtend (ε / 3) (by positivity)
    obtain ⟨n, hnU, hnL⟩ := ((hunif (ε / 3) (by positivity)).and hLev).exists
    obtain ⟨δ, hδpos, hδ⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hl n) (ε / 3) (by positivity)
    refine ⟨δ, hδpos, ?_⟩
    intro s hs hsdist
    have hs1 : s ∈ Set.Iic (t + 1) := by
      simp only [Set.mem_Iio] at hs
      simp only [Set.mem_Iic]; linarith
    have T : dist (f s) L ≤
        dist (f s) (F n s) + dist (F n s) (l n) + dist (l n) L := dist_triangle4 _ _ _ _
    have B1 : dist (f s) (F n s) < ε / 3 := hnU s hs1
    have B2 : dist (F n s) (l n) < ε / 3 := hδ hs hsdist
    have B3 : dist (l n) L < ε / 3 := hnL
    linarith [T, B1, B2, B3]

end ProbabilityTheory

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β] [Preorder α]

/-- A continuous function is càdlàg: it is continuous within `[t, ∞)` and its left limit is
just its value `f t`. -/
theorem Continuous.isCadlag {f : α → β} (hf : Continuous f) : ProbabilityTheory.IsCadlag f :=
  fun t => ⟨hf.continuousWithinAt, f t, (hf.tendsto t).mono_left nhdsWithin_le_nhds⟩

/-- Precomposition with the coercion `ℝ≥0 → ℝ` preserves the càdlàg property. At `t = 0` the
filter `𝓝[Iio 0] 0` is `⊥` (since `Iio 0 = ∅` in `ℝ≥0`), so the left limit is automatic. -/
theorem isCadlag_comp_nnrealCoe {β : Type*} [TopologicalSpace β] {f : ℝ → β}
    (hf : ProbabilityTheory.IsCadlag f) : ProbabilityTheory.IsCadlag (fun t : ℝ≥0 => f t) := by
  intro t
  constructor
  · have hmap : Set.MapsTo ((↑) : ℝ≥0 → ℝ) (Ici t) (Ici (t : ℝ)) :=
      fun s hs => NNReal.coe_le_coe.mpr hs
    exact (hf (t : ℝ)).1.comp NNReal.continuous_coe.continuousWithinAt hmap
  · obtain ⟨l, hl⟩ := (hf (t : ℝ)).2
    refine ⟨l, ?_⟩
    have hmap : Set.MapsTo ((↑) : ℝ≥0 → ℝ) (Iio t) (Iio (t : ℝ)) :=
      fun s hs => NNReal.coe_lt_coe.mpr hs
    have htend : Tendsto ((↑) : ℝ≥0 → ℝ) (𝓝[Iio t] t) (𝓝[Iio (t : ℝ)] (t : ℝ)) :=
      NNReal.continuous_coe.continuousWithinAt.tendsto_nhdsWithin hmap
    exact hl.comp htend
