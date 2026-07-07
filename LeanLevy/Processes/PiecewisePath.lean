/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.Cadlag
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Piecewise-affine jump paths

A **piecewise-affine jump path** is a deterministic real path that moves with constant
drift `b` between a discrete set of jump times `T 0 < T 1 < …` and jumps by `Y n` at time
`T n`. Such paths are the deterministic skeleton of a compound-Poisson-with-drift process:
once the arrival times and marks are fixed, the sample path is exactly one of these.

The number of jumps that have occurred strictly before (or at) time `t` is tracked by
`jumpCount T t`, the smallest index `n` with `t < T n`. The path value is then

`piecewisePath x₀ b T Y t = x₀ + b * t + ∑ n < jumpCount T t, Y n`.

## Main definitions

* `ProbabilityTheory.jumpCount` — the number of arrival times that have passed by time `t`.
* `ProbabilityTheory.piecewisePath` — the value of the drift-plus-jumps path at time `t`.

## Main results

* `ProbabilityTheory.lt_jumpCount_iff` — the defining characterization `n < jumpCount T t ↔ T n ≤ t`.
* `ProbabilityTheory.jumpCount_mono` — the jump count is monotone in time.
* `ProbabilityTheory.jumpCount_arrival_self` — `jumpCount T (T n) = n + 1`.
* `ProbabilityTheory.piecewisePath_eqOn_affine` — the path is affine on any interval on which
  the jump count is constant.
* `ProbabilityTheory.tendsto_piecewisePath_leftLim` — the left limit at `T n` is smaller than the
  value there by exactly the jump size `Y n`.
* `ProbabilityTheory.isCadlag_piecewisePath` — a piecewise-affine jump path is càdlàg.
-/

open Filter Set Topology

namespace ProbabilityTheory

section JumpCount

variable {T : ℕ → ℝ}

/-- `jumpCount T t` is the number of arrival times among `T 0, T 1, …` that have occurred by
time `t`; equivalently the least index `n` with `t < T n`. -/
noncomputable def jumpCount (T : ℕ → ℝ) (t : ℝ) : ℕ := sInf {n | t < T n}

/-- The defining characterization of the jump count: `n` jumps have occurred by time `t`
(i.e. `n < jumpCount T t`) exactly when the `n`-th arrival has already happened. -/
theorem lt_jumpCount_iff (hmono : StrictMono T) (htop : Tendsto T atTop atTop) (n : ℕ) (t : ℝ) :
    n < jumpCount T t ↔ T n ≤ t := by
  have hne : {m | t < T m}.Nonempty := (htop.eventually_gt_atTop t).exists
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have hle : jumpCount T t ≤ n := Nat.sInf_le (show n ∈ {m | t < T m} from hcon)
    omega
  · intro h
    by_contra hcon
    push_neg at hcon
    have hmem : t < T (jumpCount T t) := Nat.sInf_mem hne
    have : T (jumpCount T t) ≤ T n := hmono.monotone hcon
    linarith

/-- Before the first arrival, no jumps have occurred. -/
theorem jumpCount_eq_zero_of_lt {t : ℝ} (h : t < T 0) : jumpCount T t = 0 :=
  Nat.le_zero.mp (Nat.sInf_le (show (0 : ℕ) ∈ {n | t < T n} from h))

/-- The jump count is monotone in time. -/
theorem jumpCount_mono (hmono : StrictMono T) (htop : Tendsto T atTop atTop) :
    Monotone (jumpCount T) := by
  intro a b hab
  by_contra hcon
  push_neg at hcon
  have h1 : T (jumpCount T b) ≤ a := (lt_jumpCount_iff hmono htop _ _).mp hcon
  exact absurd ((lt_jumpCount_iff hmono htop _ _).mpr (h1.trans hab)) (lt_irrefl _)

/-- Exactly `n + 1` jumps have occurred by the time of the `n`-th arrival. -/
theorem jumpCount_arrival_self (hmono : StrictMono T) (htop : Tendsto T atTop atTop) (n : ℕ) :
    jumpCount T (T n) = n + 1 := by
  have key : ∀ k, k < jumpCount T (T n) ↔ k < n + 1 := fun k => by
    rw [lt_jumpCount_iff hmono htop, hmono.le_iff_le, Nat.lt_succ_iff]
  have lb : n < jumpCount T (T n) := (key n).mpr (Nat.lt_succ_self n)
  have ub : ¬ (n + 1 < jumpCount T (T n)) := fun h => absurd ((key (n + 1)).mp h) (lt_irrefl _)
  omega

end JumpCount

section PiecewisePath

variable {x₀ b : ℝ} {T Y : ℕ → ℝ}

/-- `piecewisePath x₀ b T Y t` is the value at time `t` of the path that starts at `x₀`, drifts
at rate `b`, and jumps by `Y n` at each arrival time `T n`. -/
noncomputable def piecewisePath (x₀ b : ℝ) (T Y : ℕ → ℝ) (t : ℝ) : ℝ :=
  x₀ + b * t + ∑ n ∈ Finset.range (jumpCount T t), Y n

/-- At time `0`, before the first arrival, the path equals its starting value. -/
theorem piecewisePath_zero (hpos : 0 < T 0) : piecewisePath x₀ b T Y 0 = x₀ := by
  simp [piecewisePath, jumpCount_eq_zero_of_lt hpos]

/-- On any interval on which the jump count is constantly `k`, the path agrees with the affine
function `s ↦ (x₀ + ∑ n < k, Y n) + b * s`. -/
theorem piecewisePath_eqOn_affine {k : ℕ} {a c : ℝ}
    (hk : ∀ s ∈ Set.Ico a c, jumpCount T s = k) :
    Set.EqOn (piecewisePath x₀ b T Y)
      (fun s => (x₀ + ∑ n ∈ Finset.range k, Y n) + b * s) (Set.Ico a c) := by
  intro s hs
  simp only [piecewisePath, hk s hs]
  ring

/-- To the left of any time `s`, the jump count is eventually constant: there is an interval
`(a, s)` on which it takes a single value `L`. -/
private theorem exists_lt_jumpCount_const (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (s : ℝ) : ∃ a < s, ∃ L : ℕ, ∀ u ∈ Set.Ioo a s, jumpCount T u = L := by
  classical
  have hBfin : ({n | T n < s} : Set ℕ).Finite := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htop.eventually_gt_atTop s)
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    intro n hn
    by_contra hcon
    exact absurd (hN n (not_lt.mp hcon)) (not_lt.mpr (le_of_lt hn))
  by_cases hBne : ({n | T n < s} : Set ℕ).Nonempty
  · obtain ⟨x0, hx0⟩ := hBne
    have hFne : hBfin.toFinset.Nonempty := ⟨x0, (Set.Finite.mem_toFinset hBfin).mpr hx0⟩
    obtain ⟨M, hMmem, hM_le⟩ : ∃ M ∈ hBfin.toFinset, ∀ n, T n < s → n ≤ M :=
      ⟨hBfin.toFinset.max' hFne, hBfin.toFinset.max'_mem hFne,
        fun n hn => hBfin.toFinset.le_max' n ((Set.Finite.mem_toFinset hBfin).mpr hn)⟩
    have hMs : T M < s := (Set.Finite.mem_toFinset hBfin).mp hMmem
    refine ⟨T M, hMs, M + 1, ?_⟩
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hlb : M < jumpCount T u := (lt_jumpCount_iff hmono htop M u).mpr (le_of_lt hu1)
    have hub : ¬ (M + 1 < jumpCount T u) := by
      intro hc
      have hTu : T (M + 1) ≤ u := (lt_jumpCount_iff hmono htop (M + 1) u).mp hc
      have hsle : s ≤ T (M + 1) := by
        by_contra hlt
        exact Nat.not_succ_le_self M (hM_le (M + 1) (not_le.mp hlt))
      linarith
    omega
  · refine ⟨s - 1, by linarith, 0, ?_⟩
    intro u hu
    obtain ⟨_, hu2⟩ := hu
    by_contra hne0
    have hpos : 0 < jumpCount T u := Nat.pos_of_ne_zero hne0
    have hT0 : T 0 ≤ u := (lt_jumpCount_iff hmono htop 0 u).mp hpos
    exact hBne ⟨0, lt_of_le_of_lt hT0 hu2⟩

/-- A piecewise-affine jump path is right-continuous at every point: the jump count is constant
on a right-neighborhood, where the path coincides with an affine function. -/
private theorem continuousWithinAt_piecewisePath_Ici (hmono : StrictMono T)
    (htop : Tendsto T atTop atTop) (s : ℝ) :
    ContinuousWithinAt (piecewisePath x₀ b T Y) (Set.Ici s) s := by
  have hne : {m | s < T m}.Nonempty := (htop.eventually_gt_atTop s).exists
  have hsJ : s < T (jumpCount T s) := Nat.sInf_mem hne
  have hconst : ∀ u ∈ Set.Ico s (T (jumpCount T s)), jumpCount T u = jumpCount T s := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hlb : jumpCount T s ≤ jumpCount T u := jumpCount_mono hmono htop hu1
    have hub : jumpCount T u ≤ jumpCount T s := by
      by_contra hh
      exact absurd ((lt_jumpCount_iff hmono htop _ u).mp (not_le.mp hh)) (not_le.mpr hu2)
    omega
  set g : ℝ → ℝ := fun u => (x₀ + ∑ i ∈ Finset.range (jumpCount T s), Y i) + b * u with hg
  have heqOn : Set.EqOn (piecewisePath x₀ b T Y) g (Set.Ico s (T (jumpCount T s))) := by
    intro u hu
    simp only [piecewisePath, hconst u hu, hg]
    ring
  have hmem : Set.Ico s (T (jumpCount T s)) ∈ 𝓝[Set.Ici s] s := by
    rw [← Set.Ici_inter_Iio]
    exact inter_mem_nhdsWithin _ (Iio_mem_nhds hsJ)
  have hgc : ContinuousWithinAt g (Set.Ici s) s := (by fun_prop : Continuous g).continuousWithinAt
  refine hgc.congr_of_eventuallyEq (Filter.eventually_of_mem hmem fun u hu => heqOn hu) ?_
  exact heqOn (Set.left_mem_Ico.mpr hsJ)

/-- The left limit of a piecewise-affine jump path at the arrival time `T n` is the value there
minus the jump size `Y n`: the path jumps up by exactly `Y n` at `T n`. -/
theorem tendsto_piecewisePath_leftLim (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (n : ℕ) :
    Tendsto (piecewisePath x₀ b T Y) (𝓝[Set.Iio (T n)] (T n))
      (𝓝 (piecewisePath x₀ b T Y (T n) - Y n)) := by
  have h_upper : ∀ᶠ u in 𝓝[Set.Iio (T n)] (T n), jumpCount T u ≤ n := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have : ¬ (n < jumpCount T u) := by
      rw [lt_jumpCount_iff hmono htop]
      exact not_le.mpr hu
    omega
  have h_lower : ∀ᶠ u in 𝓝[Set.Iio (T n)] (T n), n ≤ jumpCount T u := by
    cases n with
    | zero => exact Filter.Eventually.of_forall fun _ => Nat.zero_le _
    | succ m =>
      have hmem : Set.Ioi (T m) ∈ 𝓝[Set.Iio (T (m + 1))] (T (m + 1)) :=
        nhdsWithin_le_nhds (Ioi_mem_nhds (hmono (Nat.lt_succ_self m)))
      filter_upwards [hmem] with u hu
      exact (lt_jumpCount_iff hmono htop m u).mpr (le_of_lt hu)
  have h_count : ∀ᶠ u in 𝓝[Set.Iio (T n)] (T n), jumpCount T u = n := by
    filter_upwards [h_upper, h_lower] with u h1 h2
    omega
  set g : ℝ → ℝ := fun u => (x₀ + ∑ i ∈ Finset.range n, Y i) + b * u with hg
  have hval : piecewisePath x₀ b T Y (T n) - Y n = g (T n) := by
    simp only [piecewisePath, jumpCount_arrival_self hmono htop, Finset.sum_range_succ, hg]
    ring
  rw [hval]
  have hgc : Tendsto g (𝓝[Set.Iio (T n)] (T n)) (𝓝 (g (T n))) := by
    have : Continuous g := by fun_prop
    exact this.continuousWithinAt
  refine Filter.Tendsto.congr' ?_ hgc
  filter_upwards [h_count] with u hu
  simp only [piecewisePath, hu, hg]
  ring

/-- A piecewise-affine jump path is càdlàg: right-continuous everywhere with left limits
everywhere. -/
theorem isCadlag_piecewisePath (hmono : StrictMono T) (htop : Tendsto T atTop atTop) :
    IsCadlag (piecewisePath x₀ b T Y) := by
  intro s
  refine ⟨continuousWithinAt_piecewisePath_Ici hmono htop s, ?_⟩
  obtain ⟨a, has, L, hconst⟩ := exists_lt_jumpCount_const hmono htop s
  set g : ℝ → ℝ := fun u => (x₀ + ∑ i ∈ Finset.range L, Y i) + b * u with hg
  refine ⟨g s, ?_⟩
  have heqOn : Set.EqOn (piecewisePath x₀ b T Y) g (Set.Ioo a s) := by
    intro u hu
    simp only [piecewisePath, hconst u hu, hg]
    ring
  have hmem : Set.Ioo a s ∈ 𝓝[Set.Iio s] s := by
    rw [← Set.Ioi_inter_Iio, Set.inter_comm]
    exact inter_mem_nhdsWithin _ (Ioi_mem_nhds has)
  have hgc : Tendsto g (𝓝[Set.Iio s] s) (𝓝 (g s)) := by
    have : Continuous g := by fun_prop
    exact this.continuousWithinAt
  exact Filter.Tendsto.congr' (Filter.eventually_of_mem hmem fun u hu => (heqOn hu).symm) hgc

end PiecewisePath

end ProbabilityTheory
