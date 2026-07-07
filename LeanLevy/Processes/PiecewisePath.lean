/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import LeanLevy.Processes.Cadlag
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

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
* `ProbabilityTheory.piecewisePath_ito` — the deterministic Itô formula: for `f` with continuous
  derivative `f'`, the increment `f (path t) − f (path 0)` splits into the drift integral
  `∫₀ᵗ f' (path s)·b ds` plus the sum of jump increments `f (path (T n)) − f (path (T n) − Y n)`.
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

section Ito

open MeasureTheory
open scoped Interval

variable {x₀ b : ℝ} {T Y : ℕ → ℝ} {f f' : ℝ → ℝ}

/-- Telescoping identity underlying the deterministic Itô formula: if `J i` is the "gap" between
consecutive pieces `L (i + 1) − R i`, then the sum of piece increments `R i − L i` collapses to the
overall increment `R k − L 0` minus the accumulated gaps. -/
private theorem sum_range_succ_telescope (R L J : ℕ → ℝ) (k : ℕ)
    (h : ∀ i < k, J i = L (i + 1) - R i) :
    ∑ i ∈ Finset.range (k + 1), (R i - L i) = R k - L 0 - ∑ i ∈ Finset.range k, J i := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ (fun i => R i - L i), ih fun i hi => h i (by omega),
      Finset.sum_range_succ J, h m (by omega)]
    ring

/-- FTC on a single inter-jump interval: the derivative of the affine composite `s ↦ f (v + b·s)`
integrates to the increment of `f (v + b·-)` between the endpoints. -/
private theorem intervalIntegral_deriv_comp_affine
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') (v a c : ℝ) :
    (∫ s in a..c, f' (v + b * s) * b) = f (v + b * c) - f (v + b * a) := by
  have hderiv : ∀ s ∈ Set.uIcc a c,
      HasDerivAt (fun u => f (v + b * u)) (f' (v + b * s) * b) s := by
    intro s _
    have h1 : HasDerivAt (fun u => v + b * u) b s := by
      simpa using (HasDerivAt.const_mul b (hasDerivAt_id s)).const_add v
    exact (hf (v + b * s)).comp s h1
  have hcont : Continuous (fun s => f' (v + b * s) * b) :=
    (hf'.comp (by fun_prop : Continuous fun s => v + b * s)).mul continuous_const
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a c)

/-- On an interval `[a, c)` on which the jump count is constantly `k'`, the Itô integrand
`s ↦ f' (path s)·b` is interval-integrable and integrates to the increment of `f` along the affine
piece; the two integrands differ at most at the right endpoint, a null set. -/
private theorem piecewisePath_deriv_integral
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    {a c : ℝ} {k' : ℕ} (hac : a ≤ c) (hconst : ∀ s ∈ Set.Ico a c, jumpCount T s = k') :
    IntervalIntegrable (fun s => f' (piecewisePath x₀ b T Y s) * b) volume a c ∧
      (∫ s in a..c, f' (piecewisePath x₀ b T Y s) * b)
        = f ((x₀ + ∑ n ∈ Finset.range k', Y n) + b * c)
          - f ((x₀ + ∑ n ∈ Finset.range k', Y n) + b * a) := by
  set v : ℝ := x₀ + ∑ n ∈ Finset.range k', Y n with hv
  have hae : (fun s => f' (piecewisePath x₀ b T Y s) * b)
      =ᵐ[volume.restrict (Ι a c)] fun s => f' (v + b * s) * b := by
    refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
    rw [ae_iff]
    refine measure_mono_null ?_ (by simp : volume ({c} : Set ℝ) = 0)
    intro x hx
    simp only [Set.mem_setOf_eq, Classical.not_imp] at hx
    obtain ⟨hxmem, hxne⟩ := hx
    rw [Set.uIoc_of_le hac] at hxmem
    rcases eq_or_lt_of_le hxmem.2 with hxc | hxc
    · exact Set.mem_singleton_iff.mpr hxc
    · refine absurd ?_ hxne
      have hxIco : x ∈ Set.Ico a c := ⟨le_of_lt hxmem.1, hxc⟩
      have hpath : piecewisePath x₀ b T Y x = v + b * x := by
        simp only [piecewisePath, hconst x hxIco, hv]; ring
      rw [hpath]
  have hcont : Continuous (fun s => f' (v + b * s) * b) :=
    (hf'.comp (by fun_prop : Continuous fun s => v + b * s)).mul continuous_const
  refine ⟨(hcont.intervalIntegrable a c).congr_ae hae.symm, ?_⟩
  rw [intervalIntegral.integral_congr_ae_restrict hae]
  exact intervalIntegral_deriv_comp_affine hf hf' v a c

/-- **Deterministic Itô formula for a piecewise-affine jump path.** For a `C¹` function `f` (given by
`HasDerivAt` data with continuous derivative `f'`), the increment of `f` along a piecewise-affine
jump path decomposes as the drift integral `∫₀ᵗ f' (path s)·b ds` plus the sum of jump increments
`f (path (T n)) − f (path (T n) − Y n)` over the arrivals `T n ≤ t`. This is the pathwise skeleton
of Itô's formula for a compound-Poisson-with-drift process. -/
theorem piecewisePath_ito (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hmono : StrictMono T) (htop : Tendsto T atTop atTop) (hpos : 0 < T 0)
    {t : ℝ} (ht : 0 ≤ t) :
    f (piecewisePath x₀ b T Y t) - f (piecewisePath x₀ b T Y 0)
      = (∫ s in (0:ℝ)..t, f' (piecewisePath x₀ b T Y s) * b)
        + ∑ n ∈ Finset.range (jumpCount T t),
            (f (piecewisePath x₀ b T Y (T n)) - f (piecewisePath x₀ b T Y (T n) - Y n)) := by
  classical
  set k := jumpCount T t with hk_def
  set e : ℕ → ℝ := fun i => if i = 0 then 0 else if i ≤ k then T (i - 1) else t with he_def
  set v : ℕ → ℝ := fun i => x₀ + ∑ n ∈ Finset.range i, Y n with hv_def
  -- Endpoint-function values.
  have he0 : e 0 = 0 := by simp [he_def]
  have heS : ∀ i, 1 ≤ i → i ≤ k → e i = T (i - 1) := by
    intro i hi1 hik
    simp only [he_def]
    rw [if_neg (by omega), if_pos hik]
  have heTop : ∀ i, k < i → e i = t := by
    intro i hi
    simp only [he_def]
    rw [if_neg (by omega), if_neg (by omega)]
  -- The right endpoint `t` lies strictly before the next arrival.
  have ht_lt : t < T k := by
    have hnot : ¬ (T k ≤ t) := by rw [← lt_jumpCount_iff hmono htop k t]; omega
    exact not_le.mp hnot
  -- Lower bound: reaching `e i` means at least `i` jumps have occurred.
  have he_lb : ∀ i, i ≤ k → ∀ s, e i ≤ s → i ≤ jumpCount T s := by
    intro i hik s hs
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · omega
    · rw [heS i hipos hik] at hs
      have := (lt_jumpCount_iff hmono htop (i - 1) s).mpr hs
      omega
  -- Upper bound: the next endpoint is at most the `i`-th arrival.
  have he_ub : ∀ i, i ≤ k → e (i + 1) ≤ T i := by
    intro i hik
    rcases Nat.lt_or_ge i k with hlt | hge
    · rw [heS (i + 1) (by omega) (by omega)]; simp
    · rw [heTop (i + 1) (by omega)]
      have hik' : i = k := by omega
      rw [hik']; exact le_of_lt ht_lt
  -- The endpoints are (weakly) increasing.
  have he_le : ∀ i, i ≤ k → e i ≤ e (i + 1) := by
    intro i hik
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [he0]
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [heTop 1 (by omega)]; exact ht
      · rw [heS 1 (by omega) (by omega)]; simpa using le_of_lt hpos
    · rw [heS i hipos hik]
      rcases Nat.lt_or_ge i k with hlt | hge
      · rw [heS (i + 1) (by omega) (by omega)]
        simp only [Nat.add_sub_cancel]
        exact hmono.monotone (by omega)
      · rw [heTop (i + 1) (by omega)]
        exact (lt_jumpCount_iff hmono htop (i - 1) t).mp (by rw [← hk_def]; omega)
  -- The jump count is constantly `i` on each piece `[e i, e (i + 1))`.
  have hconst : ∀ i, i ≤ k → ∀ s ∈ Set.Ico (e i) (e (i + 1)), jumpCount T s = i := by
    intro i hik s hs
    have h1 : i ≤ jumpCount T s := he_lb i hik s hs.1
    have h2 : jumpCount T s ≤ i := by
      have hlt : s < T i := lt_of_lt_of_le hs.2 (he_ub i hik)
      by_contra hc
      push_neg at hc
      exact absurd ((lt_jumpCount_iff hmono htop i s).mp hc) (not_le.mpr hlt)
    omega
  -- Per-piece integrability and value.
  have hpiece : ∀ i, i ≤ k →
      IntervalIntegrable (fun s => f' (piecewisePath x₀ b T Y s) * b) volume (e i) (e (i + 1)) ∧
      (∫ s in e i..e (i + 1), f' (piecewisePath x₀ b T Y s) * b)
        = f (v i + b * e (i + 1)) - f (v i + b * e i) := by
    intro i hik
    have hres := piecewisePath_deriv_integral (x₀ := x₀) (b := b) (Y := Y) hf hf'
      (he_le i hik) (hconst i hik)
    simpa [hv_def] using hres
  -- Glue the pieces into the integral over `[0, t]`.
  have hint : ∀ i < k + 1,
      IntervalIntegrable (fun s => f' (piecewisePath x₀ b T Y s) * b) volume (e i) (e (i + 1)) :=
    fun i hi => (hpiece i (by omega)).1
  have hsum_int :
      ∑ i ∈ Finset.range (k + 1), ∫ s in e i..e (i + 1), f' (piecewisePath x₀ b T Y s) * b
        = ∫ s in e 0..e (k + 1), f' (piecewisePath x₀ b T Y s) * b :=
    intervalIntegral.sum_integral_adjacent_intervals hint
  rw [he0, heTop (k + 1) (by omega)] at hsum_int
  have hsum_val :
      ∑ i ∈ Finset.range (k + 1), ∫ s in e i..e (i + 1), f' (piecewisePath x₀ b T Y s) * b
        = ∑ i ∈ Finset.range (k + 1), (f (v i + b * e (i + 1)) - f (v i + b * e i)) :=
    Finset.sum_congr rfl fun i hi => (hpiece i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))).2
  have hRL : ∑ i ∈ Finset.range (k + 1), (f (v i + b * e (i + 1)) - f (v i + b * e i))
      = ∫ s in (0:ℝ)..t, f' (piecewisePath x₀ b T Y s) * b := by
    rw [← hsum_val, hsum_int]
  -- Identify the telescoped endpoints and the gaps with the stated quantities.
  have hRk : f (v k + b * e (k + 1)) = f (piecewisePath x₀ b T Y t) := by
    have hval : v k + b * e (k + 1) = piecewisePath x₀ b T Y t := by
      rw [heTop (k + 1) (by omega)]
      simp only [piecewisePath, hv_def, ← hk_def]
      ring
    rw [hval]
  have hL0 : f (v 0 + b * e 0) = f (piecewisePath x₀ b T Y 0) := by
    have hval : v 0 + b * e 0 = piecewisePath x₀ b T Y 0 := by
      rw [he0, piecewisePath_zero hpos]
      simp only [hv_def, Finset.range_zero, Finset.sum_empty]
      ring
    rw [hval]
  have hJ : ∀ i < k,
      f (piecewisePath x₀ b T Y (T i)) - f (piecewisePath x₀ b T Y (T i) - Y i)
        = f (v (i + 1) + b * e (i + 1)) - f (v i + b * e (i + 1)) := by
    intro i hi
    have hei : e (i + 1) = T i := by
      rw [heS (i + 1) (by omega) (by omega)]; simp
    rw [hei]
    have hpath : piecewisePath x₀ b T Y (T i) = v (i + 1) + b * T i := by
      simp only [piecewisePath, jumpCount_arrival_self hmono htop, hv_def]; ring
    have hpath' : piecewisePath x₀ b T Y (T i) - Y i = v i + b * T i := by
      rw [hpath]; simp only [hv_def, Finset.sum_range_succ]; ring
    rw [hpath', hpath]
  have htel := sum_range_succ_telescope
    (fun i => f (v i + b * e (i + 1))) (fun i => f (v i + b * e i))
    (fun i => f (piecewisePath x₀ b T Y (T i)) - f (piecewisePath x₀ b T Y (T i) - Y i)) k hJ
  rw [← hRL, htel]
  simp only []
  rw [hRk, hL0]
  ring

end Ito

end ProbabilityTheory
