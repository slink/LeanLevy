/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration

/-!
# Stochastic Processes

This file defines the basic vocabulary for stochastic processes indexed by an
ordered type `ι` with values in a measurable group `E`:

* `ProbabilityTheory.increment X s t` — the increment `X t - X s`.
* `ProbabilityTheory.HasIndependentIncrements X μ` — consecutive increments
  along any monotone partition are mutually independent.
* `ProbabilityTheory.HasStationaryIncrements X μ` — the law of an increment
  depends only on the length `h`, not the starting point `s`.
* `ProbabilityTheory.stronglyAdapted_naturalFiltration` — a process is adapted to
  its natural filtration.
* `ProbabilityTheory.HasIndependentIncrements.indepFun_increment` — consecutive
  non-overlapping increments are pairwise independent.
* `ProbabilityTheory.Adapted.measurable_increment` — increments of an adapted
  process are measurable w.r.t. the filtration at the later time.
-/

open MeasureTheory

namespace ProbabilityTheory

variable {ι : Type*} {Ω : Type*} {E : Type*}

section Increment

variable [Sub E]

/-- The increment of a process `X` from time `s` to time `t`. -/
def increment (X : ι → Ω → E) (s t : ι) (ω : Ω) : E := X t ω - X s ω

@[simp]
theorem increment_apply (X : ι → Ω → E) (s t : ι) (ω : Ω) :
    increment X s t ω = X t ω - X s ω := rfl

end Increment

section IncrementLemmas

variable [AddCommGroup E] {X : ι → Ω → E}

@[simp]
theorem increment_self (X : ι → Ω → E) (t : ι) (ω : Ω) :
    increment X t t ω = 0 := sub_self _

theorem increment_add (X : ι → Ω → E) (r s t : ι) (ω : Ω) :
    increment X r s ω + increment X s t ω = increment X r t ω := by
  simp only [increment_apply]; abel

theorem increment_neg (X : ι → Ω → E) (s t : ι) (ω : Ω) :
    increment X s t ω = -increment X t s ω := by
  simp only [increment_apply]; abel

end IncrementLemmas

section MeasurableIncrement

variable [MeasurableSpace Ω] [MeasurableSpace E] [Sub E] [MeasurableSub₂ E]

theorem measurable_increment {X : ι → Ω → E} {s t : ι}
    (hs : Measurable (X s)) (ht : Measurable (X t)) :
    Measurable (increment X s t) :=
  ht.sub hs

end MeasurableIncrement

/-- A process `X` has **independent increments** with respect to a measure `μ` if
for every monotone sequence of times `t₀ ≤ t₁ ≤ ⋯ ≤ tₙ`, the increments
`X(t₁) - X(t₀), …, X(tₙ) - X(tₙ₋₁)` are mutually independent. -/
def HasIndependentIncrements [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]
    (X : ι → Ω → E) (μ : Measure Ω) : Prop :=
  ∀ (n : ℕ) (t : Fin (n + 1) → ι), Monotone t →
    iIndepFun (fun k : Fin n => increment X (t k.castSucc) (t k.succ)) μ

/-- A process `X` has **stationary increments** with respect to a measure `μ` if
the distribution of `X(s + h) - X(s)` depends only on `h`, not on `s`. -/
def HasStationaryIncrements [AddMonoid ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]
    (X : ι → Ω → E) (μ : Measure Ω) : Prop :=
  ∀ (s h : ι), IdentDistrib (increment X s (s + h)) (increment X 0 h) μ μ

section IncrementIndependence

variable [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]

/-- For a process with independent increments, two consecutive non-overlapping
increments are pairwise independent. -/
theorem HasIndependentIncrements.indepFun_increment
    {X : ι → Ω → E} {μ : Measure Ω} (h : HasIndependentIncrements X μ)
    {s t u : ι} (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun (increment X s t) (increment X t u) μ := by
  -- Define the time sequence [s, t, u] : Fin 3 → ι
  let τ : Fin 3 → ι := ![s, t, u]
  -- Show the time sequence is monotone
  have hmono : Monotone τ := Fin.monotone_iff_le_succ.mpr fun i => by
    fin_cases i
    · show s ≤ t; exact hst
    · show t ≤ u; exact htu
  -- Get iIndepFun for the two increments
  have hind := h 2 τ hmono
  -- Extract pairwise independence for indices 0 and 1
  exact hind.indepFun (i := 0) (j := 1) (by decide)

end IncrementIndependence

section NaturalFiltrationIndependence

variable [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] [AddGroup E]

omit [Preorder ι] [MeasurableSpace Ω] [MeasurableSpace E] in
/-- When `X 0 = 0`, the increment from `0` to `j` equals `X j`. -/
private theorem increment_zero_eq [Zero ι] {X : ι → Ω → E}
    (h0 : X 0 = fun _ => 0) (j : ι) : increment X 0 j = X j := by
  ext ω; show X j ω - X 0 ω = X j ω
  rw [show X 0 ω = 0 from congr_fun h0 ω, sub_zero]

/-- For a process with independent increments starting at zero, `X j` is independent
of `increment X s t` whenever `0 ≤ j ≤ s ≤ t`. This follows from the partition
`[0, j, s, t]`. -/
private theorem indepFun_X_increment [Zero ι]
    {X : ι → Ω → E} {μ : Measure Ω}
    (h : HasIndependentIncrements X μ)
    (h0 : X 0 = fun _ => 0)
    {j s t : ι} (h0j : 0 ≤ j) (hjs : j ≤ s) (hst : s ≤ t) :
    IndepFun (X j) (increment X s t) μ := by
  -- Use partition [0, j, s, t] : Fin 4 → ι
  have hmono : Monotone (![0, j, s, t] : Fin 4 → ι) :=
    Fin.monotone_iff_le_succ.mpr fun i => by fin_cases i <;> assumption
  -- Get iIndepFun for the 3 consecutive increments from this partition
  have hind := h 3 ![0, j, s, t] hmono
  -- Extract IndepFun for indices 0 and 2 (increment 0→j vs increment s→t)
  have h02 := hind.indepFun (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  change IndepFun (increment X 0 j) (increment X s t) μ at h02
  rwa [increment_zero_eq h0] at h02

end NaturalFiltrationIndependence

section FiltrationIndependence

variable [LinearOrder ι] [MeasurableSpace Ω] [MeasurableSpace E] [AddGroup E]

/-- For a process with independent increments starting at zero, the join of
σ-algebras generated by finitely many past values `{X j | j ∈ F, j ≤ s}` is
independent of the increment σ-algebra `σ(X t - X s)`.

The proof builds a sorted monotone partition from `F ∪ {0, s, t}`, obtains
mutual independence of consecutive increment σ-algebras, splits into past vs
future via `indep_iSup_of_disjoint`, and uses a telescoping argument to show
each `σ(X j) ≤ ⨆ past increment σ-algebras`. -/
private theorem indep_finset_X_increment [Zero ι]
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [BorelSpace E]
    [MeasurableSub₂ E]
    {X : ι → Ω → E} {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (h : HasIndependentIncrements X μ)
    (hX : ∀ i, StronglyMeasurable (X i))
    (h0 : X 0 = fun _ => 0)
    (h0le : ∀ (i : ι), 0 ≤ i)
    {s t : ι} (hst : s ≤ t)
    (F : Finset {j : ι // j ≤ s}) :
    Indep (⨆ j ∈ F, MeasurableSpace.comap (X (j : ι)) ‹MeasurableSpace E›)
      (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›) μ := by
  -- Derive MeasurableNeg and MeasurableAdd₂ from MeasurableSub₂
  haveI : MeasurableNeg E := ⟨by
    show Measurable (fun x : E => -x)
    have : (fun x : E => -x) = fun x => (0 : E) - x := by ext x; rw [zero_sub]
    rw [this]; exact measurable_const.sub measurable_id⟩
  haveI : MeasurableAdd₂ E := ⟨by
    have : (fun p : E × E => p.1 + p.2) = fun p => p.1 - (-p.2) := by
      ext ⟨a, b⟩; rw [sub_eq_add_neg, neg_neg]
    rw [this]; exact measurable_fst.sub measurable_snd.neg⟩
  -- Step 0: Handle s = t (increment is zero, comap of const is ⊥)
  by_cases hst_eq : s = t
  · have : increment X s t = fun _ => 0 := by ext ω; simp [hst_eq]
    rw [this, MeasurableSpace.comap_const]
    exact indep_bot_right _
  -- Now s < t
  have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
  -- Step 1: Handle empty F
  by_cases hF : F = ∅
  · simp [hF]; exact indep_bot_left _
  -- Strategy: build sorted partition, get iIndep, use indep_iSup_of_disjoint.
  -- Step 2: Build sorted partition from F ∪ {0, s, t}
  let pts : Finset ι := F.image Subtype.val ∪ {0, s, t}
  have hpts_nonempty : pts.Nonempty :=
    ⟨0, Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self 0 _))⟩
  set n := pts.card with hn_def
  have hn_pos : 0 < n := Finset.card_pos.mpr hpts_nonempty
  -- τ : Fin n → ι is the sorted (strictly monotone) enumeration of pts
  let τ : Fin n → ι := pts.orderEmbOfFin rfl
  have hτ_strictMono : StrictMono τ := (pts.orderEmbOfFin rfl).strictMono
  -- τ maps the index of a ∈ pts back to a
  have hτ_val : ∀ (a : ι) (ha : a ∈ pts),
      τ ((pts.orderIsoOfFin rfl).symm ⟨a, ha⟩) = a := by
    intro a ha
    show (pts.orderEmbOfFin rfl) ((pts.orderIsoOfFin rfl).symm ⟨a, ha⟩) = a
    rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
  -- Every τ value is in pts
  have hτ_mem : ∀ i : Fin n, τ i ∈ pts :=
    fun i => Finset.orderEmbOfFin_mem pts rfl i
  -- Membership in pts
  have h0_mem : (0 : ι) ∈ pts :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_insert_self 0 _))
  have hs_mem : s ∈ pts :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self s _))))
  have ht_mem : t ∈ pts :=
    Finset.mem_union.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))))))
  -- All elements of pts are ≤ t
  have hpts_le_t : ∀ x ∈ pts, x ≤ t := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx_left | hx_right
    · obtain ⟨⟨j, hjs⟩, _, rfl⟩ := Finset.mem_image.mp hx_left
      exact le_trans hjs hst
    · rcases Finset.mem_insert.mp hx_right with rfl | hx_right
      · exact le_trans (h0le s) hst
      · rcases Finset.mem_insert.mp hx_right with rfl | hx_right
        · exact hst
        · exact le_of_eq (Finset.mem_singleton.mp hx_right)
  -- τ 0 = 0 (minimum) and τ (n-1) = t (maximum)
  have hτ_zero : τ ⟨0, hn_pos⟩ = 0 := by
    show pts.orderEmbOfFin rfl ⟨0, hn_pos⟩ = 0
    rw [Finset.orderEmbOfFin_zero rfl hn_pos]
    exact le_antisymm (Finset.min'_le pts 0 h0_mem)
      (h0le (pts.min' hpts_nonempty))
  have hτ_last : τ ⟨n - 1, Nat.sub_lt hn_pos Nat.one_pos⟩ = t := by
    show pts.orderEmbOfFin rfl ⟨n - 1, _⟩ = t
    rw [Finset.orderEmbOfFin_last rfl hn_pos]
    exact le_antisymm (Finset.max'_le pts hpts_nonempty _ hpts_le_t)
      (Finset.le_max' pts t ht_mem)
  -- n ≥ 2 since s, t ∈ pts are distinct (s < t)
  have hn_ge2 : 2 ≤ n := by
    rw [hn_def]
    apply Finset.one_lt_card.mpr
    exact ⟨s, hs_mem, t, ht_mem, ne_of_lt hst_lt⟩
  -- Step 4: Get iIndep of consecutive increments
  -- HasIndependentIncrements gives us iIndepFun for n-1 consecutive increments
  -- We need τ : Fin ((n-1) + 1) → ι, i.e. Fin n → ι.
  -- Since n - 1 + 1 = n (as n ≥ 2 > 0), we can cast.
  have hn_sub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hn_ge2))
  -- Get iIndepFun using the monotone partition
  have hτ_mono : Monotone τ := hτ_strictMono.monotone
  have hind := h (n - 1) (τ ∘ Fin.cast hn_sub) (hτ_mono.comp (Fin.cast_strictMono hn_sub).monotone)
  -- The only element of pts strictly greater than s is t
  have hpts_gt_s : ∀ x ∈ pts, s < x → x = t := by
    intro x hx hsx
    rcases Finset.mem_union.mp hx with hx_left | hx_right
    · obtain ⟨⟨j, hjs⟩, _, rfl⟩ := Finset.mem_image.mp hx_left
      exact absurd hsx (not_lt.mpr hjs)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx_right
      rcases hx_right with rfl | rfl | rfl
      · exact absurd hsx (not_lt.mpr (h0le _))
      · exact absurd hsx (lt_irrefl _)
      · rfl
  -- s is the second-to-last element: τ(n-2) = s
  have hn2_lt : n - 2 < n := Nat.sub_lt hn_pos (by omega)
  have hτ_second_last : τ ⟨n - 2, hn2_lt⟩ = s := by
    -- s is in pts, so s = τ p for some p
    set p := ((pts.orderIsoOfFin rfl).symm ⟨s, hs_mem⟩).val with hp_def
    have hp_lt : p < n := ((pts.orderIsoOfFin rfl).symm ⟨s, hs_mem⟩).isLt
    have hτp : τ ⟨p, hp_lt⟩ = s := by
      show τ ((pts.orderIsoOfFin rfl).symm ⟨s, hs_mem⟩) = s
      exact hτ_val s hs_mem
    -- Show p = n - 2
    suffices p = n - 2 by
      have : (⟨p, hp_lt⟩ : Fin n) = ⟨n - 2, hn2_lt⟩ := Fin.ext this
      rw [← this]; exact hτp
    -- p < n - 1 because τ p = s < t = τ(n-1)
    have hp_lt_last : p < n - 1 := by
      by_contra h_ge
      push_neg at h_ge
      have : p = n - 1 := by omega
      have : τ ⟨p, hp_lt⟩ = τ ⟨n - 1, Nat.sub_lt hn_pos Nat.one_pos⟩ := by
        congr 1; ext; exact this
      rw [hτp, hτ_last] at this
      exact absurd this (ne_of_lt hst_lt)
    -- If p < n - 2, then τ(p+1) is in pts, τ(p+1) > s, and τ(p+1) < t
    -- But the only element of pts > s is t. Contradiction.
    by_contra hp_ne
    have hp_lt2 : p < n - 2 := by omega
    have hp1_lt : p + 1 < n := by omega
    have hp1_lt_last : p + 1 < n - 1 := by omega
    have hgt : s < τ ⟨p + 1, hp1_lt⟩ := by
      rw [← hτp]; exact hτ_strictMono (show (⟨p, hp_lt⟩ : Fin n) < ⟨p + 1, hp1_lt⟩ by exact Fin.mk_lt_mk.mpr (by omega))
    have hlt : τ ⟨p + 1, hp1_lt⟩ < t := by
      rw [← hτ_last]; exact hτ_strictMono (show (⟨p + 1, hp1_lt⟩ : Fin n) < ⟨n - 1, _⟩ by exact Fin.mk_lt_mk.mpr (by omega))
    have := hpts_gt_s (τ ⟨p + 1, hp1_lt⟩) (hτ_mem ⟨p + 1, hp1_lt⟩) hgt
    exact absurd this (ne_of_lt hlt)
  -- Define the sigma-algebra family for the partition increments
  let m : Fin (n - 1) → MeasurableSpace Ω := fun k =>
    MeasurableSpace.comap
      (increment X (τ ⟨k.val, by omega⟩) (τ ⟨k.val + 1, by omega⟩))
      ‹MeasurableSpace E›
  -- hind gives us iIndep m μ (definitionally equal to hind)
  have hind' : iIndep m μ := hind
  -- Each m k ≤ the ambient sigma-algebra
  have hm_le : ∀ k : Fin (n - 1), m k ≤ ‹MeasurableSpace Ω› := by
    intro k
    exact Measurable.comap_le ((hX _).measurable.sub (hX _).measurable)
  -- Split into past S and future T
  let S : Set (Fin (n - 1)) := {k | k.val < n - 2}
  let T : Set (Fin (n - 1)) := {k | k.val = n - 2}
  have hST : Disjoint S T := by
    rw [Set.disjoint_iff]
    intro k ⟨hkS, hkT⟩
    simp only [S, T, Set.mem_setOf_eq] at hkS hkT
    omega
  -- The last index
  have hn2_lt' : n - 2 < n - 1 := by omega
  let last : Fin (n - 1) := ⟨n - 2, hn2_lt'⟩
  -- Apply indep_iSup_of_disjoint
  have hindST : Indep (⨆ k ∈ S, m k) (⨆ k ∈ T, m k) μ :=
    indep_iSup_of_disjoint hm_le hind' hST
  -- Step 5: Show ⨆ k ∈ T, m k = comap (increment X s t) mE
  have hT_eq : (⨆ k ∈ T, m k) = MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E› := by
    -- T = {last}, so ⨆ k ∈ T, m k = m last
    have : T = {last} := by
      ext k; simp only [T, last, Set.mem_setOf_eq, Set.mem_singleton_iff, Fin.ext_iff]
    rw [this, iSup_singleton]
    -- m last = comap (increment X s t) mE
    -- Since τ ⟨n-2, _⟩ = s and τ ⟨n-2+1, _⟩ = t
    show MeasurableSpace.comap (increment X (τ ⟨n - 2, _⟩) (τ ⟨(n - 2) + 1, _⟩)) _ = _
    have hn21 : n - 2 + 1 = n - 1 := by omega
    have hτn2plus1 : τ ⟨n - 2 + 1, by omega⟩ = t := by
      have : (⟨n - 2 + 1, (by omega : n - 2 + 1 < n)⟩ : Fin n) =
             ⟨n - 1, Nat.sub_lt hn_pos Nat.one_pos⟩ := by
        ext; exact hn21
      rw [this]; exact hτ_last
    -- Now rewrite the increment arguments
    have : increment X (τ ⟨n - 2, by omega⟩) (τ ⟨n - 2 + 1, by omega⟩) = increment X s t := by
      ext ω; simp only [increment_apply]; rw [hτ_second_last, hτn2plus1]
    rw [this]
  -- Step 6: Show ⨆ j ∈ F, comap (X j) mE ≤ ⨆ k ∈ S, m k (telescoping)
  -- For each j ∈ F with j ≤ s, X j is measurable w.r.t. ⨆ k ∈ S, m k
  have hF_le_past : ⨆ j ∈ F,
      MeasurableSpace.comap (X (j : ι)) ‹MeasurableSpace E› ≤ ⨆ k ∈ S, m k := by
    apply iSup₂_le
    intro ⟨j, hjs⟩ hjF
    -- j ∈ pts and j ≤ s, so j = τ p for some p
    have hj_pts : j ∈ pts :=
      Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨⟨j, hjs⟩, hjF, rfl⟩))
    -- Telescoping: show comap (X (τ p)) mE ≤ ⨆ k ∈ S, m k by induction on p.
    -- We prove: for all p < n with τ p ≤ s,
    --   @Measurable Ω E (⨆ k ∈ S, m k) mE (X (τ p))
    -- From this, comap (X (τ p)) mE ≤ ⨆ k ∈ S, m k follows by Measurable.comap_le.
    suffices hmeas_telescope : ∀ (p : ℕ) (hp : p < n),
        τ ⟨p, hp⟩ ≤ s → @Measurable Ω E (⨆ k ∈ S, m k) ‹MeasurableSpace E› (X (τ ⟨p, hp⟩)) by
      -- Find the index p of j in the sorted partition
      let p_fin := (pts.orderIsoOfFin rfl).symm ⟨j, hj_pts⟩
      have hτp : τ p_fin = j := hτ_val j hj_pts
      have hp_lt : p_fin.val < n := p_fin.isLt
      have : @Measurable Ω E (⨆ k ∈ S, m k) ‹MeasurableSpace E› (X j) := by
        rw [← hτp]; exact hmeas_telescope p_fin.val hp_lt (by rw [hτp]; exact hjs)
      exact this.comap_le
    -- Prove by strong induction on p
    intro p
    induction p with
    | zero =>
      intro hp _
      -- X (τ 0) = X 0 = const 0, measurable w.r.t. anything
      rw [hτ_zero, h0]; exact measurable_const
    | succ p ih =>
      intro hp hle
      -- X (τ (p+1)) ω = X (τ p) ω - (X (τ p) ω - X (τ (p+1)) ω) by sub_sub_cancel
      -- Express X (τ (p+1)) as a subtraction of two (⨆ k ∈ S, m k)-measurable functions
      have hp_lt : p < n := by omega
      -- p < n - 2 (since τ (p+1) ≤ s and τ is strict mono, so p+1 ≤ n-2, hence p < n-2)
      have hp_in_S : p < n - 2 := by
        -- τ (p+1) ≤ s, so p+1 ≤ n-2 (position of s), hence p < n-2
        by_contra h_ge; push_neg at h_ge
        -- If p ≥ n - 2, then p + 1 ≥ n - 1, but p + 1 < n, so p + 1 = n - 1
        have : p + 1 = n - 1 := by omega
        -- Then τ (p+1) = τ (n-1) = t
        have : τ ⟨p + 1, hp⟩ = t := by
          rw [show (⟨p + 1, hp⟩ : Fin n) = ⟨n - 1, _⟩ from Fin.ext (by omega)]
          exact hτ_last
        -- But τ (p+1) ≤ s < t, contradiction
        exact absurd (this ▸ hle) (not_le.mpr hst_lt)
      -- increment X (τ p) (τ (p+1)) is (⨆ k ∈ S, m k)-measurable
      have hmeas_incr : @Measurable Ω E (⨆ k ∈ S, m k) ‹MeasurableSpace E›
          (increment X (τ ⟨p, hp_lt⟩) (τ ⟨p + 1, hp⟩)) :=
        (@comap_measurable Ω E _
          (increment X (τ ⟨p, hp_lt⟩) (τ ⟨p + 1, hp⟩))).mono
          (le_iSup₂ (f := fun k (_ : k ∈ S) => m k) ⟨p, by omega⟩ hp_in_S) le_rfl
      -- X (τ p) is (⨆ k ∈ S, m k)-measurable by IH
      have hmeas_prev : @Measurable Ω E (⨆ k ∈ S, m k) ‹MeasurableSpace E›
          (X (τ ⟨p, hp_lt⟩)) :=
        ih hp_lt (le_trans (hτ_mono (Fin.mk_le_mk.mpr (by omega))) hle)
      -- X (τ (p+1)) = incr + prev by sub_add_cancel
      have heq : X (τ ⟨p + 1, hp⟩) =
          fun ω => increment X (τ ⟨p, hp_lt⟩) (τ ⟨p + 1, hp⟩) ω + X (τ ⟨p, hp_lt⟩) ω := by
        ext ω; simp only [increment_apply]; exact (sub_add_cancel _ _).symm
      rw [heq]
      exact hmeas_incr.add hmeas_prev
  -- Step 7: Combine
  rw [← hT_eq]
  exact indep_of_indep_of_le_left hindST hF_le_past

/-- For a process with independent increments starting at zero, the increment
`X(t) - X(s)` is independent of the natural filtration at time `s`.

This is a key structural property of Lévy processes: the future is independent
of the past. The proof uses `indep_iSup_of_directed_le` over a directed family
indexed by finite subsets of `{j | j ≤ s}`, where each finite subset's independence
follows from the partition argument. -/
theorem HasIndependentIncrements.indep_naturalFiltration
    [Zero ι]
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] [BorelSpace E]
    [MeasurableSub₂ E]
    {X : ι → Ω → E} {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    (h : HasIndependentIncrements X μ)
    (hX : ∀ i, StronglyMeasurable (X i))
    (h0 : X 0 = fun _ => 0)
    (h0le : ∀ (i : ι), 0 ≤ i)
    {s t : ι} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›)
      ((Filtration.natural (fun i => X i) hX).seq s) μ := by
  apply Indep.symm
  show Indep ((Filtration.natural (fun i => X i) hX).seq s)
    (MeasurableSpace.comap (increment X s t) ‹MeasurableSpace E›) μ
  simp only [Filtration.natural]
  rw [iSup_subtype']
  rw [iSup_eq_iSup_finset]
  apply indep_iSup_of_directed_le
  · exact fun F => indep_finset_X_increment h hX h0 h0le hst F
  · intro F; exact iSup₂_le fun j _ => (hX j).measurable.comap_le
  · exact ((hX t).measurable.sub (hX s).measurable).comap_le
  · exact directed_of_isDirected_le fun F₁ F₂ h12 =>
      biSup_mono fun j hj => Finset.mem_of_subset h12 hj

end FiltrationIndependence

section FiltrationAdapted

variable {m : MeasurableSpace Ω} [Preorder ι]
  [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
variable [TopologicalSpace.MetrizableSpace E]
variable [Sub E] [MeasurableSub₂ E]

omit [Sub E] [MeasurableSub₂ E] in
/-- A process is strongly adapted to its natural filtration. This is a convenience
wrapper around `Filtration.stronglyAdapted_natural` specialized to processes
with a single value type. -/
theorem stronglyAdapted_naturalFiltration
    {X : ι → Ω → E} (hX : ∀ i, StronglyMeasurable (X i)) :
    StronglyAdapted
      (Filtration.natural (fun i => X i) hX) (fun i => X i) :=
  Filtration.stronglyAdapted_natural hX

omit [TopologicalSpace E] [BorelSpace E] [TopologicalSpace.MetrizableSpace E] in
/-- If `X` is adapted to filtration `𝓕`, then `increment X s t` is `𝓕 t`-measurable
when `s ≤ t`. -/
theorem Adapted.measurable_increment
    {𝓕 : Filtration ι m} {X : ι → Ω → E}
    (hX : Adapted 𝓕 (fun i => X i))
    {s t : ι} (hst : s ≤ t) :
    Measurable[𝓕 t] (increment X s t) :=
  (hX t).sub ((hX s).mono (𝓕.mono hst) le_rfl)

end FiltrationAdapted

end ProbabilityTheory
