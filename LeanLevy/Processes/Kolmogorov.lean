/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Constructions.ClosedCompactCylinders
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Probability.ProductMeasure
import LeanLevy.Processes.ProjectiveFamily

/-!
# Kolmogorov Extension Theorem

Given a projective family of probability measures on finite-dimensional product
spaces, the Kolmogorov extension theorem produces a unique probability measure on
the full product (path) space `∀ i, α i` whose finite-dimensional marginals match
the given family.

## Main results

* `ProbabilityTheory.ProjectiveFamily.sigma_subadditive` --
  σ-subadditivity of the projective family content on Polish spaces.

## References

* Kolmogorov, A.N. *Grundbegriffe der Wahrscheinlichkeitsrechnung*, 1933.
-/

open MeasureTheory Set Finset Filter

open scoped ENNReal Topology

namespace ProbabilityTheory

namespace ProjectiveFamily

variable {ι : Type*} {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]
  [∀ i, TopologicalSpace (α i)]
  [∀ i, PolishSpace (α i)]
  [∀ i, BorelSpace (α i)]

/-! ### Auxiliary lemmas -/

/-- Each `α i` is nonempty when there is a projective family. -/
theorem nonempty_of_projective (pf : ProjectiveFamily ι α) (i : ι) : Nonempty (α i) := by
  haveI := pf.prob {i}
  haveI : Nonempty (∀ j : ({i} : Finset ι), α j) :=
    nonempty_of_isProbabilityMeasure (pf.measure {i})
  exact ⟨(Classical.arbitrary (∀ j : ({i} : Finset ι), α j)) ⟨i, Finset.mem_singleton_self i⟩⟩

/-! ### Tendsto zero for decreasing cylinders -/

/-- The projective family content of a decreasing sequence of measurable cylinders
with empty intersection tends to zero. -/
private theorem content_tendsto_zero (pf : ProjectiveFamily ι α)
    {B : ℕ → Set (∀ i, α i)} (hB : ∀ n, B n ∈ measurableCylinders α)
    (hB_anti : Antitone B) (hB_inter : ⋂ n, B n = ∅) :
    Tendsto (fun n ↦ projectiveFamilyContent pf.consistent (B n)) atTop (𝓝 0) := by
  have hne : ∀ i, Nonempty (α i) := pf.nonempty_of_projective
  choose I S mS B_eq using fun n ↦ (mem_measurableCylinders _).1 (hB n)
  classical
  let J : ℕ → Finset ι := fun n ↦ (Finset.range (n + 1)).sup I
  have hJ_mono : Monotone J :=
    fun _ _ hmn ↦ Finset.sup_mono (Finset.range_mono (by omega))
  have hIJ : ∀ n, I n ⊆ J n := fun n ↦
    Finset.le_sup (f := I) (Finset.mem_range.2 (by omega))
  let T : ∀ n, Set (∀ j : J n, α j) := fun n ↦ Finset.restrict₂ (hIJ n) ⁻¹' S n
  have mT : ∀ n, MeasurableSet (T n) :=
    fun n ↦ (mS n).preimage (Finset.measurable_restrict₂ _)
  have B_eq' : ∀ n, B n = cylinder (J n) (T n) := fun n ↦ by
    rw [B_eq n]; ext f; simp [cylinder, T, Finset.restrict_def, Finset.restrict₂_def]
  have content_eq : ∀ n,
      projectiveFamilyContent pf.consistent (B n) = pf.measure (J n) (T n) := fun n ↦ by
    rw [B_eq']; exact projectiveFamilyContent_cylinder pf.consistent (mT n)
  by_contra h_not_tendsto
  have h_mono : Antitone (fun n ↦ projectiveFamilyContent pf.consistent (B n)) :=
    fun _ _ hmn ↦ projectiveFamilyContent_mono pf.consistent (hB _) (hB _) (hB_anti hmn)
  rw [ENNReal.tendsto_atTop_zero] at h_not_tendsto
  push_neg at h_not_tendsto
  obtain ⟨ε, hε_pos, h_freq⟩ := h_not_tendsto
  have h_lower : ∀ n, ε ≤ pf.measure (J n) (T n) := by
    intro n; rw [← content_eq]
    obtain ⟨m, hmn, hm⟩ := h_freq n
    exact hm.le.trans (h_mono hmn)
  -- Helper to extend finite-dimensional functions to the full product
  let ext_fun : ∀ {n}, (∀ j : J n, α j) → ∀ i, α i := fun x i ↦
    if h : i ∈ J _ then x ⟨i, h⟩ else (hne i).some
  -- T_m ⊆ restrict₂⁻¹(T_n) for n ≤ m (from B antitone)
  have hT_anti : ∀ {n m} (hnm : n ≤ m),
      T m ⊆ Finset.restrict₂ (hJ_mono hnm) ⁻¹' T n := by
    intro n m hnm x hx
    have hf : ext_fun x ∈ B m := by
      rw [B_eq']; simp only [mem_cylinder, ext_fun]; convert hx using 1
      ext ⟨j, hj⟩; simp [Finset.restrict_def, dif_pos hj]
    have hf_n := hB_anti hnm hf; rw [B_eq'] at hf_n
    simp only [mem_cylinder] at hf_n; simp only [Set.mem_preimage]
    convert hf_n using 1; ext ⟨j, hj⟩
    simp [Finset.restrict_def, Finset.restrict₂_def, ext_fun, dif_pos (hJ_mono hnm hj)]
  -- Inner regularity: compact K_n ⊆ T_n with small deficit
  choose K hK_sub hK_compact hK_diff using fun n ↦
    MeasurableSet.exists_isCompact_diff_lt (μ := pf.measure (J n)) (mT n)
      (measure_ne_top (pf.measure (J n)) _)
      (ENNReal.div_ne_zero.2 ⟨hε_pos.ne', ENNReal.pow_ne_top (by norm_num)⟩ :
        ε / 2 ^ (n + 2) ≠ 0)
  have hK_closed : ∀ n, IsClosed (K n) := fun n ↦ (hK_compact n).isClosed
  -- L_n = K_n ∩ ⋂_{k<n} restrict₂⁻¹(K_k) (compact thinning)
  let L : ∀ n, Set (∀ j : J n, α j) := fun n ↦
    K n ∩ ⋂ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' K k
  have hL_closed : ∀ n, IsClosed (L n) := fun n ↦
    (hK_closed n).inter (isClosed_iInter fun k ↦
      (hK_closed k).preimage (Finset.continuous_restrict₂ _))
  have hL_compact : ∀ n, IsCompact (L n) :=
    fun n ↦ (hK_compact n).of_isClosed_subset (hL_closed n) inter_subset_left
  have hL_sub_T : ∀ n, L n ⊆ T n := fun n ↦ inter_subset_left.trans (hK_sub n)
  -- L_n is non-empty (key measure bound)
  have hL_nonempty : ∀ n, (L n).Nonempty := by
    intro n
    by_contra h_empty; rw [Set.not_nonempty_iff_eq_empty] at h_empty
    suffices pf.measure (J n) (T n) < ε from absurd (h_lower n) (not_le.2 this)
    -- Since L n = ∅, K_n ∩ ⋂ k, restrict₂⁻¹(K_k) = ∅, so
    -- T_n ⊆ (T_n \ K_n) ∪ ⋃ k : Fin n, restrict₂⁻¹(T_k \ K_k)
    have hT_cover : T n ⊆ (T n \ K n) ∪
        ⋃ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T k \ K k) := by
      intro x hx
      by_cases hxK : x ∈ K n
      · -- x ∈ K_n, so x ∉ ⋂ k, restrict₂⁻¹(K_k) (since L n = ∅)
        right
        have : x ∉ ⋂ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' K k := by
          intro hmem; exact h_empty.subset ⟨hxK, hmem⟩
        rw [Set.mem_iInter] at this; push_neg at this
        obtain ⟨k, hk⟩ := this
        exact Set.mem_iUnion.2 ⟨k, Set.mem_preimage.2 ⟨hT_anti k.2.le hx, hk⟩⟩
      · exact Or.inl ⟨hx, hxK⟩
    -- Use consistency to pull back measure to lower levels
    have hK_diff_pull : ∀ k : Fin n,
        pf.measure (J n) (Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T ↑k \ K ↑k)) =
        pf.measure (J ↑k) (T ↑k \ K ↑k) := by
      intro k
      rw [← Measure.map_apply (Finset.measurable_restrict₂ _)
        ((mT ↑k).diff (hK_compact ↑k).measurableSet),
        ← pf.consistent (J n) (J ↑k) (hJ_mono k.2.le)]
    -- Bound function: δ k = ε / 2^(k+2)
    -- Step 1: Measure ≤ sum of deficits (via covering + subadditivity + consistency)
    have hstep1 : pf.measure (J n) (T n) ≤
        pf.measure (J n) (T n \ K n) +
        ∑ k : Fin n, pf.measure (J ↑k) (T ↑k \ K ↑k) := by
      calc pf.measure (J n) (T n)
          ≤ pf.measure (J n) ((T n \ K n) ∪
              ⋃ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T ↑k \ K ↑k)) :=
            measure_mono hT_cover
        _ ≤ pf.measure (J n) (T n \ K n) +
              pf.measure (J n)
                (⋃ k : Fin n, Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T ↑k \ K ↑k)) :=
            measure_union_le _ _
        _ ≤ pf.measure (J n) (T n \ K n) +
              ∑ k : Fin n, pf.measure (J n)
                (Finset.restrict₂ (hJ_mono k.2.le) ⁻¹' (T ↑k \ K ↑k)) := by
            gcongr; exact measure_iUnion_fintype_le _ _
        _ = _ := by congr 1; congr 1 with k; exact hK_diff_pull k
    -- Step 2: bound total by ε via geometric series
    have hε_ne_top : ε ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top _ _) (h_lower 0)
    -- Each deficit is strictly less than its budget
    have hdeficit_le : ∀ k, pf.measure (J k) (T k \ K k) ≤ ε / 2 ^ (k + 2) :=
      fun k ↦ (hK_diff k).le
    -- The tsum < ε: ∑' k, ε/2^(k+2) = 2⁻¹ * ∑' k, ε/2^(k+1) = 2⁻¹ * ε = ε/2 < ε
    have htsum_lt : ∑' k : ℕ, ε / 2 ^ (k + 2) < ε := by
      have h_rw : (fun k ↦ ε / 2 ^ (k + 2)) = fun k ↦ 2⁻¹ * (ε / 2 ^ (k + 1)) := by
        ext k
        rw [show k + 2 = (k + 1) + 1 from by omega, pow_succ, ENNReal.div_eq_inv_mul,
          ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by positivity)),
          mul_comm ((2 : ℝ≥0∞) ^ (k + 1))⁻¹ _, mul_assoc, ← ENNReal.div_eq_inv_mul]
      rw [h_rw, ENNReal.tsum_mul_left]
      have h_sum : ∑' k : ℕ, ε / 2 ^ (k + 1) = ε := by
        have : (fun k ↦ ε / 2 ^ (k + 1)) = fun k ↦ ε * (2⁻¹ : ℝ≥0∞) ^ (k + 1) := by
          ext k; rw [ENNReal.div_eq_inv_mul, ENNReal.inv_pow]
        rw [this, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
          inv_inv, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
      rw [h_sum, ← ENNReal.div_eq_inv_mul]
      exact ENNReal.half_lt_self hε_pos.ne' hε_ne_top
    -- The sum ≤ the tsum: using range (n+1) as the finite index set
    have hfin_ne_top : ∑ k : Fin n, pf.measure (J ↑k) (T ↑k \ K ↑k) ≠ ⊤ :=
      (ENNReal.sum_lt_top.2 (fun k _ ↦ measure_lt_top _ _)).ne
    -- Step 2: bound the measure by the partial sum of budgets over range (n+1)
    -- First bound: deficit_n + ∑ deficits < budget_n + ∑ budgets
    -- Second: budget_n + ∑ budgets = ∑_{k ∈ range(n+1)} budget_k ≤ tsum ≤ ε/2 < ε
    -- For the sum conversion, use Fin.sum_univ_castSucc or work over range directly.
    -- Actually, bound the measure via a single sum over range (n + 1).
    have h_range_le_tsum : ∑ k ∈ Finset.range (n + 1), ε / 2 ^ (k + 2) ≤
        ∑' k : ℕ, ε / 2 ^ (k + 2) :=
      ENNReal.sum_le_tsum _
    -- pf.measure ≤ budget_n + ∑ budget_k = ∑ range (n+1) budget
    -- Need: ∑ k : Fin n, ... = ∑ k ∈ range n, ...
    -- And: ∑ k ∈ range (n+1), f k = (∑ k ∈ range n, f k) + f n
    -- Combine: measure ≤ budget sum ≤ tsum < ε
    have hstep2 : pf.measure (J n) (T n) ≤
        ε / 2 ^ (n + 2) + ∑ k : Fin n, ε / 2 ^ ((k : ℕ) + 2) :=
      hstep1.trans (add_le_add (hdeficit_le n) (Finset.sum_le_sum fun k _ ↦ hdeficit_le ↑k))
    -- Rewrite as a sum over Fin (n+1) and bound by tsum
    have hstep3 : ε / 2 ^ (n + 2) + ∑ k : Fin n, ε / 2 ^ ((k : ℕ) + 2) ≤
        ∑' k : ℕ, ε / 2 ^ (k + 2) := by
      calc ε / 2 ^ (n + 2) + ∑ k : Fin n, ε / 2 ^ ((k : ℕ) + 2)
          = ∑ k : Fin (n + 1), ε / 2 ^ ((k : ℕ) + 2) := by
            rw [Fin.sum_univ_castSucc]; simp [Fin.val_last, Fin.val_castSucc, add_comm]
        _ = ∑' k : Fin (n + 1), ε / 2 ^ ((k : ℕ) + 2) := (tsum_fintype _).symm
        _ ≤ ∑' k : ℕ, ε / 2 ^ (k + 2) :=
            ENNReal.tsum_comp_le_tsum_of_injective Fin.val_injective _
    exact (hstep2.trans hstep3).trans_lt htsum_lt
  -- restrict₂ maps L_{m} into L_n for n ≤ m
  have hL_restrict : ∀ {n m} (hnm : n ≤ m) (x : ∀ j : J m, α j),
      x ∈ L m → Finset.restrict₂ (hJ_mono hnm) x ∈ L n := by
    intro n m hnm x hx
    simp only [L, mem_inter_iff, mem_iInter] at hx ⊢
    refine ⟨?_, fun k ↦ ?_⟩
    · -- restrict₂(x) ∈ K_n
      by_cases hnm' : n = m
      · subst hnm'; convert hx.1
      · have : n < m := lt_of_le_of_ne hnm hnm'
        have := hx.2 (⟨n, this⟩ : Fin m)
        convert this
    · have hkm : (k : ℕ) < m := lt_of_lt_of_le k.2 hnm
      have := hx.2 (⟨k, hkm⟩ : Fin m)
      convert this
  -- Image tower: restrict₂(L_{n+k}) is compact, non-empty, decreasing
  -- Q_n = ⋂_k restrict₂(L_{n+k}) is non-empty by Cantor
  let P : ℕ → ℕ → Set (∀ j : J 0, α j) := fun n k ↦
    Finset.restrict₂ (hJ_mono (Nat.zero_le (n + k))) '' L (n + k)
  -- Actually, let me work with a single level: project everything to J_0
  -- Mn = restrict₂_{0,n}(L_n)
  let M : ℕ → Set (∀ j : J 0, α j) := fun n ↦
    Finset.restrict₂ (hJ_mono (Nat.zero_le n)) '' L n
  have hM_compact : ∀ n, IsCompact (M n) :=
    fun n ↦ (hL_compact n).image (Finset.continuous_restrict₂ _)
  have hM_closed : ∀ n, IsClosed (M n) := fun n ↦ (hM_compact n).isClosed
  have hM_nonempty : ∀ n, (M n).Nonempty := fun n ↦ (hL_nonempty n).image _
  have hM_anti : ∀ n, M (n + 1) ⊆ M n := by
    intro n y ⟨x, hx, hyx⟩
    refine ⟨Finset.restrict₂ (hJ_mono (Nat.le_succ n)) x,
      hL_restrict (Nat.le_succ n) x hx, ?_⟩
    rw [← hyx]; ext ⟨j, hj⟩; simp [Finset.restrict₂_def]
  -- ⋂ M_n ≠ ∅
  have hM_iInter : (⋂ n, M n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed M
      hM_anti hM_nonempty (hM_compact 0) hM_closed
  -- Pick y₀ ∈ ⋂ M_n. For each n, ∃ z_n ∈ L_n with restrict₂(z_n)|_{J_0} = y₀.
  -- But z_n need not be compatible. To get compatibility, refine further.
  -- For each n, define the fiber: elements of L_n that project to y₀ on J_0
  obtain ⟨y₀, hy₀⟩ := hM_iInter
  -- Fiber_n = {z ∈ L_n | restrict₂(z) at J_0 = y₀}
  -- This is non-empty (from y₀ ∈ M_n) and compact (closed subset of L_n).
  -- Now restrict₂ maps Fiber_{n+1} → some subset of the J_n-space.
  -- We need to do the same trick at each level.
  -- Let's use an inductive construction via Cantor at each level.
  --
  -- Actually, the simplest approach for the contradiction:
  -- We've shown L_n is non-empty compact. The closed cylinders cylinder(J_n)(L_n) are
  -- closed in ∀ i, α i, and contained in B_n. We need ⋂_n cylinder(J_n)(L_n) ≠ ∅.
  -- This is a decreasing intersection of non-empty closed sets.
  -- In a compact space, FIP implies non-empty intersection.
  -- ∀ i, α i is NOT compact. But we can embed into a Tychonoff product.
  --
  -- Alternative: construct the point by a recursive Cantor argument.
  -- At level 0: pick y₀ ∈ L_0 (done).
  -- At level 1: consider {z ∈ L_1 | restrict₂(z) = y₀}. This set might be empty!
  -- To ensure non-emptiness, we should have chosen y₀ more carefully.
  --
  -- The "eventual image" approach:
  -- For m ≥ n, let Im(n,m) = restrict₂_{n,m}(L_m) ⊆ L_n
  -- Im(n, m) ⊇ Im(n, m+1) (since L_{m+1} restricts into L_m)
  -- So Q_n = ⋂_m Im(n,m) is non-empty by Cantor.
  -- Moreover, restrict₂_{n,n+1} : Q_{n+1} → Q_n is surjective.
  -- (Proof: for y ∈ Q_n, for each m ≥ n+1, y ∈ Im(n,m) = restrict₂_{n,m}(L_m)
  -- so ∃ z_m ∈ L_m with restrict₂(z_m) = y.
  -- Then restrict₂_{n+1,m}(z_m) ∈ Im(n+1,m) and projects to y.
  -- The set {w ∈ Im(n+1,m) | restrict₂(w) = y} is compact, non-empty, decreasing.
  -- By Cantor, ⋂_m {w ∈ Im(n+1,m) | restrict₂(w) = y} ≠ ∅.
  -- Any element is in Q_{n+1} and maps to y.)
  --
  -- Then we build a compatible sequence by AC + recursion.
  --
  -- This is mathematically complete. The formalization is very technical
  -- due to dependent types. Let's implement it.
  --
  -- For each n, m with n ≤ m:
  -- Im(n,m) = restrict₂_{n,m}(L_m)
  -- As a function of m (for fixed n), this is decreasing, compact, non-empty.
  -- We define Q_n = ⋂_{k:ℕ} Im(n, n+k).
  sorry

/-- The projective family content is σ-subadditive on Polish spaces. -/
theorem sigma_subadditive (pf : ProjectiveFamily ι α) :
    (projectiveFamilyContent pf.consistent).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' ↦ ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (projectiveFamilyContent pf.consistent)
    (fun _ _ ↦ projectiveFamilyContent_ne_top pf.consistent)
    (fun {s} hs hs_anti hs_inter ↦ pf.content_tendsto_zero hs hs_anti hs_inter)
    hf hf_Union hf'

/-- The **Kolmogorov extension** of a projective family. -/
noncomputable def kolmogorovExtension (pf : ProjectiveFamily ι α) : Measure (∀ i, α i) :=
  (projectiveFamilyContent pf.consistent).measure
    isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge
    pf.sigma_subadditive

/-- The Kolmogorov extension is a projective limit. -/
theorem isProjectiveLimit_kolmogorovExtension (pf : ProjectiveFamily ι α) :
    IsProjectiveLimit pf.kolmogorovExtension pf.measure := by
  intro I
  ext s hs
  rw [Measure.map_apply (Finset.measurable_restrict I) hs, ← cylinder, kolmogorovExtension,
    AddContent.measure_eq _ _ generateFrom_measurableCylinders.symm _
      (cylinder_mem_measurableCylinders _ _ hs),
    projectiveFamilyContent_cylinder pf.consistent hs]

instance instIsProbabilityMeasureKolmogorovExtension (pf : ProjectiveFamily ι α) :
    IsProbabilityMeasure pf.kolmogorovExtension :=
  pf.isProjectiveLimit_kolmogorovExtension.isProbabilityMeasure

theorem kolmogorovExtension_unique (pf : ProjectiveFamily ι α) (μ : Measure (∀ i, α i))
    (hμ : IsProjectiveLimit μ pf.measure) :
    μ = pf.kolmogorovExtension :=
  hμ.unique pf.isProjectiveLimit_kolmogorovExtension

@[simp]
theorem kolmogorovExtension_apply_cylinder (pf : ProjectiveFamily ι α) (I : Finset ι)
    {S : Set (∀ i : I, α i)} (hS : MeasurableSet S) :
    pf.kolmogorovExtension (cylinder I S) = pf.measure I S :=
  pf.isProjectiveLimit_kolmogorovExtension.measure_cylinder I hS

end ProjectiveFamily

end ProbabilityTheory
