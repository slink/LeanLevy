/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.PiSystem

/-!
# Grouping mutually independent families along disjoint index sets

Mathlib's `indepSets_piiUnionInter_of_disjoint` and `iIndepFun.indepFun_finset` express that
grouping an independent family into **two** blocks indexed by disjoint index sets preserves
independence. This file generalizes the underlying mechanism from binary to finite mutual grouping:
starting from a mutually independent family indexed by `κ` and a family of pairwise-disjoint index
sets `S : ι → Set κ`, the blocks obtained by gathering the members over each `S i` are again
mutually independent.

## Main results

* `iIndepSets.piiUnionInter_of_pairwiseDisjoint`: mutual independence of π-systems is preserved by
  grouping into the finite-intersection systems `piiUnionInter π (S i)`.
* `iIndep.biSup_of_pairwiseDisjoint`: mutual independence of σ-algebras is preserved by taking the
  suprema `⨆ k ∈ S i, m k`.
* `iIndepFun.setRestrict_of_pairwiseDisjoint`: the blocks of a mutually independent family of random
  variables, restricted to each `S i`, are mutually independent.

Each statement upgrades the corresponding mathlib binary grouping lemma to an arbitrary finite family
of blocks indexed by pairwise-disjoint index sets.
-/

open MeasureTheory MeasurableSpace Set

namespace ProbabilityTheory

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Mutual independence of π-systems is preserved by grouping along pairwise-disjoint
index sets: the finite-intersection systems `piiUnionInter π (S i)` are mutually independent. -/
theorem iIndepSets.piiUnionInter_of_pairwiseDisjoint {π : κ → Set (Set Ω)} {S : ι → Set κ}
    (h_indep : iIndepSets π μ) (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepSets (fun i => piiUnionInter π (S i)) μ := by
  classical
  rw [iIndepSets_iff] at h_indep ⊢
  intro u f hf
  -- For each block index `i ∈ u`, extract the finite intersection witnessing membership of `f i`.
  have h_ex : ∀ i, ∃ (t : Finset κ) (g : κ → Set Ω),
      i ∈ u → (↑t ⊆ S i ∧ (∀ j ∈ t, g j ∈ π j) ∧ f i = ⋂ j ∈ t, g j) := by
    intro i
    by_cases hi : i ∈ u
    · obtain ⟨t, htS, g, hg, hfeq⟩ := hf i hi
      exact ⟨t, g, fun _ => ⟨htS, hg, hfeq⟩⟩
    · exact ⟨∅, fun _ => Set.univ, fun h => absurd h hi⟩
  choose p g hpg using h_ex
  -- The extracted index finsets are pairwise disjoint, since `↑(p i) ⊆ S i`.
  have hpd : (u : Set ι).PairwiseDisjoint p := by
    intro i₁ hi₁ i₂ hi₂ hne
    exact Finset.disjoint_coe.mp
      (Set.disjoint_of_subset (hpg i₁ hi₁).1 (hpg i₂ hi₂).1 (hS hne))
  -- Within `u` the finsets `p i` are disjoint, so each `j` lies in at most one of them.
  have huniq : ∀ i₁ ∈ u, ∀ i₂ ∈ u, ∀ j, j ∈ p i₁ → j ∈ p i₂ → i₁ = i₂ := by
    intro i₁ hi₁ i₂ hi₂ j hj₁ hj₂
    by_contra hne
    exact Finset.disjoint_left.mp (hpd hi₁ hi₂ hne) hj₁ hj₂
  -- The glued family: `G j` selects `g i j` for the unique block `i` containing `j`.
  set G : κ → Set Ω := fun j => ⋂ i ∈ u, (if j ∈ p i then g i j else Set.univ) with hGdef
  have hGeq : ∀ i ∈ u, ∀ j ∈ p i, G j = g i j := by
    intro i hi j hj
    apply Set.ext
    intro x
    simp only [hGdef, Set.mem_iInter]
    constructor
    · intro h
      have := h i hi
      rwa [if_pos hj] at this
    · intro hx i' hi'
      by_cases hji' : j ∈ p i'
      · rw [if_pos hji', huniq i' hi' i hi j hji' hj]
        exact hx
      · rw [if_neg hji']
        trivial
  -- The full intersection over `u` equals the intersection of the glued family over the union.
  have hA : (⋂ i ∈ u, f i) = ⋂ j ∈ u.biUnion p, G j := by
    ext x
    simp only [Set.mem_iInter, Finset.mem_biUnion, hGdef]
    constructor
    · intro h j hj i' hi'
      by_cases hji' : j ∈ p i'
      · rw [if_pos hji']
        have hxf : x ∈ f i' := h i' hi'
        rw [(hpg i' hi').2.2] at hxf
        exact Set.mem_iInter₂.mp hxf j hji'
      · rw [if_neg hji']
        trivial
    · intro h i hi
      rw [(hpg i hi).2.2]
      refine Set.mem_iInter₂.mpr fun j hji => ?_
      have := h j ⟨i, hi, hji⟩ i hi
      rwa [if_pos hji] at this
  -- The glued sets belong to the π-systems, so `h_indep` applies over the union.
  have hGmem : ∀ j ∈ u.biUnion p, G j ∈ π j := by
    intro j hj
    rw [Finset.mem_biUnion] at hj
    obtain ⟨i, hi, hji⟩ := hj
    rw [hGeq i hi j hji]
    exact (hpg i hi).2.1 j hji
  calc μ (⋂ i ∈ u, f i)
      = μ (⋂ j ∈ u.biUnion p, G j) := by rw [hA]
    _ = ∏ j ∈ u.biUnion p, μ (G j) := h_indep _ hGmem
    _ = ∏ i ∈ u, ∏ j ∈ p i, μ (G j) := Finset.prod_biUnion hpd
    _ = ∏ i ∈ u, ∏ j ∈ p i, μ (g i j) := by
        refine Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun j hj => ?_
        rw [hGeq i hi j hj]
    _ = ∏ i ∈ u, μ (f i) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [(hpg i hi).2.2]
        exact (h_indep (p i) (hpg i hi).2.1).symm

/-- Mutual independence of σ-algebras is preserved by taking suprema over
pairwise-disjoint index sets. -/
theorem iIndep.biSup_of_pairwiseDisjoint {m : κ → MeasurableSpace Ω}
    (h_le : ∀ k, m k ≤ mΩ) (h_indep : iIndep m μ) {S : ι → Set κ}
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndep (fun i => ⨆ k ∈ S i, m k) μ := by
  refine iIndepSets.iIndep (fun i => iSup₂_le fun k _ => h_le k)
    (fun i => piiUnionInter (fun k => {s | MeasurableSet[m k] s}) (S i)) ?_ ?_ ?_
  · exact fun i => isPiSystem_piiUnionInter _
      (fun k => @MeasurableSpace.isPiSystem_measurableSet Ω (m k)) (S i)
  · exact fun i => (generateFrom_piiUnionInter_measurableSet m (S i)).symm
  · exact h_indep.iIndepSets'.piiUnionInter_of_pairwiseDisjoint hS

/-- Blocks of a mutually independent family of random variables, grouped along
pairwise-disjoint index sets, are mutually independent. -/
theorem iIndepFun.setRestrict_of_pairwiseDisjoint {β : κ → Type*}
    {mβ : ∀ k, MeasurableSpace (β k)} {f : ∀ k, Ω → β k} (hf : ∀ k, Measurable (f k))
    (h_indep : iIndepFun f μ) {S : ι → Set κ}
    (hS : Pairwise (Function.onFun Disjoint S)) :
    iIndepFun (fun i ω => (S i).restrict fun k => f k ω) μ := by
  -- The σ-algebra generated by the block map over `S i` is the supremum of the individual comaps.
  have hcomap : ∀ i, MeasurableSpace.comap (fun ω => (S i).restrict fun k => f k ω)
      MeasurableSpace.pi = ⨆ k ∈ S i, MeasurableSpace.comap (f k) (mβ k) := by
    intro i
    simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, Set.restrict_apply]
    exact iSup_subtype'' (S i) fun k => MeasurableSpace.comap (f k) (mβ k)
  -- `iIndepFun` is `iIndep` of the comaps of the block maps; rewrite through the identity above.
  show iIndep (fun i => MeasurableSpace.comap (fun ω => (S i).restrict fun k => f k ω)
      MeasurableSpace.pi) μ
  simp_rw [hcomap]
  exact iIndep.biSup_of_pairwiseDisjoint (fun k => (hf k).comap_le) h_indep hS

end ProbabilityTheory
