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
