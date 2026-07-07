/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed

/-!
# Partitioning a σ-finite measure into finite pieces with normalized laws

The Poisson random measure attached to a σ-finite intensity `m` on a measurable space `E` is built
by cutting `E` into countably many disjoint measurable pieces of finite `m`-mass and running an
independent Poisson family on each. This file provides that partition and, on each piece, the
*normalized piece law* — the probability measure obtained by rescaling `m` restricted to the piece.

The partition is the classical `disjointed (spanningSets m)`: mathlib's generic σ-finite exhaustion,
disjointified so the pieces are pairwise disjoint while still covering `E`. Each piece has finite
`m`-mass, so it can be normalized to a probability measure. On a piece of zero mass the normalization
is degenerate, so we substitute a Dirac point mass at an arbitrary junk point; such a piece
contributes nothing downstream (its Poisson count is `Poisson 0 = δ₀`).

## Main definitions

* `ProbabilityTheory.prmPiece` — the `k`-th disjoint finite-mass piece of a σ-finite measure.
* `ProbabilityTheory.prmPieceLaw` — the normalized probability law of `m` on the `k`-th piece.

## Main results

* `ProbabilityTheory.pairwise_disjoint_prmPiece`, `ProbabilityTheory.iUnion_prmPiece`,
  `ProbabilityTheory.measure_prmPiece_lt_top` — the pieces form a disjoint measurable partition of
  `E` into sets of finite `m`-mass.
* `ProbabilityTheory.isProbabilityMeasure_prmPieceLaw` — each piece law is a probability measure.
* `ProbabilityTheory.lintegral_prmPieceLaw`, `ProbabilityTheory.integral_smul_prmPieceLaw` — the
  scaling bridges turning integrals against the piece law into (rescaled) integrals against `m`
  restricted to the piece, for the lower Lebesgue and the Bochner integral respectively.

This file opens the `LeanLevy/RandomMeasure/` directory; the Poisson point family, the random measure
itself, and the compensated `L²` integral are built on top of this partition.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-! ### The partition -/

/-- The `k`-th piece of the canonical partition of a σ-finite measure `m`: the disjointification of
mathlib's σ-finite exhaustion `spanningSets m`. The pieces are pairwise disjoint, measurable, cover
`E`, and each has finite `m`-mass. -/
noncomputable def prmPiece (m : Measure E) [SigmaFinite m] (k : ℕ) : Set E :=
  disjointed (spanningSets m) k

/-- The normalized law of `m` on the `k`-th partition piece: `m` restricted to the piece and rescaled
to total mass one. When the piece has zero `m`-mass the rescaling is degenerate, so we fall back to a
Dirac mass at an arbitrary junk point; either way the result is a probability measure. -/
noncomputable def prmPieceLaw (m : Measure E) [SigmaFinite m] [Nonempty E] (k : ℕ) : Measure E :=
  if m (prmPiece m k) = 0 then Measure.dirac (Classical.arbitrary E)
  else (m (prmPiece m k))⁻¹ • m.restrict (prmPiece m k)

variable {m : Measure E} [SigmaFinite m] {k : ℕ}

/-- Each partition piece is measurable. -/
theorem measurableSet_prmPiece : MeasurableSet (prmPiece m k) :=
  MeasurableSet.disjointed (measurableSet_spanningSets m) k

/-- The partition pieces are pairwise disjoint. -/
theorem pairwise_disjoint_prmPiece : Pairwise (Function.onFun Disjoint (prmPiece m)) :=
  disjoint_disjointed (spanningSets m)

/-- The partition pieces cover `E`. -/
theorem iUnion_prmPiece : ⋃ k, prmPiece m k = Set.univ := by
  simp only [prmPiece]
  rw [iUnion_disjointed]
  exact iUnion_spanningSets m

/-- Each partition piece has finite `m`-mass, since it is contained in a spanning set. -/
theorem measure_prmPiece_lt_top : m (prmPiece m k) < ⊤ :=
  lt_of_le_of_lt (measure_mono (disjointed_subset (spanningSets m) k))
    (measure_spanningSets_lt_top m k)

/-! ### The normalized piece law -/

/-- On a piece of positive `m`-mass, `prmPieceLaw` is the explicit rescaled restriction. -/
private theorem prmPieceLaw_of_ne_zero [Nonempty E] (hk : m (prmPiece m k) ≠ 0) :
    prmPieceLaw m k = (m (prmPiece m k))⁻¹ • m.restrict (prmPiece m k) := by
  unfold prmPieceLaw
  rw [if_neg hk]

/-- Each normalized piece law is a probability measure: on a zero-mass piece it is a Dirac mass, and
on a positive-mass piece the rescaling factor `(m (prmPiece m k))⁻¹` cancels the finite total mass. -/
instance isProbabilityMeasure_prmPieceLaw [Nonempty E] :
    IsProbabilityMeasure (prmPieceLaw m k) := by
  unfold prmPieceLaw
  split_ifs with h
  · infer_instance
  · refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel h (measure_prmPiece_lt_top).ne

/-- Lower Lebesgue scaling bridge: on a positive-mass piece, integrating against the normalized piece
law equals the rescaled set integral against `m`. -/
theorem lintegral_prmPieceLaw [Nonempty E] (hk : m (prmPiece m k) ≠ 0) (g : E → ℝ≥0∞) :
    ∫⁻ x, g x ∂(prmPieceLaw m k)
      = (m (prmPiece m k))⁻¹ * ∫⁻ x in prmPiece m k, g x ∂m := by
  rw [prmPieceLaw_of_ne_zero hk, lintegral_smul_measure, smul_eq_mul]

/-- Bochner scaling bridge: on a positive-mass piece, the `m`-mass of the piece times the Bochner
integral against the normalized piece law recovers the set integral against `m`. This is the form
Tasks 3–4 consume, with `f` integrable on the piece. -/
theorem integral_smul_prmPieceLaw [Nonempty E] (hk : m (prmPiece m k) ≠ 0) (f : E → ℝ) :
    (m (prmPiece m k)).toReal • ∫ x, f x ∂(prmPieceLaw m k)
      = ∫ x in prmPiece m k, f x ∂m := by
  have ht : (m (prmPiece m k)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hk, (measure_prmPiece_lt_top).ne⟩
  rw [prmPieceLaw_of_ne_zero hk, integral_smul_measure, smul_smul, ENNReal.toReal_inv,
    mul_inv_cancel₀ ht, one_smul]

end ProbabilityTheory
