/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Poisson

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
* `ProbabilityTheory.pointFamilyIndexType`, `ProbabilityTheory.pointFamilyCombined` — the combined
  index type `ℕ ⊕ ℕ × ℕ ↦ Type` and the single family gathering the piece counts and all points into
  one function, the data whose joint independence the whole random measure rests on.
* `ProbabilityTheory.IsPoissonPointFamily` — the driver predicate for the counts-and-points data.

## Main results

* `ProbabilityTheory.pairwise_disjoint_prmPiece`, `ProbabilityTheory.iUnion_prmPiece`,
  `ProbabilityTheory.measure_prmPiece_lt_top` — the pieces form a disjoint measurable partition of
  `E` into sets of finite `m`-mass.
* `ProbabilityTheory.isProbabilityMeasure_prmPieceLaw` — each piece law is a probability measure.
* `ProbabilityTheory.lintegral_prmPieceLaw`, `ProbabilityTheory.integral_smul_prmPieceLaw` — the
  scaling bridges turning integrals against the piece law into (rescaled) integrals against `m`
  restricted to the piece, for the lower Lebesgue and the Bochner integral respectively.
* `ProbabilityTheory.exists_isPoissonPointFamily` — the existence of the Poisson point family on a
  canonical probability space, built in one `exists_hasLaw_indepFun` call over the combined index so
  that mutual independence of every count and every point is free by construction.
* `ProbabilityTheory.IsPoissonPointFamily.iIndepFun_count`,
  `ProbabilityTheory.IsPoissonPointFamily.iIndepFun_point_piece` — the disjoint-block extractors that
  read independence of a sub-family off the one combined `indep` field.

This file opens the `LeanLevy/RandomMeasure/` directory; the Poisson point family, the random measure
itself, and the compensated `L²` integral are built on top of this partition.

Because the combined family mixes `ℕ`-valued counts with `E`-valued points, `exists_hasLaw_indepFun`
forces all coordinate codomains into a single universe; `E` is therefore taken in `Type` here (which
covers the intended intensities on `ℝ` and `ℝ ^ d`).
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

/-! ### The Poisson point family

The Poisson random measure is generated by, for each partition piece `k`, a Poisson-distributed count
`K k` and an i.i.d. sequence of points `X k n` drawn from the normalized piece law — with all counts
and all points jointly independent. mathlib has no block-grouping lemma delivering joint independence
of a countable family of blocks after the fact, so the entire data is built in a single
`exists_hasLaw_indepFun` call over the combined index `ℕ ⊕ ℕ × ℕ` (counts on `Sum.inl`, points on
`Sum.inr`); mutual independence is then free by construction and every disjoint-block independence
statement downstream is a `precomp` away.

Since that one call mixes `ℕ`-valued and `E`-valued coordinates, it forces every codomain into a
single universe, so this section works with `E : Type`. -/

/-- The codomain type family of the combined Poisson point family over the index `ℕ ⊕ ℕ × ℕ`: the
count coordinates on `Sum.inl` are `ℕ`-valued and the point coordinates on `Sum.inr` are `E`-valued.
`Sum.elim` into `Type` packages the two heterogeneous codomains into one dependent family. -/
def pointFamilyIndexType (E : Type) : ℕ ⊕ ℕ × ℕ → Type :=
  Sum.elim (fun _ => ℕ) (fun _ => E)

/-- Each coordinate of the combined index carries the obvious measurable space: `ℕ`'s on a count
coordinate, `E`'s on a point coordinate. -/
instance instMeasurableSpacePointFamilyIndexType (E : Type) [MeasurableSpace E]
    (i : ℕ ⊕ ℕ × ℕ) : MeasurableSpace (pointFamilyIndexType E i) := by
  rcases i with k | p
  · exact (inferInstance : MeasurableSpace ℕ)
  · exact (inferInstance : MeasurableSpace E)

/-- The single combined family gathering the piece counts `K k` (on `Sum.inl k`) and every point
`X k n` (on `Sum.inr (k, n)`) into one function `∀ i, Ω → pointFamilyIndexType E i`. Independence of
any sub-family — the counts, or the points of a fixed piece — is recovered from the joint
independence of this one function by precomposing the index with the relevant injection. -/
def pointFamilyCombined {Ω E : Type} (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) :
    ∀ i, Ω → pointFamilyIndexType E i
  | Sum.inl k => K k
  | Sum.inr p => X p.1 p.2

section PointFamily

variable {Ω E : Type} [MeasurableSpace E]

/-- The coordinate law family of the combined Poisson point family: `Poisson (m (prmPiece m k))` on a
count coordinate `Sum.inl k`, the normalized piece law `prmPieceLaw m k` on a point coordinate
`Sum.inr (k, n)`. Each is a probability measure. -/
noncomputable def pointFamilyLaw (m : Measure E) [SigmaFinite m] [Nonempty E] :
    ∀ i, Measure (pointFamilyIndexType E i)
  | Sum.inl k => ((poissonMeasure (m (prmPiece m k)).toNNReal : Measure ℕ) :
      Measure (pointFamilyIndexType E (Sum.inl k)))
  | Sum.inr p => ((prmPieceLaw m p.1 : Measure E) :
      Measure (pointFamilyIndexType E (Sum.inr p)))

/-- Every coordinate law of the combined family is a probability measure, so the family is admissible
for `exists_hasLaw_indepFun`. -/
instance instIsProbabilityMeasurePointFamilyLaw (m : Measure E) [SigmaFinite m] [Nonempty E]
    (i : ℕ ⊕ ℕ × ℕ) : IsProbabilityMeasure (pointFamilyLaw m i) := by
  rcases i with k | p
  · exact (inferInstance : IsProbabilityMeasure (poissonMeasure _))
  · exact (inferInstance : IsProbabilityMeasure (prmPieceLaw m p.1))

variable [MeasurableSpace Ω]

/-- **The Poisson point family** of a σ-finite intensity `m`: for each partition piece `k` a count
`K k` distributed as `Poisson (m (prmPiece m k))`, and for each `k` a sequence of points `X k n` each
distributed as the normalized piece law `prmPieceLaw m k`, with all counts and all points jointly
independent. The single `indep` field over the combined index makes every disjoint-block
independence statement derivable by `precomp`. -/
structure IsPoissonPointFamily (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) [SigmaFinite m] [Nonempty E] (μ : Measure Ω) : Prop where
  /-- Each count `K k` is measurable. -/
  measurable_count : ∀ k, Measurable (K k)
  /-- Each point `X k n` is measurable. -/
  measurable_point : ∀ k n, Measurable (X k n)
  /-- All counts and all points are jointly independent, phrased as one `iIndepFun` over the combined
  family `pointFamilyCombined K X` indexed by `ℕ ⊕ ℕ × ℕ`. -/
  indep : iIndepFun (pointFamilyCombined K X) μ
  /-- The count `K k` is Poisson-distributed with mean the `m`-mass of the `k`-th piece. -/
  law_count : ∀ k, HasLaw (K k) (poissonMeasure (m (prmPiece m k)).toNNReal) μ
  /-- Each point `X k n` is distributed as the normalized `k`-th piece law. -/
  law_point : ∀ k n, HasLaw (X k n) (prmPieceLaw m k) μ

/-- **Existence of the Poisson point family.** For any σ-finite intensity `m` on `E` there is a
canonical probability space carrying the piece counts `K` and the points `X` of an
`IsPoissonPointFamily`. The space is the countable product from `exists_hasLaw_indepFun` over the
combined index `ℕ ⊕ ℕ × ℕ`, so mutual independence of every count and every point holds by
construction rather than being reassembled from per-piece families. -/
theorem exists_isPoissonPointFamily (m : Measure E) [SigmaFinite m] [Nonempty E] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E),
      IsProbabilityMeasure μ ∧ IsPoissonPointFamily K X m μ := by
  obtain ⟨Ω, mΩ, μ, Z, hmeas, hlaw, hindep, hμ⟩ :=
    exists_hasLaw_indepFun (pointFamilyIndexType E) (pointFamilyLaw m)
  refine ⟨Ω, mΩ, μ, fun k => Z (Sum.inl k), fun k n => Z (Sum.inr (k, n)), hμ, ?_⟩
  have hcomb :
      pointFamilyCombined (fun k => Z (Sum.inl k)) (fun k n => Z (Sum.inr (k, n))) = Z := by
    funext i ω; rcases i with k | p
    · rfl
    · rfl
  exact
    { measurable_count := fun k => hmeas (Sum.inl k)
      measurable_point := fun k n => hmeas (Sum.inr (k, n))
      indep := by rw [hcomb]; exact hindep
      law_count := fun k => hlaw (Sum.inl k)
      law_point := fun k n => hlaw (Sum.inr (k, n)) }

end PointFamily

section Extractors

variable {Ω E : Type} [MeasurableSpace E] [MeasurableSpace Ω] {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
  {m : Measure E} [SigmaFinite m] [Nonempty E] {μ : Measure Ω}

/-- The piece counts of a Poisson point family are jointly independent, read off the combined `indep`
field by precomposing the index with `Sum.inl`. -/
theorem IsPoissonPointFamily.iIndepFun_count (hd : IsPoissonPointFamily K X m μ) :
    iIndepFun K μ := by
  have h := hd.indep.precomp (g := Sum.inl) Sum.inl_injective
  exact h

/-- For a fixed piece `k`, the points `X k ·` of a Poisson point family are jointly independent, read
off the combined `indep` field by precomposing the index with `n ↦ Sum.inr (k, n)`. -/
theorem IsPoissonPointFamily.iIndepFun_point_piece (hd : IsPoissonPointFamily K X m μ) (k : ℕ) :
    iIndepFun (fun n => X k n) μ := by
  have h := hd.indep.precomp (g := fun n => Sum.inr (k, n)) (fun a b hab => by simpa using hab)
  exact h

end Extractors

end ProbabilityTheory
