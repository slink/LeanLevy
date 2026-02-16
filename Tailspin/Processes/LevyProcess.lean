/-
Copyright (c) 2026 Tailspin Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tailspin Contributors
-/
import Tailspin.Processes.StochasticProcess
import Tailspin.Processes.Cadlag
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# Lévy Processes

This file defines the `IsLevyProcess` predicate for a stochastic process indexed by `ℝ≥0` with
values in a measurable additive group `E`. A Lévy process is characterised by:

1. Starting at zero: `X 0 = 0` a.s.
2. Independent increments.
3. Stationary increments.
4. Càdlàg sample paths a.e.

We also define the **characteristic exponent** `Ψ` via `charFun (μ.map (X 1))` and state the
Lévy–Khintchine factorisation `charFun (μ.map (X t)) ξ = exp(t · Ψ(ξ))` (sorry'd).

## Main definitions

* `ProbabilityTheory.IsLevyProcess` — the predicate bundling the four axioms.
* `ProbabilityTheory.IsLevyProcess.charExponent` — the characteristic exponent `Ψ`.

## Main results

* `ProbabilityTheory.IsLevyProcess.indepFun_increment` — two non-overlapping increments are
  pairwise independent.
* `ProbabilityTheory.IsLevyProcess.identDistrib_increment` — the law of an increment depends
  only on the lag.
* `ProbabilityTheory.IsLevyProcess.charFun_eq_exp_mul` — Lévy–Khintchine factorisation (sorry'd).
-/

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {E : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace E] [TopologicalSpace E] [AddGroup E] [Sub E]

/-- A stochastic process `X : ℝ≥0 → Ω → E` is a **Lévy process** with respect to a measure `μ`
if it starts at zero, has independent and stationary increments, and has càdlàg sample paths
almost everywhere. -/
structure IsLevyProcess (X : ℝ≥0 → Ω → E) (μ : Measure Ω) : Prop where
  /-- The process starts at the origin. -/
  start_zero : X 0 = fun _ => 0
  /-- Increments along any monotone partition are mutually independent. -/
  indep_increments : HasIndependentIncrements X μ
  /-- The law of an increment depends only on the lag, not the starting time. -/
  stationary_increments : HasStationaryIncrements X μ
  /-- Almost every sample path is càdlàg. -/
  cadlag_ae : ∀ᵐ ω ∂μ, IsCadlag (fun t => X t ω)

/-! ### API lemmas -/

namespace IsLevyProcess

/-- Two non-overlapping increments of a Lévy process are pairwise independent. -/
theorem indepFun_increment {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (h : IsLevyProcess X μ) {s t u : ℝ≥0} (hst : s ≤ t) (htu : t ≤ u) :
    IndepFun (increment X s t) (increment X t u) μ :=
  h.indep_increments.indepFun_increment hst htu

/-- The law of an increment of a Lévy process depends only on the lag. -/
theorem identDistrib_increment {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (h : IsLevyProcess X μ) (s k : ℝ≥0) :
    IdentDistrib (increment X s (s + k)) (increment X 0 k) μ μ :=
  h.stationary_increments s k

/-! ### Characteristic exponent -/

/-- The **characteristic exponent** of a Lévy process, defined as the complex logarithm of the
characteristic function of the time-1 marginal: `Ψ(ξ) = log(𝔼[exp(i⟨X₁, ξ⟩)])`. -/
noncomputable def charExponent
    [Inner ℝ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (_ : IsLevyProcess X μ) : E → ℂ :=
  fun ξ => Complex.log (charFun (μ.map (X 1)) ξ)

/-- **Lévy–Khintchine factorisation**: the characteristic function of the time-`t` marginal
of a Lévy process equals `exp(t · Ψ(ξ))` where `Ψ` is the characteristic exponent. -/
theorem charFun_eq_exp_mul
    [Inner ℝ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω}
    (h : IsLevyProcess X μ) (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ = Complex.exp (↑(t : ℝ) * h.charExponent ξ) := by
  sorry -- Requires infinite divisibility argument

end IsLevyProcess

end ProbabilityTheory
