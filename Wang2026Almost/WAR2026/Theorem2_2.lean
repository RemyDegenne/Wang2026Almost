/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.Mathlib.Probability.AsymptoticsInProbability
public import Wang2026Almost.Mathlib.Probability.SumBigOmegaInProb
public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# Theorem 2.2: almost sure divergence of `∑ Ω_p(n⁻¹)`

A series of nonnegative random variables `Z n = Ω_p(n⁻¹)` diverges almost surely. This is the
special case `a n = n⁻¹` of `ProbabilityTheory.ae_not_summable_of_isBigOmegaInProb`, which holds for
any nonnegative weights `a` with `∑ a n = ∞`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']

/-- **Theorem 2.2** (Wang, Agrawal, Ramdas 2026): if `Z n` are (almost surely) nonnegative random
variables with `Z n = Ω_p(n⁻¹)`, then `∑ Z n = ∞` almost surely. -/
theorem ae_not_summable_of_isBigOmegaInProb {Z : ℕ → Ω → ℝ} (hZ : ∀ n, AEMeasurable (Z n) P')
    (hnn : ∀ n, 0 ≤ᵐ[P'] Z n) (hΩ : IsBigOmegaInProb P' Z (fun n ↦ (n : ℝ)⁻¹)) :
    ∀ᵐ ω ∂P', ¬ Summable (fun n ↦ Z n ω) :=
  ProbabilityTheory.ae_not_summable_of_isBigOmegaInProb hZ hnn (fun n ↦ by positivity)
    Real.not_summable_natCast_inv hΩ

end Wang2026Almost
