/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lemma B.2: the limit of `∫ exp (-x A n) dγ(x)`

For a finite measure `γ` on `[0, ∞)` and a sequence `A n` tending to `∞`,
`∫ exp (-x A n) dγ(x) → γ({0})`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Wang2026Almost

/-- **Lemma B.2** (Wang, Agrawal, Ramdas 2026): for a finite measure `γ` on `[0, ∞)` and a
sequence `A n` tending to `∞`, `∫ exp (-x A n) dγ(x) → γ({0})`. The paper assumes `A` positive and
increasing; the proof (dominated convergence) does not use it. -/
lemma tendsto_integral_exp_neg_mul (γ : Measure ℝ) [IsFiniteMeasure γ] (hγ : γ (Set.Iio 0) = 0)
    {A : ℕ → ℝ} (hA : Tendsto A atTop atTop) :
    Tendsto (fun n ↦ ∫ x, Real.exp (-x * A n) ∂γ) atTop (𝓝 (γ.real {0})) := by
  sorry

end Wang2026Almost
