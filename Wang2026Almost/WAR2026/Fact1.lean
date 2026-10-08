/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Leverage

/-!
# Fact 1: the mixture of two predictable plug-in strategies (long only)

The portfolio `(1 - κ) W^lam + κ W^nu` of two predictable plug-in strategies, `κ ∈ [0, 1]`, is the
wealth of the predictable plug-in strategy with bet fractions `portfolioFraction m κ lam nu X`,
which lie in `[-1 / (1 - m), 1 / m]` (as convex combinations of `lam n` and `nu n`).
-/

@[expose] public section

open Learning.Betting

namespace Wang2026Almost

variable {Ω : Type*}

/-- **Fact 1** (Wang, Agrawal, Ramdas 2026): for two bet fraction processes `lam`, `nu` with
values in `[-1 / (1 - m), 1 / m]`, observations in `[0, 1]` and `κ ∈ [0, 1]`, the bet fractions
`portfolioFraction m κ lam nu X` are in `[-1 / (1 - m), 1 / m]` and their wealth is the portfolio
`(1 - κ) W^lam + κ W^nu`. -/
lemma wealth_portfolioFraction {m κ : ℝ} (hm : m ∈ Set.Ioo 0 1) (hκ : κ ∈ Set.Icc 0 1)
    {lam nu X : ℕ → Ω → ℝ} (hlam : ∀ n ω, lam n ω ∈ fractionRange m)
    (hnu : ∀ n ω, nu n ω ∈ fractionRange m) (hX : ∀ n ω, X n ω ∈ Set.Icc 0 1) :
    (∀ n ω, portfolioFraction m κ lam nu X n ω ∈ fractionRange m) ∧
      ∀ n ω, wealth m (portfolioFraction m κ lam nu X) X n ω =
        (1 - κ) * wealth m lam X n ω + κ * wealth m nu X n ω := by
  sorry

end Wang2026Almost
