/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Leverage

/-!
# Fact 2: the mixture of two predictable plug-in strategies (short allowed)

If two plug-in strategies `lam`, `nu` (given as functions of the observation path, depending only
on the past) satisfy `W^lam n > ρ W^nu n` on all binary paths, then the portfolio
`(1 - κ) W^lam + κ W^nu` is a valid predictable plug-in strategy on binary paths for every
`κ ∈ [-ρ / (1 - ρ), 1]`: one may long `lam` and short `nu`. In particular, for `nu = 0` (cash),
one may borrow `b ∈ (0, ρ / (1 - ρ)]` units of cash and bet the leveraged fractions
`portfolioFraction m (-b) lam 0` with wealth `(1 + b) W^lam - b`.

The strategies are written as functions of the path `x : ℕ → ℝ` of observations, on which the
coordinate process `coord k x = x k` is the observation process.
-/

@[expose] public section

open Learning.Betting

namespace Wang2026Almost

/-- The coordinate process on the path space `ℕ → ℝ`. -/
def coord : ℕ → (ℕ → ℝ) → ℝ := fun k x ↦ x k

/-- A binary path of observations, with values in `{0, 1}`. -/
def IsBinaryPath (x : ℕ → ℝ) : Prop := ∀ k, x k = 0 ∨ x k = 1

/-- A strategy `lam` on the path space is predictable if `lam n x` depends only on
`x 0, …, x (n - 1)`. -/
def IsPathPredictable (lam : ℕ → (ℕ → ℝ) → ℝ) : Prop :=
  ∀ n x y, (∀ k < n, x k = y k) → lam n x = lam n y

/-- **Fact 2** (Wang, Agrawal, Ramdas 2026): let `lam`, `nu` be two predictable strategies on the
path space with values in `[-1 / (1 - m), 1 / m]` such that `W^lam n > ρ W^nu n` for all `n` on
all binary paths, with `ρ ∈ [0, 1)`. Then for every `κ ∈ [-ρ / (1 - ρ), 1]`, on all binary paths,
the bet fractions `portfolioFraction m κ lam nu coord` are in `[-1 / (1 - m), 1 / m]` and their
wealth is the portfolio `(1 - κ) W^lam + κ W^nu`. -/
lemma wealth_portfolioFraction_short {m ρ κ : ℝ} (hm : m ∈ Set.Ioo 0 1) (hρ : ρ ∈ Set.Ico 0 1)
    (hκ : κ ∈ Set.Icc (-ρ / (1 - ρ)) 1) {lam nu : ℕ → (ℕ → ℝ) → ℝ}
    (hlam_pred : IsPathPredictable lam) (hnu_pred : IsPathPredictable nu)
    (hlam : ∀ n x, lam n x ∈ fractionRange m) (hnu : ∀ n x, nu n x ∈ fractionRange m)
    (hbin : ∀ x, IsBinaryPath x → ∀ n, ρ * wealth m nu coord n x < wealth m lam coord n x) :
    ∀ x, IsBinaryPath x → ∀ n, portfolioFraction m κ lam nu coord n x ∈ fractionRange m ∧
      wealth m (portfolioFraction m κ lam nu coord) coord n x =
        (1 - κ) * wealth m lam coord n x + κ * wealth m nu coord n x := by
  sorry

end Wang2026Almost
