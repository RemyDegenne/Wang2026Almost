/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Leverage

/-!
# Definition B.4: opportunistic leveraging

The `ρ`-opportunistic leverage `oppLeverage m ρ lam X` of a strategy `lam` (defined in
`Leverage.lean`) bets the leveraged fraction `leverageFraction m ρ lam X n` at the rounds where
the next wealth is guaranteed to stay above `ρ`, and `lam n` otherwise. The claims made in the
definition: its bet fractions are valid whenever those of `lam` are, and on
`⋂_{k < n} {nextWealthMin m lam X k > ρ}` its wealth after `n` rounds is `(W n - ρ) / (1 - ρ)`.
-/

@[expose] public section

open Learning.Betting

namespace Wang2026Almost

variable {Ω : Type*}

/-- **Definition B.4, validity** (Wang, Agrawal, Ramdas 2026): the bet fractions of the
`ρ`-opportunistic leverage of `lam` are in `[-1 / (1 - m), 1 / m]` whenever those of `lam` are. -/
lemma oppLeverage_mem_fractionRange {m ρ : ℝ} (hm : m ∈ Set.Ioo 0 1) {lam X : ℕ → Ω → ℝ}
    {n : ℕ} {ω : Ω} (hlam : lam n ω ∈ fractionRange m) :
    oppLeverage m ρ lam X n ω ∈ fractionRange m := by
  sorry

/-- **Definition B.4, wealth** (Wang, Agrawal, Ramdas 2026): on the event
`⋂_{k < n} {nextWealthMin m lam X k > ρ}`, the wealth of the `ρ`-opportunistic leverage of `lam`
after `n` rounds is `(W n - ρ) / (1 - ρ)` (for `m ∈ [0, 1]`, implicit in the paper: then the
event forces `W k > ρ`). -/
lemma wealth_oppLeverage {m ρ : ℝ} (hm : m ∈ Set.Icc 0 1) (hρ : ρ ≠ 1) {lam X : ℕ → Ω → ℝ} {n : ℕ}
    {ω : Ω}
    (h : ∀ k < n, ρ < nextWealthMin m lam X k ω) :
    wealth m (oppLeverage m ρ lam X) X n ω = (wealth m lam X n ω - ρ) / (1 - ρ) := by
  sorry

end Wang2026Almost
