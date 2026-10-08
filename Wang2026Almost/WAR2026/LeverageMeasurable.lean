/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Leverage
public import Wang2026Almost.LeanMachineLearning.Betting.WealthLemmas

/-!
# Predictability of the opportunistic leverage

If the strategy `lam` is adapted to a filtration `ℱ` and each observation `X n` is
`ℱ (n + 1)`-measurable, then the minimal next wealth `nextWealthMin m lam X`, the leveraged bet
fraction `leverageFraction m ρ lam X` and the `ρ`-opportunistic leverage `oppLeverage m ρ lam X`
are adapted to `ℱ`: the leveraged strategy is predictable for the same filtration.
-/

@[expose] public section

open MeasureTheory Learning.Betting

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {m ρ : ℝ}
  {lam X : ℕ → Ω → ℝ}

/-- The minimal next wealth of a strategy adapted to `ℱ`, on observations `X` with `X n`
`ℱ (n + 1)`-measurable, is adapted to `ℱ`. -/
lemma adapted_nextWealthMin (hlam : Adapted ℱ lam) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) :
    Adapted ℱ (nextWealthMin m lam X) := fun n ↦ by
  have hW := adapted_wealth (m := m) hlam hX n
  exact (hW.mul (measurable_const.add ((hlam n).mul measurable_const))).min
    (hW.mul (measurable_const.add ((hlam n).mul measurable_const)))

/-- The leveraged bet fraction of a strategy adapted to `ℱ`, on observations `X` with `X n`
`ℱ (n + 1)`-measurable, is adapted to `ℱ`. -/
lemma adapted_leverageFraction (hlam : Adapted ℱ lam)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) :
    Adapted ℱ (leverageFraction m ρ lam X) := fun n ↦ by
  have hW := adapted_wealth (m := m) hlam hX n
  exact (hW.mul (hlam n)).div (hW.sub_const ρ)

/-- **Predictability of the opportunistic leverage**: the `ρ`-opportunistic leverage of a
strategy adapted to `ℱ`, on observations `X` with `X n` `ℱ (n + 1)`-measurable, is adapted
to `ℱ`. -/
lemma adapted_oppLeverage (hlam : Adapted ℱ lam) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) :
    Adapted ℱ (oppLeverage m ρ lam X) := fun n ↦
  Measurable.ite (measurableSet_lt measurable_const (adapted_nextWealthMin hlam hX n))
    (adapted_leverageFraction hlam hX n) (hlam n)

end Wang2026Almost
