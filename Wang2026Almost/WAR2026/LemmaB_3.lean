/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Leverage

/-!
# Lemma B.3: the leveraged bet fraction is valid when the next wealth stays above `ρ`

On the event `{nextWealthMin m lam X n > ρ}`, the leveraged bet fraction
`leverageFraction m ρ lam X n = W n lam n / (W n - ρ)` lies strictly inside
`(-1 / (1 - m), 1 / m)`.
-/

@[expose] public section

open Learning.Betting

namespace Wang2026Almost

variable {Ω : Type*}

/-- **Lemma B.3** (Wang, Agrawal, Ramdas 2026): if the next wealth of the strategy `lam` is
guaranteed to stay above `ρ` at round `n`, then the leveraged bet fraction
`leverageFraction m ρ lam X n` is in `(-1 / (1 - m), 1 / m)`. -/
lemma leverageFraction_mem_Ioo {m ρ : ℝ} (hm : m ∈ Set.Ioo 0 1) {lam X : ℕ → Ω → ℝ} {n : ℕ}
    {ω : Ω} (h : ρ < nextWealthMin m lam X n ω) :
    leverageFraction m ρ lam X n ω ∈ Set.Ioo (-1 / (1 - m)) (1 / m) := by
  sorry

end Wang2026Almost
