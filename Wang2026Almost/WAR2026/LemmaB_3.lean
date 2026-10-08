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

/-- If the next wealth of the strategy `lam` is guaranteed to stay above `ρ` at round `n`, then
so is the current wealth: `W n - ρ` is the convex combination with weights `1 - m` and `m` of the
two possible next wealths minus `ρ`. -/
lemma sub_pos_of_lt_nextWealthMin {m ρ : ℝ} (hm : m ∈ Set.Icc 0 1) {lam X : ℕ → Ω → ℝ} {n : ℕ}
    {ω : Ω} (h : ρ < nextWealthMin m lam X n ω) :
    0 < wealth m lam X n ω - ρ := by
  set W := wealth m lam X n ω
  have h0 : ρ < W * (1 + lam n ω * (0 - m)) := h.trans_le (min_le_left _ _)
  have h1 : ρ < W * (1 + lam n ω * (1 - m)) := h.trans_le (min_le_right _ _)
  set a := W * (1 + lam n ω * (0 - m)) - ρ
  set b := W * (1 + lam n ω * (1 - m)) - ρ
  have hab : W - ρ = (1 - m) * a + m * b := by simp only [a, b]; ring
  have ha : 0 < a := sub_pos.2 h0
  have hb : 0 < b := sub_pos.2 h1
  have h1m : 0 ≤ 1 - m := sub_nonneg.2 hm.2
  rw [hab]
  rcases hm.1.eq_or_lt with hm0 | hm0
  · simp [← hm0, ha]
  · positivity

/-- **Lemma B.3** (Wang, Agrawal, Ramdas 2026): if the next wealth of the strategy `lam` is
guaranteed to stay above `ρ` at round `n`, then the leveraged bet fraction
`leverageFraction m ρ lam X n` is in `(-1 / (1 - m), 1 / m)`. -/
lemma leverageFraction_mem_Ioo {m ρ : ℝ} (hm : m ∈ Set.Ioo 0 1) {lam X : ℕ → Ω → ℝ} {n : ℕ}
    {ω : Ω} (h : ρ < nextWealthMin m lam X n ω) :
    leverageFraction m ρ lam X n ω ∈ Set.Ioo (-1 / (1 - m)) (1 / m) := by
  have hW := sub_pos_of_lt_nextWealthMin (Set.Ioo_subset_Icc_self hm) h
  have h0 : ρ < wealth m lam X n ω * (1 + lam n ω * (0 - m)) := h.trans_le (min_le_left _ _)
  have h1 : ρ < wealth m lam X n ω * (1 + lam n ω * (1 - m)) := h.trans_le (min_le_right _ _)
  rw [leverageFraction]
  constructor
  · rw [div_lt_div_iff₀ (sub_pos.2 hm.2) hW]
    linarith
  · rw [div_lt_div_iff₀ hW hm.1]
    linarith

end Wang2026Almost
