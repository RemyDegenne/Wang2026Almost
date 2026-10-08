/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Strategies

/-!
# Pathwise properties of the classical strategies

* `ktFraction_mem_fractionRange`: the Krichevsky–Trofimov fractions with constant
  `C ≥ max (m (1 - m)) (m / 2)` lie in `fractionRange m` on observations in `[0, 1]`;
* `empVar_add_sq_empMean_sub`: `σ̂²_n + (μ̂_n - m)² = (1/n) ∑_{k < n} (X k - m)²`, the
  denominator of the aGRAPA fraction;
* `agrapaFraction_mem_fractionRange`, `hedgeFraction_mem_fractionRange`: the clipped fractions
  lie in `fractionRange m` for `C ∈ [0, 1]`;
* `isPlugIn_agrapaFraction`: the aGRAPA strategy is a plug-in strategy.
-/

@[expose] public section

open Finset

namespace Learning.Betting

variable {Ω : Type*}

/-- The Krichevsky–Trofimov fractions with constant `C ≥ m (1 - m)` and `C ≥ m / 2` lie in
`[-1 / (1 - m), 1 / m]` when the first `n` observations are in `[0, 1]`. -/
lemma ktFraction_mem_fractionRange {C m : ℝ} (hm : m ∈ Set.Ioo 0 1) (hC₁ : m * (1 - m) ≤ C)
    (hC₂ : m / 2 ≤ C) {X : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} (hX : ∀ k < n, X k ω ∈ Set.Icc 0 1) :
    ktFraction C m X n ω ∈ fractionRange m := by
  obtain ⟨hm0, hm1⟩ := hm
  have h1m : 0 < 1 - m := sub_pos.2 hm1
  have hC : 0 < C := lt_of_lt_of_le (by positivity) hC₂
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hS_le : ∑ k ∈ range n, (X k ω - m) ≤ n * (1 - m) := by
    calc ∑ k ∈ range n, (X k ω - m) ≤ ∑ _k ∈ range n, (1 - m) :=
          sum_le_sum fun k hk ↦ by linarith [(hX k (mem_range.1 hk)).2]
      _ = n * (1 - m) := by simp [mul_sub]
  have hS_ge : -(n * m) ≤ ∑ k ∈ range n, (X k ω - m) := by
    calc -(n * m) = ∑ _k ∈ range n, (-m) := by simp
      _ ≤ ∑ k ∈ range n, (X k ω - m) :=
          sum_le_sum fun k hk ↦ by linarith [(hX k (mem_range.1 hk)).1]
  have hnn : (0 : ℝ) ≤ n := n.cast_nonneg
  rw [ktFraction, fractionRange, Set.mem_Icc, Nat.cast_ofNat]
  constructor
  · rw [div_le_div_iff₀ h1m (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hC₁ hnn]
  · rw [div_le_div_iff₀ (by positivity) hm0]
    nlinarith [mul_le_mul_of_nonneg_left hC₁ hnn]

/-- The empirical variance plus the squared deviation of the empirical mean from `m` is the
empirical mean of the squared deviations from `m`. -/
lemma empVar_add_sq_empMean_sub (X : ℕ → Ω → ℝ) (m : ℝ) {n : ℕ} (hn : n ≠ 0) (ω : Ω) :
    empVar X n ω + (empMean X n ω - m) ^ 2 = (∑ k ∈ range n, (X k ω - m) ^ 2) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hμ : ∑ k ∈ range n, X k ω = n * empMean X n ω := by
    rw [empMean]; field_simp
  rw [empVar, eq_div_iff hn', add_mul, div_mul_cancel₀ _ hn']
  have expand : ∀ k, (X k ω - m) ^ 2 =
      (X k ω - empMean X n ω) ^ 2 + 2 * (empMean X n ω - m) * (X k ω - empMean X n ω) +
        (empMean X n ω - m) ^ 2 := fun k ↦ by ring
  simp_rw [expand, sum_add_distrib, ← mul_sum, sum_sub_distrib, hμ]
  simp
  ring

/-- The aGRAPA fractions with `C ∈ [0, 1]` lie in `fractionRange m`. -/
lemma agrapaFraction_mem_fractionRange {C m : ℝ} (hm : m ∈ Set.Ioo 0 1) (hC : C ∈ Set.Icc 0 1)
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : agrapaFraction C m X n ω ∈ fractionRange m := by
  have h1m : 0 < 1 - m := sub_pos.2 hm.2
  have hlo : -1 / (1 - m) ≤ -C / (1 - m) := div_le_div_of_nonneg_right (by linarith [hC.2]) h1m.le
  have hhi : C / m ≤ 1 / m := div_le_div_of_nonneg_right hC.2 hm.1.le
  have hlohi : -C / (1 - m) ≤ C / m :=
    (div_nonpos_of_nonpos_of_nonneg (by linarith [hC.1]) h1m.le).trans
      (div_nonneg hC.1 hm.1.le)
  exact ⟨hlo.trans (le_max_left _ _),
    max_le (hlohi.trans hhi) ((min_le_right _ _).trans hhi)⟩

/-- The predictable hedging fractions with `C ∈ [0, 1]` lie in `fractionRange m`. -/
lemma hedgeFraction_mem_fractionRange {C α m v : ℝ} (hm : m ∈ Set.Ioo 0 1)
    (hC : C ∈ Set.Icc 0 1) (n : ℕ) : hedgeFraction C α m v n ∈ fractionRange m := by
  have h1m : 0 < 1 - m := sub_pos.2 hm.2
  have hlo : -1 / (1 - m) ≤ -C / (1 - m) := div_le_div_of_nonneg_right (by linarith [hC.2]) h1m.le
  have hhi : C / m ≤ 1 / m := div_le_div_of_nonneg_right hC.2 hm.1.le
  have hlohi : -C / (1 - m) ≤ C / m :=
    (div_nonpos_of_nonpos_of_nonneg (by linarith [hC.1]) h1m.le).trans
      (div_nonneg hC.1 hm.1.le)
  exact ⟨hlo.trans (le_max_left _ _),
    max_le (hlohi.trans hhi) ((min_le_right _ _).trans hhi)⟩

/-- The aGRAPA strategy is a plug-in strategy. -/
lemma isPlugIn_agrapaFraction (C m : ℝ) (X : ℕ → Ω → ℝ) : IsPlugIn X (agrapaFraction C m X) := by
  intro n
  refine ⟨fun x ↦ max (-C / (1 - m)) (min (((∑ k, x k) / n - m) /
    ((∑ k, (x k - (∑ j, x j) / n) ^ 2) / n + ((∑ k, x k) / n - m) ^ 2)) (C / m)),
    by fun_prop, fun ω ↦ ?_⟩
  simp only [agrapaFraction, Learning.Betting.empVar, Learning.Betting.empMean, Finset.sum_range]

end Learning.Betting
