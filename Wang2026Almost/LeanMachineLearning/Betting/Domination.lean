/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Domination of large fixed bets by small ones

By Bernoulli's inequality `1 + p s ≤ (1 + s) ^ p` (`s ≥ -1`, `p ≥ 1`), a bet of fraction `l` is
dominated by a power of a bet of the smaller fraction `ε ∈ (0, l]` of the same sign:
`∏_{k < n} (1 + l y_k) ≤ (∏_{k < n} (1 + ε y_k)) ^ (l / ε)`. In particular, when the wealth of
the fixed fraction `ε` is at most `1`, it dominates the wealth of every fixed fraction `l ≥ ε`.
The same holds for the sub-Gaussian test processes of constant alternatives.

## Main statements

* `prod_one_add_mul_le_rpow`: the domination for general products;
* `fixedWealth_le_rpow`, `fixedWealth_le_of_le_one`: the betting form for `0 < ε ≤ l`, and
  `fixedWealth_le_rpow_of_le_neg`, `fixedWealth_le_of_le_one_of_le_neg` for `l ≤ -ε < 0`;
* `subgaussianTest_le_rpow`, `subgaussianTest_le_of_le_one` (alternatives `l ≥ m + ε`) and
  `subgaussianTest_le_rpow_of_le_sub`, `subgaussianTest_le_of_le_one_of_le_sub`
  (alternatives `l ≤ m - ε`).
-/

@[expose] public section

open Finset

namespace Learning.Betting

variable {Ω : Type*}

/-- **Bernoulli domination**: for `0 < ε ≤ l` and reals `y k` with `1 + l y_k ≥ 0` and
`ε y_k ≥ -1`, `∏_{k < n} (1 + l y_k) ≤ (∏_{k < n} (1 + ε y_k)) ^ (l / ε)`. -/
lemma prod_one_add_mul_le_rpow {ε l : ℝ} (hε : 0 < ε) (hεl : ε ≤ l)
    {y : ℕ → ℝ} {n : ℕ} (hl : ∀ k < n, 0 ≤ 1 + l * y k) (hεy : ∀ k < n, -1 ≤ ε * y k) :
    ∏ k ∈ range n, (1 + l * y k) ≤ (∏ k ∈ range n, (1 + ε * y k)) ^ (l / ε) := by
  rw [← Real.finsetProd_rpow _ _ fun k hk ↦ by linarith [hεy k (mem_range.1 hk)]]
  refine prod_le_prod₀ (fun k hk ↦ hl k (mem_range.1 hk)) fun k hk ↦ ?_
  calc 1 + l * y k = 1 + l / ε * (ε * y k) := by field_simp
    _ ≤ (1 + ε * y k) ^ (l / ε) :=
      one_add_mul_self_le_rpow_one_add (hεy k (mem_range.1 hk)) ((one_le_div hε).2 hεl)

variable {m ε l : ℝ} {X : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}

/-- A fraction between `0` and a fraction of `fractionRange m` is in `fractionRange m`. -/
private lemma mem_fractionRange_of_mem_uIcc (hm : m ∈ Set.Ioo 0 1) (hl : l ∈ fractionRange m)
    (hε : ε ∈ Set.uIcc 0 l) : ε ∈ fractionRange m := by
  have h1 : -1 / (1 - m) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith [hm.2])
  have h2 : 0 ≤ 1 / m := by have := hm.1; positivity
  rcases le_total 0 l with h | h
  · rw [Set.uIcc_of_le h] at hε
    exact ⟨h1.trans hε.1, hε.2.trans hl.2⟩
  · rw [Set.uIcc_of_ge h] at hε
    exact ⟨hl.1.trans hε.1, hε.2.trans h2⟩

/-- **Bernoulli domination of fixed-fraction wealths**: for observations in `[0, 1]`,
`0 < ε ≤ l` and `l ∈ fractionRange m`, `W^l_n ≤ (W^ε_n) ^ (l / ε)`. -/
lemma fixedWealth_le_rpow (hm : m ∈ Set.Ioo 0 1) (hε : 0 < ε) (hεl : ε ≤ l)
    (hl : l ∈ fractionRange m) (hX : ∀ k < n, X k ω ∈ Set.Icc 0 1) :
    fixedWealth m l X n ω ≤ fixedWealth m ε X n ω ^ (l / ε) := by
  have hεr : ε ∈ fractionRange m := mem_fractionRange_of_mem_uIcc hm hl
    (by rw [Set.uIcc_of_le (hε.le.trans hεl)]; exact ⟨hε.le, hεl⟩)
  exact prod_one_add_mul_le_rpow hε hεl (fun k hk ↦ one_add_mul_sub_nonneg hm hl (hX k hk))
    fun k hk ↦ by linarith [one_add_mul_sub_nonneg hm hεr (hX k hk)]

/-- **Bernoulli domination of fixed-fraction wealths**, negative fractions: for observations in
`[0, 1]`, `l ≤ -ε < 0` and `l ∈ fractionRange m`, `W^l_n ≤ (W^{-ε}_n) ^ (-l / ε)`. -/
lemma fixedWealth_le_rpow_of_le_neg (hm : m ∈ Set.Ioo 0 1) (hε : 0 < ε) (hlε : l ≤ -ε)
    (hl : l ∈ fractionRange m) (hX : ∀ k < n, X k ω ∈ Set.Icc 0 1) :
    fixedWealth m l X n ω ≤ fixedWealth m (-ε) X n ω ^ (-l / ε) := by
  have hεr : -ε ∈ fractionRange m := mem_fractionRange_of_mem_uIcc hm hl
    (by rw [Set.uIcc_of_ge (by linarith)]; constructor <;> linarith)
  have h := prod_one_add_mul_le_rpow (ε := ε) (l := -l) (y := fun k ↦ -(X k ω - m)) (n := n) hε
    (by linarith) (fun k hk ↦ by linarith [one_add_mul_sub_nonneg hm hl (hX k hk)])
    fun k hk ↦ by linarith [one_add_mul_sub_nonneg hm hεr (hX k hk)]
  have e1 : fixedWealth m l X n ω = ∏ k ∈ range n, (1 + -l * -(X k ω - m)) := by
    unfold fixedWealth wealth; exact prod_congr rfl fun k _ ↦ by ring
  have e2 : fixedWealth m (-ε) X n ω = ∏ k ∈ range n, (1 + ε * -(X k ω - m)) := by
    unfold fixedWealth wealth; exact prod_congr rfl fun k _ ↦ by ring
  rw [e1, e2]
  exact h

/-- For observations in `[0, 1]`, `0 < ε ≤ l` and `l ∈ fractionRange m`, the wealth of the fixed
fraction `ε` dominates that of `l` when it is at most `1`. -/
lemma fixedWealth_le_of_le_one (hm : m ∈ Set.Ioo 0 1) (hε : 0 < ε) (hεl : ε ≤ l)
    (hl : l ∈ fractionRange m) (hX : ∀ k < n, X k ω ∈ Set.Icc 0 1)
    (h1 : fixedWealth m ε X n ω ≤ 1) :
    fixedWealth m l X n ω ≤ fixedWealth m ε X n ω := by
  have hεr : ε ∈ fractionRange m := mem_fractionRange_of_mem_uIcc hm hl
    (by rw [Set.uIcc_of_le (hε.le.trans hεl)]; exact ⟨hε.le, hεl⟩)
  refine (fixedWealth_le_rpow hm hε hεl hl hX).trans ?_
  calc fixedWealth m ε X n ω ^ (l / ε) ≤ fixedWealth m ε X n ω ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' (wealth_nonneg hm (fun _ _ ↦ hεr) hX) h1 zero_le_one
          ((one_le_div hε).2 hεl)
    _ = fixedWealth m ε X n ω := Real.rpow_one _

/-- For observations in `[0, 1]`, `l ≤ -ε < 0` and `l ∈ fractionRange m`, the wealth of the
fixed fraction `-ε` dominates that of `l` when it is at most `1`. -/
lemma fixedWealth_le_of_le_one_of_le_neg (hm : m ∈ Set.Ioo 0 1) (hε : 0 < ε) (hlε : l ≤ -ε)
    (hl : l ∈ fractionRange m) (hX : ∀ k < n, X k ω ∈ Set.Icc 0 1)
    (h1 : fixedWealth m (-ε) X n ω ≤ 1) :
    fixedWealth m l X n ω ≤ fixedWealth m (-ε) X n ω := by
  have hεr : -ε ∈ fractionRange m := mem_fractionRange_of_mem_uIcc hm hl
    (by rw [Set.uIcc_of_ge (by linarith)]; constructor <;> linarith)
  refine (fixedWealth_le_rpow_of_le_neg hm hε hlε hl hX).trans ?_
  calc fixedWealth m (-ε) X n ω ^ (-l / ε) ≤ fixedWealth m (-ε) X n ω ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' (wealth_nonneg hm (fun _ _ ↦ hεr) hX) h1 zero_le_one
          ((one_le_div hε).2 (by linarith))
    _ = fixedWealth m (-ε) X n ω := Real.rpow_one _

/-- The sub-Gaussian test process of the constant alternative `l` is
`exp ((l - m) S_n - n (l - m) ^ 2 / 2)` with `S_n = ∑_{k < n} (X k - m)`. -/
lemma subgaussianTest_const (m l : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    subgaussianTest m (fun _ _ ↦ l) X n ω
      = Real.exp ((l - m) * ∑ k ∈ range n, (X k ω - m) - n * (l - m) ^ 2 / 2) := by
  have h : ∀ k ∈ range n, ((X k ω - m) ^ 2 - (X k ω - l) ^ 2) / ((2 : ℕ) : ℝ)
      = (l - m) * (X k ω - m) - (l - m) ^ 2 / 2 := fun k _ ↦ by push_cast; ring
  rw [subgaussianTest, sum_congr rfl h, sum_sub_distrib, ← mul_sum, sum_const, card_range,
    nsmul_eq_mul]
  ring_nf

/-- **Domination of sub-Gaussian test processes**: for `ε > 0` and an alternative `l ≥ m + ε`,
`M^l_n ≤ (M^{m+ε}_n) ^ ((l - m) / ε)`. -/
lemma subgaussianTest_le_rpow (hε : 0 < ε) (hl : m + ε ≤ l) :
    subgaussianTest m (fun _ _ ↦ l) X n ω
      ≤ subgaussianTest m (fun _ _ ↦ m + ε) X n ω ^ ((l - m) / ε) := by
  rw [subgaussianTest_const, subgaussianTest_const, ← Real.exp_mul]
  gcongr
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have h : ε * (l - m) ≤ (l - m) ^ 2 := by nlinarith
  rw [add_sub_cancel_left]
  field_simp
  nlinarith

/-- **Domination of sub-Gaussian test processes**: for `ε > 0` and an alternative `l ≤ m - ε`,
`M^l_n ≤ (M^{m-ε}_n) ^ ((m - l) / ε)`. -/
lemma subgaussianTest_le_rpow_of_le_sub (hε : 0 < ε) (hl : l ≤ m - ε) :
    subgaussianTest m (fun _ _ ↦ l) X n ω
      ≤ subgaussianTest m (fun _ _ ↦ m - ε) X n ω ^ ((m - l) / ε) := by
  rw [subgaussianTest_const, subgaussianTest_const, ← Real.exp_mul]
  gcongr
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have h : ε * (m - l) ≤ (l - m) ^ 2 := by nlinarith
  rw [sub_sub_cancel_left]
  field_simp
  nlinarith

/-- For `ε > 0` and an alternative `l ≥ m + ε`, the sub-Gaussian test process of the alternative
`m + ε` dominates that of `l` when it is at most `1`. -/
lemma subgaussianTest_le_of_le_one (hε : 0 < ε) (hl : m + ε ≤ l)
    (h1 : subgaussianTest m (fun _ _ ↦ m + ε) X n ω ≤ 1) :
    subgaussianTest m (fun _ _ ↦ l) X n ω ≤ subgaussianTest m (fun _ _ ↦ m + ε) X n ω := by
  refine (subgaussianTest_le_rpow hε hl).trans ?_
  calc subgaussianTest m (fun _ _ ↦ m + ε) X n ω ^ ((l - m) / ε)
      ≤ subgaussianTest m (fun _ _ ↦ m + ε) X n ω ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' (Real.exp_nonneg _) h1 zero_le_one
          ((one_le_div hε).2 (by linarith))
    _ = subgaussianTest m (fun _ _ ↦ m + ε) X n ω := Real.rpow_one _

/-- For `ε > 0` and an alternative `l ≤ m - ε`, the sub-Gaussian test process of the alternative
`m - ε` dominates that of `l` when it is at most `1`. -/
lemma subgaussianTest_le_of_le_one_of_le_sub (hε : 0 < ε) (hl : l ≤ m - ε)
    (h1 : subgaussianTest m (fun _ _ ↦ m - ε) X n ω ≤ 1) :
    subgaussianTest m (fun _ _ ↦ l) X n ω ≤ subgaussianTest m (fun _ _ ↦ m - ε) X n ω := by
  refine (subgaussianTest_le_rpow_of_le_sub hε hl).trans ?_
  calc subgaussianTest m (fun _ _ ↦ m - ε) X n ω ^ ((m - l) / ε)
      ≤ subgaussianTest m (fun _ _ ↦ m - ε) X n ω ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' (Real.exp_nonneg _) h1 zero_le_one
          ((one_le_div hε).2 (by linarith))
    _ = subgaussianTest m (fun _ _ ↦ m - ε) X n ω := Real.rpow_one _

end Learning.Betting
