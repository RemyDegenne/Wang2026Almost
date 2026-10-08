/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Leverage
public import Wang2026Almost.LeanMachineLearning.Betting.WealthLemmas

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

/-- The portfolio fraction times the portfolio wealth `(1 - κ) W^lam_n + κ W^nu_n` is the
numerator `(1 - κ) W^lam_n lam_n + κ W^nu_n nu_n`, provided the numerator vanishes when the
portfolio wealth does. -/
lemma mul_portfolioFraction {m κ : ℝ} {lam nu X : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}
    (h : (1 - κ) * wealth m lam X n ω + κ * wealth m nu X n ω = 0 →
      (1 - κ) * wealth m lam X n ω * lam n ω + κ * wealth m nu X n ω * nu n ω = 0) :
    ((1 - κ) * wealth m lam X n ω + κ * wealth m nu X n ω) * portfolioFraction m κ lam nu X n ω =
      (1 - κ) * wealth m lam X n ω * lam n ω + κ * wealth m nu X n ω * nu n ω := by
  rw [portfolioFraction]
  by_cases hD : (1 - κ) * wealth m lam X n ω + κ * wealth m nu X n ω = 0
  · rw [hD, zero_mul, h hD]
  · exact mul_div_cancel₀ _ hD

/-- The wealth of the portfolio fractions is the portfolio `(1 - κ) W^lam + κ W^nu`, as long as
at every round before `n` the numerator `(1 - κ) W^lam_k lam_k + κ W^nu_k nu_k` of the portfolio
fraction vanishes when the portfolio wealth does. -/
lemma wealth_portfolioFraction_eq {m κ : ℝ} {lam nu X : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}
    (h : ∀ k < n, (1 - κ) * wealth m lam X k ω + κ * wealth m nu X k ω = 0 →
      (1 - κ) * wealth m lam X k ω * lam k ω + κ * wealth m nu X k ω * nu k ω = 0) :
    wealth m (portfolioFraction m κ lam nu X) X n ω =
      (1 - κ) * wealth m lam X n ω + κ * wealth m nu X n ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmul := mul_portfolioFraction (h n n.lt_succ_self)
    rw [wealth_succ, ih fun k hk ↦ h k (hk.trans n.lt_succ_self), wealth_succ, wealth_succ,
      mul_add, mul_one, ← mul_assoc, hmul]
    ring

/-- The portfolio fraction is in `fractionRange m` when the bet fractions `lam n`, `nu n` are and
the two parts `(1 - κ) W^lam_n`, `κ W^nu_n` of the portfolio wealth are nonnegative: it is then a
convex combination of `lam n` and `nu n` (or `0` if the portfolio wealth vanishes). -/
lemma portfolioFraction_mem_fractionRange {m κ : ℝ} (hm : m ∈ Set.Icc 0 1)
    {lam nu X : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} (hlam : lam n ω ∈ fractionRange m)
    (hnu : nu n ω ∈ fractionRange m) (ha : 0 ≤ (1 - κ) * wealth m lam X n ω)
    (hb : 0 ≤ κ * wealth m nu X n ω) :
    portfolioFraction m κ lam nu X n ω ∈ fractionRange m := by
  rw [portfolioFraction]
  set a := (1 - κ) * wealth m lam X n ω
  set b := κ * wealth m nu X n ω
  rcases (add_nonneg ha hb).eq_or_lt with hD | hD
  · rw [← hD, div_zero]
    exact zero_mem_fractionRange hm
  · obtain ⟨hl1, hl2⟩ := hlam
    obtain ⟨hn1, hn2⟩ := hnu
    constructor
    · rw [le_div_iff₀ hD]
      nlinarith [mul_le_mul_of_nonneg_left hl1 ha, mul_le_mul_of_nonneg_left hn1 hb]
    · rw [div_le_iff₀ hD]
      nlinarith [mul_le_mul_of_nonneg_left hl2 ha, mul_le_mul_of_nonneg_left hn2 hb]

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
  have hmI : m ∈ Set.Icc 0 1 := Set.Ioo_subset_Icc_self hm
  have ha : ∀ n ω, 0 ≤ (1 - κ) * wealth m lam X n ω := fun n ω ↦
    mul_nonneg (sub_nonneg.2 hκ.2) (wealth_nonneg hm (fun k _ ↦ hlam k ω) fun k _ ↦ hX k ω)
  have hb : ∀ n ω, 0 ≤ κ * wealth m nu X n ω := fun n ω ↦
    mul_nonneg hκ.1 (wealth_nonneg hm (fun k _ ↦ hnu k ω) fun k _ ↦ hX k ω)
  refine ⟨fun n ω ↦ portfolioFraction_mem_fractionRange hmI (hlam n ω) (hnu n ω) (ha n ω)
    (hb n ω), fun n ω ↦ wealth_portfolioFraction_eq fun k _ hD ↦ ?_⟩
  have ha0 : (1 - κ) * wealth m lam X k ω = 0 := by linarith [ha k ω, hb k ω]
  have hb0 : κ * wealth m nu X k ω = 0 := by linarith [ha k ω, hb k ω]
  rw [ha0, hb0]
  ring

end Wang2026Almost
