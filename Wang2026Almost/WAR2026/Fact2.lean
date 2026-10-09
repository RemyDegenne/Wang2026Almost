/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Fact1

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
  have hmI : m ∈ Set.Icc 0 1 := Set.Ioo_subset_Icc_self hm
  have h1ρ : 0 < 1 - ρ := sub_pos.2 hρ.2
  have hκρ : -ρ ≤ κ * (1 - ρ) := (div_le_iff₀ h1ρ).1 hκ.1
  have hW : ∀ mu : ℕ → (ℕ → ℝ) → ℝ, (∀ n x, mu n x ∈ fractionRange m) →
      ∀ y, IsBinaryPath y → ∀ n, 0 ≤ wealth m mu coord n y := by
    refine fun mu hmu y hy n ↦ wealth_nonneg hmI (fun k _ ↦ hmu k y) fun k _ ↦ ?_
    rcases hy k with h | h <;> simp [coord, h]
  -- On a binary path, the portfolio wealth is nonnegative, and its numerator vanishes with it.
  have hD : ∀ y, IsBinaryPath y → ∀ n,
      0 ≤ (1 - κ) * wealth m lam coord n y + κ * wealth m nu coord n y ∧
      ((1 - κ) * wealth m lam coord n y + κ * wealth m nu coord n y = 0 →
        (1 - κ) * wealth m lam coord n y * lam n y + κ * wealth m nu coord n y * nu n y = 0) := by
    intro y hy n
    have hlν := hbin y hy n
    have hν := hW nu hnu y hy n
    rcases lt_or_ge κ 0 with hκ0 | hκ0
    · -- For `κ < 0`: `(1 - κ) W^lam + κ W^nu ≥ (1 - κ) (W^lam - ρ W^nu) > 0`.
      have hκρ' : 0 ≤ κ + ρ * (1 - κ) := by linarith
      have hpos : 0 < (1 - κ) * wealth m lam coord n y + κ * wealth m nu coord n y := by
        nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - κ) (sub_pos.2 hlν), mul_nonneg hκρ' hν]
      exact ⟨hpos.le, fun h ↦ absurd h hpos.ne'⟩
    · -- For `κ ∈ [0, 1]`: both parts of the portfolio wealth are nonnegative.
      have ha := mul_nonneg (sub_nonneg.2 hκ.2) (hW lam hlam y hy n)
      have hb := mul_nonneg hκ0 hν
      refine ⟨add_nonneg ha hb, fun h ↦ ?_⟩
      have ha0 : (1 - κ) * wealth m lam coord n y = 0 := by linarith
      have hb0 : κ * wealth m nu coord n y = 0 := by linarith
      rw [ha0, hb0]
      ring
  intro x hx n
  refine ⟨?_, wealth_portfolioFraction_eq fun k _ ↦ (hD x hx k).2⟩
  rcases (hD x hx n).1.eq_or_lt with h0 | hpos
  · rw [portfolioFraction, ← h0, div_zero]
    exact zero_mem_fractionRange hmI
  -- Modify the path at time `n` to `c ∈ {0, 1}`: the next portfolio wealth is nonnegative.
  have key : ∀ c : ℝ, (c = 0 ∨ c = 1) →
      0 ≤ 1 + portfolioFraction m κ lam nu coord n x * (c - m) := by
    intro c hc
    set y := Function.update x n c
    have hy : IsBinaryPath y := by
      intro k
      by_cases hk : k = n
      · subst hk
        simpa [y] using hc
      · simpa [y, hk] using hx k
    have hyx : ∀ k < n, y k = x k := fun k hk ↦ Function.update_of_ne hk.ne _ _
    have hpred : ∀ mu : ℕ → (ℕ → ℝ) → ℝ, IsPathPredictable mu → ∀ k ≤ n, mu k y = mu k x :=
      fun mu hmu k hk ↦ hmu k y x fun j hj ↦ hyx j (hj.trans_le hk)
    have hWy : ∀ mu : ℕ → (ℕ → ℝ) → ℝ, IsPathPredictable mu →
        wealth m mu coord n y = wealth m mu coord n x :=
      fun mu hmu ↦ wealth_congr (fun k hk ↦ hpred mu hmu k hk.le) fun k hk ↦ hyx k hk
    have hyn : coord n y = c := Function.update_self _ _ _
    have hnext := (hD y hy (n + 1)).1
    rw [wealth_succ, wealth_succ, hWy lam hlam_pred, hWy nu hnu_pred,
      hpred lam hlam_pred n le_rfl, hpred nu hnu_pred n le_rfl, hyn] at hnext
    have hmul := mul_portfolioFraction (hD x hx n).2
    have heq : (1 - κ) * (wealth m lam coord n x * (1 + lam n x * (c - m))) +
        κ * (wealth m nu coord n x * (1 + nu n x * (c - m))) =
        ((1 - κ) * wealth m lam coord n x + κ * wealth m nu coord n x) *
          (1 + portfolioFraction m κ lam nu coord n x * (c - m)) := by
      linear_combination (m - c) * hmul
    rw [heq] at hnext
    exact nonneg_of_mul_nonneg_right hnext hpos
  have h0 := key 0 (Or.inl rfl)
  have h1 := key 1 (Or.inr rfl)
  constructor
  · rw [div_le_iff₀ (sub_pos.2 hm.2)]
    linarith
  · rw [le_div_iff₀ hm.1]
    linarith

end Wang2026Almost
