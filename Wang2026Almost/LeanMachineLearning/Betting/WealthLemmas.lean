/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Order.Compact

/-!
# Testing by betting: basic properties of the wealth processes

Pathwise properties of the wealth processes of `Wealth.lean`.

## Main results

* `wealth_congr`: the wealth after `n` rounds depends only on the first `n` bet fractions and
  observations;
* `measurable_wealth_of_lt`, `adapted_wealth`: the wealth after `n` rounds is measurable with
  respect to the information available before the observation `X n`;
* `bddAbove_fixedWealth`, `one_le_iSup_fixedWealth`, `hindsightLogWealth_nonneg`: the
  best-in-hindsight wealth is finite and at least the wealth `1` of the null bet;
* `not_bddAbove_logRegret_of_tendsto_zero`: a strategy whose wealth stays positive and tends to
  `0` has unbounded regret.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped Topology

namespace Learning.Betting

variable {Ω : Type*}

/-- The null bet fraction `0` is in `fractionRange m` for `m ∈ [0, 1]`. -/
lemma zero_mem_fractionRange {m : ℝ} (hm : m ∈ Set.Icc 0 1) : 0 ∈ fractionRange m :=
  ⟨div_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.2 hm.2),
    div_nonneg zero_le_one hm.1⟩

/-- The wealth after `n` rounds depends only on the first `n` bet fractions and observations. -/
lemma wealth_congr {m : ℝ} {lam lam' X X' : ℕ → Ω → ℝ} {n : ℕ} {ω ω' : Ω}
    (hlam : ∀ k < n, lam k ω = lam' k ω') (hX : ∀ k < n, X k ω = X' k ω') :
    wealth m lam X n ω = wealth m lam' X' n ω' :=
  prod_congr rfl fun k hk ↦ by rw [hlam k (mem_range.1 hk), hX k (mem_range.1 hk)]

/-- The wealth after `n` rounds is measurable if the first `n` bet fractions and observations
are. -/
lemma measurable_wealth_of_lt [MeasurableSpace Ω] {m : ℝ} {lam X : ℕ → Ω → ℝ} {n : ℕ}
    (hlam : ∀ k < n, Measurable (lam k)) (hX : ∀ k < n, Measurable (X k)) :
    Measurable (wealth m lam X n) :=
  Finset.measurable_prod _ fun k hk ↦
    measurable_const.add ((hlam k (mem_range.1 hk)).mul ((hX k (mem_range.1 hk)).sub_const m))

/-- The wealth of a strategy `lam` adapted to a filtration `ℱ`, on observations `X` such that
`X n` is `ℱ (n + 1)`-measurable, is adapted to `ℱ`: the wealth after `n` rounds is known before
the observation `X n`. -/
lemma adapted_wealth {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ} {m : ℝ}
    {lam X : ℕ → Ω → ℝ} (hlam : Adapted ℱ lam) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) :
    Adapted ℱ (wealth m lam X) := fun n ↦
  @measurable_wealth_of_lt Ω (ℱ n) m lam X n (fun k hk ↦ (hlam k).mono (ℱ.mono hk.le) le_rfl)
    fun k hk ↦ (hX k).mono (ℱ.mono (Nat.succ_le_of_lt hk)) le_rfl

/-- The wealth of the null bet fraction `0` is `1`. -/
lemma fixedWealth_zero_fraction (m : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    fixedWealth m 0 X n ω = 1 := by
  simp [fixedWealth, wealth]

/-- The wealth after `n` rounds of the fixed fraction `l` is continuous in `l`
(a polynomial in `l`). -/
lemma continuous_fixedWealth (m : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Continuous fun l ↦ fixedWealth m l X n ω := by
  unfold fixedWealth wealth
  fun_prop

/-- The wealths after `n` rounds of the fixed fractions in `fractionRange m` are bounded
above (a continuous function on a compact interval). -/
lemma bddAbove_fixedWealth (m : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    BddAbove (Set.range fun l : fractionRange m ↦ fixedWealth m l X n ω) := by
  have h : BddAbove ((fun l ↦ fixedWealth m l X n ω) '' fractionRange m) :=
    isCompact_Icc.bddAbove_image (continuous_fixedWealth m X n ω).continuousOn
  exact BddAbove.mono (Set.range_subset_iff.2 fun l ↦
    Set.mem_image_of_mem (fun l ↦ fixedWealth m l X n ω) l.2) h

/-- The best-in-hindsight wealth is at least the wealth `1` of the null bet fraction. -/
lemma one_le_iSup_fixedWealth {m : ℝ} (hm : m ∈ Set.Icc 0 1) (X : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) :
    1 ≤ ⨆ l : fractionRange m, fixedWealth m l X n ω := by
  have h := le_ciSup (bddAbove_fixedWealth m X n ω) ⟨0, zero_mem_fractionRange hm⟩
  rwa [fixedWealth_zero_fraction] at h

/-- The best-in-hindsight log-wealth is nonnegative. -/
lemma hindsightLogWealth_nonneg {m : ℝ} (hm : m ∈ Set.Icc 0 1) (X : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) :
    0 ≤ hindsightLogWealth m X n ω :=
  Real.log_nonneg (one_le_iSup_fixedWealth hm X n ω)

/-- The regret of a strategy is at least minus its log-wealth. -/
lemma neg_log_wealth_le_logRegret {m : ℝ} (hm : m ∈ Set.Icc 0 1) (lam X : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) :
    -Real.log (wealth m lam X n ω) ≤ logRegret m lam X n ω := by
  rw [logRegret]
  linarith [hindsightLogWealth_nonneg hm X n ω]

/-- If the wealth of a strategy never vanishes and tends to `0`, then its regret tends to `∞`. -/
lemma tendsto_logRegret_atTop {m : ℝ} (hm : m ∈ Set.Icc 0 1) {lam X : ℕ → Ω → ℝ} {ω : Ω}
    (h0 : ∀ n, wealth m lam X n ω ≠ 0)
    (h : Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0)) :
    Tendsto (fun n ↦ logRegret m lam X n ω) atTop atTop := by
  have hlog : Tendsto (fun n ↦ Real.log (wealth m lam X n ω)) atTop atBot :=
    Real.tendsto_log_nhdsNE_zero.comp (tendsto_nhdsWithin_iff.2 ⟨h, Eventually.of_forall h0⟩)
  exact tendsto_atTop_mono (neg_log_wealth_le_logRegret hm lam X · ω)
    (tendsto_neg_atBot_atTop.comp hlog)

/-- If the wealth of a strategy tends to `0`, then either it vanishes after finitely many rounds
or the regret of the strategy is unbounded. -/
lemma not_bddAbove_logRegret_of_tendsto_zero {m : ℝ} (hm : m ∈ Set.Icc 0 1)
    {lam X : ℕ → Ω → ℝ} {ω : Ω} (h : Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0)) :
    (∃ n, wealth m lam X n ω = 0) ∨ ¬ BddAbove (Set.range fun n ↦ logRegret m lam X n ω) := by
  refine or_iff_not_imp_left.2 fun h0 ↦ not_bddAbove_of_tendsto_atTop (l := atTop) ?_
  exact tendsto_logRegret_atTop hm (fun n hn ↦ h0 ⟨n, hn⟩) h

end Learning.Betting
