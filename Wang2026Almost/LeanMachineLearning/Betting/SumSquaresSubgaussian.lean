/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.SumSquares

/-!
# The sum-of-squares criterion for sub-Gaussian test processes

Let `P` be a distribution such that `x - m` is `1`-sub-Gaussian under `P`, let the observations
`X` be i.i.d. with law `P` along a filtration `ℱ` and let `lam` be adapted to `ℱ`. The plug-in
sub-Gaussian test process `subgaussianTest m lam X n` converges almost surely, to `0` exactly on
the paths where `∑ (lam n - m) ^ 2 = ∞` (Theorem 5.2 of Wang, Agrawal, Ramdas 2026, in filtration
form).

Since `(x - m)² - (x - l)² = 2 (l - m) (x - m) - (l - m)²`, the test process is
`exp (T n - A n / 2)` with `T n = ∑_{k < n} (lam k - m) (X k - m)` and
`A n = ∑_{k < n} (lam k - m) ^ 2`: it is the exponential supermartingale of the conditionally
sub-Gaussian sums `T`. On `{A ∞ < ∞}`, `T n` converges; on `{A ∞ = ∞}`, `T n ≤ C + A n / 4`, so
the test process tends to `0`.

## Main statements

* `supermartingale_subgaussianTest`: the test process is a supermartingale;
* `ae_tendsto_subgaussianTest_zero_of_not_summable`,
  `ae_exists_tendsto_subgaussianTest_pos_of_summable`: the two halves of the criterion;
* `sum_sq_criterion_subgaussian_of_indep`: the criterion (Theorem 5.2) in filtration form;
* `ae_tendsto_subgaussianTest_zero`: the test process of a constant `l ≠ m` tends to `0` almost
  surely on i.i.d. observations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology NNReal

namespace Learning.Betting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The plug-in sub-Gaussian test process is `exp (T n - A n / 2)` with
`T n = ∑_{k < n} (lam k - m) (X k - m)` and `A n = ∑_{k < n} (lam k - m) ^ 2`. -/
lemma subgaussianTest_eq (m : ℝ) (lam X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    subgaussianTest m lam X n ω = Real.exp (∑ k ∈ range n, (lam k ω - m) * (X k ω - m)
      - (∑ k ∈ range n, (lam k ω - m) ^ 2) / 2) := by
  rw [subgaussianTest, sum_div, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun k _ ↦ ?_
  push_cast
  ring

/-- Pathwise: if `A n = ∑_{k < n} (lam k - m) ^ 2 → ∞` and `|T n| ≤ C + A n / 4`, then the test
process tends to `0`. -/
lemma tendsto_subgaussianTest_zero_of_abs_sum_le {m : ℝ} {lam X : ℕ → Ω → ℝ} {ω : Ω} {C : ℝ}
    (hC : ∀ n, |∑ k ∈ range n, (lam k ω - m) * (X k ω - m)|
      ≤ C + 1 / 4 * ∑ k ∈ range n, (lam k ω - m) ^ 2)
    (hsum : ¬ Summable (fun n ↦ (lam n ω - m) ^ 2)) :
    Tendsto (fun n ↦ subgaussianTest m lam X n ω) atTop (𝓝 0) := by
  have hA : Tendsto (fun n ↦ ∑ k ∈ range n, (lam k ω - m) ^ 2) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n ↦ sq_nonneg _).1 hsum
  have hlim : Tendsto (fun n ↦ Real.exp (C - 1 / 4 * ∑ k ∈ range n, (lam k ω - m) ^ 2)) atTop
      (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h := tendsto_atBot_add_const_left atTop C
      (tendsto_neg_atTop_atBot.comp (hA.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4)))
    refine h.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n ↦ (Real.exp_pos _).le) fun n ↦ ?_
  rw [subgaussianTest_eq]
  refine Real.exp_le_exp.2 ?_
  linarith [(le_abs_self _).trans (hC n)]

/-- Pathwise: if `∑ (lam k - m) ^ 2 < ∞` and `T n = ∑_{k < n} (lam k - m) (X k - m)` converges,
then the test process converges to a positive limit. -/
lemma exists_tendsto_subgaussianTest_pos {m : ℝ} {lam X : ℕ → Ω → ℝ} {ω : Ω}
    (hsum : Summable (fun n ↦ (lam n ω - m) ^ 2)) {T : ℝ}
    (hT : Tendsto (fun n ↦ ∑ k ∈ range n, (lam k ω - m) * (X k ω - m)) atTop (𝓝 T)) :
    ∃ L, 0 < L ∧ Tendsto (fun n ↦ subgaussianTest m lam X n ω) atTop (𝓝 L) := by
  refine ⟨Real.exp (T - (∑' n, (lam n ω - m) ^ 2) / 2), Real.exp_pos _, ?_⟩
  simp_rw [subgaussianTest_eq]
  exact (Real.continuous_exp.tendsto _).comp
    (hT.sub (hsum.hasSum.tendsto_sum_nat.div_const 2))

variable {ℱ : Filtration ℕ mΩ} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} {m : ℝ} {lam X : ℕ → Ω → ℝ}

/-- **The plug-in sub-Gaussian test process is a supermartingale** under a `1`-sub-Gaussian null:
if the observations are i.i.d. along `ℱ` with a law `P` such that `x - m` is `1`-sub-Gaussian and
`lam` is adapted to `ℱ`, then `subgaussianTest m lam X` is a supermartingale. -/
lemma supermartingale_subgaussianTest (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam) :
    Supermartingale (subgaussianTest m lam X) ℱ P' := by
  have h := supermartingale_exp_sum_mul (Y := fun n ω ↦ X n ω - m) (w := fun n ω ↦ lam n ω - m)
    (c := 1) (fun n ↦ (hX n).sub_const m)
    (fun n ↦ indep_comap_comp (hindep n) (f := fun x ↦ x - m) (measurable_id.sub_const m))
    (fun n ↦ (hlaw n).hasSubgaussianMGF_comp hP) (fun n ↦ (hlam n).sub_const m) 1
  convert h using 2 with n
  ext ω
  rw [subgaussianTest_eq]
  congr 1
  push_cast
  ring

/-- The almost sure events used in the proof of the sub-Gaussian sum-of-squares criterion:
`T n = ∑_{k < n} (lam k - m) (X k - m)` converges on `{∑ (lam k - m) ^ 2 < ∞}`, and
`|T n| ≤ C + ε ∑_{k < n} (lam k - m) ^ 2` for every `ε > 0`. -/
lemma ae_sum_sq_subgaussian_events (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam) :
    ∀ᵐ ω ∂P', (Summable (fun n ↦ (lam n ω - m) ^ 2) →
        ∃ T, Tendsto (fun n ↦ ∑ k ∈ range n, (lam k ω - m) * (X k ω - m)) atTop (𝓝 T)) ∧
      ∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ range n, (lam k ω - m) * (X k ω - m)|
        ≤ C + ε * ∑ k ∈ range n, (lam k ω - m) ^ 2 := by
  have hY : ∀ n, Measurable[ℱ (n + 1)] (fun ω ↦ X n ω - m) := fun n ↦ (hX n).sub_const m
  have hi : ∀ n, Indep (MeasurableSpace.comap (fun ω ↦ X n ω - m) inferInstance) (ℱ n) P' :=
    fun n ↦ indep_comap_comp (hindep n) (f := fun x ↦ x - m) (measurable_id.sub_const m)
  have hs : ∀ n, HasSubgaussianMGF (fun ω ↦ X n ω - m) 1 P' :=
    fun n ↦ (hlaw n).hasSubgaussianMGF_comp hP
  have hw : Adapted ℱ (fun n ω ↦ lam n ω - m) := fun n ↦ (hlam n).sub_const m
  filter_upwards [ae_exists_tendsto_sum_mul hY hi hs hw, ae_forall_abs_sum_mul_le hY hi hs hw]
    with ω h1 h2
  exact ⟨h1, h2⟩

/-- **Divergence half of the sub-Gaussian criterion**: almost surely on
`{∑ (lam n - m) ^ 2 = ∞}`, the test process tends to `0`. -/
lemma ae_tendsto_subgaussianTest_zero_of_not_summable
    (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam) :
    ∀ᵐ ω ∂P', ¬ Summable (fun n ↦ (lam n ω - m) ^ 2) →
      Tendsto (fun n ↦ subgaussianTest m lam X n ω) atTop (𝓝 0) := by
  filter_upwards [ae_sum_sq_subgaussian_events hP hX hindep hlaw hlam] with ω ⟨_, h⟩ hsum
  obtain ⟨C, hC⟩ := h (1 / 4) (by norm_num)
  exact tendsto_subgaussianTest_zero_of_abs_sum_le hC hsum

/-- **Convergence half of the sub-Gaussian criterion**: almost surely on
`{∑ (lam n - m) ^ 2 < ∞}`, the test process converges to a positive limit. -/
lemma ae_exists_tendsto_subgaussianTest_pos_of_summable
    (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam) :
    ∀ᵐ ω ∂P', Summable (fun n ↦ (lam n ω - m) ^ 2) →
      ∃ L, 0 < L ∧ Tendsto (fun n ↦ subgaussianTest m lam X n ω) atTop (𝓝 L) := by
  filter_upwards [ae_sum_sq_subgaussian_events hP hX hindep hlaw hlam] with ω ⟨h, _⟩ hsum
  obtain ⟨T, hT⟩ := h hsum
  exact exists_tendsto_subgaussianTest_pos hsum hT

/-- **Sum-of-squares criterion for sub-Gaussian test processes, filtration form**
(`thm:sos_crit_subg_filtration`). Let `x - m` be `1`-sub-Gaussian under `P`, let the observations
be i.i.d. with law `P` along a filtration `ℱ` and `lam` be adapted to `ℱ`. Then the plug-in test
process converges almost surely to a random variable `M` such that, almost surely, `M = 0` iff
`∑ (lam n - m) ^ 2 = ∞`, and `M > 0` iff `∑ (lam n - m) ^ 2 < ∞`. -/
lemma sum_sq_criterion_subgaussian_of_indep (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam) :
    ∃ M : Ω → ℝ, (∀ᵐ ω ∂P', Tendsto (fun n ↦ subgaussianTest m lam X n ω) atTop (𝓝 (M ω))) ∧
      (∀ᵐ ω ∂P', M ω = 0 ↔ ¬ Summable (fun n ↦ (lam n ω - m) ^ 2)) ∧
      (∀ᵐ ω ∂P', 0 < M ω ↔ Summable (fun n ↦ (lam n ω - m) ^ 2)) := by
  have key : ∀ᵐ ω ∂P', ∃ L, Tendsto (fun n ↦ subgaussianTest m lam X n ω) atTop (𝓝 L) ∧
      (L = 0 ↔ ¬ Summable (fun n ↦ (lam n ω - m) ^ 2)) ∧
      (0 < L ↔ Summable (fun n ↦ (lam n ω - m) ^ 2)) := by
    filter_upwards [ae_tendsto_subgaussianTest_zero_of_not_summable hP hX hindep hlaw hlam,
      ae_exists_tendsto_subgaussianTest_pos_of_summable hP hX hindep hlaw hlam]
      with ω hdiv hconv
    by_cases hsum : Summable (fun n ↦ (lam n ω - m) ^ 2)
    · obtain ⟨L, hL, hT⟩ := hconv hsum
      exact ⟨L, hT, by simp [hL.ne', hsum], by simp [hL, hsum]⟩
    · exact ⟨0, hdiv hsum, by simp [hsum], by simp [hsum]⟩
  refine ⟨fun ω ↦ limUnder atTop (fun n ↦ subgaussianTest m lam X n ω), ?_, ?_, ?_⟩ <;>
    filter_upwards [key] with ω ⟨L, hL, h1, h2⟩
  · rwa [hL.limUnder_eq]
  · rwa [hL.limUnder_eq]
  · rwa [hL.limUnder_eq]

/-- **Constant alternatives are rejected.** If `x - m` is `1`-sub-Gaussian under `P`, then on
i.i.d. observations with law `P`, the test process of the constant alternative `l ≠ m` tends to `0`
almost surely. -/
lemma ae_tendsto_subgaussianTest_zero (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P)
    (hXm : ∀ n, Measurable (X n)) (hiid : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P')
    {l : ℝ} (hl : l ≠ m) :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ subgaussianTest m (fun _ _ ↦ l) X n ω) atTop (𝓝 0) := by
  have h := ae_tendsto_subgaussianTest_zero_of_not_summable (ℱ := pastFiltration X hXm)
    (lam := fun _ _ ↦ l) hP (measurable_pastFiltration_succ X hXm)
    (indep_pastFiltration hXm hiid) hlaw (fun _ ↦ measurable_const)
  have hns : ¬ Summable (fun _ : ℕ ↦ (l - m) ^ 2) := by
    rw [summable_const_iff]
    exact pow_ne_zero 2 (sub_ne_zero.2 hl)
  filter_upwards [h] with ω hω using hω hns

end Learning.Betting
