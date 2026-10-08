/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Null
public import Wang2026Almost.LeanMachineLearning.Betting.PastFiltration
public import Wang2026Almost.LeanMachineLearning.Betting.WealthLemmas
public import Wang2026Almost.Mathlib.Analysis.SpecialFunctions.Log.OneAdd
public import Wang2026Almost.Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Wang2026Almost.Mathlib.Probability.Martingale.SubgaussianSum
public import Wang2026Almost.Mathlib.Probability.SumBigOmegaInProb
public import Mathlib.Probability.HasLaw

/-!
# The sum-of-squares criterion for null bankruptcy

Let `P` be a non-degenerate distribution on `[0, 1]` with mean `m`, and let the observations `X`
be i.i.d. with law `P` along a filtration `ℱ`: `X n` is `ℱ (n + 1)`-measurable, independent of
`ℱ n`, with law `P`. Let `lam` be a betting strategy adapted to `ℱ` (a predictable strategy) with
values in `fractionRange m` almost surely. Then the wealth `wealth m lam X n` converges almost
surely, to `0` exactly on the paths where `∑ lam n ^ 2 = ∞` or where an all-in bet loses the whole
wealth (Theorem 2.1 of Wang, Agrawal, Ramdas 2026, in filtration form).

The proof does not use the martingale convergence and divergence theorems of the paper. With
`T n = ∑_{k < n} lam k (X k - m)` and `A n = ∑_{k < n} lam k ^ 2`:
* on `{A ∞ = ∞}`, `log (1 + x) ≤ x - c x²` gives `wealth n ≤ exp (T n - c ∑_{k < n} x_k²)`, and
  the bounds `|T n| ≤ C + ε A n` and `|∑_{k < n} lam k ^ 2 ((X k - m)² - σ²)| ≤ C + ε A n` of the
  conditionally sub-Gaussian sums give `wealth n ≤ exp (C - c σ² A n / 4) → 0`;
* on `{A ∞ < ∞}` with no all-in loss, `T n` converges and `|log (1 + x) - x| ≤ x²` for small `x`,
  so the log-wealth converges.

## Main statements

* `supermartingale_wealth`: the wealth of a predictable strategy is a supermartingale under the
  null, hence converges almost surely (`ae_exists_tendsto_wealth`);
* `ae_tendsto_wealth_zero_of_not_summable`: almost surely, the wealth tends to `0` on
  `{∑ lam n ^ 2 = ∞}`;
* `ae_exists_tendsto_wealth_pos_of_summable`: almost surely, the wealth tends to a positive limit
  on `{∑ lam n ^ 2 < ∞}` when no bet loses the whole wealth;
* `sum_sq_criterion_of_indep`: the sum-of-squares criterion (Theorem 2.1) in filtration form;
* `tendsto_wealth_zero_of_isBigOmega_of_indep`: the `n^{-1/2}` criterion (Corollary 2.4) in
  filtration form;
* `ae_tendsto_fixedWealth_zero`: the wealth of a nonzero constant bet tends to `0` almost surely
  on i.i.d. observations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal NNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P' : Measure Ω}
  {μ : Measure 𝓧} {Y : Ω → 𝓧}

/-- A function `f ∘ Y` of a random variable `Y` with law `μ` is sub-Gaussian if `f` is
sub-Gaussian under `μ`. -/
lemma HasLaw.hasSubgaussianMGF_comp (hY : HasLaw Y μ P') {f : 𝓧 → ℝ} {c : ℝ≥0}
    (hf : HasSubgaussianMGF f c μ) : HasSubgaussianMGF (fun ω ↦ f (Y ω)) c P' :=
  HasSubgaussianMGF.of_map hY.aemeasurable (hY.map_eq ▸ hf)

/-- If `Y` is independent of a `σ`-algebra `m'`, so is every measurable function of `Y`. -/
lemma indep_comap_comp {m' : MeasurableSpace Ω}
    (h : Indep (MeasurableSpace.comap Y m𝓧) m' P') {f : 𝓧 → ℝ} (hf : Measurable f) :
    Indep (MeasurableSpace.comap (fun ω ↦ f (Y ω)) inferInstance) m' P' :=
  indep_of_indep_of_le_left h (hf.comp (comap_measurable Y)).comap_le

end ProbabilityTheory

namespace Learning.Betting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Pathwise

/-- `1 + x ≤ exp (x - x² / (2 (1 + M)))` for `-1 ≤ x ≤ M`, `M ≥ 0`. -/
lemma one_add_le_exp_sub_mul_sq {x M : ℝ} (hM : 0 ≤ M) (hx1 : -1 ≤ x) (hxM : x ≤ M) :
    1 + x ≤ Real.exp (x - x ^ 2 / (2 * (1 + M))) := by
  rcases hx1.eq_or_lt with h | h
  · rw [← h]
    norm_num
    positivity
  · calc 1 + x = Real.exp (Real.log (1 + x)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.2 (Real.log_one_add_le_sub_mul_sq hM h hxM)

/-- `|log (1 + x) - x| ≤ x²` for `|x| ≤ 1 / 2`. -/
lemma abs_log_one_add_sub_self_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have h1 : 0 < 1 + x := by linarith [neg_abs_le x]
  have h2 := Real.sub_sq_le_log_one_add hx
  have h3 := Real.log_le_sub_one_of_pos h1
  rw [abs_le]
  constructor <;> linarith

/-- A bet fraction in `fractionRange m` has absolute value at most `1 / m + 1 / (1 - m)`. -/
lemma abs_le_of_mem_fractionRange {m l : ℝ} (hm : m ∈ Set.Ioo 0 1) (hl : l ∈ fractionRange m) :
    |l| ≤ 1 / m + 1 / (1 - m) := by
  have h1 : 0 < 1 / m := one_div_pos.2 hm.1
  have h2 : 0 < 1 / (1 - m) := one_div_pos.2 (sub_pos.2 hm.2)
  have h3 : -1 / (1 - m) = -(1 / (1 - m)) := neg_div _ _
  rw [abs_le]
  constructor <;> linarith [hl.1, hl.2]

/-- **Bankruptcy on the divergence event, pathwise.** If the bets are in `fractionRange m`, the
observations in `[0, 1]`, `σ2 > 0`, `∑ lam k ^ 2 = ∞` and the sums `∑_{k < n} lam k (X k - m)`
and `∑_{k < n} lam k ^ 2 ((X k - m)² - σ2)` are `o(∑_{k < n} lam k ^ 2)` in the sense of the
bounds `hT`, `hU`, then the wealth tends to `0`. -/
lemma tendsto_wealth_zero_of_forall_abs_sum_le {m σ2 : ℝ} {lam X : ℕ → Ω → ℝ} {ω : Ω}
    (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2) (hlam : ∀ n, lam n ω ∈ fractionRange m)
    (hX : ∀ n, X n ω ∈ Set.Icc 0 1)
    (hT : ∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ range n, lam k ω * (X k ω - m)|
      ≤ C + ε * ∑ k ∈ range n, lam k ω ^ 2)
    (hU : ∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ range n, lam k ω ^ 2 * ((X k ω - m) ^ 2 - σ2)|
      ≤ C + ε * ∑ k ∈ range n, (lam k ω ^ 2) ^ 2)
    (hsum : ¬ Summable (fun n ↦ lam n ω ^ 2)) :
    Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0) := by
  set L := 1 / m + 1 / (1 - m) with hL_def
  have hL : 0 ≤ L := by
    have := one_div_pos.2 hm.1
    have := one_div_pos.2 (sub_pos.2 hm.2)
    positivity
  have hlamL : ∀ k, |lam k ω| ≤ L := fun k ↦ abs_le_of_mem_fractionRange hm (hlam k)
  have hY : ∀ k, |X k ω - m| ≤ 1 := fun k ↦ by
    rw [abs_le]
    constructor <;> linarith [(hX k).1, (hX k).2, hm.1, hm.2]
  set c := 1 / (2 * (1 + L)) with hc_def
  have hc : 0 < c := by positivity
  set A : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, lam k ω ^ 2 with hA_def
  set T : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, lam k ω * (X k ω - m) with hT_def
  set U : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, lam k ω ^ 2 * ((X k ω - m) ^ 2 - σ2) with hU_def
  -- the pathwise upper bound on the wealth
  have hfac : ∀ k, 1 + lam k ω * (X k ω - m)
      ≤ Real.exp (lam k ω * (X k ω - m) - c * (lam k ω ^ 2 * (X k ω - m) ^ 2)) := by
    intro k
    have h1 : -1 ≤ lam k ω * (X k ω - m) := by
      linarith [one_add_mul_sub_nonneg hm (hlam k) (hX k)]
    have h2 : lam k ω * (X k ω - m) ≤ L := by
      calc lam k ω * (X k ω - m) ≤ |lam k ω * (X k ω - m)| := le_abs_self _
        _ = |lam k ω| * |X k ω - m| := abs_mul _ _
        _ ≤ L * 1 := mul_le_mul (hlamL k) (hY k) (abs_nonneg _) hL
        _ = L := mul_one L
    convert one_add_le_exp_sub_mul_sq hL h1 h2 using 2
    rw [hc_def, mul_pow]
    ring
  have hW : ∀ n, wealth m lam X n ω ≤ Real.exp (T n - c * (σ2 * A n + U n)) := by
    intro n
    have hsq : σ2 * A n + U n = ∑ k ∈ range n, lam k ω ^ 2 * (X k ω - m) ^ 2 := by
      simp only [hA_def, hU_def, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun k _ ↦ by ring
    rw [hsq, mul_sum, ← sum_sub_distrib, Real.exp_sum]
    exact prod_le_prod₀ (fun k _ ↦ one_add_mul_sub_nonneg hm (hlam k) (hX k)) fun k _ ↦ hfac k
  -- the bounds on the martingale parts
  obtain ⟨C1, hC1⟩ := hT (c * σ2 / 4) (by positivity)
  obtain ⟨C2, hC2⟩ := hU (σ2 / (2 * (L ^ 2 + 1))) (by positivity)
  have hbound : ∀ n, T n - c * (σ2 * A n + U n) ≤ C1 + c * C2 - c * σ2 / 4 * A n := by
    intro n
    have h1 : T n ≤ C1 + c * σ2 / 4 * A n := (le_abs_self _).trans (hC1 n)
    have h4 : ∑ k ∈ range n, (lam k ω ^ 2) ^ 2 ≤ (L ^ 2 + 1) * A n := by
      rw [hA_def, mul_sum]
      refine sum_le_sum fun k _ ↦ ?_
      have : lam k ω ^ 2 ≤ L ^ 2 + 1 := by
        have := sq_le_sq.2 ((hlamL k).trans (le_abs_self L))
        linarith
      rw [sq]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have h2 : -U n ≤ C2 + σ2 / 2 * A n := by
      have h5 : σ2 / (2 * (L ^ 2 + 1)) * ∑ k ∈ range n, (lam k ω ^ 2) ^ 2 ≤ σ2 / 2 * A n := by
        calc σ2 / (2 * (L ^ 2 + 1)) * ∑ k ∈ range n, (lam k ω ^ 2) ^ 2
            ≤ σ2 / (2 * (L ^ 2 + 1)) * ((L ^ 2 + 1) * A n) := by gcongr
          _ = σ2 / 2 * A n := by field_simp
      linarith [neg_le_abs (U n), hC2 n]
    nlinarith [mul_le_mul_of_nonneg_left h2 hc.le]
  -- conclusion
  have hA : Tendsto A atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n ↦ sq_nonneg _).1 hsum
  have hlim : Tendsto (fun n ↦ Real.exp (C1 + c * C2 - c * σ2 / 4 * A n)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h := tendsto_atBot_add_const_left atTop (C1 + c * C2)
      (tendsto_neg_atTop_atBot.comp (hA.const_mul_atTop (by positivity : 0 < c * σ2 / 4)))
    refine h.congr fun n ↦ ?_
    simp only [Function.comp_apply]
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n ↦ wealth_nonneg hm (fun k _ ↦ hlam k) (fun k _ ↦ hX k)) fun n ↦ ?_
  exact (hW n).trans (Real.exp_le_exp.2 (hbound n))

/-- **Non-bankruptcy on the convergence event, pathwise.** If no bet loses the whole wealth,
`|X k - m| ≤ 1`, `∑ lam k ^ 2 < ∞` and the sums `∑_{k < n} lam k (X k - m)` converge, then the
wealth converges to a positive limit. -/
lemma exists_tendsto_wealth_pos {m : ℝ} {lam X : ℕ → Ω → ℝ} {ω : Ω}
    (hpos : ∀ n, -1 < lam n ω * (X n ω - m)) (hX : ∀ n, |X n ω - m| ≤ 1)
    (hsum : Summable (fun n ↦ lam n ω ^ 2)) {T : ℝ}
    (hT : Tendsto (fun n ↦ ∑ k ∈ range n, lam k ω * (X k ω - m)) atTop (𝓝 T)) :
    ∃ L, 0 < L ∧ Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 L) := by
  set x : ℕ → ℝ := fun k ↦ lam k ω * (X k ω - m) with hx_def
  have hx2 : ∀ k, x k ^ 2 ≤ lam k ω ^ 2 := fun k ↦ by
    have h : (X k ω - m) ^ 2 ≤ 1 := by
      have := sq_le_sq.2 ((hX k).trans_eq (abs_one).symm)
      simpa using this
    calc x k ^ 2 = lam k ω ^ 2 * (X k ω - m) ^ 2 := mul_pow _ _ _
      _ ≤ lam k ω ^ 2 * 1 := mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = lam k ω ^ 2 := mul_one _
  have hsmall : ∀ᶠ k in atTop, |x k| ≤ 1 / 2 := by
    filter_upwards [hsum.tendsto_atTop_zero.eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with k hk
    have h : x k ^ 2 ≤ (1 / 2) ^ 2 := by linarith [hx2 k]
    exact (sq_le_sq.1 h).trans_eq (abs_of_pos (by norm_num))
  set g : ℕ → ℝ := fun k ↦ Real.log (1 + x k) - x k with hg_def
  have hg : Summable g := by
    refine Summable.of_norm_bounded_eventually hsum ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hsmall] with k hk
    exact (abs_log_one_add_sub_self_le hk).trans (hx2 k)
  have hW : ∀ n, wealth m lam X n ω
      = Real.exp (∑ k ∈ range n, x k + ∑ k ∈ range n, g k) := by
    intro n
    rw [← sum_add_distrib, Real.exp_sum]
    refine prod_congr rfl fun k _ ↦ ?_
    rw [hg_def, add_sub_cancel, Real.exp_log (by linarith [hpos k])]
  refine ⟨Real.exp (T + ∑' k, g k), Real.exp_pos _, ?_⟩
  simp_rw [hW]
  exact (Real.continuous_exp.tendsto _).comp (hT.add hg.hasSum.tendsto_sum_nat)

end Pathwise

section Indep

variable {ℱ : Filtration ℕ mΩ} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ} {lam X : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P'] [IsProbabilityMeasure P] in
/-- An observation with law `P` on `[0, 1]` is in `[0, 1]` almost surely. -/
private lemma ae_mem_Icc_of_hasLaw {Y : Ω → ℝ} (hY : HasLaw Y P P')
    (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) : ∀ᵐ ω ∂P', Y ω ∈ Set.Icc 0 1 := by
  rw [← hY.map_eq] at hP
  exact ae_of_ae_map hY.aemeasurable hP

/-- **The wealth is a supermartingale** under the null: if the observations are i.i.d. along `ℱ`
with a law `P` on `[0, 1]` with mean `m ∈ (0, 1)` and the strategy `lam` is adapted to `ℱ` with
values in `fractionRange m` almost surely, then the wealth is a supermartingale (in fact a
martingale). -/
lemma supermartingale_wealth (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hm01 : m ∈ Set.Ioo 0 1) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam)
    (hlam_mem : ∀ n, ∀ᵐ ω ∂P', lam n ω ∈ fractionRange m) :
    Supermartingale (wealth m lam X) ℱ P' := by
  have hXm : ∀ n, Measurable (X n) := fun n ↦ (hX n).mono (ℱ.le _) le_rfl
  have hall : ∀ᵐ ω ∂P', (∀ n, lam n ω ∈ fractionRange m) ∧ ∀ n, X n ω ∈ Set.Icc 0 1 :=
    (ae_all_iff.2 hlam_mem).and (ae_all_iff.2 fun n ↦ ae_mem_Icc_of_hasLaw (hlaw n) hP)
  have hW_nonneg : ∀ n, 0 ≤ᵐ[P'] wealth m lam X n := fun n ↦ by
    filter_upwards [hall] with ω hω
    exact wealth_nonneg hm01 (fun k _ ↦ hω.1 k) (fun k _ ↦ hω.2 k)
  have hW0 : wealth m lam X 0 = fun _ ↦ 1 := funext fun ω ↦ wealth_zero m lam X ω
  have hint : Integrable (fun x : ℝ ↦ x) P := (memLp_two_id_of_mem_Icc hP).integrable one_le_two
  refine supermartingale_of_lintegral_le (adapted_wealth hlam hX) hW_nonneg
    (by rw [hW0]; exact integrable_const _) (Z := fun n ω ↦ (wealth m lam X n ω, lam n ω))
    (Y := X) (fun n ↦ (adapted_wealth hlam hX n).prodMk (hlam n)) hXm hindep
    (Φ := fun _ p ↦ ENNReal.ofReal (p.1.1 * (1 + p.1.2 * (p.2 - m)))) (fun n ↦ by fun_prop)
    (fun n ↦ ae_of_all _ fun ω ↦ by simp only [wealth_succ]) fun n ↦ ?_
  filter_upwards [hW_nonneg n, hlam_mem n] with ω hω hlω
  rw [(hlaw n).map_eq]
  set w := wealth m lam X n ω
  have hfun : (fun x ↦ w * (1 + lam n ω * (x - m)))
      = fun x ↦ w * (1 - lam n ω * m) + w * lam n ω * x := by
    ext x
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rw [hfun, integral_add (integrable_const _) (hint.const_mul _), integral_const,
      integral_const_mul, hm]
    simp only [probReal_univ, one_smul]
    ring
  · exact ((integrable_const _).add ((hint.sub (integrable_const _)).const_mul _)).const_mul _
  · filter_upwards [hP] with x hx
    exact mul_nonneg hω (one_add_mul_sub_nonneg hm01 hlω hx)

/-- The wealth of a predictable strategy converges almost surely under the null (it is a
nonnegative supermartingale). -/
lemma ae_exists_tendsto_wealth (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hm01 : m ∈ Set.Ioo 0 1) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam)
    (hlam_mem : ∀ n, ∀ᵐ ω ∂P', lam n ω ∈ fractionRange m) :
    ∀ᵐ ω ∂P', ∃ L, Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 L) := by
  have hall : ∀ᵐ ω ∂P', (∀ n, lam n ω ∈ fractionRange m) ∧ ∀ n, X n ω ∈ Set.Icc 0 1 :=
    (ae_all_iff.2 hlam_mem).and (ae_all_iff.2 fun n ↦ ae_mem_Icc_of_hasLaw (hlaw n) hP)
  obtain ⟨L, -, hL, -⟩ := (supermartingale_wealth hP hm hm01 hX hindep hlaw hlam
    hlam_mem).exists_ae_tendsto_of_nonneg fun n ↦ by
      filter_upwards [hall] with ω hω
      exact wealth_nonneg hm01 (fun k _ ↦ hω.1 k) (fun k _ ↦ hω.2 k)
  filter_upwards [hL] with ω hω using ⟨L ω, hω⟩

/-- Under a null distribution on `[0, 1]` with mean `m`, `x - m` is `1 / 4`-sub-Gaussian
(Hoeffding's lemma). -/
lemma hasSubgaussianMGF_sub_of_mem_Icc (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) :
    HasSubgaussianMGF (fun x ↦ x - m) (1 / 4) P := by
  have hint : Integrable (fun x : ℝ ↦ x) P := (memLp_two_id_of_mem_Icc hP).integrable one_le_two
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := P) (X := fun x ↦ x - m) (a := -m)
    (b := 1 - m) (by fun_prop) ?_ ?_
  · have hc : (‖(1 - m) - (-m)‖₊ / 2) ^ 2 = 1 / 4 := by norm_num
    rwa [hc] at h
  · filter_upwards [hP] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [integral_sub hint (integrable_const _), hm]
    simp

/-- Under a null distribution on `[0, 1]` with mean `m ∈ [0, 1]`, `(x - m)² - Var[id; P]` is
`1 / 4`-sub-Gaussian (Hoeffding's lemma). -/
lemma hasSubgaussianMGF_sq_sub_variance (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hm01 : m ∈ Set.Icc 0 1) :
    HasSubgaussianMGF (fun x ↦ (x - m) ^ 2 - Var[id; P]) (1 / 4) P := by
  have hb : ∀ᵐ x ∂P, (x - m) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hP] with x hx
    refine ⟨sq_nonneg _, ?_⟩
    have h : |x - m| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hm01.1, hm01.2]
    simpa using sq_le_sq.2 (h.trans_eq abs_one.symm)
  have hint : Integrable (fun x : ℝ ↦ (x - m) ^ 2) P := Integrable.of_mem_Icc 0 1 (by fun_prop) hb
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := P) (X := fun x ↦ (x - m) ^ 2 - Var[id; P]) (a := -Var[id; P]) (b := 1 - Var[id; P])
    (by fun_prop) ?_ ?_
  · have hc : (‖(1 - Var[id; P]) - (-Var[id; P])‖₊ / 2) ^ 2 = 1 / 4 := by norm_num
    rwa [hc] at h
  · filter_upwards [hb] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [integral_sub hint (integrable_const _), variance_eq_integral aemeasurable_id]
    simp [hm]

/-- The almost sure events used in the proof of the sum-of-squares criterion: the sums
`∑ lam k (X k - m)` and `∑ lam k ^ 2 ((X k - m)² - σ²)` are small compared to the sums of the
squared weights, and `∑ lam k (X k - m)` converges on `{∑ lam k ^ 2 < ∞}`. -/
lemma ae_sum_sq_events (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hm01 : m ∈ Set.Icc 0 1) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam) :
    ∀ᵐ ω ∂P', (∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ range n, lam k ω * (X k ω - m)|
        ≤ C + ε * ∑ k ∈ range n, lam k ω ^ 2) ∧
      (∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ range n, lam k ω ^ 2 * ((X k ω - m) ^ 2 - Var[id; P])|
        ≤ C + ε * ∑ k ∈ range n, (lam k ω ^ 2) ^ 2) ∧
      (Summable (fun n ↦ lam n ω ^ 2) →
        ∃ T, Tendsto (fun n ↦ ∑ k ∈ range n, lam k ω * (X k ω - m)) atTop (𝓝 T)) := by
  have hY1 : ∀ n, Measurable[ℱ (n + 1)] (fun ω ↦ X n ω - m) := fun n ↦ (hX n).sub_const m
  have hY2 : ∀ n, Measurable[ℱ (n + 1)] (fun ω ↦ (X n ω - m) ^ 2 - Var[id; P]) :=
    fun n ↦ ((hX n).sub_const m).pow_const 2 |>.sub_const _
  have hi1 : ∀ n, Indep (MeasurableSpace.comap (fun ω ↦ X n ω - m) inferInstance) (ℱ n) P' :=
    fun n ↦ indep_comap_comp (hindep n) (measurable_id.sub_const m)
  have hi2 : ∀ n, Indep (MeasurableSpace.comap (fun ω ↦ (X n ω - m) ^ 2 - Var[id; P])
      inferInstance) (ℱ n) P' :=
    fun n ↦ indep_comap_comp (hindep n) (f := fun x ↦ (x - m) ^ 2 - Var[id; P]) (by fun_prop)
  have hs1 := fun n ↦ (hlaw n).hasSubgaussianMGF_comp (hasSubgaussianMGF_sub_of_mem_Icc hP hm)
  have hs2 := fun n ↦ (hlaw n).hasSubgaussianMGF_comp
    (hasSubgaussianMGF_sq_sub_variance hP hm hm01)
  have hw2 : Adapted ℱ (fun n ω ↦ lam n ω ^ 2) := fun n ↦ (hlam n).pow_const 2
  filter_upwards [ae_forall_abs_sum_mul_le hY1 hi1 hs1 hlam,
    ae_forall_abs_sum_mul_le hY2 hi2 hs2 hw2, ae_exists_tendsto_sum_mul hY1 hi1 hs1 hlam]
    with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **Bankruptcy on the divergence event** (`lem:sos_diverge`). Under a non-degenerate null
distribution, for a predictable strategy with values in `fractionRange m` almost surely, the
wealth tends to `0` almost surely on `{∑ lam n ^ 2 = ∞}`. -/
lemma ae_tendsto_wealth_zero_of_not_summable (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hnd : P ≠ Measure.dirac m) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam)
    (hlam_mem : ∀ n, ∀ᵐ ω ∂P', lam n ω ∈ fractionRange m) :
    ∀ᵐ ω ∂P', ¬ Summable (fun n ↦ lam n ω ^ 2) →
      Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0) := by
  have hm01 := mem_Ioo_of_ne_dirac hP hm hnd
  filter_upwards [ae_all_iff.2 hlam_mem, ae_all_iff.2 fun n ↦ ae_mem_Icc_of_hasLaw (hlaw n) hP,
    ae_sum_sq_events hP hm (Set.Ioo_subset_Icc_self hm01) hX hindep hlaw hlam]
    with ω h1 h2 ⟨h3, h4, _⟩ hsum
  exact tendsto_wealth_zero_of_forall_abs_sum_le hm01 (variance_pos_of_ne_dirac hP hm hnd) h1 h2
    h3 h4 hsum

/-- **Non-bankruptcy on the convergence event** (`lem:sos_converge`). Under a null distribution
on `[0, 1]`, for a predictable strategy, almost surely on `{∑ lam n ^ 2 < ∞}`, if no bet loses the
whole wealth, then the wealth converges to a positive limit. The bets need not be in
`fractionRange m`. -/
lemma ae_exists_tendsto_wealth_pos_of_summable (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hm01 : m ∈ Set.Icc 0 1) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam) :
    ∀ᵐ ω ∂P', Summable (fun n ↦ lam n ω ^ 2) → (∀ n, -1 < lam n ω * (X n ω - m)) →
      ∃ L, 0 < L ∧ Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 L) := by
  filter_upwards [ae_all_iff.2 fun n ↦ ae_mem_Icc_of_hasLaw (hlaw n) hP,
    ae_sum_sq_events hP hm hm01 hX hindep hlaw hlam] with ω h2 ⟨_, _, h5⟩ hsum hpos
  obtain ⟨T, hT⟩ := h5 hsum
  refine exists_tendsto_wealth_pos hpos (fun n ↦ ?_) hsum hT
  rw [abs_le]
  constructor <;> linarith [(h2 n).1, (h2 n).2, hm01.1, hm01.2]

/-- **Sum-of-squares criterion, filtration form** (`thm:sos_crit_filtration`). Let `P` be a
non-degenerate distribution on `[0, 1]` with mean `m`, let the observations be i.i.d. with law `P`
along a filtration `ℱ` and `lam` be adapted to `ℱ` with values in `fractionRange m` almost surely.
Then the wealth converges almost surely to a random variable `W` such that, almost surely,
`W = 0` iff `∑ lam n ^ 2 = ∞` or some bet loses the whole wealth, and `W > 0` iff
`∑ lam n ^ 2 < ∞` and no bet loses the whole wealth. -/
lemma sum_sq_criterion_of_indep (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hnd : P ≠ Measure.dirac m) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam)
    (hlam_mem : ∀ n, ∀ᵐ ω ∂P', lam n ω ∈ fractionRange m) :
    ∃ W : Ω → ℝ, (∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 (W ω))) ∧
      (∀ᵐ ω ∂P', W ω = 0 ↔ ¬ Summable (fun n ↦ lam n ω ^ 2) ∨ ∃ n, lam n ω * (X n ω - m) = -1) ∧
      (∀ᵐ ω ∂P', 0 < W ω ↔ Summable (fun n ↦ lam n ω ^ 2) ∧ ∀ n, -1 < lam n ω * (X n ω - m)) := by
  have hm01 := mem_Ioo_of_ne_dirac hP hm hnd
  have key : ∀ᵐ ω ∂P', ∃ L, Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 L) ∧
      (L = 0 ↔ ¬ Summable (fun n ↦ lam n ω ^ 2) ∨ ∃ n, lam n ω * (X n ω - m) = -1) ∧
      (0 < L ↔ Summable (fun n ↦ lam n ω ^ 2) ∧ ∀ n, -1 < lam n ω * (X n ω - m)) := by
    filter_upwards [ae_all_iff.2 hlam_mem, ae_all_iff.2 fun n ↦ ae_mem_Icc_of_hasLaw (hlaw n) hP,
      ae_tendsto_wealth_zero_of_not_summable hP hm hnd hX hindep hlaw hlam hlam_mem,
      ae_exists_tendsto_wealth_pos_of_summable hP hm (Set.Ioo_subset_Icc_self hm01) hX hindep
        hlaw hlam] with ω h1 h2 hdiv hconv
    have hge : ∀ n, -1 ≤ lam n ω * (X n ω - m) := fun n ↦ by
      linarith [one_add_mul_sub_nonneg hm01 (h1 n) (h2 n)]
    by_cases hloss : ∃ n, lam n ω * (X n ω - m) = -1
    · obtain ⟨n, hn⟩ := hloss
      refine ⟨0, tendsto_atTop_of_eventually_const (i₀ := n + 1) fun k hk ↦ ?_,
        by simp only [true_iff]; exact Or.inr ⟨n, hn⟩, ?_⟩
      · exact prod_eq_zero (i := n) (mem_range.2 (by omega)) (by rw [hn]; ring)
      · simp only [lt_self_iff_false, false_iff, not_and, not_forall, not_lt]
        exact fun _ ↦ ⟨n, hn.le⟩
    · simp only [not_exists] at hloss
      have hgt : ∀ n, -1 < lam n ω * (X n ω - m) := fun n ↦ (hge n).lt_of_ne (Ne.symm (hloss n))
      by_cases hsum : Summable (fun n ↦ lam n ω ^ 2)
      · obtain ⟨L, hL, hT⟩ := hconv hsum hgt
        refine ⟨L, hT, ?_, ?_⟩
        · simp only [hL.ne', false_iff, not_or, not_not, not_exists]
          exact ⟨hsum, hloss⟩
        · simp only [hL, true_iff]
          exact ⟨hsum, hgt⟩
      · refine ⟨0, hdiv hsum, by simp [hsum], ?_⟩
        simp [hsum]
  refine ⟨fun ω ↦ limUnder atTop (fun n ↦ wealth m lam X n ω), ?_, ?_, ?_⟩ <;>
    filter_upwards [key] with ω ⟨L, hL, h1, h2⟩
  · rwa [hL.limUnder_eq]
  · rwa [hL.limUnder_eq]
  · rwa [hL.limUnder_eq]

/-- `(x ^ (-1 / 2)) ^ 2 = x⁻¹` for `x ≥ 0`. -/
lemma rpow_neg_one_half_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ (-1 / 2 : ℝ)) ^ 2 = x⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num [Real.rpow_neg_one]

/-- **The `n^{-1/2}` criterion, filtration form** (`cor:sq_crit_filtration`). In the setting of
`sum_sq_criterion_of_indep`, if `lam n = Ω_p(n^{-1/2})` or `lam n = Ω_{a.s.}((n log n)^{-1/2})`,
then the wealth converges to `0` almost surely. -/
lemma tendsto_wealth_zero_of_isBigOmega_of_indep (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hnd : P ≠ Measure.dirac m) (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hlam : Adapted ℱ lam)
    (hlam_mem : ∀ n, ∀ᵐ ω ∂P', lam n ω ∈ fractionRange m)
    (hrate : IsBigOmegaInProb P' lam (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) ∨
      IsBigOmegaAE P' lam (fun n ↦ ((n : ℝ) * Real.log n) ^ (-1 / 2 : ℝ))) :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0) := by
  have hns : ∀ᵐ ω ∂P', ¬ Summable (fun n ↦ lam n ω ^ 2) := by
    rcases hrate with h | h
    · have h2 := h.sq (Eventually.of_forall fun n ↦ by positivity)
      have h3 : IsBigOmegaInProb P' (fun n ω ↦ lam n ω ^ 2) (fun n ↦ (n : ℝ)⁻¹) :=
        h2.mono one_pos (Eventually.of_forall fun n ↦ by
          rw [one_mul, rpow_neg_one_half_sq (Nat.cast_nonneg n)])
      have hmeas : ∀ n, Measurable (lam n) := fun n ↦ (hlam n).mono (ℱ.le n) le_rfl
      exact ae_not_summable_of_isBigOmegaInProb (fun n ↦ ((hmeas n).pow_const 2).aemeasurable)
        (fun n ↦ ae_of_all _ fun ω ↦ sq_nonneg _) (fun n ↦ by positivity)
        Real.not_summable_natCast_inv h3
    · filter_upwards [h] with ω hω hsum
      have h2 : (fun n : ℕ ↦ ((n : ℝ) * Real.log n)⁻¹) =O[atTop] (fun n ↦ lam n ω ^ 2) :=
        (hω.pow 2).congr_left fun n ↦
          rpow_neg_one_half_sq (mul_nonneg (Nat.cast_nonneg n) (Real.log_natCast_nonneg n))
      exact Real.not_summable_inv_mul_log (summable_of_isBigO_nat hsum h2)
  filter_upwards [hns, ae_tendsto_wealth_zero_of_not_summable hP hm hnd hX hindep hlaw hlam
    hlam_mem] with ω h1 h2 using h2 h1

/-- **Constant bets go bankrupt.** Under a non-degenerate null distribution `P`, on i.i.d.
observations with law `P`, the wealth of the constant bet `l ∈ fractionRange m`, `l ≠ 0`, tends to
`0` almost surely. -/
lemma ae_tendsto_fixedWealth_zero (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hnd : P ≠ Measure.dirac m) (hXm : ∀ n, Measurable (X n)) (hiid : iIndepFun X P')
    (hlaw : ∀ n, HasLaw (X n) P P') {l : ℝ} (hl : l ∈ fractionRange m) (hl0 : l ≠ 0) :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ fixedWealth m l X n ω) atTop (𝓝 0) := by
  have h := ae_tendsto_wealth_zero_of_not_summable (ℱ := pastFiltration X hXm) (lam := fun _ _ ↦ l)
    hP hm hnd (measurable_pastFiltration_succ X hXm) (indep_pastFiltration hXm hiid) hlaw
    (fun _ ↦ measurable_const) (fun _ ↦ ae_of_all _ fun _ ↦ hl)
  have hns : ¬ Summable (fun _ : ℕ ↦ l ^ 2) := by
    rw [summable_const_iff]
    exact pow_ne_zero 2 hl0
  filter_upwards [h] with ω hω using hω hns

end Indep

end Learning.Betting
