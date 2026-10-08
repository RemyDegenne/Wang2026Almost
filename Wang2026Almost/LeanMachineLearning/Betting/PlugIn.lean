/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.PastFiltration
public import Wang2026Almost.LeanMachineLearning.Betting.SumSquares
public import Wang2026Almost.LeanMachineLearning.Betting.GoodEvent
public import Wang2026Almost.LeanMachineLearning.Betting.WealthLemmas

/-!
# The `n^{-1/2}` criterion for plug-in strategies

The paper's strategies are *predictable plug-in* strategies: each bet fraction `lam n` is a
measurable function of the first `n` observations (`IsPlugIn X lam`). For i.i.d. observations they
are predictable for the past filtration of the observations, along which the observations are
i.i.d., so the general criteria apply.

## Main statements

* `tendsto_wealth_zero_of_isBigOmega_of_isPlugIn`: the `n^{-1/2}` criterion (Corollary 2.4) for
  plug-in strategies on i.i.d. observations;
* `tendsto_wealth_zero_of_isBigOmegaAE_of_eventually_mem`: the almost sure branch of the
  criterion for plug-in strategies whose bet fractions are only eventually in `fractionRange m`
  (restart the strategy at a deterministic time and project it onto the range);
* `ae_forall_mem_Icc_of_hasLaw`: observations with a law on `[0, 1]` are all in `[0, 1]` almost
  surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Asymptotics
open scoped Topology

namespace Learning.Betting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ} {lam X : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure P'] [IsProbabilityMeasure P] in
/-- Observations with a law on `[0, 1]` are all in `[0, 1]` almost surely. -/
lemma ae_forall_mem_Icc_of_hasLaw (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hlaw : ∀ n, HasLaw (X n) P P') : ∀ᵐ ω ∂P', ∀ n, X n ω ∈ Set.Icc (0 : ℝ) 1 :=
  ae_all_iff.2 fun n ↦ ae_mem_Icc_of_hasLaw hP (hlaw n)

/-- **The `n^{-1/2}` criterion for plug-in strategies**: under a non-degenerate null
distribution on `[0, 1]`, a plug-in strategy on i.i.d. observations with bet fractions in
`fractionRange m` and `lam n = Ω_p(n^{-1/2})` or `Ω_{a.s.}((n log n)^{-1/2})` goes bankrupt almost
surely. -/
lemma tendsto_wealth_zero_of_isBigOmega_of_isPlugIn (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hnd : P ≠ Measure.dirac m) (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P') (hlam : IsPlugIn X lam)
    (hlam_mem : ∀ n, ∀ᵐ ω ∂P', lam n ω ∈ fractionRange m)
    (hrate : IsBigOmegaInProb P' lam (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) ∨
      IsBigOmegaAE P' lam (fun n ↦ ((n : ℝ) * Real.log n) ^ (-1 / 2 : ℝ))) :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0) :=
  tendsto_wealth_zero_of_isBigOmega_of_indep (ℱ := pastFiltration X hX) hP hm hnd
    (measurable_pastFiltration_succ X hX) (indep_pastFiltration hX hindep) hlaw
    (hlam.adapted_pastFiltration hX) hlam_mem hrate

omit [IsProbabilityMeasure P'] [IsProbabilityMeasure P] in
/-- The wealth of the strategy that does not bet before time `N` and bets `lam` afterwards. -/
lemma wealth_eq_mul_wealth_restart {N n : ℕ} (hN : N ≤ n) {lam' : ℕ → Ω → ℝ} {ω : Ω}
    (h0 : ∀ k < N, lam' k ω = 0) (h1 : ∀ k, N ≤ k → lam' k ω = lam k ω) :
    wealth m lam X n ω = wealth m lam X N ω * wealth m lam' X n ω := by
  simp only [wealth]
  have hsplit := prod_range_mul_prod_Ico (fun k ↦ 1 + lam k ω * (X k ω - m)) hN
  have hsplit' := prod_range_mul_prod_Ico (fun k ↦ 1 + lam' k ω * (X k ω - m)) hN
  have hone : ∏ k ∈ range N, (1 + lam' k ω * (X k ω - m)) = 1 :=
    prod_eq_one fun k hk ↦ by rw [h0 k (mem_range.1 hk)]; ring
  have hIco : ∏ k ∈ Ico N n, (1 + lam' k ω * (X k ω - m)) =
      ∏ k ∈ Ico N n, (1 + lam k ω * (X k ω - m)) :=
    prod_congr rfl fun k hk ↦ by rw [h1 k (mem_Ico.1 hk).1]
  rw [← hsplit, ← hsplit', hone, one_mul, hIco]

/-- **The almost sure `n^{-1/2}` criterion for strategies eventually in range**: under a
non-degenerate null distribution on `[0, 1]`, a plug-in strategy on i.i.d. observations whose
bet fractions are almost surely eventually in `fractionRange m` and are
`Ω_{a.s.}((n log n)^{-1/2})` goes bankrupt almost surely. -/
lemma tendsto_wealth_zero_of_isBigOmegaAE_of_eventually_mem
    (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m) (hnd : P ≠ Measure.dirac m)
    (hX : ∀ n, Measurable (X n)) (hindep : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P')
    (hlam : IsPlugIn X lam) (hlam_ev : ∀ᵐ ω ∂P', ∀ᶠ n in atTop, lam n ω ∈ fractionRange m)
    (hrate : IsBigOmegaAE P' lam (fun n ↦ ((n : ℝ) * Real.log n) ^ (-1 / 2 : ℝ))) :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0) := by
  have hm01 := mem_Ioo_of_ne_dirac hP hm hnd
  have hle : -1 / (1 - m) ≤ 1 / m := (div_nonpos_of_nonpos_of_nonneg (by norm_num)
    (sub_pos.2 hm01.2).le).trans (div_nonneg zero_le_one hm01.1.le)
  set proj : ℝ → ℝ := fun x ↦ max (-1 / (1 - m)) (min x (1 / m)) with hproj
  have hproj_mem : ∀ x, proj x ∈ fractionRange m := fun x ↦
    ⟨le_max_left _ _, max_le hle (min_le_right _ _)⟩
  have hproj_eq : ∀ x ∈ fractionRange m, proj x = x := fun x hx ↦ by
    simp only [hproj]
    rw [min_eq_left hx.2, max_eq_right hx.1]
  -- the restarted, projected strategies
  set lamN : ℕ → ℕ → Ω → ℝ := fun N n ω ↦ if n < N then 0 else proj (lam n ω) with hlamN
  have hW : ∀ N, ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m (lamN N) X n ω) atTop (𝓝 0) := by
    intro N
    refine tendsto_wealth_zero_of_isBigOmega_of_isPlugIn hP hm hnd hX hindep hlaw ?_
      (fun n ↦ ae_of_all _ fun ω ↦ ?_) (Or.inr ?_)
    · intro n
      obtain ⟨f, hf, hlamf⟩ := hlam n
      by_cases hn : n < N
      · exact ⟨fun _ ↦ 0, measurable_const, fun ω ↦ by simp [hlamN, hn]⟩
      · refine ⟨fun x ↦ proj (f x), by fun_prop, fun ω ↦ ?_⟩
        simp [hlamN, hn, hlamf ω]
    · simp only [hlamN]
      split_ifs
      · exact zero_mem_fractionRange (Set.Ioo_subset_Icc_self hm01)
      · exact hproj_mem _
    · filter_upwards [hrate, hlam_ev] with ω h1 h2
      refine h1.congr' EventuallyEq.rfl ?_
      filter_upwards [h2, eventually_ge_atTop N] with n hn hnN
      simp [hlamN, not_lt.2 hnN, hproj_eq _ hn]
  filter_upwards [ae_all_iff.2 hW, hlam_ev] with ω hWω hev
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have h := (hWω N).const_mul (wealth m lam X N ω)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (wealth_eq_mul_wealth_restart hn (fun k hk ↦ by simp [hlamN, hk])
    (fun k hk ↦ by simp [hlamN, not_lt.2 hk, hproj_eq _ (hN k hk)])).symm

end Learning.Betting
