/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.ChiSquareLimit
public import Wang2026Almost.LeanMachineLearning.Betting.GoodEvent
public import Wang2026Almost.LeanMachineLearning.Betting.Hindsight

/-!
# The Bahadur expansion and the asymptotic normality of the GRAPA bet fractions

A GRAPA strategy `gr` bets at round `n` a maximizer of the hindsight wealth
`l ↦ fixedWealth m l X n` over `fractionRange m`. On the event of probability one where
`S_n = O(√n log n)` and `V_n - n σ² = O(√n log n)` (`ae_isBigO_sum_sub`, `ae_isBigO_sum_sq_sub`),
the location of the maximizer (`eventually_abs_sub_div_le_of_isMaxOn_fixedWealth`) gives the
Bahadur expansion `√n gr_n = S_n / (σ² √n) + O(log² n / √n)`, which is `o(n^{-1/4} log n)`.
Consequently `√n gr_n → N(0, σ⁻²)` in distribution and `gr_n = Ω_p(n^{-1/2})`.

## Main statements

* `isBigO_sqrt_mul_sub_of_isMaxOn`: the pathwise Bahadur bound;
* `isLittleO_log_sq_div_sqrt`, `tendsto_log_sq_div_sqrt`: `log² n / √n = o(n^{-1/4} log n)` and
  `log² n / √n → 0`;
* `ae_isLittleO_grapa`, `tendstoInDistribution_sqrt_mul_grapa`, `isBigOmegaInProb_grapa`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Asymptotics
open scoped Topology

namespace Learning.Betting

/-- `log n / n^{1/4} → 0`. -/
lemma tendsto_log_div_rpow_quarter :
    Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
  ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop

lemma log_sq_div_sqrt_eq {n : ℕ} (hn : 0 < n) :
    Real.log n ^ 2 / √n = (Real.log n / (n : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ (1 / 4 : ℝ)), ← Real.rpow_mul hn'.le,
    Real.sqrt_eq_rpow]
  norm_num

/-- `log² n / √n → 0`. -/
lemma tendsto_log_sq_div_sqrt : Tendsto (fun n : ℕ ↦ Real.log n ^ 2 / √n) atTop (𝓝 0) := by
  have h := tendsto_log_div_rpow_quarter.pow 2
  rw [zero_pow two_ne_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [log_sq_div_sqrt_eq hn]

/-- `log² n / √n = o(n^{-1/4} log n)`. -/
lemma isLittleO_log_sq_div_sqrt :
    (fun n : ℕ ↦ Real.log n ^ 2 / √n) =o[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (-1 / 4 : ℝ) * Real.log n := by
  set u : ℕ → ℝ := fun n ↦ Real.log n / (n : ℝ) ^ (1 / 4 : ℝ) with hu
  have hu0 : u =o[atTop] (fun _ ↦ (1 : ℝ)) := (isLittleO_one_iff ℝ).2 tendsto_log_div_rpow_quarter
  have h := (isBigO_refl u atTop).mul_isLittleO hu0
  simp only [mul_one] at h
  refine (h.congr' ?_ ?_)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    rw [log_sq_div_sqrt_eq hn, sq]
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [hu]
    rw [show (-1 / 4 : ℝ) = -(1 / 4) by norm_num, Real.rpow_neg hn'.le, div_eq_mul_inv,
      mul_comm]

variable {Ω : Type*}

/-- **Pathwise Bahadur bound for GRAPA**: on a path where the observations are in `[0, 1]`,
`S_n = O(√n log n)` and `V_n - n σ² = O(√n log n)`, any sequence `g n` of maximizers of the
hindsight wealth satisfies `√n g n - S_n / (σ² √n) = O(log² n / √n)`. -/
lemma isBigO_sqrt_mul_sub_of_isMaxOn {m σ2 : ℝ} (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    {X : ℕ → Ω → ℝ} {ω : Ω} (hX : ∀ k, X k ω ∈ Set.Icc 0 1)
    (hS : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m)) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
    (hV : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m) ^ 2 - n * σ2) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n))
    {g : ℕ → ℝ} (hg : ∀ n, g n ∈ fractionRange m ∧
      IsMaxOn (fun l ↦ fixedWealth m l X n ω) (fractionRange m) (g n)) :
    (fun n : ℕ ↦ √n * g n - (∑ k ∈ range n, (X k ω - m)) / (σ2 * √n)) =O[atTop]
      (fun n : ℕ ↦ Real.log n ^ 2 / √n) := by
  obtain ⟨K, hK⟩ := eventually_abs_sub_div_le_of_isMaxOn_fixedWealth hm hσ hX hS hV
  obtain ⟨C1, hC1pos, hC1⟩ := hS.exists_pos
  obtain ⟨C2, hC2pos, hC2⟩ := hV.exists_pos
  have hsmall : ∀ᶠ n : ℕ in atTop, C2 * (√n * Real.log n) ≤ n * σ2 / 2 := by
    have h := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
      |>.comp tendsto_natCast_atTop_atTop).const_mul C2
    rw [mul_zero] at h
    filter_upwards [h.eventually (gt_mem_nhds (by positivity : 0 < σ2 / 2)),
      eventually_gt_atTop 0] with n hn hn0
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn'
    have hsq : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt hn'.le
    simp only [Function.comp_apply, ← Real.sqrt_eq_rpow] at hn
    rw [mul_div_assoc', div_lt_iff₀ hs] at hn
    nlinarith
  refine IsBigO.of_bound (K + 2 * C1 * C2 / σ2 ^ 2) ?_
  filter_upwards [hK, hC1.bound, hC2.bound, hsmall, eventually_ge_atTop 2] with n hKn hC1n hC2n
    hsn hn
  set S := ∑ k ∈ range n, (X k ω - m) with hSdef
  set V := ∑ k ∈ range n, (X k ω - m) ^ 2 with hVdef
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 < Real.log n := Real.log_pos (by linarith)
  have hR : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hRR : √(n : ℝ) * √(n : ℝ) = n := Real.mul_self_sqrt (by linarith)
  have hSb : |S| ≤ C1 * (√n * Real.log n) := by
    simpa [Real.norm_eq_abs, abs_of_pos hR, abs_of_pos hL] using hC1n
  have hVb : |V - n * σ2| ≤ C2 * (√n * Real.log n) := by
    simpa [Real.norm_eq_abs, abs_of_pos hR, abs_of_pos hL] using hC2n
  have hVlow : n * σ2 / 2 ≤ V := by
    have := (abs_le.1 hVb).1
    linarith
  have hVpos : 0 < V := lt_of_lt_of_le (by positivity) hVlow
  have hg := hKn (g n) (hg n).2 (hg n).1
  -- split the difference
  have hN : (n : ℝ) = √(n : ℝ) ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hsplit : √n * g n - S / (σ2 * √n) =
      √n * (g n - S / V) + √n * S * (n * σ2 - V) / (V * n * σ2) := by
    have key : ∀ R N : ℝ, 0 < R → N = R ^ 2 →
        R * g n - S / (σ2 * R) = R * (g n - S / V) + R * S * (N * σ2 - V) / (V * N * σ2) := by
      intro R N hR hN
      subst hN
      field_simp
      ring
    exact key _ _ hR hN
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity), hsplit]
  have hT1 : |√n * (g n - S / V)| ≤ K * Real.log n ^ 2 / √n := by
    rw [abs_mul, abs_of_pos hR]
    calc √n * |g n - S / V| ≤ √n * (K * Real.log n ^ 2 / n) :=
          mul_le_mul_of_nonneg_left hg hR.le
      _ = K * Real.log n ^ 2 / √n := by
          have key : ∀ R N : ℝ, 0 < R → N = R ^ 2 →
              R * (K * Real.log n ^ 2 / N) = K * Real.log n ^ 2 / R := by
            intro R N hR hN
            subst hN
            field_simp
          exact key _ _ hR hN
  have hT2 : |√n * S * (n * σ2 - V) / (V * n * σ2)| ≤
      2 * C1 * C2 / σ2 ^ 2 * (Real.log n ^ 2 / √n) := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hR, abs_of_pos (by positivity : 0 < V * n * σ2),
      abs_sub_comm]
    have hnum : √n * |S| * |V - n * σ2| ≤ √n * (C1 * (√n * Real.log n)) *
        (C2 * (√n * Real.log n)) := by gcongr
    have hden : (n * σ2 / 2) * n * σ2 ≤ V * n * σ2 := by gcongr
    calc √n * |S| * |V - n * σ2| / (V * n * σ2)
        ≤ √n * (C1 * (√n * Real.log n)) * (C2 * (√n * Real.log n)) / ((n * σ2 / 2) * n * σ2) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 2 * C1 * C2 / σ2 ^ 2 * (Real.log n ^ 2 / √n) := by
          have key : ∀ R N : ℝ, 0 < R → N = R ^ 2 →
              R * (C1 * (R * Real.log n)) * (C2 * (R * Real.log n)) / ((N * σ2 / 2) * N * σ2)
                = 2 * C1 * C2 / σ2 ^ 2 * (Real.log n ^ 2 / R) := by
            intro R N hR hN
            subst hN
            field_simp
          exact key _ _ hR hN
  calc |√n * (g n - S / V) + √n * S * (n * σ2 - V) / (V * n * σ2)|
      ≤ |√n * (g n - S / V)| + |√n * S * (n * σ2 - V) / (V * n * σ2)| := abs_add_le _ _
    _ ≤ K * Real.log n ^ 2 / √n + 2 * C1 * C2 / σ2 ^ 2 * (Real.log n ^ 2 / √n) := add_le_add hT1 hT2
    _ = (K + 2 * C1 * C2 / σ2 ^ 2) * (Real.log n ^ 2 / √n) := by ring

lemma IsPlugIn.measurable {X lam : ℕ → Ω → ℝ} [MeasurableSpace Ω] (hX : ∀ n, Measurable (X n))
    (h : IsPlugIn X lam) (n : ℕ) : Measurable (lam n) := by
  obtain ⟨f, hf, hlam⟩ := h n
  rw [show lam n = f ∘ (fun ω (k : Fin n) ↦ X k ω) from funext hlam]
  exact hf.comp (measurable_pi_iff.2 fun k ↦ hX k)

variable {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ} {X gr : ℕ → Ω → ℝ}

/-- **Bahadur expansion of GRAPA**, `O` form: almost surely
`√n gr_n - S_n / (σ² √n) = O(log² n / √n)`. -/
lemma ae_isBigO_grapa (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hvar : 0 < Var[id; P]) (hindep : iIndepFun X μ)
    (hlaw : ∀ n, HasLaw (X n) P μ) (hgr : IsGrapa m X gr) :
    ∀ᵐ ω ∂μ, (fun n : ℕ ↦ √n * gr n ω - (∑ k ∈ range n, (X k ω - m)) / (Var[id; P] * √n))
      =O[atTop] (fun n : ℕ ↦ Real.log n ^ 2 / √n) := by
  have hm01 := mem_Ioo_of_variance_pos hP hm hvar
  filter_upwards [ae_all_iff.2 fun k ↦ (hlaw k).ae_comp hP,
    ae_isBigO_sum_sub hP hm hindep hlaw, ae_isBigO_sum_sq_sub hP hm hindep hlaw]
    with ω hω hS hV
  exact isBigO_sqrt_mul_sub_of_isMaxOn hm01 hvar hω hS hV fun n ↦ hgr.2 n ω

/-- **Bahadur expansion of GRAPA**: almost surely
`√n gr_n = S_n / (σ² √n) + o(n^{-1/4} log n)`. -/
lemma ae_isLittleO_grapa (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hvar : 0 < Var[id; P]) (hindep : iIndepFun X μ)
    (hlaw : ∀ n, HasLaw (X n) P μ) (hgr : IsGrapa m X gr) :
    ∀ᵐ ω ∂μ, (fun n : ℕ ↦ √n * gr n ω - (∑ k ∈ range n, (X k ω - m)) / (Var[id; P] * √n))
      =o[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (-1 / 4 : ℝ) * Real.log n) := by
  filter_upwards [ae_isBigO_grapa hP hm hvar hindep hlaw hgr] with ω hω
  exact hω.trans_isLittleO isLittleO_log_sq_div_sqrt

/-- **Asymptotic normality of GRAPA**: `√n gr_n → N(0, σ⁻²)` in distribution. -/
lemma tendstoInDistribution_sqrt_mul_grapa (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hvar : 0 < Var[id; P]) (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) (hgr : IsGrapa m X gr) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * gr n ω) atTop (id : ℝ → ℝ) (fun _ ↦ μ)
      (gaussianReal 0 (Var[id; P])⁻¹.toNNReal) := by
  set σ2 := Var[id; P] with hσ2
  have hclt := tendstoInDistribution_sum_sub_div_sqrt hindep hlaw (memLp_id_of_mem_Icc hP 2)
  rw [hm] at hclt
  have h1 := hclt.mul_add_of_tendsto (tendsto_const_nhds (x := σ2⁻¹))
    (tendsto_const_nhds (x := (0 : ℝ)))
  have h2 : TendstoInDistribution
      (fun (n : ℕ) ω ↦ (∑ k ∈ range n, (X k ω - m)) / (σ2 * √n)) atTop (id : ℝ → ℝ) (fun _ ↦ μ)
      (gaussianReal 0 σ2⁻¹.toNNReal) := by
    refine (h1.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)).of_map_eq ?_
    · simp only [add_zero]
      rw [div_mul_eq_div_div_swap, div_eq_inv_mul (_ / _)]
    · have hmap := gaussianReal_map_inv_mul σ2 σ2 hvar.le
      have hσ : σ2 / σ2 ^ 2 = σ2⁻¹ := by field_simp
      rw [hσ] at hmap
      rw [← hmap]
      congr 1
      funext x
      simp
  have hdiff : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ √n * gr n ω -
      (∑ k ∈ range n, (X k ω - m)) / (σ2 * √n)) atTop (𝓝 0) := by
    filter_upwards [ae_isBigO_grapa hP hm hvar hindep hlaw hgr] with ω hω
    exact hω.trans_tendsto tendsto_log_sq_div_sqrt
  have hgr_meas := hgr.1.measurable hX
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ h2 ?_
    fun n ↦ ((hgr_meas n).const_mul _).aemeasurable
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) hdiff
  exact (((hgr_meas n).const_mul _).sub ((Finset.measurable_sum _ fun k _ ↦
    (hX k).sub_const m).div_const _)).aestronglyMeasurable

/-- The GRAPA bet fractions are `Ω_p(n^{-1/2})`. -/
lemma isBigOmegaInProb_grapa (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hvar : 0 < Var[id; P]) (hX : ∀ n, Measurable (X n)) (hindep : iIndepFun X μ)
    (hlaw : ∀ n, HasLaw (X n) P μ) (hgr : IsGrapa m X gr) :
    IsBigOmegaInProb μ gr (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) :=
  isBigOmegaInProb_rpow_of_tendstoInDistribution_sqrt_mul
    (tendstoInDistribution_sqrt_mul_grapa hP hm hvar hX hindep hlaw hgr)
    (gaussianReal_preimage_id_zero (by simpa using inv_pos.2 hvar))

end Learning.Betting
