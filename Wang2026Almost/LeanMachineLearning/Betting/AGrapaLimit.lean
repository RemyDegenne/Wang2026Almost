/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.KTLimit
public import Wang2026Almost.LeanMachineLearning.Betting.Null
public import Wang2026Almost.LeanMachineLearning.Betting.StrategyBounds

/-!
# Asymptotic normality of the approximate GRAPA bet fractions

For i.i.d. observations with a law `P` on `[0, 1]` of mean `m` and variance `σ² > 0`, and a
clipping constant `C > 0`, `√n λ^aGRAPA_n → N(0, σ⁻²)` in distribution. The unclipped fraction is
`S_n / V_n` with `S_n = ∑_{k < n} (X k - m)` and `V_n = ∑_{k < n} (X k - m)²`
(`empVar_add_sq_empMean_sub`); by the strong law, `S_n / n → 0` and `V_n / n → σ²` almost surely,
so the clipping is eventually inactive and `√n λ^aGRAPA_n - (S_n / √n) (n / V_n) → 0` almost
surely; conclude with the CLT and Slutsky's lemma.

## Main statements

* `ae_tendsto_sum_sub_div`, `ae_tendsto_sum_sub_sq_div`: the strong laws for `S_n / n` and
  `V_n / n` under a null distribution on `[0, 1]`;
* `tendstoInDistribution_sqrt_mul_agrapaFraction`, and its consequence
  `isBigOmegaInProb_agrapaFraction`: `λ^aGRAPA_n = Ω_p(n^{-1/2})`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology

namespace Learning.Betting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ} {X : ℕ → Ω → ℝ}

lemma integrable_of_mem_Icc_of_continuous (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) {f : ℝ → ℝ}
    (hf : Continuous f) : Integrable f P := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable K (hP.mono fun x hx ↦ hK x hx)

omit [IsProbabilityMeasure μ] in
/-- Strong law under a null distribution on `[0, 1]`: `S_n / n → 0` almost surely. -/
lemma ae_tendsto_sum_sub_div (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ k ∈ range n, (X k ω - m)) / n) atTop (𝓝 0) := by
  have h := ae_tendsto_sum_comp_div hindep hlaw (f := fun x ↦ x - m) (by fun_prop)
    (integrable_of_mem_Icc_of_continuous hP (by fun_prop))
  have h0 : ∫ x, (x - m) ∂P = 0 := by
    rw [integral_sub (integrable_of_mem_Icc_of_continuous hP (f := fun x ↦ x) continuous_id')
      (integrable_const m), hm]
    simp
  simpa [h0] using h

omit [IsProbabilityMeasure μ] in
/-- Strong law under a null distribution on `[0, 1]`: `V_n / n → σ²` almost surely. -/
lemma ae_tendsto_sum_sub_sq_div (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ k ∈ range n, (X k ω - m) ^ 2) / n) atTop
      (𝓝 Var[id; P]) := by
  have h := ae_tendsto_sum_comp_div hindep hlaw (f := fun x ↦ (x - m) ^ 2) (by fun_prop)
    (integrable_of_mem_Icc_of_continuous hP (by fun_prop))
  have hvar : Var[id; P] = ∫ x, (x - m) ^ 2 ∂P := by
    rw [variance_eq_integral aemeasurable_id]
    simp [hm]
  rwa [hvar]

lemma measurable_agrapaFraction (hX : ∀ n, Measurable (X n)) (C m : ℝ) (n : ℕ) :
    Measurable (agrapaFraction C m X n) := by
  unfold agrapaFraction empVar empMean
  fun_prop

/-- **Asymptotic normality of the aGRAPA bet fractions**: under a null distribution on `[0, 1]`
with mean `m` and variance `σ² > 0`, for `C > 0`, `√n λ^aGRAPA_n → N(0, σ⁻²)` in
distribution. -/
lemma tendstoInDistribution_sqrt_mul_agrapaFraction (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hvar : 0 < Var[id; P]) {C : ℝ} (hC : 0 < C)
    (hX : ∀ n, Measurable (X n)) (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * agrapaFraction C m X n ω) atTop (id : ℝ → ℝ)
      (fun _ ↦ μ) (gaussianReal 0 (Var[id; P])⁻¹.toNNReal) := by
  set σ2 := Var[id; P] with hσ2
  have hm01 := mem_Ioo_of_variance_pos hP hm hvar
  have hclt := tendstoInDistribution_sum_sub_div_sqrt hindep hlaw (memLp_two_id_of_mem_Icc hP)
  rw [hm] at hclt
  -- the random factor `n / V_n → σ⁻²`
  set R : ℕ → Ω → ℝ := fun n ω ↦ n / ∑ k ∈ range n, (X k ω - m) ^ 2 with hR
  have hR_ae : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ R n ω) atTop (𝓝 σ2⁻¹) := by
    filter_upwards [ae_tendsto_sum_sub_sq_div hP hm hindep hlaw] with ω hω
    refine (hω.inv₀ hvar.ne').congr fun n ↦ ?_
    simp [hR]
  have hR_meas : ∀ n, AEMeasurable (R n) μ := fun n ↦ by
    simp only [hR]
    fun_prop
  have hRm : TendstoInMeasure μ R atTop (fun _ ↦ σ2⁻¹) :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ (hR_meas n).aestronglyMeasurable) hR_ae
  have h1 := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ ↦ p.1 * p.2) (by fun_prop) hRm hR_meas
  -- the clipping is eventually inactive
  have hdiff : ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ √n * agrapaFraction C m X n ω -
      (∑ k ∈ range n, (X k ω - m)) / √n * R n ω) atTop (𝓝 0) := by
    filter_upwards [ae_tendsto_sum_sub_div hP hm hindep hlaw,
      ae_tendsto_sum_sub_sq_div hP hm hindep hlaw] with ω hS hV
    have hu := hS.div hV hvar.ne'
    rw [zero_div] at hu
    have hlo : -C / (1 - m) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hC) (sub_pos.2 hm01.2)
    have hhi : 0 < C / m := div_pos hC hm01.1
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hu (Ioo_mem_nhds hlo hhi), eventually_ge_atTop 1] with n hn hn1
    simp only [Set.mem_preimage, Set.mem_Ioo, Pi.div_apply] at hn
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.1 hn1
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn0
    have hmean : empMean X n ω - m = (∑ k ∈ range n, (X k ω - m)) / n := by
      rw [empMean, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      field_simp
    have hden := empVar_add_sq_empMean_sub X m hn0 ω
    have hagr : agrapaFraction C m X n ω =
        (∑ k ∈ range n, (X k ω - m)) / n / ((∑ k ∈ range n, (X k ω - m) ^ 2) / n) := by
      rw [agrapaFraction, hden, hmean, min_eq_left hn.2.le, max_eq_right hn.1.le]
    rw [hagr, hR]
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    rcases eq_or_ne (∑ k ∈ range n, (X k ω - m) ^ 2) 0 with hV0 | hV0
    · simp [hV0]
    field_simp
    linear_combination (-(∑ k ∈ range n, (X k ω - m))) * hsq
  have hdiff_m : TendstoInMeasure μ
      ((fun (n : ℕ) ω ↦ √n * agrapaFraction C m X n ω) -
        fun n ω ↦ (∑ k ∈ range n, (X k ω - m)) / √n * R n ω) atTop 0 :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ by
      refine (Measurable.aestronglyMeasurable ?_)
      exact ((measurable_agrapaFraction hX C m n).const_mul _).sub
        ((Finset.measurable_sum _ fun k _ ↦ (hX k).sub_const m).div_const _ |>.mul
          (by simp only [hR]; fun_prop))) hdiff
  have h2 := tendstoInDistribution_of_tendstoInMeasure_sub _ _ h1 hdiff_m
    (fun n ↦ ((measurable_agrapaFraction hX C m n).const_mul _).aemeasurable)
  refine h2.of_map_eq ?_
  have hmap := gaussianReal_map_inv_mul σ2 σ2 hvar.le
  have hσ : σ2 / σ2 ^ 2 = σ2⁻¹ := by field_simp
  rw [hσ] at hmap
  rw [← hmap]
  congr 1
  funext x
  simp [mul_comm]

/-- The aGRAPA bet fractions are `Ω_p(n^{-1/2})` under a null distribution on `[0, 1]` with
positive variance. -/
lemma isBigOmegaInProb_agrapaFraction (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hvar : 0 < Var[id; P]) {C : ℝ} (hC : 0 < C)
    (hX : ∀ n, Measurable (X n)) (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    IsBigOmegaInProb μ (agrapaFraction C m X) (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) :=
  isBigOmegaInProb_rpow_of_tendstoInDistribution_sqrt_mul
    (tendstoInDistribution_sqrt_mul_agrapaFraction hP hm hvar hC hX hindep hlaw)
    (gaussianReal_preimage_id_zero (by simpa using inv_pos.2 hvar))

end Learning.Betting
