/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.AGrapaLimit
public import Wang2026Almost.Mathlib.Probability.Distributions.Gaussian.Sq

/-!
# The `χ²` limit of `S_n² / V_n`

For i.i.d. observations with a law `P` on `[0, 1]` of mean `m` and variance `σ² > 0`, with
`S_n = ∑_{k < n} (X k - m)` and `V_n = ∑_{k < n} (X k - m)²`, `S_n² / V_n` converges in
distribution to the `χ²` distribution with one degree of freedom: `S_n / √n → N(0, σ²)` (CLT),
`n / V_n → σ⁻²` almost surely (strong law), Slutsky's lemma, and the law of the square of a
standard Gaussian (`gaussianReal_map_sq`).

## Main statements

* `gaussianReal_map_sq_mul_inv`: `x ↦ x² / σ²` maps `N(0, σ²)` to `χ²₁`;
* `tendstoInDistribution_sq_sum_sub_div`: `S_n² / V_n → χ²₁` in distribution.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology NNReal

namespace Learning.Betting

/-- The image of `N(0, σ²)` by `x ↦ x² σ⁻²` is the `χ²` distribution with one degree of
freedom. -/
lemma gaussianReal_map_sq_mul_inv {σ2 : ℝ} (hσ : 0 < σ2) :
    (gaussianReal 0 σ2.toNNReal).map (fun x ↦ x ^ 2 * σ2⁻¹) = chiSquareMeasure 1 := by
  have hs : 0 < √σ2 := Real.sqrt_pos.2 hσ
  have h1 : (gaussianReal 0 σ2.toNNReal).map (fun x ↦ (√σ2)⁻¹ * x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hσ.le, NNReal.coe_one, inv_pow,
      Real.sq_sqrt hσ.le]
    field_simp
  have hcomp : (fun x : ℝ ↦ x ^ 2 * σ2⁻¹) = (fun y ↦ y ^ 2) ∘ (fun x ↦ (√σ2)⁻¹ * x) := by
    funext x
    simp only [Function.comp_apply, mul_pow, inv_pow, Real.sq_sqrt hσ.le]
    ring
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1, gaussianReal_map_sq]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ} {X : ℕ → Ω → ℝ}

/-- Under a null distribution on `[0, 1]` with positive variance, `S_n² / V_n` converges in
distribution to `χ²₁`. -/
lemma tendstoInDistribution_sq_sum_sub_div (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hvar : 0 < Var[id; P]) (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (∑ k ∈ range n, (X k ω - m)) ^ 2 / ∑ k ∈ range n, (X k ω - m) ^ 2)
      atTop (id : ℝ → ℝ) (fun _ ↦ μ) (chiSquareMeasure 1) := by
  set σ2 := Var[id; P] with hσ2
  have hclt := tendstoInDistribution_sum_sub_div_sqrt hindep hlaw (memLp_id_of_mem_Icc hP 2)
  rw [hm] at hclt
  set R : ℕ → Ω → ℝ := fun n ω ↦ n / ∑ k ∈ range n, (X k ω - m) ^ 2 with hR
  have hR_ae : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ R n ω) atTop (𝓝 σ2⁻¹) := by
    filter_upwards [ae_tendsto_sum_sub_sq_div hP hm (fun _ _ hij ↦ hindep.indepFun hij) hlaw]
      with ω hω
    refine (hω.inv₀ hvar.ne').congr fun n ↦ ?_
    simp [hR]
  have hR_meas : ∀ n, AEMeasurable (R n) μ := fun n ↦ by
    simp only [hR]
    fun_prop
  have hRm : TendstoInMeasure μ R atTop (fun _ ↦ σ2⁻¹) :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ (hR_meas n).aestronglyMeasurable) hR_ae
  have h1 := hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ ↦ p.1 ^ 2 * p.2) (by fun_prop) hRm hR_meas
  refine (h1.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)).of_map_eq ?_
  · simp only [hR]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rcases eq_or_ne (∑ k ∈ range n, (X k ω - m) ^ 2) 0 with hV0 | hV0
    · simp [hV0]
    rw [div_pow, hsq]
    field_simp
  · rw [← gaussianReal_map_sq_mul_inv hvar]
    rfl

end Learning.Betting
