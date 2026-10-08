/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Strategies
public import Wang2026Almost.Mathlib.Probability.LimitTheorems
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Wang2026Almost.Mathlib.Probability.AsymptoticsInProbability

/-!
# Asymptotic normality of the Krichevsky–Trofimov bet fractions

For i.i.d. observations with law `P` (mean `m`, finite variance `σ²`) and a constant `C > 0`,
`√n λ^KT_n = √n (1/2 + ∑_{k < n} (X k - m)) / (C (n + 1))` converges in distribution to
`N(0, σ² / C²)`: the CLT for `∑_{k < n} (X k - m) / √n` and Slutsky's lemma with the deterministic
factors `n / (C (n + 1)) → 1 / C` and `√n / (2 C (n + 1)) → 0`.

## Main statements

* `gaussianReal_map_inv_mul`: `N(0, v)` scaled by `1 / C` is `N(0, v / C²)`;
* `tendstoInDistribution_sqrt_mul_ktFraction`: the asymptotic normality of `√n λ^KT_n`;
* `isBigOmegaInProb_ktFraction`: consequently `λ^KT_n = Ω_p(n^{-1/2})` when `σ² > 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology NNReal

namespace Learning.Betting

/-- The image of `N(0, v)` by `x ↦ C⁻¹ * x` is `N(0, v / C²)`. -/
lemma gaussianReal_map_inv_mul (C v : ℝ) (hv : 0 ≤ v) :
    (gaussianReal 0 v.toNNReal).map (fun x ↦ C⁻¹ * x) = gaussianReal 0 (v / C ^ 2).toNNReal := by
  rw [gaussianReal_map_const_mul, mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hv,
    Real.coe_toNNReal _ (div_nonneg hv (sq_nonneg C))]
  rw [div_eq_inv_mul, inv_pow]

/-- A Gaussian with positive variance has no atom at `0`. -/
lemma gaussianReal_preimage_id_zero {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal 0 v ((id : ℝ → ℝ) ⁻¹' {0}) = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Asymptotic normality of the KT bet fractions**: for i.i.d. square integrable observations
with law `P` of mean `m` and a constant `C > 0`, `√n λ^KT_n → N(0, Var_P / C²)` in
distribution. -/
lemma tendstoInDistribution_sqrt_mul_ktFraction {P : Measure ℝ}
    {m C : ℝ} (hC : 0 < C) (hm : ∫ x, x ∂P = m) (hP : MemLp id 2 P) {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * ktFraction C m X n ω) atTop (id : ℝ → ℝ)
      (fun _ ↦ μ) (gaussianReal 0 (Var[id; P] / C ^ 2).toNNReal) := by
  have hclt := tendstoInDistribution_sum_sub_div_sqrt hindep hlaw hP
  rw [hm] at hclt
  have ha : Tendsto (fun n : ℕ ↦ (n : ℝ) / (n + 1) * C⁻¹) atTop (𝓝 (1 * C⁻¹)) :=
    tendsto_natCast_div_add_atTop (1 : ℝ) |>.mul_const _
  have hb : Tendsto (fun n : ℕ ↦ (√n)⁻¹ * ((n : ℝ) / (n + 1)) / (2 * C)) atTop
      (𝓝 (0 * 1 / (2 * C))) := by
    refine (Tendsto.mul ?_ (tendsto_natCast_div_add_atTop (1 : ℝ))).div_const _
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := hclt.mul_add_of_tendsto ha hb
  simp only [one_mul, zero_mul, zero_div, add_zero, id_eq] at h
  refine (h.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)).of_map_eq ?_
  · rw [ktFraction, Nat.cast_ofNat]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
    field_simp
    linear_combination (-(2 * ∑ k ∈ range n, (X k ω - m)) - 1) * hsq
  · simpa using gaussianReal_map_inv_mul C Var[id; P] (variance_nonneg _ _)

/-- The KT bet fractions are `Ω_p(n^{-1/2})` for i.i.d. observations with positive variance. -/
lemma isBigOmegaInProb_ktFraction {P : Measure ℝ} {m C : ℝ} (hC : 0 < C) (hm : ∫ x, x ∂P = m)
    (hP : MemLp id 2 P) (hvar : 0 < Var[id; P]) {X : ℕ → Ω → ℝ} (hindep : iIndepFun X μ)
    (hlaw : ∀ n, HasLaw (X n) P μ) :
    IsBigOmegaInProb μ (ktFraction C m X) (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) :=
  isBigOmegaInProb_rpow_of_tendstoInDistribution_sqrt_mul
    (tendstoInDistribution_sqrt_mul_ktFraction hC hm hP hindep hlaw)
    (gaussianReal_preimage_id_zero (by simpa using div_pos hvar (pow_pos hC 2)))

end Learning.Betting
