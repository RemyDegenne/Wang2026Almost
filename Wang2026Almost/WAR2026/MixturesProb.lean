/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Mixtures
public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The universal portfolio and Robbins' mixing distributions

Properties of the two mixing distributions of Proposition 3.2 used to apply the no-cash
criterion (Theorem 3.1): both are probability measures, concentrated on `[-1, 1]` (hence on the
range `fractionRange m` of the bet fractions for every `m ∈ (0, 1)`), without atom at `0`.

For Robbins' mixture, the total mass is computed with the antiderivative
`l ↦ 1 / log (log (C / l))` of `l ↦ 1 / (l log (C / l) (log log (C / l))²)` on `(0, 1]`.

## Main statements

* `isProbabilityMeasure_betaMixture`, `ae_mem_Icc_betaMixture`, `betaMixture_singleton_zero`;
* `isProbabilityMeasure_robbinsMixture`, `ae_mem_Icc_robbinsMixture`,
  `robbinsMixture_singleton_zero`;
* `Icc_subset_fractionRange`: `[-1, 1] ⊆ fractionRange m` for `m ∈ (0, 1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Topology

namespace Wang2026Almost

/-- For `m ∈ (0, 1)`, the interval `[-1, 1]` is contained in the range of the bet fractions. -/
lemma Icc_subset_fractionRange {m : ℝ} (hm : m ∈ Ioo 0 1) :
    Icc (-1 : ℝ) 1 ⊆ Learning.Betting.fractionRange m := by
  intro x hx
  have h1m : 0 < 1 - m := sub_pos.2 hm.2
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ h1m]
    nlinarith [mul_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x + 1) h1m.le, hm.1]
  · rw [le_div_iff₀ hm.1]
    nlinarith [mul_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x) hm.1.le, hm.2]

/-! ### The universal portfolio -/

lemma measurable_two_mul_sub_one : Measurable (fun x : ℝ ↦ ((2 : ℕ) : ℝ) * x - 1) := by fun_prop

/-- The rescaled Beta distribution is a probability measure. -/
lemma isProbabilityMeasure_betaMixture {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (betaMixture a b) := by
  have := isProbabilityMeasureBeta ha hb
  exact (Measure.isProbabilityMeasure_map_iff measurable_two_mul_sub_one.aemeasurable).2 this

/-- The Beta distribution is concentrated on `[0, 1]`. -/
lemma betaMeasure_compl_Icc (a b : ℝ) : betaMeasure a b (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [betaMeasure, withDensity_apply _ measurableSet_Icc.compl]
  refine setLIntegral_eq_zero measurableSet_Icc.compl fun x hx ↦ ?_
  simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact betaPDF_eq_zero_of_nonpos hx.le
  · exact betaPDF_eq_zero_of_one_le hx.le

/-- The Beta distribution has no atoms. -/
lemma betaMeasure_singleton (a b x : ℝ) : betaMeasure a b {x} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

/-- The rescaled Beta distribution is concentrated on `[-1, 1]`. -/
lemma ae_mem_Icc_betaMixture (a b : ℝ) : ∀ᵐ l ∂(betaMixture a b), l ∈ Icc (-1 : ℝ) 1 := by
  rw [betaMixture]
  refine (ae_map_iff measurable_two_mul_sub_one.aemeasurable ?_).2 ?_
  · exact measurableSet_Icc
  refine measure_mono_null (fun x hx ↦ ?_) (betaMeasure_compl_Icc a b)
  rw [mem_compl_iff]
  intro h
  exact hx (by simp only [mem_Icc, Nat.cast_ofNat]; constructor <;> linarith [h.1, h.2])

/-- The rescaled Beta distribution has no atom at `0`. -/
lemma betaMixture_singleton_zero (a b : ℝ) : betaMixture a b {0} = 0 := by
  rw [betaMixture, Measure.map_apply measurable_two_mul_sub_one (measurableSet_singleton 0)]
  refine measure_mono_null (fun x hx ↦ ?_) (betaMeasure_singleton a b (1 / 2))
  simp only [mem_preimage, mem_singleton_iff, Nat.cast_ofNat] at hx ⊢
  linarith

/-! ### Robbins' mixture -/

lemma one_lt_robbinsConst : Real.exp 1 < robbinsConst := by
  rw [robbinsConst]
  have : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

lemma robbinsConst_pos : 0 < robbinsConst := (Real.exp_pos 1).trans one_lt_robbinsConst

/-- For `0 < l ≤ 1`, `log (C / l) > 1`. -/
lemma one_lt_log_robbinsConst_div {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    1 < Real.log (robbinsConst / l) := by
  rw [Real.lt_log_iff_exp_lt (div_pos robbinsConst_pos hl0)]
  calc Real.exp 1 < robbinsConst := one_lt_robbinsConst
    _ ≤ robbinsConst / l := le_div_self robbinsConst_pos.le hl0 hl1

/-- For `0 < l ≤ 1`, `log (log (C / l)) > 0`. -/
lemma log_log_robbinsConst_div_pos {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    0 < Real.log (Real.log (robbinsConst / l)) :=
  Real.log_pos (one_lt_log_robbinsConst_div hl0 hl1)

/-- The antiderivative `l ↦ 1 / log (log (C / l))` (extended by `0` at `0`). -/
noncomputable def robbinsAntideriv (l : ℝ) : ℝ :=
  if l = 0 then 0 else (Real.log (Real.log (robbinsConst / l)))⁻¹

/-- The derivative of the Robbins antiderivative. -/
noncomputable def robbinsDeriv (l : ℝ) : ℝ :=
  (l * Real.log (robbinsConst / l) * Real.log (Real.log (robbinsConst / l)) ^ 2)⁻¹

lemma hasDerivAt_robbinsAntideriv {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    HasDerivAt robbinsAntideriv (robbinsDeriv l) l := by
  have hC := robbinsConst_pos
  have h1 := one_lt_log_robbinsConst_div hl0 hl1
  have h2 := log_log_robbinsConst_div_pos hl0 hl1
  have hdiv : HasDerivAt (fun x ↦ robbinsConst / x) (-(robbinsConst / l ^ 2)) l := by
    have := (hasDerivAt_inv hl0.ne').const_mul robbinsConst
    simp only [div_eq_mul_inv]
    convert this using 1
    ring
  have hlog : HasDerivAt (fun x ↦ Real.log (robbinsConst / x))
      (-(robbinsConst / l ^ 2) / (robbinsConst / l)) l :=
    hdiv.log (div_pos hC hl0).ne'
  have hloglog : HasDerivAt (fun x ↦ Real.log (Real.log (robbinsConst / x)))
      (-(robbinsConst / l ^ 2) / (robbinsConst / l) / Real.log (robbinsConst / l)) l :=
    hlog.log (by linarith)
  have hinv := hloglog.inv h2.ne'
  refine (hinv.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [lt_mem_nhds hl0] with x hx
    simp [robbinsAntideriv, hx.ne']
  · rw [robbinsDeriv]
    field_simp

lemma robbinsDeriv_nonneg {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) : 0 ≤ robbinsDeriv l := by
  have := one_lt_log_robbinsConst_div hl0 hl1
  rw [robbinsDeriv]
  positivity

lemma tendsto_robbinsAntideriv_zero :
    Tendsto robbinsAntideriv (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ ↦ robbinsConst / x) (𝓝[>] 0) atTop := by
    simp_rw [div_eq_mul_inv]
    exact tendsto_inv_nhdsGT_zero.const_mul_atTop robbinsConst_pos
  have h2 := (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)).inv_tendsto_atTop
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [robbinsAntideriv, (mem_Ioi.1 hx).ne']

lemma continuousOn_robbinsAntideriv : ContinuousOn robbinsAntideriv (Icc 0 1) := by
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hx0
  · have h : robbinsAntideriv 0 = 0 := by simp [robbinsAntideriv]
    have h' : ContinuousWithinAt robbinsAntideriv (Ioi 0) 0 := by
      rw [ContinuousWithinAt, h]
      exact tendsto_robbinsAntideriv_zero
    exact (continuousWithinAt_Ioi_iff_Ici.1 h').mono Icc_subset_Ici_self
  · exact (hasDerivAt_robbinsAntideriv hx0 hx.2).continuousAt.continuousWithinAt

lemma integrableOn_robbinsDeriv : IntegrableOn robbinsDeriv (Ioc 0 1) :=
  intervalIntegral.integrableOn_deriv_of_nonneg continuousOn_robbinsAntideriv
    (fun _ hx ↦ hasDerivAt_robbinsAntideriv hx.1 hx.2.le)
    (fun _ hx ↦ robbinsDeriv_nonneg hx.1 hx.2.le)


/-- The integral of the Robbins derivative over `(0, 1]` is `1 / log (log C)`. -/
lemma integral_robbinsDeriv :
    ∫ x in Ioc (0 : ℝ) 1, robbinsDeriv x = (Real.log (Real.log robbinsConst))⁻¹ := by
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      continuousOn_robbinsAntideriv (fun x hx ↦ hasDerivAt_robbinsAntideriv hx.1 hx.2.le)
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one |>.2 integrableOn_robbinsDeriv)]
  simp [robbinsAntideriv]

/-- The Robbins density on `(0, ∞)`: `log (log C) / 2` times the Robbins derivative on `(0, 1]`,
`0` elsewhere. The Robbins density is `l ↦ robbinsHalfDensity |l|`. -/
noncomputable def robbinsHalfDensity (x : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator (fun y ↦ Real.log (Real.log robbinsConst) / 2 * robbinsDeriv y) x

lemma robbinsDensity_eq (l : ℝ) : robbinsDensity l = robbinsHalfDensity |l| := by
  rw [robbinsDensity, robbinsHalfDensity, Set.indicator_apply]
  by_cases hl : |l| ≤ 1
  · rcases eq_or_ne l 0 with rfl | hl0
    · simp
    · have hpos : 0 < |l| := abs_pos.2 hl0
      have hmem : |l| ∈ Ioc (0 : ℝ) 1 := ⟨hpos, hl⟩
      simp only [hl, hmem, ite_true, robbinsDeriv, Nat.cast_ofNat]
      field_simp
  · have hmem : |l| ∉ Ioc (0 : ℝ) 1 := fun h ↦ hl h.2
    simp only [hl, hmem, ite_false]

lemma robbinsHalfDensity_nonneg (x : ℝ) : 0 ≤ robbinsHalfDensity x := by
  rw [robbinsHalfDensity, Set.indicator_apply]
  split_ifs with hx
  · exact mul_nonneg (div_nonneg (log_log_robbinsConst_div_pos one_pos le_rfl |>.le.trans_eq
      (by rw [div_one])) zero_le_two) (robbinsDeriv_nonneg hx.1 hx.2)
  · exact le_rfl

lemma robbinsDensity_nonneg (l : ℝ) : 0 ≤ robbinsDensity l :=
  (robbinsDensity_eq l).symm ▸ robbinsHalfDensity_nonneg _

lemma integral_Ioi_robbinsHalfDensity : ∫ x in Ioi (0 : ℝ), robbinsHalfDensity x = 1 / 2 := by
  have hC : 0 < Real.log (Real.log robbinsConst) := by
    simpa using log_log_robbinsConst_div_pos one_pos le_rfl
  simp only [robbinsHalfDensity]
  rw [integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, Ioc_inter_Ioi, max_self, integral_const_mul,
    integral_robbinsDeriv]
  field_simp

lemma integral_robbinsDensity : ∫ l, robbinsDensity l = 1 := by
  simp_rw [robbinsDensity_eq]
  rw [integral_comp_abs (f := robbinsHalfDensity), integral_Ioi_robbinsHalfDensity]
  norm_num

lemma integrable_robbinsDensity : Integrable robbinsDensity := by
  by_contra h
  have := integral_robbinsDensity
  rw [integral_undef h] at this
  exact zero_ne_one this

/-- Robbins' mixing distribution is a probability measure. -/
lemma isProbabilityMeasure_robbinsMixture : IsProbabilityMeasure robbinsMixture := by
  constructor
  rw [robbinsMixture, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_robbinsDensity
      (ae_of_all _ robbinsDensity_nonneg), integral_robbinsDensity, ENNReal.ofReal_one]

/-- Robbins' mixing distribution is concentrated on `[-1, 1]`. -/
lemma ae_mem_Icc_robbinsMixture : ∀ᵐ l ∂robbinsMixture, l ∈ Icc (-1 : ℝ) 1 := by
  rw [ae_iff]
  change robbinsMixture (Icc (-1 : ℝ) 1)ᶜ = 0
  rw [robbinsMixture, withDensity_apply _ (measurableSet_Icc.compl)]
  refine setLIntegral_eq_zero measurableSet_Icc.compl fun x hx ↦ ?_
  have hx' : ¬ |x| ≤ 1 := fun h ↦ hx (abs_le.1 h)
  simp [robbinsDensity, hx']

/-- Robbins' mixing distribution has no atom at `0`. -/
lemma robbinsMixture_singleton_zero : robbinsMixture {0} = 0 :=
  withDensity_absolutelyContinuous _ _ (Real.volume_singleton)

end Wang2026Almost
