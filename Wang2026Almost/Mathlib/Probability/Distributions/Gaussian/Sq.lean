/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.ComplexMGF
public import Wang2026Almost.Mathlib.Probability.Distributions.ChiSquare

/-!
# The square of a standard Gaussian

The law of `X ^ 2` for `X ~ N(0, 1)` is the chi-squared distribution with one degree of freedom.
The proof compares moment generating functions, which determine distributions when they are finite
in a neighbourhood of `0` (Mathlib only has the equality of the complex moment generating functions
on a strip, `eqOn_complexMGF_of_mgf`, and the injectivity of the complex moment generating
function `Measure.ext_of_complexMGF_eq`).

## Main statements

* `MeasureTheory.Measure.ext_of_eqOn_mgf`, `MeasureTheory.Measure.ext_of_mgf_eq`: **moment
  generating functions finite near `0` determine distributions**;
* `ProbabilityTheory.integral_exp_mul_sq_gaussianReal_zero_one`: for `X ~ N(0, 1)` and `t < 1/2`,
  `E[exp (t X²)] = (1 - 2t) ^ (-1/2)`; `not_integrable_exp_mul_sq_gaussianReal`: `exp (t X²)` is
  not integrable for `t ≥ 1/2`;
* `ProbabilityTheory.gaussianReal_map_sq`: `(gaussianReal 0 1).map (· ^ 2) = chiSquareMeasure 1`.
-/

@[expose] public section

open MeasureTheory
open scoped Topology NNReal

namespace ProbabilityTheory

section MGF

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {μ' : Measure Ω'} {X : Ω → ℝ} {Y : Ω' → ℝ}

/-- **Moment generating functions determine distributions**, local form: if the moment generating
functions of `X` and `Y` are finite in a neighbourhood of `0` and agree near `0`, then `X` and `Y`
have the same law. The two complex moment generating functions are analytic on a common vertical
strip containing the imaginary axis and agree near `0` on the real axis, hence on the imaginary
axis, where they are the characteristic functions. -/
lemma _root_.MeasureTheory.Measure.ext_of_eqOn_mgf [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ')
    (hX0 : 0 ∈ interior (integrableExpSet X μ)) (hY0 : 0 ∈ interior (integrableExpSet Y μ'))
    (h : mgf X μ =ᶠ[𝓝 0] mgf Y μ') :
    μ.map X = μ'.map Y := by
  -- the common vertical strip on which both `complexMGF` are analytic
  set S : Set ℝ := interior (integrableExpSet X μ) ∩ interior (integrableExpSet Y μ') with hS
  set T : Set ℂ := {z : ℂ | z.re ∈ S} with hT
  have hS0 : (0 : ℝ) ∈ S := ⟨hX0, hY0⟩
  have hSconv : Convex ℝ S :=
    convex_integrableExpSet.interior.inter convex_integrableExpSet.interior
  have hTconn : IsPreconnected T := (hSconv.linear_preimage Complex.reLm).isPreconnected
  have hXan : AnalyticOnNhd ℂ (complexMGF X μ) T :=
    analyticOnNhd_complexMGF.mono fun z hz ↦ hz.1
  have hYan : AnalyticOnNhd ℂ (complexMGF Y μ') T :=
    analyticOnNhd_complexMGF.mono fun z hz ↦ hz.2
  -- the two functions agree frequently near `0`, along the real axis
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF X μ z = complexMGF Y μ' z := by
    have hreal : ∃ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), complexMGF X μ x = complexMGF Y μ' x := by
      refine Filter.Eventually.frequently ?_
      filter_upwards [h.filter_mono nhdsWithin_le_nhds] with x hx
      rw [complexMGF_ofReal, complexMGF_ofReal, hx]
    rw [Filter.frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := hreal
    refine ⟨fun n ↦ xs n, ?_, fun n ↦ by simp [hx_eq n]⟩
    rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
    refine ⟨?_, by simpa using hx_tendsto.2⟩
    have := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hx_tendsto.1
    simpa [Function.comp_def] using this
  have hEqOn : Set.EqOn (complexMGF X μ) (complexMGF Y μ') T :=
    hXan.eqOn_of_preconnected_of_frequently_eq hYan hTconn (z₀ := 0) (by simp [hT, hS0]) hfreq
  refine Measure.ext_of_charFun (funext fun t ↦ ?_)
  rw [← complexMGF_mul_I hX, ← complexMGF_mul_I hY]
  exact hEqOn (by simp [hT, hS0])

/-- **Moment generating functions determine distributions**: if two random variables have the same
moment generating function, and it is finite in a neighbourhood of `0`, then they have the same
law. -/
lemma _root_.MeasureTheory.Measure.ext_of_mgf_eq [IsProbabilityMeasure μ] [IsFiniteMeasure μ']
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ')
    (h0 : 0 ∈ interior (integrableExpSet X μ)) (h : mgf X μ = mgf Y μ') :
    μ.map X = μ'.map Y :=
  Measure.ext_of_eqOn_mgf hX hY h0 (by rwa [← integrableExpSet_eq_of_mgf h])
    (Filter.Eventually.of_forall fun x ↦ congrFun h x)

end MGF

section Gaussian

open Real

/-- Integrability with respect to `N(m, v)`, `v ≠ 0`, is integrability against its density. -/
lemma integrable_gaussianReal_iff {m : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → ℝ} :
    Integrable g (gaussianReal m v) ↔ Integrable (fun x ↦ gaussianPDFReal m v x * g x) := by
  rw [gaussianReal_of_var_ne_zero _ hv, integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF _ _) (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

/-- The density of `N(0, 1)` times `exp (t x²)` is a centered Gaussian function. -/
lemma gaussianPDFReal_zero_one_mul_exp_mul_sq (t x : ℝ) :
    gaussianPDFReal 0 1 x * exp (t * x ^ 2) = (√(2 * π))⁻¹ * exp (-(1 / 2 - t) * x ^ 2) := by
  rw [gaussianPDFReal, mul_assoc, ← exp_add]
  congr 2
  · simp
  · push_cast
    ring

/-- For `X ~ N(0, 1)` and `t < 1/2`, `exp (t X²)` is integrable. -/
lemma integrable_exp_mul_sq_gaussianReal_zero_one {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x ↦ exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [integrable_gaussianReal_iff one_ne_zero]
  simp_rw [gaussianPDFReal_zero_one_mul_exp_mul_sq]
  exact (integrable_exp_neg_mul_sq (by linarith)).const_mul _

/-- **Moment generating function of the square of a standard Gaussian**: for `X ~ N(0, 1)` and
`t < 1/2`, `E[exp (t X²)] = (1 - 2t) ^ (-1/2)`. -/
lemma integral_exp_mul_sq_gaussianReal_zero_one {t : ℝ} (ht : t < 1 / 2) :
    ∫ x, exp (t * x ^ 2) ∂gaussianReal 0 1 = (1 - 2 * t) ^ (-(1 : ℝ) / 2) := by
  have h1 : 0 < 1 - 2 * t := by linarith
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [smul_eq_mul, gaussianPDFReal_zero_one_mul_exp_mul_sq]
  have h2 : π / (1 / 2 - t) = 2 * π * (1 - 2 * t)⁻¹ := by
    field_simp
  rw [integral_const_mul, integral_gaussian, h2,
    Real.sqrt_mul (x := 2 * π) (by positivity) (1 - 2 * t)⁻¹, ← mul_assoc,
    inv_mul_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne', one_mul, Real.sqrt_eq_rpow,
    Real.inv_rpow h1.le, ← Real.rpow_neg h1.le]
  norm_num

/-- For `X ~ N(0, 1)` and `1/2 ≤ t`, `exp (t X²)` is not integrable: the integrand against the
density is bounded below by the constant `(√(2π))⁻¹`. -/
lemma not_integrable_exp_mul_sq_gaussianReal {t : ℝ} (ht : 1 / 2 ≤ t) :
    ¬ Integrable (fun x : ℝ ↦ exp (t * x ^ 2)) (gaussianReal 0 1) := by
  intro hint
  rw [integrable_gaussianReal_iff one_ne_zero] at hint
  simp_rw [gaussianPDFReal_zero_one_mul_exp_mul_sq] at hint
  have hconst : Integrable (fun _ : ℝ ↦ (√(2 * π))⁻¹) volume := by
    refine Integrable.mono' hint (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have : (1 : ℝ) ≤ exp (-(1 / 2 - t) * x ^ 2) :=
      Real.one_le_exp (mul_nonneg (by linarith) (sq_nonneg x))
    calc (√(2 * π))⁻¹ = (√(2 * π))⁻¹ * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  rw [integrable_const_iff] at hconst
  rcases hconst with h | h
  · have : (0 : ℝ) < √(2 * π) := Real.sqrt_pos.2 (by positivity)
    simp only [inv_eq_zero] at h
    linarith
  · exact (isFiniteMeasure_iff _).not.2 (by simp) h

/-- **The square of a standard Gaussian has the chi-squared distribution with one degree of
freedom**: both laws have the moment generating function `(1 - 2t) ^ (-1/2)` for `t < 1/2`, and
`+∞` (in Lean, `0`: non-integrable) for `t ≥ 1/2`. -/
lemma gaussianReal_map_sq : (gaussianReal 0 1).map (fun x ↦ x ^ 2) = chiSquareMeasure 1 := by
  have hmgf : mgf (fun x ↦ x ^ 2) (gaussianReal 0 1) = mgf id (chiSquareMeasure 1) := by
    funext t
    rcases lt_or_ge t (1 / 2) with h | h
    · rw [mgf, integral_exp_mul_sq_gaussianReal_zero_one h, mgf_chiSquareMeasure one_ne_zero h]
      norm_num
    · rw [mgf, mgf, integral_undef (not_integrable_exp_mul_sq_gaussianReal h), integral_undef]
      simpa [chiSquareMeasure] using
        not_integrable_exp_mul_gammaMeasure (a := (1 : ℝ) / 2) (r := 1 / 2)
          (t := t) (by positivity) (by norm_num) (by linarith)
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet (fun x ↦ x ^ 2) (gaussianReal 0 1)) :=
    mem_interior.2 ⟨Set.Iio (1 / 2), fun x hx ↦ integrable_exp_mul_sq_gaussianReal_zero_one hx,
      isOpen_Iio, by norm_num⟩
  have := Measure.ext_of_mgf_eq (μ := gaussianReal 0 1) (μ' := chiSquareMeasure 1)
    (by fun_prop) aemeasurable_id h0 hmgf
  rwa [Measure.map_id] at this

end Gaussian

end ProbabilityTheory
