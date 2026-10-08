/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gamma

/-!
# Exponential moments of the gamma distribution

Mathlib has the gamma distribution `gammaMeasure a r` (shape `a`, rate `r`) but not its moment
generating function.

## Main statements

* `integral_exp_mul_gammaMeasure`: `∫ exp (t x) dγ(a, r) = (r / (r - t)) ^ a` for `t < r`;
* `integrable_exp_mul_gammaMeasure`, `not_integrable_exp_mul_gammaMeasure`: `exp (t x)` is
  integrable for the gamma distribution if and only if `t < r`.
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ENNReal

namespace ProbabilityTheory

variable {a r t : ℝ}

/-- The moment generating function of the gamma distribution: `∫ exp (t x) dγ(a, r)`
is `(r / (r - t)) ^ a` for `t < r`. -/
lemma integral_exp_mul_gammaMeasure (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    ∫ x, exp (t * x) ∂gammaMeasure a r = (r / (r - t)) ^ a := by
  have hrt : 0 < r - t := by linarith
  have hmeas : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas
    (ae_of_all _ fun x ↦ by simp [gammaPDF])]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  have hzero : ∀ x, x ∉ Ici (0 : ℝ) → gammaPDFReal a r x * exp (t * x) = 0 := by
    intro x hx
    rw [gammaPDFReal, ite_eq_right (by simpa using hx), zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, integral_Ici_eq_integral_Ioi,
    setIntegral_congr_fun (g := fun x ↦ r ^ a / Gamma a * (x ^ (a - 1) * exp (-((r - t) * x))))
      measurableSet_Ioi (fun x hx ↦ ?_), integral_const_mul,
    integral_rpow_mul_exp_neg_mul_Ioi ha hrt, Real.div_rpow hr.le hrt.le,
    show (1 : ℝ) / (r - t) = (r - t)⁻¹ by ring, Real.inv_rpow hrt.le]
  · field_simp
  · rw [gammaPDFReal, ite_eq_left (le_of_lt hx), mul_assoc, mul_assoc, ← exp_add]
    ring_nf

/-- For `t < r`, `exp (t x)` is integrable for the gamma distribution: the integrand is a multiple
of the gamma density with rate `r - t`. -/
lemma integrable_exp_mul_gammaMeasure (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x ↦ exp (t * x)) (gammaMeasure a r) := by
  have hrt : 0 < r - t := by linarith
  have hmeas : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hpdf : Integrable (gammaPDFReal a (r - t)) := by
    refine ⟨(stronglyMeasurable_gammaPDFReal a (r - t)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gammaPDFReal_nonneg ha hrt))]
    rw [show (fun x ↦ ENNReal.ofReal (gammaPDFReal a (r - t) x)) = gammaPDF a (r - t) from rfl,
      lintegral_gammaPDF_eq_one ha hrt]
    exact ENNReal.one_lt_top
  rw [gammaMeasure, integrable_withDensity_iff hmeas (ae_of_all _ fun x ↦ by simp [gammaPDF])]
  refine ((hpdf.const_mul ((r / (r - t)) ^ a)).congr (ae_of_all _ fun x ↦ ?_)).congr
    (ae_of_all _ fun x ↦ rfl)
  simp only [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
  rcases le_or_gt 0 x with hx | hx
  · have hG : Gamma a ≠ 0 := (Gamma_pos_of_pos ha).ne'
    have hrta : (r - t) ^ a ≠ 0 := (Real.rpow_pos_of_pos hrt a).ne'
    have hcomb : exp (t * x) * exp (-(r * x)) = exp (-((r - t) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [gammaPDFReal, gammaPDFReal, ite_eq_left hx, ite_eq_left hx, Real.div_rpow hr.le hrt.le,
      show exp (t * x) * (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x)))
        = r ^ a / Gamma a * x ^ (a - 1) * (exp (t * x) * exp (-(r * x))) by ring, hcomb]
    field_simp
  · rw [gammaPDFReal, gammaPDFReal, ite_eq_right (by linarith), ite_eq_right (by linarith)]
    ring

/-- For `r ≤ t`, `exp (t x)` is *not* integrable for the gamma distribution: on `(1, ∞)` the
integrand dominates `x ↦ c x ^ (a - 1)`, which is not integrable there since `a - 1 ≥ -1`. -/
lemma not_integrable_exp_mul_gammaMeasure (ha : 0 < a) (hr : 0 < r) (ht : r ≤ t) :
    ¬ Integrable (fun x ↦ exp (t * x)) (gammaMeasure a r) := by
  have hmeas : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have hG : 0 < Gamma a := Gamma_pos_of_pos ha
  have hc : 0 < r ^ a / Gamma a := by positivity
  intro hint
  rw [gammaMeasure, integrable_withDensity_iff hmeas (ae_of_all _ fun x ↦ by simp [gammaPDF])]
    at hint
  have hint' : IntegrableOn (fun x ↦ exp (t * x) * (gammaPDF a r x).toReal) (Ioi 1) :=
    hint.integrableOn
  have hsmall : IntegrableOn (fun x ↦ r ^ a / Gamma a * x ^ (a - 1)) (Ioi 1) := by
    refine Integrable.mono' hint' (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioi ?_)
    intro x hx
    simp only [mem_Ioi] at hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hcomb : exp (t * x) * (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x)))
        = r ^ a / Gamma a * x ^ (a - 1) * exp ((t - r) * x) := by
      rw [show r ^ a / Gamma a * x ^ (a - 1) * exp ((t - r) * x)
          = r ^ a / Gamma a * x ^ (a - 1) * (exp (t * x) * exp (-(r * x))) by
        rw [← Real.exp_add]; congr 1; ring_nf]
      ring
    rw [Real.norm_of_nonneg (by positivity), gammaPDF,
      ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), gammaPDFReal, ite_eq_left hx0.le, hcomb]
    have h1 : (1 : ℝ) ≤ exp ((t - r) * x) := Real.one_le_exp (by nlinarith)
    have h2 : (0 : ℝ) < x ^ (a - 1) := Real.rpow_pos_of_pos hx0 _
    nlinarith [mul_pos hc h2]
  have : IntegrableOn (fun x : ℝ ↦ x ^ (a - 1)) (Ioi 1) := by
    have := hsmall.const_mul (Gamma a / r ^ a)
    refine this.congr (ae_of_all _ fun x ↦ ?_)
    field_simp
  rw [integrableOn_Ioi_rpow_iff one_pos] at this
  linarith

end ProbabilityTheory
