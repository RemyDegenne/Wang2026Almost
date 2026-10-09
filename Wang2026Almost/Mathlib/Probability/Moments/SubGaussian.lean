/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.Mathlib.Probability.Independence.Freezing
public import Wang2026Almost.Mathlib.Probability.Kernel.Condexp
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Conditionally sub-Gaussian random variables at a random parameter

A random variable `X` which is conditionally `c`-sub-Gaussian given a σ-algebra `m` satisfies the
moment bound `E[exp (s X) | m] ≤ exp (c s² / 2)` also for an `m`-measurable random parameter `s`.
We state it in integrated form: for every `m`-measurable `g ≥ 0`,
`∫⁻ g * exp (s * X) ≤ ∫⁻ g * exp (c * s ^ 2 / 2)`. The same holds for a sub-Gaussian `X`
independent of `m`, without any assumption on the measurable space, and such an `X` is
conditionally sub-Gaussian given `m` when the space is standard Borel.

## Main statements

* `ProbabilityTheory.HasCondSubgaussianMGF.lintegral_mul_exp_le`: the moment bound at an
  `m`-measurable parameter;
* `ProbabilityTheory.HasSubgaussianMGF.lintegral_mul_exp_le_of_indep`: the same for `X`
  independent of `m`;
* `ProbabilityTheory.HasSubgaussianMGF.hasCondSubgaussianMGF_of_indep`: a sub-Gaussian random
  variable independent of `m` is conditionally sub-Gaussian given `m`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c : ℝ≥0}

/-- **Conditional moment bound at a random parameter.** If `X` is measurable and conditionally
`c`-sub-Gaussian given `m`, then for every `m`-measurable `s` and `m`-measurable `g ≥ 0`,
`∫⁻ g * exp (s * X) ≤ ∫⁻ g * exp (c * s ^ 2 / 2)`. -/
lemma HasCondSubgaussianMGF.lintegral_mul_exp_le [StandardBorelSpace Ω] [IsFiniteMeasure μ]
    {hm : m ≤ mΩ} (h : HasCondSubgaussianMGF m hm X c μ) (hX : Measurable X) {s : Ω → ℝ}
    (hs : Measurable[m] s) {g : Ω → ℝ≥0∞} (hg : Measurable[m] g) :
    ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (s ω * X ω)) ∂μ
      ≤ ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (c * s ω ^ 2 / 2)) ∂μ := by
  have hΦ : Measurable
      (fun p : (ℝ≥0∞ × ℝ) × Ω ↦ p.1.1 * ENNReal.ofReal (Real.exp (p.1.2 * X p.2))) := by
    fun_prop
  rw [lintegral_comp_condExpKernel hm (hg.prodMk hs) hΦ]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_of_ae_trim hm (Kernel.HasSubgaussianMGF.mgf_le h),
    ae_of_ae_trim hm (Kernel.HasSubgaussianMGF.ae_forall_integrable_exp_mul h)] with ω hmgf hint
  rw [lintegral_const_mul _ (by fun_prop)]
  gcongr
  rw [← ofReal_integral_eq_lintegral_ofReal (hint (s ω))
    (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)]
  exact ENNReal.ofReal_le_ofReal (hmgf (s ω))

/-- **Moment bound at a random parameter, independent case.** If `X` is measurable,
`c`-sub-Gaussian and independent of `m`, then for every `m`-measurable `s` and `m`-measurable
`g ≥ 0`, `∫⁻ g * exp (s * X) ≤ ∫⁻ g * exp (c * s ^ 2 / 2)`. -/
lemma HasSubgaussianMGF.lintegral_mul_exp_le_of_indep [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    (h : HasSubgaussianMGF X c μ) (hX : Measurable X)
    (hindep : Indep (MeasurableSpace.comap X inferInstance) m μ) {s : Ω → ℝ}
    (hs : Measurable[m] s) {g : Ω → ℝ≥0∞} (hg : Measurable[m] g) :
    ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (s ω * X ω)) ∂μ
      ≤ ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (c * s ω ^ 2 / 2)) ∂μ := by
  have hΦ : Measurable
      (fun p : (ℝ≥0∞ × ℝ) × ℝ ↦ p.1.1 * ENNReal.ofReal (Real.exp (p.1.2 * p.2))) := by
    fun_prop
  have h_eq := setLIntegral_comp_of_indep hm (hg.prodMk hs) hX hindep hΦ MeasurableSet.univ
  simp only [Measure.restrict_univ] at h_eq
  rw [h_eq]
  refine lintegral_mono fun ω ↦ ?_
  rw [lintegral_const_mul _ (by fun_prop), lintegral_map (by fun_prop) hX,
    ← ofReal_integral_eq_lintegral_ofReal (h.integrable_exp_mul (s ω))
      (ae_of_all _ fun _ ↦ (Real.exp_pos _).le)]
  gcongr
  exact h.mgf_le (s ω)

/-- A measurable `c`-sub-Gaussian random variable independent of a sub-σ-algebra `m` is
conditionally `c`-sub-Gaussian given `m`. -/
lemma HasSubgaussianMGF.hasCondSubgaussianMGF_of_indep [StandardBorelSpace Ω]
    [IsProbabilityMeasure μ] (hm : m ≤ mΩ) (h : HasSubgaussianMGF X c μ) (hX : Measurable X)
    (hindep : Indep (MeasurableSpace.comap X inferInstance) m μ) :
    HasCondSubgaussianMGF m hm X c μ := by
  refine Kernel.HasSubgaussianMGF.of_rat (fun t ↦ ?_) (fun q ↦ ?_)
  · rw [condExpKernel_comp_trim]
    exact h.integrable_exp_mul t
  · have h1 := condExp_ae_eq_trim_integral_condExpKernel hm (h.integrable_exp_mul q)
    have h2 : μ[fun ω ↦ Real.exp (q * X ω) | m]
        =ᵐ[μ.trim hm] fun _ ↦ μ[fun ω ↦ Real.exp (q * X ω)] :=
      StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable hm stronglyMeasurable_condExp
        stronglyMeasurable_const (condExp_indep_eq hX.comap_le hm
          ((by fun_prop : Measurable (fun x ↦ Real.exp (q * x))).comp
            (comap_measurable X)).stronglyMeasurable hindep)
    filter_upwards [h1, h2] with ω h1 h2
    rw [mgf, ← h1, h2]
    exact h.mgf_le q

end ProbabilityTheory
