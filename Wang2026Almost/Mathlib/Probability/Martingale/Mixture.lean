/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.Mathlib.Probability.Martingale.Nonneg
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Mixtures of nonnegative supermartingales

A mixture `n ↦ ∫ l, f l n ∂π` of a measurable family of nonnegative supermartingales `f l` with
respect to a measure `π` on the parameter space is a supermartingale, as soon as
`l ↦ ∫ f l 0 ∂μ` is `π`-integrable (Tonelli's theorem).

## Main statements

* `MeasureTheory.supermartingale_integral_of_integrable`: the general statement, for an s-finite
  mixing measure `π` and `l ↦ ∫ f l 0 ∂μ` integrable.
* `MeasureTheory.supermartingale_integral`: the case of a finite mixing measure and initial
  expectations bounded uniformly in `l`.
* `MeasureTheory.exists_ae_tendsto_setIntegral_of_supermartingale`: the mixture over a set `B` of
  nonnegative supermartingales starting at `1` converges almost surely to a limit of expectation
  at most `π B`.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω L : Type*} {mΩ : MeasurableSpace Ω} {mL : MeasurableSpace L} {μ : Measure Ω}
  {π : Measure L}

/-- **Mixtures of supermartingales.** Let `(f l)_l` be a family of nonnegative supermartingales
such that `(l, ω) ↦ f l n ω` is `mL ⊗ ℱ n`-measurable for each `n`, and `π` an s-finite measure
on the parameter space such that `l ↦ ∫ ω, f l 0 ω ∂μ` is `π`-integrable. Then the mixture
`n ↦ ∫ l, f l n ∂π` is a supermartingale. -/
lemma supermartingale_integral_of_integrable [IsFiniteMeasure μ] [SFinite π]
    {ℱ : Filtration ℕ mΩ} {f : L → ℕ → Ω → ℝ} (hf : ∀ l, Supermartingale (f l) ℱ μ)
    (hf_nonneg : ∀ l n ω, 0 ≤ f l n ω)
    (hmeas : ∀ n, Measurable[mL.prod (ℱ n)] (fun p : L × Ω ↦ f p.1 n p.2))
    (hint : Integrable (fun l ↦ ∫ ω, f l 0 ω ∂μ) π) :
    Supermartingale (fun n ω ↦ ∫ l, f l n ω ∂π) ℱ μ := by
  set G : ℕ → Ω → ℝ≥0∞ := fun n ω ↦ ∫⁻ l, ENNReal.ofReal (f l n ω) ∂π with hG_def
  have hmeas' : ∀ n, Measurable (fun p : L × Ω ↦ f p.1 n p.2) := fun n ↦
    (hmeas n).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (ℱ.le n))) le_rfl
  have hsec : ∀ n ω, Measurable (fun l ↦ f l n ω) := fun n ω ↦
    (hmeas' n).comp measurable_prodMk_right
  have hg_eq : ∀ n ω, ∫ l, f l n ω ∂π = (G n ω).toReal := fun n ω ↦
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun l ↦ hf_nonneg l n ω)
      (hsec n ω).aestronglyMeasurable
  have hGm : ∀ n, Measurable (G n) := fun n ↦ (hmeas' n).ennreal_ofReal.lintegral_prod_left'
  -- Tonelli
  have hswap : ∀ n s, MeasurableSet s →
      ∫⁻ ω in s, G n ω ∂μ = ∫⁻ l, ENNReal.ofReal (∫ ω in s, f l n ω ∂μ) ∂π := by
    intro n s hs
    rw [hG_def, lintegral_lintegral_swap]
    · refine lintegral_congr fun l ↦ ?_
      rw [ofReal_integral_eq_lintegral_ofReal ((hf l).integrable n).integrableOn
        (ae_of_all _ fun ω ↦ hf_nonneg l n ω)]
    · exact ((hmeas' n).comp measurable_swap).ennreal_ofReal.aemeasurable
  have key : ∀ i j, i ≤ j → ∀ s, MeasurableSet[ℱ i] s →
      ∫⁻ ω in s, G j ω ∂μ ≤ ∫⁻ ω in s, G i ω ∂μ := by
    intro i j hij s hs
    rw [hswap j s (ℱ.le i _ hs), hswap i s (ℱ.le i _ hs)]
    exact lintegral_mono fun l ↦ ENNReal.ofReal_le_ofReal ((hf l).setIntegral_le hij hs)
  have hfin : ∀ n, ∫⁻ ω, G n ω ∂μ < ∞ := by
    intro n
    refine lt_of_le_of_lt (by simpa using key 0 n (Nat.zero_le n) Set.univ MeasurableSet.univ) ?_
    rw [← setLIntegral_univ, hswap 0 Set.univ MeasurableSet.univ]
    simpa using (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun l ↦
      integral_nonneg (hf_nonneg l 0))).1 hint.2
  have hG_lt : ∀ n, ∀ᵐ ω ∂μ, G n ω < ∞ := fun n ↦ ae_lt_top (hGm n) (hfin n).ne
  have hint' : ∀ n, Integrable (fun ω ↦ ∫ l, f l n ω ∂π) μ := fun n ↦ by
    simp_rw [hg_eq]
    exact integrable_toReal_of_lintegral_ne_top (hGm n).aemeasurable (hfin n).ne
  have hadapt : StronglyAdapted ℱ (fun n ω ↦ ∫ l, f l n ω ∂π) := fun n ↦ by
    let := ℱ n
    exact (hmeas n).stronglyMeasurable.integral_prod_left'
  refine supermartingale_of_setIntegral_succ_le hadapt hint' fun n s hs ↦ ?_
  simp_rw [hg_eq]
  rw [integral_toReal (hGm _).aemeasurable (ae_restrict_of_ae (hG_lt _)),
    integral_toReal (hGm _).aemeasurable (ae_restrict_of_ae (hG_lt _))]
  exact ENNReal.toReal_mono ((setLIntegral_le_lintegral _ _).trans_lt (hfin n)).ne
    (key n (n + 1) (Nat.le_succ n) s hs)

/-- **Mixtures of supermartingales**, for a finite mixing measure: if `(f l)_l` is a family of
nonnegative supermartingales such that `(l, ω) ↦ f l n ω` is `mL ⊗ ℱ n`-measurable for each `n`
and `∫ ω, f l 0 ω ∂μ ≤ C` for all `l`, then `n ↦ ∫ l, f l n ∂π` is a supermartingale. -/
lemma supermartingale_integral [IsFiniteMeasure μ] [IsFiniteMeasure π]
    {ℱ : Filtration ℕ mΩ} {f : L → ℕ → Ω → ℝ} (hf : ∀ l, Supermartingale (f l) ℱ μ)
    (hf_nonneg : ∀ l n ω, 0 ≤ f l n ω)
    (hmeas : ∀ n, Measurable[mL.prod (ℱ n)] (fun p : L × Ω ↦ f p.1 n p.2))
    (hbdd : ∃ C, ∀ l, ∫ ω, f l 0 ω ∂μ ≤ C) :
    Supermartingale (fun n ω ↦ ∫ l, f l n ω ∂π) ℱ μ := by
  obtain ⟨C, hC⟩ := hbdd
  refine supermartingale_integral_of_integrable hf hf_nonneg hmeas ?_
  have hm : Measurable (fun p : L × Ω ↦ f p.1 0 p.2) :=
    (hmeas 0).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (ℱ.le 0))) le_rfl
  refine Integrable.of_bound (C := C)
    hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable (ae_of_all _ fun l ↦ ?_)
  rw [Real.norm_of_nonneg (integral_nonneg (hf_nonneg l 0))]
  exact hC l

/-- **Mixtures of supermartingales over a set of parameters converge.** Let `f l`, `l ∈ Λ`, be a
family of nonnegative supermartingales starting at `1`, jointly measurable in `(l, ω)`, and `π`
a finite measure on `Λ`. For every set `B ⊆ Λ`, the mixture `∫_B f l n ∂π(l)` converges almost
surely to a nonnegative limit `L` with `∫⁻ L ≤ π B`. -/
lemma exists_ae_tendsto_setIntegral_of_supermartingale {Λ : Type*} {mΛ : MeasurableSpace Λ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {π : Measure Λ}
    [IsFiniteMeasure π] {f : Λ → ℕ → Ω → ℝ} (hf : ∀ l, Supermartingale (f l) ℱ μ)
    (hf_nonneg : ∀ l n ω, 0 ≤ f l n ω)
    (hmeas : ∀ n, Measurable[mΛ.prod (ℱ n)] (fun p : Λ × Ω ↦ f p.1 n p.2))
    (hf0 : ∀ l ω, f l 0 ω = 1) (B : Set Λ) :
    ∃ L : Ω → ℝ, Measurable L ∧ 0 ≤ᵐ[μ] L ∧ ∫⁻ ω, ENNReal.ofReal (L ω) ∂μ ≤ π B ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ l in B, f l n ω ∂π) atTop (𝓝 (L ω)) := by
  have hV := supermartingale_integral (π := π.restrict B) hf hf_nonneg hmeas
    ⟨1, fun l ↦ by simp [hf0]⟩
  obtain ⟨L, hLm, hL, hL0, hLint⟩ := hV.exists_ae_tendsto_of_nonneg fun n ↦
    ae_of_all _ fun ω ↦ integral_nonneg fun l ↦ hf_nonneg l n ω
  refine ⟨L, hLm, hL0, hLint.trans_eq ?_, hL⟩
  simp [hf0]

end MeasureTheory
