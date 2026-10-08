/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.StrongLaw

/-!
# Convenient forms of the central limit theorem and of Slutsky's lemma

* `TendstoInDistribution.of_map_eq`: convergence in distribution only depends on the law of the
  limit; a limit `Z` under `μ'` can be replaced by the identity under the law `μ'.map Z`;
* `TendstoInDistribution.mul_add_of_tendsto`: Slutsky's lemma with deterministic factors: if
  `X n → Z` in distribution, `a n → a₀` and `b n → b₀`, then `a n X n + b n → a₀ Z + b₀`;
* `tendstoInDistribution_sum_sub_div_sqrt`: the central limit theorem for i.i.d. variables with
  law `P`: `(∑_{k < n} (X k - E_P)) / √n` converges in distribution to `N(0, Var_P)`, stated with
  the identity under `gaussianReal 0 Var[id; P]` as limit;
* `ae_tendsto_sum_comp_div`: the strong law of large numbers for `f (X k)`, `X k` i.i.d. with law
  `P` and `f` integrable for `P`.
-/

@[expose] public section

open MeasureTheory Filter Finset Function
open scoped Topology

namespace MeasureTheory

variable {ι Ω' Ω'' E : Type*} {m' : MeasurableSpace Ω'} {μ' : Measure Ω'}
  [IsProbabilityMeasure μ'] {m'' : MeasurableSpace Ω''} {μ'' : Measure Ω''}
  [IsProbabilityMeasure μ''] {mE : MeasurableSpace E} [TopologicalSpace E]
  [OpensMeasurableSpace E] {l : Filter ι}

/-- Convergence in distribution only depends on the law of the limit. -/
lemma TendstoInDistribution.of_map_eq {X : ι → Ω'' → E} {Z : Ω' → E} {ν : Measure E}
    [IsProbabilityMeasure ν] (h : TendstoInDistribution X l Z (fun _ ↦ μ'') μ')
    (hν : μ'.map Z = ν) :
    TendstoInDistribution X l (id : E → E) (fun _ ↦ μ'') ν where
  forall_aemeasurable := h.forall_aemeasurable
  aemeasurable_limit := aemeasurable_id
  tendsto := by
    convert h.tendsto using 2
    simp [hν]

/-- **Slutsky's lemma** with deterministic factors: if `X n → Z` in distribution, `a n → a₀` and
`b n → b₀`, then `a n * X n + b n → a₀ * Z + b₀` in distribution. -/
lemma TendstoInDistribution.mul_add_of_tendsto {X : ℕ → Ω'' → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ μ'') μ') {a b : ℕ → ℝ} {a₀ b₀ : ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀)) :
    TendstoInDistribution (fun n ω ↦ a n * X n ω + b n) atTop (fun ω ↦ a₀ * Z ω + b₀)
      (fun _ ↦ μ'') μ' := by
  have hY : TendstoInMeasure μ'' (fun n (_ : Ω'') ↦ (a n, b n)) atTop (fun _ ↦ (a₀, b₀)) :=
    tendstoInMeasure_of_tendsto_ae (fun _ ↦ aestronglyMeasurable_const)
      (ae_of_all _ fun _ ↦ ha.prodMk_nhds hb)
  exact h.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : ℝ × ℝ × ℝ ↦ p.2.1 * p.1 + p.2.2) (by fun_prop) hY
    (fun _ ↦ aemeasurable_const)

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Central limit theorem** for i.i.d. variables with law `P`: `(∑_{k < n} (X k - E_P)) / √n`
converges in distribution to the centered Gaussian with the variance of `P`. -/
lemma tendstoInDistribution_sum_sub_div_sqrt {X : ℕ → Ω → ℝ} {P : Measure ℝ}
    (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ)
    (hP : MemLp id 2 P) :
    TendstoInDistribution (fun n ω ↦ (∑ k ∈ range n, (X k ω - ∫ x, x ∂P)) / √n) atTop
      (id : ℝ → ℝ) (fun _ ↦ μ) (gaussianReal 0 Var[id; P].toNNReal) := by
  have hident : ∀ i, IdentDistrib (X i) (X 0) μ μ :=
    fun i ↦ (hlaw i).identDistrib (hlaw 0)
  have hX0 : MemLp (X 0) 2 μ := by
    rw [← (hlaw 0).map_eq] at hP
    exact (memLp_map_measure_iff aestronglyMeasurable_id (hlaw 0).aemeasurable).1 hP
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum_sub (Y := (id : ℝ → ℝ))
    (P' := gaussianReal 0 Var[X 0; μ].toNNReal) HasLaw.id hX0 hindep hident
  rw [(hlaw 0).variance_eq, (hlaw 0).integral_eq] at hclt
  refine hclt.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
  simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  rw [div_eq_inv_mul]

omit [IsProbabilityMeasure μ] in
/-- **Strong law of large numbers** for `f (X k)`, with `X k` i.i.d. with law `P` and `f`
integrable for `P`: `(1/n) ∑_{k < n} f (X k) → E_P[f]` almost surely. -/
lemma ae_tendsto_sum_comp_div {X : ℕ → Ω → ℝ} {P : Measure ℝ}
    (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : Integrable f P) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ ↦ (∑ k ∈ range n, f (X k ω)) / n) atTop (𝓝 (∫ x, f x ∂P)) := by
  have hlaw' : ∀ n, HasLaw (fun ω ↦ f (X n ω)) (P.map f) μ := fun n ↦
    (hasLaw_map hf.aemeasurable).comp (hlaw n)
  have hident : ∀ i, IdentDistrib (fun ω ↦ f (X i ω)) (fun ω ↦ f (X 0 ω)) μ μ :=
    fun i ↦ (hlaw' i).identDistrib (hlaw' 0)
  have hint : Integrable (fun ω ↦ f (X 0 ω)) μ := (hlaw 0).integrable_comp hfi
  have hpair : Pairwise ((· ⟂ᵢ[μ] ·) on fun i ω ↦ f (X i ω)) := fun i j hij ↦
    (hindep.comp (fun _ ↦ f) (fun _ ↦ hf)).indepFun hij
  have hmean : μ[fun ω ↦ f (X 0 ω)] = ∫ x, f x ∂P :=
    (hlaw 0).integral_comp hf.aestronglyMeasurable
  filter_upwards [strong_law_ae (fun i ω ↦ f (X i ω)) hint hpair hident] with ω hω
  rw [hmean] at hω
  refine hω.congr fun n ↦ ?_
  rw [smul_eq_mul, inv_mul_eq_div]

end ProbabilityTheory
