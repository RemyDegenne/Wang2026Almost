/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.GrapaLimit
public import Wang2026Almost.LeanMachineLearning.Betting.PlugIn
public import Wang2026Almost.LeanMachineLearning.Betting.Strategies
public import Wang2026Almost.Mathlib.Probability.AsymptoticsInProbability
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Proposition 2.6: null bankruptcy of the GRAPA bettor

Under a null distribution on `[0, 1]` with mean `m` and variance `σ² > 0`, the GRAPA
(follow-the-leader) bet fractions satisfy the almost sure Bahadur expansion
`√n gr n = S n / (σ² √n) + o_{a.s.}(n^{-1/4} log n)` with `S n = ∑_{k < n} (X k - m)`, hence
`√n gr n → N(0, σ⁻²)` in distribution and `gr n = Ω_p(n^{-1/2})`, and the GRAPA wealth process
converges to `0` almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting Real Asymptotics
open scoped Topology ProbabilityTheory

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Proposition 2.6** (Wang, Agrawal, Ramdas 2026): for i.i.d. observations `X` of law `P` on
`[0, 1]` with mean `m` and variance `σ² > 0`, a GRAPA bet fraction process `gr` (`gr n` maximizes
the hindsight wealth of the first `n` rounds) satisfies the almost sure Bahadur expansion
`√n gr n = S n / (σ² √n) + o_{a.s.}(n^{-1/4} log n)`, `S n = ∑_{k < n} (X k - m)`, hence
`√n gr n → N(0, σ⁻²)` in distribution and `gr n = Ω_p(n^{-1/2})`, and the GRAPA wealth process
converges to `0` almost surely. -/
theorem grapa_bankrupt (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hvar : 0 < Var[id; P]) {X gr : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P')
    (hlaw : ∀ n, HasLaw (X n) P P') (hgr : IsGrapa m X gr) :
    (∀ᵐ ω ∂P', (fun n : ℕ ↦ √n * gr n ω - (∑ k ∈ Finset.range n, (X k ω - m)) / (Var[id; P] * √n))
        =o[atTop] fun n : ℕ ↦ (n : ℝ) ^ (-1 / 4 : ℝ) * Real.log n) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ √n * gr n ω) atTop (id : ℝ → ℝ) (fun _ ↦ P')
        (gaussianReal 0 ((Var[id; P])⁻¹).toNNReal) ∧
      IsBigOmegaInProb P' gr (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) ∧
      ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m gr X n ω) atTop (𝓝 0) := by
  have hΩ := isBigOmegaInProb_grapa hP hm hvar hX hindep hlaw hgr
  refine ⟨ae_isLittleO_grapa hP hm hvar hX hindep hlaw hgr,
    tendstoInDistribution_sqrt_mul_grapa hP hm hvar hX hindep hlaw hgr, hΩ, ?_⟩
  exact tendsto_wealth_zero_of_isBigOmega_of_isPlugIn hP hm (ne_dirac_of_variance_pos hvar) hX
    hindep hlaw hgr.1 (fun n ↦ ae_of_all _ fun ω ↦ (hgr.2 n ω).1) (Or.inl hΩ)

end Wang2026Almost
