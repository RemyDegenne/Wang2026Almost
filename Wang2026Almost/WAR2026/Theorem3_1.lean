/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

/-!
# Theorem 3.1: the no-cash criterion for null bankruptcy of mixture strategies

Under a non-degenerate null distribution, the wealth of the mixture strategy with mixing
distribution `π` converges almost surely to `π({0})`, the fraction of the wealth kept as cash:
the mixture strategy goes bankrupt iff `π` has no atom at `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting
open scoped Topology

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Theorem 3.1** (no-cash criterion, Wang, Agrawal, Ramdas 2026): for i.i.d. observations `X`
of a non-degenerate law `P` on `[0, 1]` with mean `m`, and a probability measure `π` on
`[-1 / (1 - m), 1 / m]`, the mixture wealth process converges almost surely to `π({0})`. In
particular it converges to `0` almost surely iff `π` has no atom at `0`. -/
theorem tendsto_mixtureWealth (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hnd : P ≠ Measure.dirac m) {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P')
    (hlaw : ∀ n, HasLaw (X n) P P') (π : Measure ℝ) [IsProbabilityMeasure π]
    (hπ : ∀ᵐ l ∂π, l ∈ fractionRange m) :
    (∀ᵐ ω ∂P', Tendsto (fun n ↦ mixtureWealth m π X n ω) atTop (𝓝 (π.real {0}))) ∧
      ((∀ᵐ ω ∂P', Tendsto (fun n ↦ mixtureWealth m π X n ω) atTop (𝓝 0)) ↔ π {0} = 0) := by
  sorry

end Wang2026Almost
