/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Landau notation in probability and almost surely

For a sequence of real random variables `X n` on a measure space `(Ω, P)` and a sequence of
nonrandom numbers `a n` (Mathlib has the deterministic `Asymptotics.IsBigO` and the convergence in
probability `MeasureTheory.TendstoInMeasure`, but no stochastic Landau notation).

## Main definitions

* `IsBigOInProb P X a` (`X n = O_p(a n)`): for every `ε > 0` there is `M > 0` such that
  `P(|X n| ≤ M a n) ≥ 1 - ε` for all but finitely many `n`;
* `IsBigOmegaInProb P X a` (`X n = Ω_p(a n)`): for every `ε > 0` there is `δ > 0` such that
  `P(|X n| ≥ δ a n) ≥ 1 - ε` for all but finitely many `n`;
* `IsBigOAE P X a` (`X n = O_{a.s.}(a n)`) and `IsBigOmegaAE P X a` (`X n = Ω_{a.s.}(a n)`): the
  pathwise events `X n = O(a n)` and `X n = Ω(a n)` (that is, `a n = O(X n)`) happen `P`-almost
  surely.
-/

@[expose] public section

open Filter MeasureTheory Asymptotics

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)

/-- `X n = O_p(a n)`: for every `ε > 0` there is `M > 0` such that `P(|X n| ≤ M a n) ≥ 1 - ε`
for all but finitely many `n`. -/
def IsBigOInProb (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, 1 - ε ≤ P.real {ω | |X n ω| ≤ M * a n}

/-- `X n = Ω_p(a n)`: for every `ε > 0` there is `δ > 0` such that `P(|X n| ≥ δ a n) ≥ 1 - ε`
for all but finitely many `n`. -/
def IsBigOmegaInProb (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, 1 - ε ≤ P.real {ω | δ * a n ≤ |X n ω|}

/-- `X n = O_{a.s.}(a n)`: almost surely, the path `n ↦ X n ω` is `O(a n)`. -/
def IsBigOAE (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, (fun n ↦ X n ω) =O[atTop] a

/-- `X n = Ω_{a.s.}(a n)`: almost surely, the path `n ↦ X n ω` is `Ω(a n)`, that is
`a n = O(X n ω)`. -/
def IsBigOmegaAE (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, a =O[atTop] (fun n ↦ X n ω)

end ProbabilityTheory
