/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Distributions.Beta

/-!
# The mixing distributions of the universal portfolio and of Robbins' mixture

The two mixing distributions on the bet fractions used by Orabona and Jun (2023) and discussed in
Proposition 3.2 of Wang, Agrawal, Ramdas (2026):

* `betaMixture a b`: the Beta distribution with parameters `a, b` rescaled to `[-1, 1]` (the
  universal portfolio strategy);
* `robbinsMixture`: Robbins' iterated-logarithm mixing distribution on `[-1, 1]`, with density
  `robbinsDensity l = log log C / (2 |l| log (C / |l|) (log log (C / |l|))²)` for `|l| ≤ 1`,
  `C = robbinsConst = 6.6 e`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Wang2026Almost

/-- The mixing distribution of the universal portfolio strategy: the Beta distribution with
parameters `a, b` rescaled to `[-1, 1]`. -/
noncomputable def betaMixture (a b : ℝ) : Measure ℝ :=
  (betaMeasure a b).map (fun x ↦ ((2 : ℕ) : ℝ) * x - 1)

/-- The constant `C = 6.6 e` of Robbins' mixture. -/
noncomputable def robbinsConst : ℝ := 6.6 * Real.exp 1

/-- The density of Robbins' iterated-logarithm mixing distribution on `[-1, 1]`:
`log log C / (2 |l| log (C / |l|) (log log (C / |l|))²)`. -/
noncomputable def robbinsDensity (l : ℝ) : ℝ :=
  if |l| ≤ 1 then
    Real.log (Real.log robbinsConst) /
      (((2 : ℕ) : ℝ) * |l| * Real.log (robbinsConst / |l|) *
        Real.log (Real.log (robbinsConst / |l|)) ^ 2)
  else 0

/-- Robbins' iterated-logarithm mixing distribution. -/
noncomputable def robbinsMixture : Measure ℝ :=
  volume.withDensity fun l ↦ ENNReal.ofReal (robbinsDensity l)

end Wang2026Almost
