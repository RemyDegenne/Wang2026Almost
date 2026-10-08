/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
-- One import per file proving a headline result of formalization.yaml.
import Wang2026Almost.WAR2026.Theorem2_1
import Wang2026Almost.WAR2026.Theorem2_2
import Wang2026Almost.WAR2026.Corollary2_3
import Wang2026Almost.WAR2026.Corollary2_4
import Wang2026Almost.WAR2026.Proposition2_5
import Wang2026Almost.WAR2026.Proposition2_6
import Wang2026Almost.WAR2026.Proposition2_7
import Wang2026Almost.WAR2026.Proposition2_8
import Wang2026Almost.WAR2026.Theorem3_1
import Wang2026Almost.WAR2026.Proposition3_2
import Wang2026Almost.WAR2026.Theorem4_1
import Wang2026Almost.WAR2026.Theorem5_1
import Wang2026Almost.WAR2026.Theorem5_2
import Wang2026Almost.WAR2026.Theorem5_3

/-! # Comparator solution module

The solution side of the [comparator](https://github.com/leanprover/comparator) setup in
`comparator/`: this module imports the project files proving the headline results listed in
`formalization.yaml`, so its environment contains, at the exact names stated (with `sorry`) in
the `comparator/Challenge_*.lean` files, the headline theorems of the paper (see
`comparator/README.md`). -/
