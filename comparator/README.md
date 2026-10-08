# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
without having to read or trust the Lean development in `Wang2026Almost/`.

**Status.** Phase 1 (2026-10-08): the 16 challenges are generated and compile
(`lake build Comparator`); the headline theorems are still `sorry` in the project, so comparator
fails on `sorryAx` until phase 2 proves them.

Each challenge is one self-contained file whose transitive imports resolve to Mathlib and Lean
core only, the shape the [Palomar registry](https://palomar-registry.org/) enforces: no LML, no
project modules, no sibling helpers.

## The trust story

For each headline theorem `Wang2026Almost.<name>` there is a challenge file `Challenge_<name>.lean` and a
config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Theorem 2.1 (sum-of-squares criterion) | `sum_sq_criterion` |
| Theorem 2.2 (a.s. divergence of `Σ Ω_p(1/n)`) | `ae_not_summable_of_isBigOmegaInProb` |
| Corollary 2.3 (`Σ S_n²/n² = ∞`) | `ae_not_summable_sum_sq_div_sq` |
| Corollary 2.4 (`n^{-1/2}` criterion) | `tendsto_wealth_zero_of_isBigOmega` |
| Proposition 2.5 (KT) | `kt_bankrupt` |
| Proposition 2.6 (GRAPA) | `grapa_bankrupt` |
| Proposition 2.7 (aGRAPA) | `agrapa_bankrupt` |
| Proposition 2.8 (predictable hedging) | `hedged_bankrupt` |
| Theorem 3.1 (no-cash criterion) | `tendsto_mixtureWealth` |
| Proposition 3.2 (universal portfolio, Robbins) | `tendsto_mixtureWealth_betaMixture`, `tendsto_mixtureWealth_robbinsMixture` |
| Theorem 4.1 (improvability) | `exists_improve` |
| Theorem 5.1 (χ² limit, unbounded regret) | `tendstoInDistribution_hindsightLogWealth`, `not_bddAbove_logRegret_of_tendsto_wealth_zero` |
| Theorem 5.2 (sum-of-squares criterion II) | `sum_sq_criterion_subgaussian` |
| Theorem 5.3 (no-cash criterion II) | `tendsto_subgaussianMixtureTest` |

Each challenge states the theorem with `sorry`, with every definition the statement rests on
copied verbatim from its source by [challenge-gen](https://github.com/LeanTrustBuilders/challenge-gen):
the project's definitions and the LML declarations they build on. A reader checks the *statement*
(the challenge file) by hand and lets comparator check that the project proves exactly it, with
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, the proofs replayed through the
kernel. The config also lists the lemmas the definitions use, left `sorry` in the challenge and
proved by the project, and the theorems Lean makes of the proofs inside definitions.

## Regenerating and running

`scripts/make-challenges.py` regenerates every challenge and config from `targets.txt`;
`lake build Comparator` checks that they compile; `scripts/comparator-verify.sh [--insecure]`
runs comparator on every config (see the script header for the sandbox requirements).
