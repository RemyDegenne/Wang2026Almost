# Wang2026Almost

Lean 4 formalization of the paper

> Hongjian Wang, Shubhada Agrawal, Aaditya Ramdas, *Almost sure null bankruptcy of
> testing-by-betting strategies*, COLT 2026, [arXiv:2602.08888](https://arxiv.org/abs/2602.08888),

built on Mathlib and the [Lean Machine Learning](https://github.com/LeanMachineLearning/LML)
library (LML, branch `rename`). The development is blueprint-driven:
[blueprint](https://remydegenne.github.io/Wang2026Almost/blueprint/),
[dependency graph](https://remydegenne.github.io/Wang2026Almost/blueprint/dep_graph_document.html).

**Status: phase 1 (statements).** Every result of the paper is stated in Lean with its proof
`sorry`ed; the headline results are listed in [`formalization.yaml`](formalization.yaml) and are
standalone challenges for [comparator](https://github.com/leanprover/comparator) in
[`comparator/`](comparator/). Phase 2 proves them, following the blueprint.

## Layout

* `Wang2026Almost/WAR2026/`: the paper, one file per result (`Theorem2_1.lean`, …,
  `LemmaB_3.lean`, `Fact2.lean`), namespace `Wang2026Almost`, and the paper-specific definitions
  (`Leverage.lean`: predictably non-bankrupt events, leverage, portfolios; `Mixtures.lean`: the
  universal portfolio and Robbins' mixing distributions).
* `Wang2026Almost/LeanMachineLearning/`: material for LML: the i.i.d. environment
  `Environment.const` (`SequentialLearning/ObliviousEnv.lean`), the betting wealth processes
  (`Betting/Wealth.lean`) and the classical strategies KT, GRAPA, aGRAPA, hedging
  (`Betting/Strategies.lean`).
* `Wang2026Almost/Mathlib/`: material for Mathlib: Landau notation in probability
  (`Probability/AsymptoticsInProbability.lean`), the gamma and chi-squared distributions.
* `blueprint/src/`: the blueprint (Part I follows the paper, Part II the prerequisites);
  `notes/blueprint-outline.md`: the outline it was written from (labels, proof routes, modelling
  decisions); `source/`: the paper's LaTeX source.

## Results of the paper

| Result | Lean declaration | Notes |
|---|---|---|
| Theorem 2.1 (sum-of-squares criterion) | `sum_sq_criterion` | strategies = runs of LML algorithms in `Environment.const P` |
| Theorem 2.2 (a.s. divergence of `Σ Ω_p(1/n)`) | `ae_not_summable_of_isBigOmegaInProb` | |
| Corollary 2.3 | `ae_not_summable_sum_sq_div_sq` | |
| Corollary 2.4 (`n^{-1/2}` criterion) | `tendsto_wealth_zero_of_isBigOmega` | |
| Proposition 2.5 (KT) | `kt_bankrupt` | needs `C ≥ m/2` besides `C ≥ m(1-m)` |
| Proposition 2.6 (GRAPA) | `grapa_bankrupt` | |
| Proposition 2.7 (aGRAPA) | `agrapa_bankrupt` | |
| Proposition 2.8 (hedging) | `hedged_bankrupt` | consistent plug-in variance estimator as hypothesis |
| Theorem 3.1 (no-cash criterion) | `tendsto_mixtureWealth` | |
| Proposition 3.2 | `tendsto_mixtureWealth_betaMixture`, `tendsto_mixtureWealth_robbinsMixture` | |
| Theorem 4.1 (improvability) | `exists_improve` | strategies predictable for a filtration |
| Theorem 5.1 | `tendstoInDistribution_hindsightLogWealth`, `not_bddAbove_logRegret_of_tendsto_wealth_zero` | |
| Theorem 5.2 | `sum_sq_criterion_subgaussian` | non-degeneracy not needed |
| Theorem 5.3 | `tendsto_subgaussianMixtureTest` | non-degeneracy not needed |
| Lemma B.1 (Skorokhod continuity) | — | not formalized: no Skorokhod space in Mathlib |
| Lemma B.2 | `tendsto_integral_exp_neg_mul` | monotonicity and positivity not needed |
| Lemma B.3 | `leverageFraction_mem_Ioo` | |
| Definition B.4 (claims) | `oppLeverage_mem_fractionRange`, `wealth_oppLeverage` | |
| Facts 1, 2 | `wealth_portfolioFraction`, `wealth_portfolioFraction_short` | Fact 2 on the path space |

The deviations from the paper are listed in the blueprint introduction and in
`notes/blueprint-outline.md` (section 2).

## Building and checking

```
lake exe cache get
lake build Wang2026Almost --wfail
lake exe runLinter Wang2026Almost
python3 scripts/check-blueprint.py && leanblueprint pdf && leanblueprint web
lake exe checkdecls blueprint/lean_decls
python3 scripts/make-challenges.py && lake build Comparator
```
