# Blueprint outline: Wang, Agrawal, Ramdas, "Almost sure null bankruptcy of testing-by-betting strategies"

COLT 2026, arXiv 2602.08888. Source in `source/bankrupt/` (`main.tex`, `appdx.tex`).

This file is the contract between the blueprint chapters and the Lean files: it fixes every
label, the statement of every result, its proof route and what Mathlib/LML already provide.
Lean library `Wang2026Almost`; paper directory `Wang2026Almost/WAR2026/` (namespace
`Wang2026Almost`); library material in `Wang2026Almost/Mathlib/` (namespaces `MeasureTheory`,
`ProbabilityTheory`) and `Wang2026Almost/LeanMachineLearning/` (namespace `Learning`,
`Learning.Betting`).

## 0. Modelling decisions

* **Indexing.** Time is `0`-indexed: `lam n` is the fraction bet on `X n`, chosen before `X n`
  is revealed; the wealth after `n` rounds is `wealth m lam X n = ∏_{k < n} (1 + lam k (X k - m))`.
  The paper's `λ_n`, `X_n` (`n ≥ 1`) are `lam (n - 1)`, `X (n - 1)`; the paper's GRAPA fraction
  `λ^GRAPA_{n+1} = λ^KL_n` is Lean's `gr n` (maximizer of the hindsight wealth of the first `n`
  observations).
* **Betting strategies.** A *predictable strategy* is a process `lam` adapted to a filtration
  `ℱ` along which the observations are i.i.d.: `X n` is `ℱ (n + 1)`-measurable, independent of
  `ℱ n`, with law `P` ("the i.i.d.-along-`ℱ` setting", hypotheses `hXm`, `hXi`, `hXl`). This
  covers
  - the paper's predictable plug-in strategies (`ℱ = pastFiltration X`, `σ(X 0, …, X (n-1))`,
    strategies `IsPlugIn X lam`), and
  - runs of a (possibly randomized) LML algorithm `alg : Algorithm Unit ℝ ℝ` in the i.i.d.
    environment `Environment.const P` (`ℱ = h.filtrationAction`, LML), which is how the headline
    Theorem 2.1, Corollary 2.4 and Theorem 5.2 are stated (`IsAlgEnvSeq (fun _ _ ↦ ()) lam X alg
    (Environment.const P) P'`).
  The general (filtration) results are library lemmas in `Learning.Betting`; the paper's
  statements are one-line specializations.
* **Explicit strategies** (KT, GRAPA, aGRAPA, hedging, mixtures) are processes computed from
  i.i.d. observations (`iIndepFun X P'`, `∀ n, HasLaw (X n) P P'`).
* **Null hypothesis.** `hP : ∀ᵐ x ∂P, x ∈ Set.Icc 0 1`, `hm : ∫ x, x ∂P = m`, non-degeneracy
  `hnd : P ≠ Measure.dirac m` or `hvar : 0 < Var[id; P]`. Consequences used everywhere
  (`lem:null_basic`): `m ∈ (0, 1)`, `σ² := Var[id; P] > 0`, `X n ∈ [0, 1]` a.s.
* **Asymptotic notation** (`def:asymp`): `IsBigOInProb`, `IsBigOmegaInProb`, `IsBigOAE`,
  `IsBigOmegaAE` (`Wang2026Almost/Mathlib/Probability/AsymptoticsInProbability.lean`).
* **Convergence in distribution**: Mathlib's `TendstoInDistribution`; limits `gaussianReal`,
  `chiSquareMeasure` (`Wang2026Almost/Mathlib/Probability/Distributions/ChiSquare.lean`).
* **Theorem 4.1** is stated for predictable processes w.r.t. an arbitrary filtration (pathwise,
  as in the paper): the improved strategy is the explicit `ρ`-opportunistic leverage, predictable
  for the same filtration. It is *not* stated as "∃ an LML algorithm": a randomized LML policy
  only sees its own actions, from which the original strategy's actions cannot in general be
  recovered (the leverage map `λ ↦ Wλ/(W - ρ)` collides with the identity on the switching
  rounds), so the statement for randomized algorithms is false or at least not provable this way.

## 1. Headline results (comparator targets)

| Paper | Lean name (namespace `Wang2026Almost`) | label |
|---|---|---|
| Thm 2.1 | `sum_sq_criterion` | `thm:sos_crit` |
| Thm 2.2 | `ae_not_summable_of_isBigOmegaInProb` | `thm:sum_of_op` |
| Cor 2.3 | `ae_not_summable_sum_sq_div_sq` | `cor:div_sample_mean` |
| Cor 2.4 | `tendsto_wealth_zero_of_isBigOmega` | `cor:sq_crit` |
| Prop 2.5 | `kt_bankrupt` | `prop:kt` |
| Prop 2.6 | `grapa_bankrupt` | `prop:grapa` |
| Prop 2.7 | `agrapa_bankrupt` | `prop:agrapa` |
| Prop 2.8 | `hedged_bankrupt` | `prop:hedge` |
| Thm 3.1 | `tendsto_mixtureWealth` | `thm:nocash` |
| Prop 3.2 | `tendsto_mixtureWealth_betaMixture`, `tendsto_mixtureWealth_robbinsMixture` | `prop:mixture_bankrupt` |
| Thm 4.1 | `exists_improve` | `thm:improve` |
| Thm 5.1 | `tendstoInDistribution_hindsightLogWealth`, `not_bddAbove_logRegret_of_tendsto_wealth_zero` | `thm:chisq_klinf`, `thm:unbounded_regret` |
| Thm 5.2 | `sum_sq_criterion_subgaussian` | `thm:sos_crit_subg` |
| Thm 5.3 | `tendsto_subgaussianMixtureTest` | `thm:nocash_subg` |

Supporting paper results (stated, proved, `lemma`, not comparator targets):
Lemma B.2 `tendsto_integral_exp_neg_mul` (`lem:exp_regular`), Lemma B.3
`leverageFraction_mem_Ioo` (`lem:leverage_valid`), Definition B.4 claims
`oppLeverage_mem_fractionRange`, `wealth_oppLeverage` (`lem:opp_leverage_valid`,
`lem:wealth_opp_leverage`), Fact 1 `wealth_portfolioFraction` (`fact:mixture_of_two`), Fact 2
`wealth_portfolioFraction_short` (`fact:short`).

Not formalized: Lemma B.1 (continuity on the Skorokhod space; Mathlib has no `J₁` topology) and
the Donsker proof of Corollary 2.3 that uses it (Appendix B.3, an alternative proof); the
Examples C.1, C.2 and the discussion of Appendix C (not statements).

## 2. Deviations from the paper (each gets a remark in the blueprint)

1. Prop 2.5 (KT): the paper's `C ≥ m(1 - m)` does not make the first bet `1/(2C)` valid when
   `m > 1/2`; we add `C ≥ m/2` (with it, all KT fractions are in `[-1/(1-m), 1/m]`).
2. Thm 2.1, proof: instead of the martingale convergence/divergence theorems of Hall–Heyde and
   Fitzsimmons (not in Mathlib), use exponential supermartingales of conditionally sub-Gaussian
   sums (`chap:pre_martingale`): on `{Σ λ² < ∞}` the martingale `Σ λ_k (X_k - m)` converges, on
   `{Σ λ² = ∞}` it is `o(Σ λ²)`, and `log(1+x) ≤ x - c x²`.
3. Thm 3.1, 5.3, proof: instead of the law of the iterated logarithm (not in Mathlib) and
   Lemma B.2 along a random subsequence, split the mixture at `|λ| = ε`: the bets `|λ| ≥ ε` are
   dominated by the fixed-fraction wealths `W^{±ε} → 0` (Bernoulli's inequality), the bets
   `0 < |λ| < ε` form a nonnegative supermartingale whose limit has expectation
   `≤ π(0 < |λ| < ε)`. Lemma B.2 is still formalized, and is not used.
4. Prop 2.6, proof: instead of Niemiro's general Bahadur theorem, a direct one-dimensional
   analysis of the concave log-wealth on the event `S_n = O(√n log n)`,
   `Σ (X_k - m)² - nσ² = O(√n log n)` (Hoeffding + Borel–Cantelli), which gives the stronger
   remainder `O(log² n / √n)`. The same analysis gives `2L*_n = S_n²/V_n + o(1)` (Thm 5.1).
5. Thm 5.1: `L*_n = log (sup_λ W^λ_n)` (not `sup_λ log W^λ_n`, which meets Lean's `log 0 = 0`);
   the representation `L*_n = Σ log(1 + λ^KL_n (X_k - m))` is not restated; the unbounded
   regret statement allows the wealth to vanish at a finite time.
6. Thm 5.2, 5.3: the non-degeneracy hypothesis is not used by the proofs and is dropped.
7. Lemma B.2: positivity and monotonicity of `A_n` are not used (dominated convergence) and are
   dropped.
8. Def B.4 / Thm 4.1: the wealth identity needs `m ∈ [0, 1]` (implicit in the paper); validity of
   the leveraged fraction needs `m ∈ (0, 1)`.
9. Prop 2.8: the consistent variance estimator is a hypothesis: any plug-in `v` with
   `v n → σ²` a.s.
10. Fact 2 is stated on the path space `ℕ → ℝ` (strategies as functions of the observation path
    depending only on the past), as its hypothesis quantifies over all binary paths.

## 3. Part I: the paper

### Chapter `chap:setting` (Setting; file per definition group)

Definitions (all `\lean`-tagged, `\leanok` from phase 1):
`def:fraction_range` `Learning.Betting.fractionRange`; `def:wealth` `Learning.Betting.wealth`;
`def:fixed_wealth` `fixedWealth`; `def:mixture_wealth` `mixtureWealth`; `def:hedged_wealth`
`hedgedWealth`; `def:hindsight` `hindsightLogWealth`, `logRegret`; `def:subg_test`
`subgaussianTest`, `subgaussianMixtureTest`; `def:plug_in` `IsPlugIn`; `def:kt` `ktFraction`;
`def:grapa` `IsGrapa`; `def:agrapa` `empMean`, `empVar`, `agrapaFraction`; `def:hedge_fraction`
`hedgeFraction`; `def:iid_env` `Learning.Environment.const`; `def:past_filtration`
`Learning.Betting.pastFiltration`; `def:asymp` (four notions, `ProbabilityTheory`);
`def:next_wealth_min` `Wang2026Almost.nextWealthMin`; `def:pnb` `pnbEvent`;
`def:leverage_fraction` `leverageFraction`; `def:opp_leverage` `oppLeverage`;
`def:portfolio_fraction` `portfolioFraction`; `def:beta_mixture` `betaMixture`;
`def:robbins_mixture` `robbinsConst`, `robbinsDensity`, `robbinsMixture`.

Basic lemmas: `lem:null_basic` (`m ∈ (0,1)`, `σ² > 0`, `X ∈ [0,1]` a.s.; `Learning.Betting`
or paper-level helper), `lem:wealth_basic` (`wealth_zero`, `wealth_succ`, `wealth_nonneg`,
`measurable_wealth`, `one_add_mul_sub_nonneg`), `lem:iid_of_run` (from `IsAlgEnvSeq` with
`Environment.const P`: `λ` adapted to `filtrationAction`, `X n` `filtrationAction (n+1)`-measurable,
independent of `filtrationAction n`, law `P`), `lem:iid_of_plug_in` (from `iIndepFun X P'` and
`IsPlugIn X lam`: the same with `pastFiltration X`).

### Chapter `chap:predictable` (Section 2)

* `thm:sos_crit_filtration` (`Learning.Betting.sum_sq_criterion_of_iid`): the i.i.d.-along-`ℱ`
  version of Thm 2.1. Proof (`\uses`): `lem:null_basic`, `lem:wealth_supermartingale`
  (`W` nonneg supermartingale, converges a.s., `lem:supermartingale_tendsto`),
  `lem:sos_converge` (on `{Σλ² < ∞} ∩ {no all-in}`, `liminf log W_n > -∞`: `T_n` converges
  (`lem:subg_sum_tendsto`) and `log(1+x) ≥ x - x²` for `|x| ≤ 1/2` (`lem:log_ge_sub_sq`)),
  `lem:sos_diverge` (on `{Σλ² = ∞}`, `log W_n → -∞`: `log(1+x) ≤ x - c x²` on `(-1, M]`
  (`lem:log_le_sub_mul_sq`), `T_n = o(Σλ²)` and `Σλ²((X-m)² - σ²) = o(Σλ²) + O(1)`
  (`lem:subg_sum_little_o`)), all-in losses (`W_k = 0` for `k > n`).
* `thm:sos_crit` (Thm 2.1, `Wang2026Almost.sum_sq_criterion`): LML form, from the above and
  `lem:iid_of_run`.
* `thm:sum_of_op` (Thm 2.2): proof as in the paper with `lem:cesaro_of_summable_div`
  (`a_k ∈ [0,1]`, `Σ a_k/k < ∞` ⇒ `(1/n) Σ_{k<n} a_k → 0`; replaces Kronecker),
  `lem:measure_liminf_le` (Fatou for sets), Markov. Library version
  `ProbabilityTheory.ae_not_summable_of_isBigOmegaInProb`.
* `cor:div_sample_mean` (Cor 2.3): CLT (Mathlib `tendstoInDistribution_inv_sqrt_mul_sum_sub`) +
  `lem:isBigOmegaInProb_of_tendstoInDistribution` + `lem:isBigOmegaInProb_sq`,
  `lem:isBigOmegaInProb_mono` + `thm:sum_of_op`.
* `cor:sq_crit_filtration`, `cor:sq_crit` (Cor 2.4): `Ω_p(n^{-1/2})` ⇒ `λ² = Ω_p(n⁻¹)` ⇒
  `Σλ² = ∞` a.s. (`thm:sum_of_op`); `Ω_as((n log n)^{-1/2})` ⇒ `λ_n² ≥ c/(n log n)` eventually ⇒
  `Σλ² = ∞` (`lem:not_summable_inv_mul_log`); then `thm:sos_crit_filtration`.
* `prop:kt` (Prop 2.5): `lem:kt_mem` (fractions in range under `C ≥ m(1-m)`, `C ≥ m/2`),
  `lem:kt_clt` (CLT, Slutsky with deterministic factors `n/(C(n+1)) → 1/C`,
  `√n/(2C(n+1)) → 0`, `gaussianReal_map_const_mul`), Ω_p by
  `lem:isBigOmegaInProb_of_tendstoInDistribution`, bankruptcy by `cor:sq_crit_filtration` with
  `pastFiltration` (`isPlugIn_ktFraction`).
* `prop:grapa` (Prop 2.6): `lem:good_event` (a.s.: `S_n = O(√n log n)`,
  `V_n - nσ² = O(√n log n)`, from `lem:hoeffding_rate`), `lem:grapa_location` (deterministic:
  eventually `|g - S_n/V_n| ≤ K log² n / n` for every maximizer `g`), algebra for the
  Bahadur remainder; distributional limit: CLT for `S_n/√n`, `√n gr_n - S_n/(σ²√n) → 0` a.s.
  (`tendstoInMeasure_of_tendsto_ae`) and Slutsky (`add_of_tendstoInMeasure_const`); Ω_p; bankruptcy
  by `cor:sq_crit_filtration` (`IsGrapa` contains `IsPlugIn` and range membership).
* `prop:agrapa` (Prop 2.7): `empVar + (empMean - m)² = (1/n) Σ (X_k - m)²` (`lem:empVar_add_sq`),
  SLLN (Mathlib `strong_law_ae`) ⇒ denominator `→ σ²` a.s. and unclipped fraction `→ 0` a.s.
  (clipping eventually inactive), CLT + Slutsky (product with `1/denominator`); Ω_p; bankruptcy.
* `prop:hedge` (Prop 2.8): eventually unclipped and `≥ c (n log n)^{-1/2}` a.s. (`v_n → σ² > 0`);
  `cor:sq_crit_filtration` applied to `λ` and `-λ`.

### Chapter `chap:mixture` (Section 3)

* `lem:exp_regular` (Lemma B.2): dominated convergence, `exp(-x A_n) ≤ 1` eventually, pointwise
  limit `𝟙{x = 0}`.
* `thm:nocash` (Thm 3.1): `lem:fixedWealth_le_rpow` (Bernoulli: for `0 < ε ≤ λ`,
  `W^λ_n ≤ (W^ε_n)^{λ/ε}`; symmetric for negative), `W^{±ε}_n → 0` a.s.
  (`thm:sos_crit_filtration` with constant bets), `lem:supermartingale_integral` (mixture of
  nonnegative supermartingales), `lem:supermartingale_tendsto`, Fatou for the limit of the
  small-bet part, `ε = 1/(j+1)`.
* `prop:mixture_bankrupt` (Prop 3.2): `lem:betaMixture_prob` (probability measure on `[-1,1]`,
  no atom), `lem:robbins_prob` (density integrates to `1`: antiderivative `1/log log(C/λ)` on
  `(0, 1]`; no atom: absolutely continuous), `[-1, 1] ⊆ fractionRange m`, then `thm:nocash`.

### Chapter `chap:improve` (Section 4, Appendix B.5)

* `fact:mixture_of_two` (Fact 1): induction on `n`; convex combination for the range.
* `fact:short` (Fact 2): positivity of the denominator `(1-κ)W^λ + κW^ν ≥ (1-κ)(W^λ - ρW^ν) > 0`;
  range by modifying the path at `n` to `0` and `1` (predictability).
* `lem:leverage_valid` (Lemma B.3): `1 + β(x - m) = (W(1 + λ(x-m)) - ρ)/(W - ρ) > 0` for
  `x ∈ {0, 1}`; `W - ρ > 0` as a convex combination.
* `lem:opp_leverage_valid`, `lem:wealth_opp_leverage` (Definition B.4 claims): induction.
* `thm:improve` (Thm 4.1): `gam := oppLeverage`, adapted (`lem:measurable_oppLeverage`), range
  from `lem:opp_leverage_valid`, wealth identity from `lem:wealth_opp_leverage`, the four
  consequences by algebra and limits.

### Chapter `chap:odds` (Section 5)

* `thm:chisq_klinf` (Thm 5.1, χ²): `lem:measurable_hindsightLogWealth` (sup over a countable
  dense subset), `lem:hindsight_value` (deterministic: eventually
  `|2 log sup_λ W^λ_n - S_n²/V_n| ≤ K (log² n · n^{-1/3} + log³ n / √n)`), `lem:good_event`,
  CLT for `S_n/(σ√n)`, continuous mapping `x ↦ x²`, `lem:gaussian_sq` (law of `Z²` is
  `chiSquareMeasure 1`), Slutsky (`S_n²/V_n = (S_n/√n)² · n/V_n`, `n/V_n → 1/σ²` a.s. by SLLN; and
  `2L* - S²/V → 0` a.s.).
* `thm:unbounded_regret` (Thm 5.1, regret): pathwise: `L*_n ≥ log W^0_n = 0` and
  `log W_n → -∞` when `W_n → 0` with no zero.
* `thm:sos_crit_subg_filtration`, `thm:sos_crit_subg` (Thm 5.2): `log M_n = T_n - A_n/2` with
  `T_n = Σ (λ_k - m)(X_k - m)`, `A_n = Σ (λ_k - m)²`; `M` nonneg supermartingale
  (`lem:exp_subg_supermartingale`, `t = 1`) converges; on `{A_∞ < ∞}` `T` converges
  (`lem:subg_sum_tendsto`) so `M_∞ > 0`; on `{A_∞ = ∞}` `T_n ≤ C + A_n/4`
  (`lem:subg_sum_little_o`) so `log M_n → -∞`.
* `thm:nocash_subg` (Thm 5.3): as `thm:nocash`, with `lem:subgTest_le_rpow`
  (`M^{m+u}_n ≤ (M^{m+ε}_n)^{u/ε}` for `u ≥ ε > 0`) and `thm:sos_crit_subg_filtration` for
  constant `λ = m ± ε`.

## 4. Part II: prerequisites

### Chapter `chap:pre_martingale` (`Wang2026Almost/Mathlib/Probability/Martingale/*.lean`, `ProbabilityTheory`/`MeasureTheory`)

* `lem:lintegral_comp_indep` (`ProbabilityTheory.lintegral_comp_of_indep`): `Y` independent of
  the σ-algebra `m`, `W` `m`-measurable, `F ≥ 0` measurable, `A ∈ m`:
  `∫⁻_A F(W, Y) dP = ∫⁻_A ∫⁻ F(W, y) d(P∘Y⁻¹)(y) dP`. Mathlib: `indepFun_iff_map_prod_eq_prod_map_map`,
  `lintegral_map`, `lintegral_prod`.
* `lem:supermartingale_of_markov` (`MeasureTheory.supermartingale_of_lintegral_le`): `V` adapted,
  nonneg, `V 0` integrable, `V (n+1) = Φ_n(W_n, Y_n)` a.s. with `W_n` `ℱ n`-measurable, `Y_n`
  independent of `ℱ n`, `∫⁻ Φ_n(W_n, y) dP_{Y_n} ≤ V_n` a.s. ⇒ supermartingale.
  Mathlib: `supermartingale_of_setIntegral_succ_le`.
* `lem:supermartingale_tendsto` (`MeasureTheory.Supermartingale.ae_tendsto_of_nonneg`):
  nonnegative supermartingale converges a.s. to a finite limit, with `E[lim] ≤ E[V_0]`
  (Mathlib `Submartingale.ae_tendsto_limitProcess` applied to `-V`, Fatou).
* `lem:supermartingale_integral`: `f l` nonnegative supermartingales, jointly measurable,
  `∫ f l n dπ` integrable ⇒ `n ↦ ∫ f l n dπ(l)` supermartingale (Fubini).
* `lem:exp_subg_supermartingale`: i.i.d.-along-`ℱ`-type setting for a real process `Y` with
  `HasSubgaussianMGF (Y n) c P'`, `w` adapted; `T_n = Σ_{k<n} w_k Y_k`, `A_n = Σ_{k<n} w_k²`:
  for all `t`, `exp(t T_n - c t² A_n / 2)` is a nonnegative supermartingale.
* `lem:subg_sum_tendsto`: a.s. on `{Summable w²}`, `T_n` converges.
* `lem:subg_sum_little_o`: a.s., for all `ε > 0` there is `C` with `|T_n| ≤ C + ε A_n` for all `n`.
* `lem:hoeffding_rate` (`ProbabilityTheory.ae_isBigO_sum_sqrt_mul_log`): i.i.d. (pairwise
  enough? use `iIndepFun`) sub-Gaussian `Y` ⇒ a.s. `Σ_{k<n} Y_k = O(√n log n)`. Mathlib:
  `measure_sum_range_ge_le_of_iIndepFun`, `measure_limsup_atTop_eq_zero`.

### Chapter `chap:pre_asymptotics` (`Wang2026Almost/Mathlib/Probability/AsymptoticsInProbability.lean` and neighbours)

* `lem:isBigOmegaInProb_mono`, `lem:isBigOmegaInProb_sq`, `lem:isBigOmegaInProb_of_tendstoInDistribution`
  (`X n / a n → Z` in distribution, `P(Z = 0) = 0`, `a n > 0` eventually ⇒ `X = Ω_p(a)`;
  Mathlib portmanteau `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`).
* `lem:cesaro_of_summable_div`, `lem:measure_liminf_le`, `lem:not_summable_inv_mul_log`
  (`Σ 1/(n log n) = ∞`; Mathlib condensation `summable_condensed_iff_of_nonneg` or integral test).
* `lem:gaussian_sq` (`ProbabilityTheory.gaussianReal_map_sq`): `(gaussianReal 0 1).map (·^2) =
  chiSquareMeasure 1` (MGF equality, Mathlib `Measure.ext_of_mgf_eq`, `integral_gaussian`).
* `lem:tendstoInDistribution_congr_ae`: Slutsky helpers (a.s. convergence ⇒ in measure:
  Mathlib `tendstoInMeasure_of_tendsto_ae`).

### Chapter `chap:pre_betting` (`Wang2026Almost/LeanMachineLearning/Betting/*.lean`)

* `lem:log_ge_sub_sq` (`log(1+x) ≥ x - x²`, `|x| ≤ 1/2`), `lem:log_le_sub_mul_sq`
  (`log(1+x) ≤ x - x²/(2(1+M))` for `-1 < x ≤ M`), `lem:log_taylor` (`|log(1+x) - x + x²/2| ≤ 2|x|³`,
  `|x| ≤ 1/2`; Mathlib `Real.abs_log_sub_add_sum_range_le`).
* `lem:fixedWealth_le_rpow`, `lem:subgTest_le_rpow` (Bernoulli: Mathlib
  `one_add_mul_self_le_rpow_one_add`).
* `lem:wealth_supermartingale`: `W` is a nonnegative supermartingale in the i.i.d.-along-`ℱ`
  setting (from `lem:supermartingale_of_markov`).
* `lem:hindsight_neg` (eventually `W^λ_n < 1` for `|λ| ≥ n^{-1/3}`), `lem:grapa_location`,
  `lem:hindsight_value` (deterministic analysis of `λ ↦ Σ log(1 + λ y_k)` under
  `S_n = O(√n log n)`, `V_n - nσ² = O(√n log n)`, `y_k ∈ [-m, 1-m]`).
* `lem:good_event`: under the null, a.s. `S_n = O(√n log n)` and `V_n - nσ² = O(√n log n)`
  (Hoeffding's lemma, Mathlib `hasSubgaussianMGF_of_mem_Icc`, + `lem:hoeffding_rate`).
* `lem:pastFiltration_indep`: `iIndepFun X P'` ⇒ `X n` independent of `pastFiltration X n`
  (Mathlib `iIndepFun.indepFun_finset`).
