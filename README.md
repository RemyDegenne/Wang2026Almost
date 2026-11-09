# Wang2026Almost

A Lean 4 formalization of *Almost sure null bankruptcy of testing-by-betting strategies* (Hongjian
Wang, Shubhada Agrawal and Aaditya Ramdas, COLT 2026,
[arXiv:2602.08888](https://arxiv.org/abs/2602.08888)), on top of
[LMLExplore](https://github.com/LeanMachineLearning/LMLExplore), and so of
[LML](https://github.com/LeanMachineLearning/LML), [Tau Ceti](https://github.com/TauCetiProject/TauCeti)
and [Mathlib](https://github.com/leanprover-community/mathlib4). It follows the layout of
[lml-paper-template](https://github.com/LeanMachineLearning/lml-paper-template).

It formalizes the results of the paper: the sum-of-squares criterion for the null bankruptcy of
predictable betting strategies (Theorem 2.1), the almost sure divergence of series of order
`Ω_p(1/n)` (Theorem 2.2, Corollary 2.3), the `n^{-1/2}` criterion (Corollary 2.4) and the null
bankruptcy of the KT, GRAPA, aGRAPA and predictable hedging bettors (Propositions 2.5–2.8), the
no-cash criterion for mixtures (Theorem 3.1, Proposition 3.2), the improvability of strategies by
leverage (Theorem 4.1), the `χ²₁` limit of the best-in-hindsight log-wealth and the unbounded
regret of null-bankrupt strategies (Theorem 5.1), the sub-Gaussian criteria (Theorems 5.2, 5.3),
and the supporting results of Appendix B. Proposition 2.5 is stated with an extra hypothesis on
the KT constant: see the errata. Lemma B.1, on the Skorokhod space, is not formalized. Every
headline result is proved, with no `sorry`.

- Website: https://RemyDegenne.github.io/Wang2026Almost/, with the blueprint, the referee site and
  the literature links (which declarations formalize which results of the paper). CI builds it on
  each push to `main`. `scripts/formalize.sh` also commits the literature links, as
  `literature/annotations.jsonl`, when the paper is formalized and after the final bump.
- The paper: `source/`. Errors found in it, with their corrections: `notes/paper-errata.md`.
- The paper's results: `Wang2026Almost/WAR2026/`, one file per result, listed with their status in
  `formalization.yaml`; comparator challenges in `comparator/`.
- Library-shaped material: `Wang2026Almost/ForLMLExplore/`, which Tau Ceti workers port to
  LMLExplore; `PAPER_ROADMAP.md` says where each item goes.
- The blueprint outline, the design decisions and the upstreaming candidates: `notes/`.

## Building

```bash
scripts/build.sh
```

The script fetches Mathlib's and Tau Ceti's prebuilt files, then runs `lake build`; its arguments go
to `lake build`.

## Working on it

The workflow is the `formalize-paper` skill of the `lml` Claude Code plugin
([lml-claude](https://github.com/LeanMachineLearning/lml-claude)). The paper is formalized; what is
left is to contribute its library-shaped part. `scripts/formalize.sh`, in a terminal or tmux, tags
`PAPER_ROADMAP.md`, sends the reusable parts to LMLExplore, and once they are merged moves the paper
to the current LMLExplore.
