# Private-capacity superactivation in Lean 4

[![arXiv](https://img.shields.io/badge/arXiv-2609.10520-b31b1b.svg)](https://arxiv.org/abs/2609.10520)

Lean proofs supporting *Private communication via zero-private-capacity quantum
channels* by Chengkai Zhu and Xin Wang. `main` supports the transition-channel
construction in arXiv:2609.10520. This repository contains proof source code and
verification tools; the manuscript is distributed separately.

## Formalized result

For every $1/2 \le p < 1$,

$$
P(\mathcal N)=P(\mathcal E_{2,p})=0,\qquad
P(\mathcal E_{2,p}\otimes\mathcal N)
\ge \frac{6\ln 2}{49(27+169p)}(1-p)^2>0.
$$

The endpoint is [`QIT.Transition.superactivation_main`](QIT/Coding/Private/TransitionSuperactivation.lean).
Its only hypotheses are the bounds on `p`. The proof constructs the channels, full
complements, encoding and fixed receiver measurement, and proves the information bounds.

**Scope:** `P` is the regularized private-information formula. Operational coding,
its equivalence with this formula, and the PPT-decoder converse remain outside Lean.
See the [proof correspondence](docs/PROOF_MAP.md) for the precise coverage.

## Verify

With Git, Python 3.9+ and [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
python3 -B scripts/verify_release.py
```

This rebuilds all 113 QIT modules, checks the literal theorem and audits its axioms.
Lean 4.30.0 and all dependencies are pinned. Only `propext`, `Classical.choice` and
`Quot.sound` are allowed. See [verification details](docs/VERIFICATION.md).

The required Lean QIT sources are bundled; no separate Lean-QIT checkout is needed.
See the [dependency overview](docs/DEPENDENCIES.md).

## Branches

| Branch | Proof version |
|---|---|
| [`main`](https://github.com/QudeLeap/lean-private-capacity/tree/main) | Transition-channel construction, all `1/2 ≤ p < 1`. |
| [`pre-main-new-proof`](https://github.com/QudeLeap/lean-private-capacity/tree/pre-main-new-proof) | Earlier deformed half-erasure example. |

## Repository layout

- `QIT/` — mathematical definitions, theorems and exact certificates.
- `CurrentProof.lean`, `Check.lean` — build entry point and theorem/axiom checks.
- `scripts/` — reproducible verification and optional exact calculations.
- `docs/`, `audit/`, `release/` — proof map, verification records and source hashes.

Licensed under [Apache 2.0](LICENSE). See [NOTICE](NOTICE) for attribution and
[CITATION.cff](CITATION.cff) for citation guidance.
