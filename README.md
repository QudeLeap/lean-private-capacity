# Private-capacity superactivation — earlier proof

This branch preserves the **deformed half-erasure example preceding `main-new.tex`**.
The latest manuscript's proof is on [`main`](https://github.com/QudeLeap/lean-private-capacity).
Manuscripts are distributed separately.

## Formalized result

`P(N) = P(E₂,½) = 0` and `P(N ⊗ E₂,½) > 181/400000`.

The endpoint is [`QIT.QubitActivation.deformed_superactivation_main`](QIT/Coding/Private/QubitDeformedSuperactivation.lean),
with no hypotheses. It uses the deformed encoding and specified receiver measurement;
the measured information difference is strictly between `0.00045259148246` and
`0.00045259148249`.

**Scope:** `P` is the regularized private-information formula. Operational coding,
capacity equivalence, the general-erasure bound and decoder converses are outside
this earlier proof. See the [proof correspondence](docs/PROOF_MAP.md).

## Verify

With Git, Python 3.9+ and [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
python3 -B scripts/verify_release.py
```

This rebuilds all 135 QIT modules and checks the literal theorem and transitive axioms.
Lean 4.30.0 and all dependencies are pinned. The unchanged sources' original kernel
verification is preserved with its date; see [verification details](docs/VERIFICATION.md).

## Branches

| Branch | Proof version |
|---|---|
| [`main`](https://github.com/QudeLeap/lean-private-capacity/tree/main) | Latest transition-channel construction, all `1/2 ≤ p < 1`. |
| [`pre-main-new-proof`](https://github.com/QudeLeap/lean-private-capacity/tree/pre-main-new-proof) | Earlier deformed half-erasure example, preceding `main-new.tex`. |

## Repository layout

- `QIT/` — mathematical definitions, theorems and exact certificates.
- `QIT.lean`, `Check.lean` — build entry point and theorem/axiom checks.
- `scripts/` — reproducible source and kernel verification.
- `docs/`, `audit/`, `release/` — proof map, evidence and source hashes.

Licensed under [Apache 2.0](LICENSE). See [NOTICE](NOTICE) for attribution and
[CITATION.cff](CITATION.cff) for citation guidance.
