# Verification

Install Git, Python 3.9 or later and [elan](https://github.com/leanprover/elan).
The toolchain is pinned to Lean 4.30.0. The nine Lake dependencies, including
mathlib, are pinned in `lake-manifest.json`.

```sh
python3 -B scripts/verify_release.py --check-sources-only
lake exe cache get
python3 -B scripts/verify_release.py
python3 -B -m unittest discover -s scripts -p 'test_release.py'
```

The source-only command checks file identity; it does not check a proof. The full
verifier deletes the local `.lake/build`, rebuilds every distributed QIT module,
and compiles `Check.lean`. It compares Lean's actual imports with the reviewed
source closure and checks the literal capacity statement. All imported
private-capacity declarations, including internal helpers, are checked for unsafe
code and transitive axioms. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed. The negative controls test rejection of changed sources, weakened checks,
wrong import closures and malformed or nonstandard axiom evidence.

Results are written to `audit/release-verification.json`, with build inputs and
logs in the same directory. The toolchain and pinned third-party cached artifacts
are trusted build inputs; QIT artifacts are rebuilt locally. No manuscript,
private dependency checkout or authentication token is required for verification.

`audit/source-review.json` preserves the previously reviewed mathematical source
hashes. `release/source-manifest.json` binds this package and its verification
scripts. Hashes establish identity, not mathematical equivalence. After a proof
change, review definitions, statements and proofs before updating these records.

Editorial changes to Lean comments are recorded in `audit/editorial-source-review.json`.
For these changes, text outside comments is byte-identical to the cited source commit.
Historical build records retain their original inputs and dates; subsequent build
and kernel checks are recorded separately in `audit/editorial-verification.json`.

## Supplementary exact calculations

These optional checks require SymPy and do not supply premises to Lean.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r scripts/requirements.txt
.venv/bin/python -B scripts/check_transition_channel.py
```

The checker reconstructs the finite matrices and checks the exact simulator,
encoding, full environment bounds and rate substitution. Negative controls reject
incorrect smaller domination constants and a shared eigenbasis for noncommuting blocks.

To regenerate the rational certificate sources, run from the repository root:

```sh
.venv/bin/python -B scripts/generate_transition_data.py
.venv/bin/python -B scripts/generate_transition_encoding.py
.venv/bin/python -B scripts/generate_transition_paper_certificates.py
python3 -B scripts/verify_release.py --check-sources-only
```

The final command confirms exact reproduction of the reviewed certificate sources.
Every generated identity is checked again in Lean; the generators are not trusted proof oracles.
