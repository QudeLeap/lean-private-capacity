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

## Preserved evidence

The source-only cleanup retains all 135 mathematical files, `QIT.lean` and
`Check.lean` byte-for-byte from the earlier verified proof. The original kernel
check completed on 2026-09-08 UTC and audited 1,564 private-capacity declarations.
`audit/prior-verification.json` binds those source hashes and the two `prior-*.log`
files. The updated verifier revalidates this evidence's import closure and axioms;
this is not described as a fresh Lean rebuild. Running the full command above
produces a new verification result for this package.
