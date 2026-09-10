# Lean QIT dependencies

The current proof imports 113 local QIT modules: 96 foundational modules derived
from Lean-QIT-Dev and 17 private-capacity modules. The private-capacity modules
directly import 13 distinct foundational modules; the other foundational imports
are transitive. These counts describe the module import closure, not a minimal
set of declarations required by the final theorem.

| Layer | Role in the proof |
|---|---|
| States, matrices and channels | Density operators, positivity, Kraus maps, Choi characterization and tensor products |
| Ensembles and measurements | Classical-quantum states, output ensembles and measurement probabilities |
| Entropy and information | Von Neumann entropy, Holevo information, data processing and dimension bounds |
| Tensor powers and supporting analysis | Block-length constructions, entropy identities and the analytic results imported by the information library |
| Private-capacity modules | Capacity definitions, zero-capacity criteria, explicit channels and complements, encoding, certificates and the positive rate |

`Basic.lean` imports `HSW` and `HSWConverse` for shared interfaces and the proved
classical-quantum Holevo identity. This import does not establish the operational
private-capacity coding theorem. The formalization scope remains the regularized
private-information formula described in the README.

The foundational sources are bundled in this repository. Reproduction requires
no separate Lean-QIT checkout or access to its repository. Of the 96 files,
95 are byte-identical to upstream commit
`575c608c5794283b690e30e0f294c240699fcc79`. The remaining file,
`EntropyTensorPower.lean`, exposes an existing proved helper; its statement and
proof are unchanged. See [NOTICE](../NOTICE) for attribution.

Lake directly requires mathlib. Its lockfile pins nine public packages including
mathlib's dependencies. The Lean toolchain and these packages are external build
inputs; all bundled QIT modules are compiled locally by the full verifier.

The proof therefore depends substantially on Lean QIT mathematically, while its
source distribution is independent of a separate Lean-QIT installation. Reducing
the module closure would require a separate import and library refactoring review.
