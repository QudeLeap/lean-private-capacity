# Earlier half-erasure proof

This branch preserves the deformed half-erasure construction preceding `main-new.tex`.
The endpoint `QIT.QubitActivation.deformed_superactivation_main` has no hypotheses.

| Proof step | Source module in `QIT/Coding/Private/` |
|---|---|
| Main channel, full complement and transpose simulator | `ExplicitChannel`, `SimulatorCertificate`, `TransposeSimulation` |
| Standalone zero capacities and actual product | `HalfErasure`, `QubitProduct`, `QubitSuperactivation` |
| Deformed density operators and priors | `QubitDeformedEncoding`, `QubitDeformedEnsemble` |
| Exact receiver and complete environment outputs | `QubitDeformedMatrices`, `QubitDeformedOutputs` |
| Specified fixed measurement | `QubitDeformedMeasurement`, `QubitDeformedFlaggedMeasurement` |
| Complete characteristic-polynomial root multisets | `QubitDeformedSpectrum`, `QubitDeformedNumerics` |
| Rational logarithm bounds and twelve entropy intervals | `QubitEntropyIntervals`, `QubitDeformedMeasuredTable`, `QubitDeformedEnvironmentTable` |
| Measured information difference and strict capacity bound | `QubitDeformedRate`, `QubitDeformedSuperactivation` |

The parameters are `r₀=1001/1000`, `r₁=999/1000`, `t=27/1000`, `q=3/16`.
The measured information difference lies strictly between `0.00045259148246` and
`0.00045259148249`, giving product capacity greater than `181/400000`.
All input, Bob and Eve dimensions are 8, 12 and 24 respectively. The entire
complement is retained; simultaneous diagonalization is not assumed.

The entropy bounds use a proved finite logarithm expansion with a conservative
remainder. The simulator is checked on all matrix units and extended by linearity.
These are explicit algebraic counterparts of the earlier argument, not a line-by-line
formalization of every presentation choice in the paper.

The capacity is the regularized private-information formula. Operational coding,
capacity equivalence, a general-erasure quadratic bound and decoder converses are
outside this branch's proof. The latest construction is on `main`.
