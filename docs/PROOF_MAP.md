# Proof correspondence

This map covers the transition-channel information-capacity argument in
[arXiv:2609.10520](https://arxiv.org/abs/2609.10520).
The external manuscript fingerprint is recorded in `audit/source-review.json`;
no manuscript is distributed or required to build the proof.
The actual endpoint is `QIT.Transition.superactivation_main` in
[TransitionSuperactivation.lean](../QIT/Coding/Private/TransitionSuperactivation.lean).
Only `1/2 ≤ p < 1` is assumed. Every matrix, state, channel, measurement and entropy
bound needed for that endpoint is constructed or proved in Lean.

1. **Main channel, Eqs. (errors), (main-channel), (tp), (kraus).**
   `TransitionData.errors` and `weights` enter the literal real rational matrices.
   `Transition.root` supplies their positive square roots; `kraus` scales each error.
   `kraus_completeness` proves the sum of adjoint products equals the identity.
   `mainChannel_apply` connects this CPTP channel to the weighted channel formula.
   `complement` is its full eight-dimensional Kraus complement, certified by
   `complement_isComplementOf`.

2. **Transpose simulator, Eq. (transpose) and Appendix A.**
   `TransitionPaperData.simulator_formula` binds the actual rational H table to the
   paper's listed vectors, M, Q and reflection. `m_ldl`, `pivots_pos` and
   `reflection_orthogonal` check the corresponding finite identities.
   `TransitionData.h_gram` gives a positive Gram decomposition, so `h_pos` and
   `simulatorChoi_pos` prove positivity on all 32 Choi dimensions.
   `h_partialTrace` proves trace preservation; `simulation` checks all matrix units.
   `simulator_identity` extends the equality to every complex input by linearity.
   The general transpose criterion then proves zero regularized capacity.
   Lean uses an explicit LDL/Gram proof instead of invoking Sylvester's criterion.

3. **Erasure channel and both standalone zeros.**
   `GeneralErasure.lean` defines the erasure channel and its full complement for all
   probabilities in `[0,1]`. `erasure_isComplementOf` derives them from one Kraus
   family. For `p≥1/2`, a CPTP simulator keeps Eve's received input with probability
   `(1-p)/p`; `erasure_antidegradable` proves exact simulation. The zero-capacity
   theorem includes `p=1` and requires no unproved physical premise.

4. **Encoding and error detection, Eqs. (encoding), (inputs), (detection).**
   `inputState false` is `(v₀v₀†+v₁v₁†)/10`, with unnormalized vectors
   `v₀=2|00⟩+|11⟩` and `v₁=|02⟩+2|13⟩`. `inputState true` is
   `vv†/2`, `v=|01⟩+|12⟩`. These are exactly the density operators of the
   paper's normalized vectors. Positivity and trace one are proved, not assumed.
   The helper-marginal theorems prove `I₂/2` for both states and every weak mixture.
   `TransitionPaperData.error_detection` checks `P(I⊗Lₑ)P=0` for each of the seven errors.

5. **Actual product and fixed measurement, Eqs. (click), (bob-gain).**
   `productChannel` uses the paper's `R×A` ordering and equals erasure tensored with
   the main channel. `product_isComplementOf` certifies the entire 24-dimensional
   product environment. `receiverEffect` embeds the signal projector on the arriving
   branch and is zero on the erased branch; positivity and `F≤I` are proved.
   `full_input_event` and `weak_input_event` give probabilities `0` and `(1-p)t/7`.
   `measured_information` proves exactly `h₂(aₚt/4)-h₂(aₚt)/4` for prior `1/4`.
   `rare_signal_gain` proves the linear lower bound `aₚt/2`.

6. **Full environmental states, Eqs. (environment), (order), Appendix B.**
   `sigma_entry` connects the physical complement to the unweighted rational
   16-dimensional table, with both W factors included. `environment_blocks` verifies
   the displayed T-block congruence. `environment_remainder` is a positive Gram
   decomposition of `(205/9)σ₀−σ₁` on the entire environment.
   `epsilon_entry` gives the eight actual weighted diagonal entries, and
   `erased_environment_order` proves the factor 4. `full_environment` proves the
   complete orthogonally embedded mixture `pσ+(1-p)ε` without discarding any output.
   Exact ranks are also checked independently in Python but are not a Lean premise.

7. **Classical coin estimate, Lemma (coin) and Eqs. (coin)–(coin-bound).**
   `DominatedCoin.preparingChannel_bias` proves reconstruction from a Bernoulli
   coin of bias `(1+(c-1)s)/c`; the other preparation state is proved positive and
   trace one from the order bound. The corrected natural entropy has nonnegative
   second derivative on `[0,1/2]` for `c≥3`. Weighted Jensen at priors `3/4,1/4`
   yields `3(c-1)t²/(32 ln 2)`, including both interval endpoints.
   Quantum Holevo data processing gives the same bound without commutativity.

8. **Flag weighting, Eq. (eve-cost).**
   `FlaggedCoin.flagState_entropy` proves the cq entropy formula for an independent
   flag with weights `p,1-p`. One preparation channel sends its two coins to the
   two embedded quantum branches. This gives the full environment bound with
   `κₚ=p(205/9−1)+(1-p)(4−1)=(27+169p)/9`.
   This is a direct flagged-preparation implementation of the paper's flag-entropy
   cancellation; a separate spectral direct-sum theorem on unequal block sizes is
   not assumed.

9. **Measured advantage and rate, Eqs. (gain), (rate).**
   `measuredRate_lower` proves the inequality for the actual fixed measurement and
   every `0<t≤1/2`. The chosen `amplitude` is `8aₚ ln2/(3κₚ)`; it is positive and
   bounded by `ln2/63<1/2`. `amplitude_rate_identity` gives the exact stated rate.
   `certifiedRate_le_measuredRate` preserves the operationally relevant measured
   quantity; Holevo data processing and the one-use inclusion in the regularized
   supremum yield `certifiedRate_le_privateCapacity`.

10. **Endpoint and boundary.**
    `superactivation_main` combines the two zeros and the strictly positive bound
    for all `1/2≤p<1`. `half_erasure_rate` gives `3 ln2/10927`. `Check.lean` checks
    the actual capacity expression with the coefficient written literally, plus
    genuine complements, dimensions and the fully erased endpoint.

Operational trace-distance coding, the equality between operational capacity and
this regularized formula, and the PPT-decoder converse are outside this Lean proof.
The correspondence above covers the core information-capacity argument, including
the equivalent algebraic proof routes used by Lean.
