/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitProduct
public import QIT.Coding.Private.QubitReference
public import QIT.Coding.Private.QubitStructure
public import QIT.Coding.Private.QubitFullReceiver
public import QIT.Coding.Private.QubitFullEnvironment
public import QIT.Coding.Private.TransposeSimulation

/-!
# The certified half-erasure instance of private-capacity superactivation

The two zero capacities, physical product complement, encoding, finite
certificates, full-output Holevo bounds and rate arithmetic are proved.
`superactivation_main` proves the p=1/2, q=2^-48 instance discussed in the
2026-09-08 manuscript's Lean paragraph, for the regularized information formula,
with no unproved entropy hypotheses. The all-p extension, stronger bound >2^-26,
PPT-decoder converse and operational coding theorem are not formalized here.
-/

@[expose] public section
namespace QIT.QubitActivation
open Channel
noncomputable section
universe u

/-- Both individual zeros, for the actual half-erasure pair in the paper. -/
theorem individual_capacities_zero :
    Channel.privateCapacity.{0, 0, 0, u} privateN complementN = 0 ∧
      Channel.privateCapacity.{0, 0, 0, u} erasure2 erasure2Complement = 0 :=
  ⟨privateN_privateCapacity_eq_zero, erasure2_privateCapacity_eq_zero⟩

/-- Capacity consequence of two full physical output entropy estimates.
Both estimates are supplied by proved theorems in the unconditional result below. -/
theorem privateCapacity_ge_certifiedRate_of_holevo_bounds
    (hBob : signalProbability / 12 * log2 (1 / signalProbability) ≤
      fullBobEnsemble.holevoInformation)
    (hEve : fullEveEnsemble.holevoInformation ≤ signalProbability / 2 * log2 112) :
    certifiedRate ≤ Channel.privateCapacity.{0, 0, 0, u} productChannel productComplement := by
  have hgap : certifiedRate ≤ productChannel.privateInformationWith productComplement fixedEnsemble
    := by
    rw [← rate_identity]
    exact sub_le_sub hBob hEve
  have hcap := Channel.privateInformationWith_le_privateCapacity productChannel productComplement
    (fixedEnsemble.relabelIndex (Equiv.ulift : ULift.{u, 0} Bool ≃ Bool))
  apply hgap.trans
  simpa only [Channel.privateInformationWith, Channel.outputEnsemble_relabelIndex,
    Ensemble.relabelIndex_holevoInformation] using hcap

/-- Reusable implication from the two full-output Holevo estimates. -/
theorem superactivation_of_holevo_bounds
    (hBob : signalProbability / 12 * log2 (1 / signalProbability) ≤
      fullBobEnsemble.holevoInformation)
    (hEve : fullEveEnsemble.holevoInformation ≤ signalProbability / 2 * log2 112) :
    Channel.privateCapacity.{0, 0, 0, u} privateN complementN = 0 ∧
      Channel.privateCapacity.{0, 0, 0, u} erasure2 erasure2Complement = 0 ∧
      ((2 : ℝ) ^ 49)⁻¹ < certifiedRate ∧
      certifiedRate ≤ Channel.privateCapacity.{0, 0, 0, u} productChannel productComplement :=
  ⟨individual_capacities_zero.1, individual_capacities_zero.2, certifiedRate_gt,
    privateCapacity_ge_certifiedRate_of_holevo_bounds hBob hEve⟩

/-- The certified positive rate of the actual qubit-erasure product channel. -/
theorem privateCapacity_ge_certifiedRate :
    certifiedRate ≤ Channel.privateCapacity.{0, 0, 0, u} productChannel productComplement :=
  privateCapacity_ge_certifiedRate_of_holevo_bounds
    full_receiver_holevo_lower full_environment_holevo_upper

/-- The half-erasure, q=2^-48 instance of `thm:private`, with lower bound
2^-49 log₂(16/7)>2^-49 for the regularized information definition of capacity.
No Holevo bounds or matrix identities are assumed. This does not assert the
new manuscript's all-p extension or its stronger numerical lower bound. -/
theorem superactivation_main :
    Channel.privateCapacity.{0, 0, 0, u} privateN complementN = 0 ∧
      Channel.privateCapacity.{0, 0, 0, u} erasure2 erasure2Complement = 0 ∧
      ((2 : ℝ) ^ 49)⁻¹ < certifiedRate ∧
      certifiedRate ≤ Channel.privateCapacity.{0, 0, 0, u} productChannel productComplement :=
  superactivation_of_holevo_bounds full_receiver_holevo_lower full_environment_holevo_upper

/-- Positivity follows from the exact certified rate, without numerical evaluation. -/
theorem product_privateCapacity_pos :
    0 < Channel.privateCapacity.{0, 0, 0, u} productChannel productComplement :=
  certifiedRate_pos.trans_le privateCapacity_ge_certifiedRate

end
end QIT.QubitActivation
