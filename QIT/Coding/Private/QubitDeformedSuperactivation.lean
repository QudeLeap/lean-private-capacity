/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedRate
public import QIT.Coding.Private.QubitSuperactivation

/-!
# The revised half-erasure superactivation theorem

The rationally deformed encoding and fixed receiver measurement give a rate
strictly above 181/400000. Capacity here is the regularized information formula;
the operational coding theorem and the all-p extension are separate obligations.
-/

@[expose] public section
namespace QIT.QubitActivation
open Channel
noncomputable section
universe u

/-- The new rate bound for the actual channels, with no spectral or entropy hypotheses. -/
theorem deformed_superactivation_main :
    Channel.privateCapacity.{0, 0, 0, u} privateN complementN = 0 ∧
      Channel.privateCapacity.{0, 0, 0, u} erasure2 erasure2Complement = 0 ∧
      (181 / 400000 : ℝ) <
        Channel.privateCapacity.{0, 0, 0, u} productChannel productComplement :=
  ⟨individual_capacities_zero.1, individual_capacities_zero.2,
    deformedMeasuredRate_gt.trans_le deformedMeasuredRate_le_privateCapacity⟩

end
end QIT.QubitActivation
