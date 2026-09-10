/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module
public import QIT.Coding.Private.SimulatorCertificate

/-! # From the finite simulator certificate to zero private capacity -/

@[expose] public section
namespace QIT
open Channel
noncomputable section

/-- The exact simulation identity on every input matrix (`cert:transpose`). -/
theorem simulator_identity (X : CMatrix (Fin 4)) :
    simulatorD.map (complementN.map X) = Matrix.transpose (privateN.map X) := by
  change (simulatorD.map.comp complementN.map) X = (MatrixMap.transposeMap.comp privateN.map) X
  rw [MatrixMap.map_eq_sum_single _ X, MatrixMap.map_eq_sum_single
    (MatrixMap.transposeMap.comp privateN.map) X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact simulator_matrix_unit i j

/-- Zero regularized private information at all blocklengths.
`complementN_isComplementOf` certifies the full complement used here. -/
theorem privateN_privateCapacity_eq_zero :
    Channel.privateCapacity privateN complementN = 0 :=
  Channel.privateCapacity_eq_zero_of_transpose_simulator privateN complementN
    simulatorD simulator_identity

end
end QIT
