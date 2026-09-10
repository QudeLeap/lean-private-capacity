/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedData

/-! # Equality of the finite tables and the physical Kraus maps -/

@[expose] public section
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 4000 in
/-- The full 16-dimensional matrix is the actual Kraus complement, with all coherences. -/
theorem deformedSigmaTable_correct (a b c d : ℂ) :
    referencedEnvironment.map
        ((deformedInputTable a b c d).submatrix deformedRAIndex deformedRAIndex) =
      (deformedSigmaTable a b c d).submatrix deformedREIndex deformedREIndex := by
  ext ⟨r, i⟩ ⟨s, j⟩
  change MatrixMap.kron (idChannel (Fin 2)).map complementN.map _ _ _ = _
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  change (krausN i * _ * (krausN j).conjTranspose).trace = _
  rw [← ks_eq]
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [deformedInputTable, deformedSigmaTable, Matrix.submatrix_apply,
      deformedRAIndex, deformedREIndex, finProdFinEquiv, ks, Matrix.trace,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_two, map_ofNat] <;> ring_nf
  all_goals (norm_num; ring)

end
end QIT.QubitActivation
