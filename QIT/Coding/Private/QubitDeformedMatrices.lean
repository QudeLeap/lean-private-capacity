/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedEnvironmentTable

/-! # Equality of the finite tables and the physical Kraus maps -/

@[expose] public section
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 4000 in
/-- The full receiver output of the same four-coefficient input. -/
theorem deformedBetaTable_correct (a b c d : ℂ) :
    referencedReceiver.map
        ((deformedInputTable a b c d).submatrix deformedRAIndex deformedRAIndex) =
      (deformedBetaTable a b c d).submatrix deformedRAIndex deformedRAIndex := by
  ext ⟨r, i⟩ ⟨s, j⟩
  change MatrixMap.kron (idChannel (Fin 2)).map privateN.map _ _ _ = _
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  change (∑ k : Fin 8, (krausN k * _ * (krausN k).conjTranspose : CMatrix (Fin 4))) i j = _
  rw [← ks_eq]
  fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [deformedInputTable, deformedBetaTable, Matrix.submatrix_apply,
      deformedRAIndex, finProdFinEquiv, ks, Matrix.sum_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.cons_val, Matrix.cons_val_two, map_ofNat] <;> ring_nf
  all_goals (norm_num; ring)

end
end QIT.QubitActivation
