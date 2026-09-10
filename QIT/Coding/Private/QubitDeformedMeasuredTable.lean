/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedData
public import QIT.Coding.Private.QubitDeformedFlaggedMeasurement

/-! # Born probabilities of the paper's eight-vector receiver measurement -/

@[expose] public section
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 4000 in
theorem deformedBetaTable_measurement (a b c d : ℂ) (j : Fin 8) :
    ((deformedBetaTable a b c d).submatrix deformedRAIndex deformedRAIndex *
      deformedReferenceMeasurement.effects j).trace = deformedMeasurementTable a b c d j := by
  have hexpand (M : CMatrix RA) (i : Fin 8) :
      (M * deformedReferenceMeasurement.effects i).trace =
      ∑ r : Fin 2, ∑ x : Fin 4, ∑ s : Fin 2, ∑ y : Fin 4,
        M (r, x) (s, y) *
          (deformedReceiverVector i (s, y) * star (deformedReceiverVector i (r, x))) := by
    simp only [deformedReferenceMeasurement, Matrix.trace, Matrix.diag_apply,
      Matrix.mul_apply, rankOneMatrix_apply, Fintype.sum_prod_type]
  rw [hexpand]
  fin_cases j <;>
    simp only [Fin.sum_univ_succ] <;>
    norm_num [deformedReceiverVector, phiCanonical, map_ofNat] <;>
    norm_num [deformedBetaTable, deformedMeasurementTable, deformedReferenceMeasurement,
      deformedReceiverVector, phiCanonical, rankOneMatrix_apply, Matrix.trace,
      Matrix.mul_apply, Matrix.submatrix_apply, deformedRAIndex, finProdFinEquiv,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.cons_val, Matrix.cons_val_two,
      Fin.ext_iff, map_ofNat] <;> ring_nf
  all_goals (norm_num; ring)

theorem coordinate_measure_preserves_diagonal {a : Type*} [Fintype a] [DecidableEq a]
    (rho : State a) (p : a → ℂ) (h : rho.matrix = Matrix.diagonal p) :
    (measure (POVM.coordinate a)).applyState rho = rho := by
  apply State.ext
  change (measure (POVM.coordinate a)).map rho.matrix = rho.matrix
  rw [measure_map_state_diagonal, h]
  congr 1
  funext i
  simp [POVM.coordinate, Matrix.trace, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.single_apply, ite_and, eq_comm]

end
end QIT.QubitActivation
