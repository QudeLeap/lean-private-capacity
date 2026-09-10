/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedMeasurement
public import QIT.Coding.Private.QubitEntropyIntervals

/-! # Entropy bookkeeping for the fixed measurement with the erasure flag -/

@[expose] public section
namespace QIT.QubitActivation
open Channel
noncomputable section

def deformedReferenceMeasurement : POVM (Fin 8) RA where
  effects j := rankOneMatrix (deformedReceiverVector j)
  pos _ := rankOneMatrix_pos _
  sum_eq_one := deformedReceiverVector_complete

def deformedBlockEffect (j : DeformedOutcome) : CMatrix (RA ⊕ Fin 4) :=
  match j with
  | Sum.inl i => Matrix.fromBlocks (rankOneMatrix (deformedReceiverVector i)) 0 0 0
  | Sum.inr i => Matrix.fromBlocks 0 0 0 (Matrix.single i i 1)

theorem deformedMeasurement_effect_blocks (j : DeformedOutcome) :
    (deformedMeasurement.effects j).submatrix receiverRegisterEquiv receiverRegisterEquiv =
      deformedBlockEffect j := by
  cases j <;> ext x y <;> rcases x with x | x <;> rcases y with y | y <;>
    simp [deformedMeasurement, deformedFullVector, deformedBlockEffect,
      receiverRegisterEquiv, Matrix.submatrix_apply, rankOneMatrix_apply,
      Matrix.single_apply, ite_and, mul_ite]
  all_goals split_ifs <;> simp_all

theorem trace_submatrix_equiv_local {a b : Type*} [Fintype a] [Fintype b]
    (e : a ≃ b) (X : CMatrix b) : (X.submatrix e e).trace = X.trace := by
  exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)

theorem deformedMeasurement_expectation (rho : State RA) (j : DeformedOutcome) :
    ((productChannel.applyState (rho.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).matrix *
      deformedMeasurement.effects j).trace =
    (1 / 2 : ℂ) * match j with
    | Sum.inl i => ((referencedReceiver.applyState rho).matrix *
        deformedReferenceMeasurement.effects i).trace
    | Sum.inr i => ((privateN.applyState rho.marginalB).matrix *
        (POVM.coordinate (Fin 4)).effects i).trace := by
  rw [← trace_submatrix_equiv_local receiverRegisterEquiv,
    ← Matrix.submatrix_mul_equiv _ _ _ receiverRegisterEquiv _,
    full_receiver_outputs, deformedMeasurement_effect_blocks]
  cases j <;>
    simp [deformedBlockEffect, deformedReferenceMeasurement, POVM.coordinate,
      Matrix.fromBlocks_multiply, Matrix.trace_smul,
      Matrix.trace_fromBlocks_diagonal, smul_eq_mul]

theorem deformedMeasured_half_blocks (rho : State RA) :
    ((measure deformedMeasurement).applyState
      (productChannel.applyState (rho.reindex (Equiv.prodComm (Fin 2) (Fin 4))))).matrix =
    (1 / 2 : ℂ) • Matrix.fromBlocks
      ((measure deformedReferenceMeasurement).applyState
        (referencedReceiver.applyState rho)).matrix 0 0
      ((measure (POVM.coordinate (Fin 4))).applyState (privateN.applyState rho.marginalB)).matrix :=
        by
  change (measure deformedMeasurement).map
    (productChannel.applyState (rho.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).matrix =
    (1 / 2 : ℂ) • Matrix.fromBlocks
      ((measure deformedReferenceMeasurement).map (referencedReceiver.applyState rho).matrix) 0 0
      ((measure (POVM.coordinate (Fin 4))).map (privateN.applyState rho.marginalB).matrix)
  rw [measure_map_state_diagonal, measure_map_state_diagonal, measure_map_state_diagonal]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.diagonal_apply, deformedMeasurement_expectation]

theorem deformedMeasured_entropy (rho : State RA) :
    ((measure deformedMeasurement).applyState
      (productChannel.applyState (rho.reindex (Equiv.prodComm (Fin 2) (Fin 4))))).vonNeumann =
    1 + ((measure deformedReferenceMeasurement).applyState
      (referencedReceiver.applyState rho)).vonNeumann / 2 +
      ((measure (POVM.coordinate (Fin 4))).applyState
        (privateN.applyState rho.marginalB)).vonNeumann / 2 :=
  vonNeumann_half_blocks _ _ _ (deformedMeasured_half_blocks rho)

end
end QIT.QubitActivation
