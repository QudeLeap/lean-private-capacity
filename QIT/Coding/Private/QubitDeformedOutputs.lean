/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedMatrices

/-! # Exact outputs of the two new letters and their average -/

@[expose] public section
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

/-- Order: abundant letter, diluted signal, average with signal probability 3/16. -/
def deformedTestState (k : Fin 3) : State RA :=
  ![deformedLetter false, deformedLetter true,
    mixInput (deformedLetter false) (deformedLetter true) deformedProbability
      (by norm_num [deformedProbability]) (by norm_num [deformedProbability])] k

/-- Exact rational coefficients of the three physical input states. -/
def deformedCoefficients (k : Fin 3) : Fin 4 → ℂ :=
  ![![3006003 / 8012006, 500000 / 4006003, 500500 / 4006003, 0],
    ![2913164919 / 7988006000, 486500 / 3994003, 972027 / 7988006, 27 / 2000],
    ![191088247215143271 / 511999616000288000, 7951945219625 / 63999952000036,
      63655790273243 / 511999616000288, 81 / 32000]] k

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
theorem deformedTestState_matrix (k : Fin 3) :
    (deformedTestState k).matrix =
      (deformedInputTable (deformedCoefficients k 0) (deformedCoefficients k 1)
        (deformedCoefficients k 2) (deformedCoefficients k 3)).submatrix
          deformedRAIndex deformedRAIndex := by
  ext ⟨r, i⟩ ⟨s, j⟩
  fin_cases k <;> fin_cases r <;> fin_cases s <;> fin_cases i <;> fin_cases j <;>
    norm_num [deformedTestState, deformedCoefficients, deformedInputTable,
      deformedLetter, mixInput, deformedBase, deformationNorm, deformedKet0, deformedKet1,
      deformedR0, deformedR1, deformedMixing, deformedProbability,
      rho1, rho1Mat, phi2, rankOneMatrix_apply, deformedRAIndex, finProdFinEquiv,
      Matrix.submatrix_apply, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three,
      erasureInvSqrtTwo, r3, map_ofNat, inv_pow,
      ← pow_two, div_pow, ← Complex.ofReal_pow, Real.sq_sqrt] <;> ring_nf
  all_goals norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

def deformedSigma (k : Fin 3) : State RE :=
  referencedEnvironment.applyState (deformedTestState k)

def deformedBeta (k : Fin 3) : State RA :=
  referencedReceiver.applyState (deformedTestState k)

def deformedB (k : Fin 3) : State (Fin 4) :=
  privateN.applyState (deformedTestState k).marginalB

def deformedEpsilon (k : Fin 3) : State (Fin 8) :=
  complementN.applyState (deformedTestState k).marginalB

theorem deformedSigma_matrix (k : Fin 3) :
    (deformedSigma k).matrix =
      (deformedSigmaTable (deformedCoefficients k 0) (deformedCoefficients k 1)
        (deformedCoefficients k 2) (deformedCoefficients k 3)).submatrix
          deformedREIndex deformedREIndex := by
  change referencedEnvironment.map (deformedTestState k).matrix = _
  rw [deformedTestState_matrix, deformedSigmaTable_correct]

theorem deformedBeta_matrix (k : Fin 3) :
    (deformedBeta k).matrix =
      (deformedBetaTable (deformedCoefficients k 0) (deformedCoefficients k 1)
        (deformedCoefficients k 2) (deformedCoefficients k 3)).submatrix
          deformedRAIndex deformedRAIndex := by
  change referencedReceiver.map (deformedTestState k).matrix = _
  rw [deformedTestState_matrix, deformedBetaTable_correct]

theorem deformedB_matrix (k : Fin 3) :
    (deformedB k).matrix = deformedBTable (deformedCoefficients k 0)
      (deformedCoefficients k 1) (deformedCoefficients k 2) (deformedCoefficients k 3) := by
  have h := congrArg State.matrix (State.marginalB_applyState_prod
    (deformedTestState k) (idChannel (Fin 2)) privateN)
  change partialTraceA (deformedBeta k).matrix = (deformedB k).matrix at h
  rw [← h, deformedBeta_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceA, deformedBetaTable, deformedBTable, Matrix.submatrix_apply,
      deformedRAIndex, finProdFinEquiv, Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 2000000 in
theorem deformedEpsilon_matrix (k : Fin 3) :
    (deformedEpsilon k).matrix = deformedEpsilonTable (deformedCoefficients k 0)
      (deformedCoefficients k 1) (deformedCoefficients k 2) (deformedCoefficients k 3) := by
  have h := congrArg State.matrix (State.marginalB_applyState_prod
    (deformedTestState k) (idChannel (Fin 2)) complementN)
  change partialTraceA (deformedSigma k).matrix = (deformedEpsilon k).matrix at h
  rw [← h, deformedSigma_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [partialTraceA, deformedSigmaTable, deformedEpsilonTable, Matrix.submatrix_apply,
      deformedREIndex, finProdFinEquiv, Fin.sum_univ_succ] <;> ring

end
end QIT.QubitActivation
