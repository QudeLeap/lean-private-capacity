/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedEncoding

/-! # The average state and Holevo expression of the new binary code -/

@[expose] public section
namespace QIT.QubitActivation
open Channel
noncomputable section

def deformedAverage : State RA :=
  mixInput (deformedLetter false) (deformedLetter true) deformedProbability
    (by norm_num [deformedProbability]) (by norm_num [deformedProbability])

theorem deformed_output_average {b : Type*} [Fintype b] [DecidableEq b]
    (N : Channel ProductInput b) :
    (N.outputEnsemble deformedEnsemble).averageState =
      N.applyState (deformedAverage.reindex (Equiv.prodComm (Fin 2) (Fin 4))) := by
  have hm : (N.outputEnsemble deformedEnsemble).averageState =
      N.applyState deformedEnsemble.averageState := by
    apply State.ext
    change (∑ x, (deformedEnsemble.probs x) • N.map (deformedEnsemble.states x).matrix) =
      N.map (∑ x, (deformedEnsemble.probs x) • (deformedEnsemble.states x).matrix)
    simp only [NNReal.smul_def, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact ((N.map.restrictScalars ℝ).map_smul (deformedEnsemble.probs x : ℝ)
      (deformedEnsemble.states x).matrix).symm
  rw [hm]
  congr 1
  apply State.ext
  ext i j
  norm_num [Ensemble.averageState, deformedEnsemble, ensemble, Fintype.sum_bool,
    deformedAverage, mixInput, State.reindex, deformedProbability, Matrix.submatrix_apply,
    NNReal.smul_def, NNReal.toReal, Complex.real_smul]
  ring

theorem deformed_output_holevo {b : Type*} [Fintype b] [DecidableEq b]
    (N : Channel ProductInput b) :
    (N.outputEnsemble deformedEnsemble).holevoInformation =
      (N.applyState (deformedAverage.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann -
      (13 / 16) * (N.applyState
        ((deformedLetter false).reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann -
      (3 / 16) * (N.applyState
        ((deformedLetter true).reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann := by
  rw [Ensemble.holevoInformation_def, deformed_output_average, Fintype.sum_bool]
  change (N.applyState (deformedAverage.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann -
      ((3 / 16) * (N.applyState
        ((deformedLetter true).reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann +
       (1 - 3 / 16) * (N.applyState
        ((deformedLetter false).reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann) = _
  ring

end
end QIT.QubitActivation
