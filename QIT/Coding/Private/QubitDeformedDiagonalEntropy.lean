/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedOutputs
public import QIT.Coding.Private.QubitDeformedNumerics
public import QIT.Coding.Private.QubitDeformedMeasuredTable

/-! # Entropies of the diagonal and measured outputs of the new code -/

@[expose] public section
namespace QIT.QubitActivation
open Channel
noncomputable section

set_option maxHeartbeats 2000000

theorem deformedB_entropy (k : Fin 3) :
    (deformedB k).vonNeumann = deformedShannon (deformedNumericB k) := by
  apply State.vonNeumann_eq_neg_sum_xlog2_of_diagonal
  rw [deformedB_matrix]
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [deformedBTable, deformedNumericB, deformedCoefficients,
      Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem deformedEpsilon_entropy (k : Fin 3) :
    (deformedEpsilon k).vonNeumann = deformedShannon (deformedNumericE k) := by
  apply State.vonNeumann_eq_neg_sum_xlog2_of_diagonal
  rw [deformedEpsilon_matrix]
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [deformedEpsilonTable, deformedNumericE, deformedCoefficients,
      Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]


theorem deformedReferenceMeasured_entropy (k : Fin 3) :
    ((measure deformedReferenceMeasurement).applyState (deformedBeta k)).vonNeumann =
      deformedShannon (deformedNumericM k) := by
  apply State.vonNeumann_eq_neg_sum_xlog2_of_diagonal
  change (measure deformedReferenceMeasurement).map (deformedBeta k).matrix = _
  rw [measure_map_state_diagonal, deformedBeta_matrix]
  congr 1
  funext j
  rw [deformedBetaTable_measurement]
  fin_cases k <;> fin_cases j <;>
    norm_num [deformedMeasurementTable, deformedNumericM, deformedCoefficients,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem deformedCoordinateB_entropy (k : Fin 3) :
    ((measure (POVM.coordinate (Fin 4))).applyState (deformedB k)).vonNeumann =
      deformedShannon (deformedNumericB k) := by
  rw [coordinate_measure_preserves_diagonal (deformedB k)
    (fun i ↦ (deformedNumericB k i : ℂ)) ?_, deformedB_entropy]
  rw [deformedB_matrix]
  ext i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [deformedBTable, deformedNumericB, deformedCoefficients,
      Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

theorem deformedFullMeasured_entropy (k : Fin 3) :
    ((measure deformedMeasurement).applyState
      (productChannel.applyState
        ((deformedTestState k).reindex (Equiv.prodComm (Fin 2) (Fin 4))))).vonNeumann =
      1 + deformedShannon (deformedNumericM k) / 2 +
        deformedShannon (deformedNumericB k) / 2 := by
  rw [deformedMeasured_entropy]
  change 1 + ((measure deformedReferenceMeasurement).applyState
    (deformedBeta k)).vonNeumann / 2 +
    ((measure (POVM.coordinate (Fin 4))).applyState (deformedB k)).vonNeumann / 2 = _
  rw [deformedReferenceMeasured_entropy, deformedCoordinateB_entropy]

/-- First column of the manuscript's entropy table, for the actual fixed measurement. -/
theorem deformedMeasuredEntropy_table (k : Fin 3) :
    (![2743053503 / 1000000000, 2769824801 / 1000000000,
      2750133614 / 1000000000] k : ℝ) ≤
      ((measure deformedReferenceMeasurement).applyState (deformedBeta k)).vonNeumann ∧
    ((measure deformedReferenceMeasurement).applyState (deformedBeta k)).vonNeumann ≤
      ![2743053503 / 1000000000, 2769824801 / 1000000000,
        2750133614 / 1000000000] k + 1 / 1000000000 := by
  rw [deformedReferenceMeasured_entropy]
  convert deformedNumericM_table k using 1 <;> norm_num

/-- Second column of the manuscript's entropy table. -/
theorem deformedBEntropy_table (k : Fin 3) :
    (![1979808092 / 1000000000, 1983064558 / 1000000000,
      1980440773 / 1000000000] k : ℝ) ≤ (deformedB k).vonNeumann ∧
    (deformedB k).vonNeumann ≤ ![1979808092 / 1000000000, 1983064558 / 1000000000,
      1980440773 / 1000000000] k + 1 / 1000000000 := by
  rw [deformedB_entropy]
  convert deformedNumericB_table k using 1 <;> norm_num

/-- Fourth column of the manuscript's entropy table. -/
theorem deformedEpsilonEntropy_table (k : Fin 3) :
    (![2918760088 / 1000000000, 2930141639 / 1000000000,
      2920972682 / 1000000000] k : ℝ) ≤ (deformedEpsilon k).vonNeumann ∧
    (deformedEpsilon k).vonNeumann ≤ ![2918760088 / 1000000000, 2930141639 / 1000000000,
      2920972682 / 1000000000] k + 1 / 1000000000 := by
  rw [deformedEpsilon_entropy]
  convert deformedNumericE_table k using 1 <;> norm_num

end
end QIT.QubitActivation
