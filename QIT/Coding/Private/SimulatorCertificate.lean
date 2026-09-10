/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module
public import QIT.Coding.Private.SimulatorData

/-!
# The transpose simulator on all sixteen matrix units

This is the finite check described in Appendix A, `cert:finite-sums`
and `cert:transpose`. Every entry is checked with exact radical arithmetic
by the Lean kernel; the author-supplied Python results are not proof inputs.
-/

@[expose] public section
namespace QIT
open Channel SimulatorCanonical
set_option maxRecDepth 4000 in
set_option maxHeartbeats 30000000 in
theorem simulator_matrix_unit (i j : Fin 4) :
    simulatorD.map (complementN.map (Matrix.single i j (1 : ℂ))) =
      Matrix.transpose (privateN.map (Matrix.single i j (1 : ℂ))) := by
  ext r s
  change ((MatrixMap.ofKraus simulatorKraus).comp
      (MatrixMap.complementOfKraus krausN)) (Matrix.single i j 1) r s =
    MatrixMap.ofKraus krausN (Matrix.single i j 1) s r
  rw [← ks_eq, ← ds_eq, MatrixMap.complementOfKraus_eq_ofKraus,
    MatrixMap.ofKraus_comp_ofKraus]
  simp only [ofKraus_single_apply]
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases s <;>
    norm_num [ds, ks, as, bs, Matrix.mul_apply, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fin.sum_univ_succ, star_mul, star_neg, star_div,
    map_ofNat, Matrix.cons_val_two, Matrix.cons_val, Fin.reduceFinMk] <;> ring_nf
  all_goals norm_num <;> ring
end QIT
