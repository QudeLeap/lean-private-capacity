/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedData
public import QIT.Coding.Private.QubitEntropyIntervals

/-! # Exact environmental block characteristic polynomials -/

@[expose] public section
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

-- The eight nested finite sums require a larger instance-search size budget.
set_option synthInstance.maxSize 4096

def deformedBlock0 (a b c d : ℂ) : CMatrix (Fin 3) :=
  ![![((1 / 6) * a + (1 / 6) * b + (1 / 6) * d), ((-1 / 14) * b * r7 + (-1 / 42) * a * r7 + (1 / 14)
    * d * r7), ((-1 / 21) * d * r3 * r7 + (2 / 21) * c * r3 * r7)],
    ![((-1 / 14) * b * r7 + (-1 / 42) * a * r7 + (1 / 14) * d * r7), ((1 / 42) * a + (3 / 14) * b +
      (3 / 14) * d), ((-4 / 21) * c * r3 + (-1 / 7) * d * r3)],
    ![((-1 / 21) * d * r3 * r7 + (2 / 21) * c * r3 * r7), ((-4 / 21) * c * r3 + (-1 / 7) * d * r3),
      ((2 / 7) * d + (2 / 21) * a + (2 / 21) * b)]]

def deformedBlock1 (_a _b _c _d : ℂ) : CMatrix (Fin 1) :=
  ![![0]]

def deformedBlock2 (a b c _d : ℂ) : CMatrix (Fin 2) :=
  ![![(5 / 21) * b, (-5 / 21) * c * r2 * r3],
    ![(-5 / 21) * c * r2 * r3, (10 / 21) * a]]

def deformedBlock3 (a b c d : ℂ) : CMatrix (Fin 2) :=
  ![![((2 / 7) * b + (2 / 21) * d), ((-1 / 7) * c * r2 * r5 + (-1 / 21) * d * r2 * r5)],
    ![((-1 / 7) * c * r2 * r5 + (-1 / 21) * d * r2 * r5), ((5 / 21) * a + (5 / 21) * d)]]

def deformedBlock4 (a b c d : ℂ) : CMatrix (Fin 3) :=
  ![![((2 / 7) * d + (2 / 21) * a + (2 / 21) * b), ((-2 / 21) * c * r3 * r7 + (1 / 21) * d * r3 *
    r7), ((-4 / 21) * c * r3 + (-1 / 7) * d * r3)],
    ![((-2 / 21) * c * r3 * r7 + (1 / 21) * d * r3 * r7), ((1 / 6) * a + (1 / 6) * b + (1 / 6) * d),
      ((-1 / 14) * d * r7 + (1 / 14) * b * r7 + (1 / 42) * a * r7)],
    ![((-4 / 21) * c * r3 + (-1 / 7) * d * r3), ((-1 / 14) * d * r7 + (1 / 14) * b * r7 + (1 / 42) *
      a * r7), ((1 / 42) * a + (3 / 14) * b + (3 / 14) * d)]]

def deformedBlock5 (a b c d : ℂ) : CMatrix (Fin 2) :=
  ![![((5 / 21) * a + (5 / 21) * d), ((-1 / 7) * c * r2 * r5 + (-1 / 21) * d * r2 * r5)],
    ![((-1 / 7) * c * r2 * r5 + (-1 / 21) * d * r2 * r5), ((2 / 7) * b + (2 / 21) * d)]]

def deformedBlock6 (a b c _d : ℂ) : CMatrix (Fin 2) :=
  ![![(10 / 21) * a, (-5 / 21) * c * r2 * r3],
    ![(-5 / 21) * c * r2 * r3, (5 / 21) * b]]

def deformedBlock7 (_a _b _c _d : ℂ) : CMatrix (Fin 1) :=
  ![![0]]

def deformedPoly0 (a b c d : ℂ) : Polynomial ℂ :=
  Polynomial.C (1) * Polynomial.X ^ 3 +
    Polynomial.C (((-10 / 21) * b + (-2 / 3) * d + (-2 / 7) * a)) * Polynomial.X ^ 2 +
    Polynomial.C (((-44 / 147) * (c) ^ 2 + (8 / 441) * (a) ^ 2 + (16 / 441) * (b) ^ 2 + (4 / 147) *
      c * d + (31 / 441) * a * b + (68 / 441) * a * d + (127 / 441) * b * d)) * Polynomial.X +
    Polynomial.C (((-8 / 1323) * d * (a) ^ 2 + (-2 / 147) * d * (b) ^ 2 + (-2 / 1323) * a * (b) ^ 2
      + (-2 / 1323) * b * (a) ^ 2 + (2 / 441) * a * (c) ^ 2 + (2 / 441) * b * (c) ^ 2 + (50 / 441) *
      d * (c) ^ 2 + (-32 / 1323) * a * b * d + (-4 / 147) * b * c * d + (8 / 441) * a * c * d))

def deformedPoly2 (a b c _d : ℂ) : Polynomial ℂ :=
  Polynomial.C (1) * Polynomial.X ^ 2 +
    Polynomial.C (((-10 / 21) * a + (-5 / 21) * b)) * Polynomial.X +
    Polynomial.C (((-50 / 147) * (c) ^ 2 + (50 / 441) * a * b))

def deformedPoly3 (a b c d : ℂ) : Polynomial ℂ :=
  Polynomial.C (1) * Polynomial.X ^ 2 +
    Polynomial.C (((-5 / 21) * a + (-2 / 7) * b + (-1 / 3) * d)) * Polynomial.X +
    Polynomial.C (((-10 / 49) * (c) ^ 2 + (-20 / 147) * c * d + (10 / 147) * a * b + (10 / 147) * b
      * d + (10 / 441) * a * d))

set_option maxHeartbeats 2000000 in
theorem deformedBlock0_charpoly (a b c d : ℂ) :
    (deformedBlock0 a b c d).charpoly = deformedPoly0 a b c d := by
  apply Polynomial.funext
  intro z
  norm_num [Matrix.eval_charpoly, deformedBlock0, deformedPoly0, Matrix.scalar,
    Matrix.det_fin_three, Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Fin.ext_iff]
  ring_nf
  all_goals (norm_num; ring)

set_option maxHeartbeats 2000000 in
theorem deformedBlock1_charpoly (a b c d : ℂ) :
    (deformedBlock1 a b c d).charpoly = Polynomial.X := by
  apply Polynomial.funext
  intro z
  norm_num [Matrix.eval_charpoly, deformedBlock1, Matrix.scalar,
    Matrix.det_unique, Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Fin.ext_iff]

set_option maxHeartbeats 2000000 in
theorem deformedBlock2_charpoly (a b c d : ℂ) :
    (deformedBlock2 a b c d).charpoly = deformedPoly2 a b c d := by
  apply Polynomial.funext
  intro z
  norm_num [Matrix.eval_charpoly, deformedBlock2, deformedPoly2, Matrix.scalar,
    Matrix.det_fin_two, Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Fin.ext_iff]
  ring_nf
  all_goals (norm_num; ring)

set_option maxHeartbeats 2000000 in
theorem deformedBlock3_charpoly (a b c d : ℂ) :
    (deformedBlock3 a b c d).charpoly = deformedPoly3 a b c d := by
  apply Polynomial.funext
  intro z
  norm_num [Matrix.eval_charpoly, deformedBlock3, deformedPoly3, Matrix.scalar,
    Matrix.det_fin_two, Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Fin.ext_iff]
  ring_nf
  all_goals (norm_num; ring)

set_option maxHeartbeats 2000000 in
theorem deformedBlock4_charpoly (a b c d : ℂ) :
    (deformedBlock4 a b c d).charpoly = deformedPoly0 a b c d := by
  apply Polynomial.funext
  intro z
  norm_num [Matrix.eval_charpoly, deformedBlock4, deformedPoly0, Matrix.scalar,
    Matrix.det_fin_three, Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Fin.ext_iff]
  ring_nf
  all_goals (norm_num; ring)

set_option maxHeartbeats 2000000 in
theorem deformedBlock5_charpoly (a b c d : ℂ) :
    (deformedBlock5 a b c d).charpoly = deformedPoly3 a b c d := by
  apply Polynomial.funext
  intro z
  norm_num [Matrix.eval_charpoly, deformedBlock5, deformedPoly3, Matrix.scalar,
    Matrix.det_fin_two, Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Fin.ext_iff]
  ring_nf
  all_goals (norm_num; ring)

set_option maxHeartbeats 2000000 in
theorem deformedBlock6_charpoly (a b c d : ℂ) :
    (deformedBlock6 a b c d).charpoly = deformedPoly2 a b c d := by
  apply Polynomial.funext
  intro z
  norm_num [Matrix.eval_charpoly, deformedBlock6, deformedPoly2, Matrix.scalar,
    Matrix.det_fin_two, Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Fin.ext_iff]
  ring_nf
  all_goals (norm_num; ring)

set_option maxHeartbeats 2000000 in
theorem deformedBlock7_charpoly (a b c d : ℂ) :
    (deformedBlock7 a b c d).charpoly = Polynomial.X := by
  apply Polynomial.funext
  intro z
  norm_num [Matrix.eval_charpoly, deformedBlock7, Matrix.scalar,
    Matrix.det_unique, Matrix.diagonal_apply, Matrix.cons_val, Matrix.cons_val_two, Fin.ext_iff]

abbrev DeformedBlocks :=
  Fin 3 ⊕ (Fin 1 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ (Fin 3 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin 1))))))

instance : DecidableEq DeformedBlocks := inferInstanceAs (DecidableEq
  (Fin 3 ⊕ (Fin 1 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ (Fin 3 ⊕ (Fin 2 ⊕ (Fin 2 ⊕ Fin 1))))))))

def deformedBlockNatural : DeformedBlocks ≃ Fin 16 :=
  (Equiv.sumCongr (Equiv.refl _) (
    (Equiv.sumCongr (Equiv.refl _) (
      (Equiv.sumCongr (Equiv.refl _) (
        (Equiv.sumCongr (Equiv.refl _) (
          (Equiv.sumCongr (Equiv.refl _) (
            (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
              finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans
                finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv

def deformedBlockPermutation : Fin 16 ≃ Fin 16 := Equiv.ofBijective
  (fun i ↦ ![0, 4, 11, 1, 2, 9, 3, 10, 5, 8, 12, 6, 13, 7, 14, 15] i) (by decide)

def deformedBlockIndex : DeformedBlocks ≃ Fin 16 :=
  deformedBlockNatural.trans deformedBlockPermutation

def deformedBlockDiagonal (a b c d : ℂ) : CMatrix DeformedBlocks :=
  Matrix.fromBlocks (deformedBlock0 a b c d) 0 0 (
    Matrix.fromBlocks (deformedBlock1 a b c d) 0 0 (
      Matrix.fromBlocks (deformedBlock2 a b c d) 0 0 (
        Matrix.fromBlocks (deformedBlock3 a b c d) 0 0 (
          Matrix.fromBlocks (deformedBlock4 a b c d) 0 0 (
            Matrix.fromBlocks (deformedBlock5 a b c d) 0 0 (
              Matrix.fromBlocks (deformedBlock6 a b c d) 0 0 (
                deformedBlock7 a b c d)))))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 4000 in
theorem deformedBlockDiagonal_correct (a b c d : ℂ) :
    (deformedSigmaTable a b c d).submatrix deformedBlockIndex deformedBlockIndex =
      deformedBlockDiagonal a b c d := by
  ext x y
  rcases x with x | x | x | x | x | x | x | x <;>
    rcases y with y | y | y | y | y | y | y | y <;>
    fin_cases x <;> fin_cases y <;>
    rfl

theorem deformedSigmaTable_charpoly (a b c d : ℂ) :
    (deformedSigmaTable a b c d).charpoly = Polynomial.X ^ 2 *
      (deformedPoly0 a b c d) ^ 2 * (deformedPoly2 a b c d) ^ 2 *
      (deformedPoly3 a b c d) ^ 2 := by
  have h := Matrix.charpoly_reindex deformedBlockIndex.symm (deformedSigmaTable a b c d)
  change ((deformedSigmaTable a b c d).submatrix deformedBlockIndex deformedBlockIndex).charpoly = _
    at h
  rw [deformedBlockDiagonal_correct] at h
  rw [← h]
  simp only [deformedBlockDiagonal, Matrix.charpoly_fromBlocks_zero₁₂,
    deformedBlock0_charpoly, deformedBlock1_charpoly, deformedBlock2_charpoly,
    deformedBlock3_charpoly, deformedBlock4_charpoly, deformedBlock5_charpoly,
    deformedBlock6_charpoly, deformedBlock7_charpoly]
  ring

end
end QIT.QubitActivation
