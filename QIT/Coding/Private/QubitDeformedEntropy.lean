/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedOutputs
public import QIT.Coding.Private.QubitDeformedSpectrum
public import QIT.Coding.Private.QubitDeformedNumerics
public import QIT.Coding.Private.QubitDeformedMeasurement

/-! # Connecting the entropy certificates to the physical output states -/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
open Channel Polynomial
noncomputable section

def deformedNumericPolynomial : Fin 3 → ℝ[X] :=
  ![X ^ 2 * deformed_numeric_poly_0_0 ^ 2 * deformed_numeric_poly_0_2 ^ 2 *
      deformed_numeric_poly_0_3 ^ 2,
    X ^ 2 * deformed_numeric_poly_1_0 ^ 2 * deformed_numeric_poly_1_2 ^ 2 *
      deformed_numeric_poly_1_3 ^ 2,
    X ^ 2 * deformed_numeric_poly_2_0 ^ 2 * deformed_numeric_poly_2_2 ^ 2 *
      deformed_numeric_poly_2_3 ^ 2]

theorem roots_three_squares (p q r : ℝ[X]) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    (X ^ 2 * p ^ 2 * q ^ 2 * r ^ 2).roots =
      2 • ({0} : Multiset ℝ) + 2 • p.roots + 2 • q.roots + 2 • r.roots := by
  have hx : (X : ℝ[X]) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
  have hp2 := pow_ne_zero 2 hp
  have hq2 := pow_ne_zero 2 hq
  have hr2 := pow_ne_zero 2 hr
  rw [roots_mul (mul_ne_zero (mul_ne_zero (mul_ne_zero hx hp2) hq2) hr2),
    roots_mul (mul_ne_zero (mul_ne_zero hx hp2) hq2), roots_mul (mul_ne_zero hx hp2)]
  simp only [roots_pow, roots_X]

set_option maxHeartbeats 4000000 in
theorem deformedNumericPolynomial_roots (k : Fin 3) :
    (deformedNumericPolynomial k).roots = deformedNumericRoots k := by
  have hu2 : (Finset.univ : Finset (Fin 2)).val = ({0, 1} : Multiset (Fin 2)) := by decide
  have hu3 : (Finset.univ : Finset (Fin 3)).val = ({0, 1, 2} : Multiset (Fin 3)) := by decide
  have hn0 : deformed_numeric_poly_0_0 ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_0_0] at he
  have hn1 : deformed_numeric_poly_0_2 ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_0_2] at he
  have hn2 : deformed_numeric_poly_0_3 ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_0_3] at he
  have hn3 : deformed_numeric_poly_1_0 ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_1_0] at he
  have hn4 : deformed_numeric_poly_1_2 ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_1_2] at he
  have hn5 : deformed_numeric_poly_1_3 ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_1_3] at he
  have hn6 : deformed_numeric_poly_2_0 ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_2_0] at he
  have hn7 : deformed_numeric_poly_2_2 ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_2_2] at he
  have hn8 : deformed_numeric_poly_2_3 ≠ 0 := by
    intro h
    have he := congrArg (fun p : ℝ[X] ↦ p.eval 1) h
    norm_num [deformed_numeric_poly_2_3] at he
  fin_cases k
  · change (X ^ 2 * _ ^ 2 * _ ^ 2 * _ ^ 2).roots = _
    rw [roots_three_squares _ _ _ hn0 hn1 hn2, deformed_roots_0_0_complete,
      deformed_roots_0_2_complete, deformed_roots_0_3_complete]
    norm_num [deformedNumericRoots, deformed_roots_0_0, deformed_roots_0_2,
      deformed_roots_0_3, hu2, hu3, two_nsmul, Matrix.cons_val_two]
    simp only [← Multiset.singleton_add]
    ac_rfl
  · change (X ^ 2 * _ ^ 2 * _ ^ 2 * _ ^ 2).roots = _
    rw [roots_three_squares _ _ _ hn3 hn4 hn5, deformed_roots_1_0_complete,
      deformed_roots_1_2_complete, deformed_roots_1_3_complete]
    norm_num [deformedNumericRoots, deformed_roots_1_0, deformed_roots_1_2,
      deformed_roots_1_3, hu2, hu3, two_nsmul, Matrix.cons_val_two]
    simp only [← Multiset.singleton_add]
    ac_rfl
  · change (X ^ 2 * _ ^ 2 * _ ^ 2 * _ ^ 2).roots = _
    rw [roots_three_squares _ _ _ hn6 hn7 hn8, deformed_roots_2_0_complete,
      deformed_roots_2_2_complete, deformed_roots_2_3_complete]
    norm_num [deformedNumericRoots, deformed_roots_2_0, deformed_roots_2_2,
      deformed_roots_2_3, hu2, hu3, two_nsmul, Matrix.cons_val_two]
    simp only [← Multiset.singleton_add]
    ac_rfl

set_option maxHeartbeats 4000000 in
theorem deformedSigma_charpoly (k : Fin 3) :
    (deformedSigma k).matrix.charpoly =
      (deformedNumericPolynomial k).map Complex.ofRealHom := by
  rw [deformedSigma_matrix]
  have h := Matrix.charpoly_reindex deformedREIndex.symm
    (deformedSigmaTable (deformedCoefficients k 0) (deformedCoefficients k 1)
      (deformedCoefficients k 2) (deformedCoefficients k 3))
  change ((deformedSigmaTable _ _ _ _).submatrix deformedREIndex deformedREIndex).charpoly = _ at h
  rw [h, deformedSigmaTable_charpoly]
  fin_cases k <;> apply Polynomial.funext <;> intro z <;>
    norm_num [deformedNumericPolynomial, deformedCoefficients, deformedPoly0,
      deformedPoly2, deformedPoly3, deformed_numeric_poly_0_0, deformed_numeric_poly_0_2,
      deformed_numeric_poly_0_3, deformed_numeric_poly_1_0, deformed_numeric_poly_1_2,
      deformed_numeric_poly_1_3, deformed_numeric_poly_2_0, deformed_numeric_poly_2_2,
      deformed_numeric_poly_2_3, Polynomial.eval_map, Complex.ofRealHom,
      Matrix.cons_val, Matrix.cons_val_two, Matrix.cons_val_three]

/-- The certified polynomial roots are precisely the full sixteen-dimensional spectrum. -/
theorem deformedSigma_entropy (k : Fin 3) :
    (deformedSigma k).vonNeumann = deformedNumericSigmaEntropy k := by
  apply entropy_of_charpoly_roots _ _ _ (deformedSigma_charpoly k)
    (deformedNumericPolynomial_roots k)
  have hdegree := Polynomial.natDegree_map_eq_of_injective
    (f := Complex.ofRealHom) Complex.ofReal_injective (deformedNumericPolynomial k)
  rw [← deformedSigma_charpoly k, Matrix.charpoly_natDegree_eq_dim] at hdegree
  rw [← hdegree]
  fin_cases k <;> norm_num [deformedNumericRoots, RE, Matrix.cons_val, Matrix.cons_val_two]

/-- Third column of the manuscript's entropy table, including all sixteen eigenvalues. -/
theorem deformedSigmaEntropy_table (k : Fin 3) :
    (![2672873388 / 1000000000, 2732163220 / 1000000000,
      2685089082 / 1000000000] k : ℝ) ≤ (deformedSigma k).vonNeumann ∧
    (deformedSigma k).vonNeumann ≤ ![2672873388 / 1000000000, 2732163220 / 1000000000,
      2685089082 / 1000000000] k + 1 / 1000000000 := by
  rw [deformedSigma_entropy]
  convert deformedNumericSigma_table k using 1 <;> norm_num

end
end QIT.QubitActivation
