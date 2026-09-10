/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.HalfErasure

/-!
# The three-vector qubit encoding

The register order is exactly the paper's `RA = Fin 2 × Fin 4`.
The definitions correspond to `eq:vectors` and `eq:encoding` in the
2026-09-08 manuscript; the marginal comparisons are also used in Appendix B. In particular the two A-marginals
are different; the erased environmental branch cannot be discarded.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
noncomputable section

abbrev RA := Fin 2 × Fin 4

/-- `(√3 |00⟩ + |11⟩)/2`. -/
def phi0 (x : RA) : ℂ :=
  if x.1.val = 0 ∧ x.2.val = 0 then (Real.sqrt 3 : ℂ) / 2 else if x.1.val = 1 ∧ x.2.val = 1 then 1 /
    2 else 0

/-- `(|02⟩ + √3 |13⟩)/2`. -/
def phi1 (x : RA) : ℂ :=
  if x.1.val = 0 ∧ x.2.val = 2 then 1 / 2 else if x.1.val = 1 ∧ x.2.val = 3 then (Real.sqrt 3 : ℂ) /
    2 else 0

/-- `(|01⟩ + |12⟩)/√2`. -/
def phi2 (x : RA) : ℂ :=
  if (x.1.val = 0 ∧ x.2.val = 1) ∨ (x.1.val = 1 ∧ x.2.val = 2) then erasureInvSqrtTwo else 0

def phi (j : Fin 3) : RA → ℂ := ![phi0, phi1, phi2] j

/-- All three vectors are normalized and pairwise orthogonal. -/
theorem phi_inner (i j : Fin 3) :
    (∑ x : RA, phi i x * star (phi j x)) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [phi, phi0, phi1, phi2, Fintype.sum_prod_type,
      Fin.sum_univ_succ,  map_ofNat, erasureInvSqrtTwo, inv_pow, ← pow_two, div_pow,
      ← Complex.ofReal_pow, Real.sq_sqrt]

theorem phi_trace (j : Fin 3) : (rankOneMatrix (phi j)).trace = 1 := by
  simpa [rankOneMatrix_trace, dotProduct] using phi_inner j j

def rho0Mat : CMatrix RA := (1 / 2 : ℂ) • (rankOneMatrix phi0 + rankOneMatrix phi1)
def rho1Mat : CMatrix RA := rankOneMatrix phi2

def rho0 : State RA where
  matrix := rho0Mat
  pos := ((rankOneMatrix_pos phi0).add (rankOneMatrix_pos phi1)).smul (by norm_num
    [Complex.nonneg_iff, Complex.div_re, Complex.div_im])
  trace_eq_one := by
    have h0 : (rankOneMatrix phi0).trace = 1 := phi_trace 0
    have h1 : (rankOneMatrix phi1).trace = 1 := phi_trace 1
    rw [rho0Mat, Matrix.trace_smul, Matrix.trace_add, h0, h1]
    norm_num

def rho1 : State RA where
  matrix := rho1Mat
  pos := rankOneMatrix_pos phi2
  trace_eq_one := phi_trace 2

/-- The abundant letter's A-marginal is `diag(3,1,1,3)/8`. -/
theorem rho0_marginal :
    partialTraceA rho0.matrix = Matrix.diagonal ![3 / 8, 1 / 8, 1 / 8, 3 / 8] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho0, rho0Mat, partialTraceA, rankOneMatrix_apply, phi0, phi1,
      Fin.sum_univ_succ,  map_ofNat, Matrix.diagonal_apply, ← pow_two, div_pow,
      ← Complex.ofReal_pow, Real.sq_sqrt]

/-- The signal's A-marginal is `diag(0,1,1,0)/2`. -/
theorem rho1_marginal :
    partialTraceA rho1.matrix = Matrix.diagonal ![0, 1 / 2, 1 / 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho1, rho1Mat, partialTraceA, rankOneMatrix_apply, phi2,
      Fin.sum_univ_succ,  map_ofNat, Matrix.diagonal_apply, erasureInvSqrtTwo, inv_pow, ← pow_two,
        div_pow,
      ← Complex.ofReal_pow, Real.sq_sqrt]

/-- The base letter carries no information in the helper alone: its R-marginal is I₂/2. -/
theorem rho0_helper_marginal :
    partialTraceB rho0.matrix = (1 / 2 : ℂ) • (1 : CMatrix (Fin 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho0, rho0Mat, partialTraceB, rankOneMatrix_apply, phi0, phi1,
      Fin.sum_univ_succ, map_ofNat, Matrix.one_apply, ← pow_two, div_pow,
      ← Complex.ofReal_pow, Real.sq_sqrt]

/-- The signal has the same R-marginal, despite its different A-marginal. -/
theorem rho1_helper_marginal :
    partialTraceB rho1.matrix = (1 / 2 : ℂ) • (1 : CMatrix (Fin 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rho1, rho1Mat, partialTraceB, rankOneMatrix_apply, phi2,
      Fin.sum_univ_succ, map_ofNat, Matrix.one_apply, erasureInvSqrtTwo,
      inv_pow, ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt]

/-- Exact positive remainder in the marginal comparison. -/
theorem marginal_remainder :
    (4 : ℂ) • partialTraceA rho0.matrix - partialTraceA rho1.matrix =
      Matrix.diagonal ![3 / 2, 0, 0, 3 / 2] := by
  rw [rho0_marginal, rho1_marginal]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal_apply]

theorem marginal_order : partialTraceA rho1.matrix ≤ (4 : ℂ) • partialTraceA rho0.matrix := by
  apply Matrix.le_iff.mpr
  rw [marginal_remainder]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]

/-- The binary codeword ensemble, with signal probability `q`. -/
def ensemble (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Ensemble Bool RA where
  probs x := if x then ⟨q, hq0⟩ else ⟨1 - q, sub_nonneg.mpr hq1⟩
  weights_sum := by
    rw [Fintype.sum_bool]
    apply NNReal.eq
    change q + (1 - q) = 1
    ring
  states x := if x then rho1 else rho0

end
end QIT.QubitActivation
