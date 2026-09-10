/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitReceiver
public import QIT.Coding.Private.QubitEnvironment
public import QIT.Util.SDP.HermitianPSDTraceDuality

/-! # Receiver probabilities and the failure of a positive environmental effect -/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

private theorem paperKernel_phi (j : Fin 3) :
    Matrix.mulVec paperKernel (phiCanonical j) =
      (if j.val = 2 then (7 : ℂ) else 0) • phiCanonical j := by
  funext x
  rcases x with ⟨r, a⟩
  fin_cases j <;> fin_cases r <;> fin_cases a <;>
    norm_num [paperKernel, phiCanonical, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring_nf
  all_goals norm_num

/-- `H_w φ₀ = H_w φ₁ = 0` and `H_w φ₂ = φ₂/6`. -/
theorem receiver_kernel_eigenvector (j : Fin 3) :
    eventPullback.mulVec (phi j) =
      (if j.val = 2 then (1 / 6 : ℂ) else 0) • phi j := by
  have h := congrArg (fun M : CMatrix RA => M.mulVec (phi j)) receiver_kernel
  dsimp only at h
  rw [Matrix.smul_mulVec, ← phiCanonical_eq, paperKernel_phi] at h
  rw [phiCanonical_eq] at h
  funext x
  have hx := congrFun h x
  simp only [Pi.smul_apply, smul_eq_mul] at hx ⊢
  fin_cases j <;> norm_num at hx ⊢
  all_goals first | exact hx | linear_combination (1 / 42 : ℂ) * hx

theorem receiverEffect_pos : receiverEffect.PosSemidef := rankOneMatrix_pos phi2

theorem receiverEffect_le_one : receiverEffect ≤ 1 := by
  apply Matrix.le_iff.mpr
  apply MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent receiverEffect receiverEffect_pos
  exact (PureVector.state_matrix_mul_self (ψ := ⟨phi2, phi_trace 2⟩))

/-- The exact event expectation for each pure encoding vector. -/
theorem receiver_pure_event (j : Fin 3) :
    (referencedReceiver.map (rankOneMatrix (phi j)) * receiverEffect).trace =
      if j.val = 2 then (1 / 6 : ℂ) else 0 := by
  rw [referencedReceiver_map, MatrixMap.ofKraus_trace_duality, Matrix.trace_mul_comm]
  change (eventPullback * rankOneMatrix (phi j)).trace = _
  have h : eventPullback * rankOneMatrix (phi j) =
      (if j.val = 2 then (1 / 6 : ℂ) else 0) • rankOneMatrix (phi j) := by
    rw [rankOneMatrix, Matrix.mul_vecMulVec, receiver_kernel_eigenvector]
    ext i k
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, mul_assoc]
  rw [h, Matrix.trace_smul, phi_trace, smul_eq_mul, mul_one]

def beta0 : State RA := referencedReceiver.applyState rho0
def beta1 : State RA := referencedReceiver.applyState rho1

theorem receiver_event_base : (beta0.matrix * receiverEffect).trace = 0 := by
  change (referencedReceiver.map ((1 / 2 : ℂ) •
    (rankOneMatrix (phi 0) + rankOneMatrix (phi 1))) * receiverEffect).trace = 0
  rw [map_smul, map_add, Matrix.smul_mul, Matrix.add_mul, Matrix.trace_smul,
    Matrix.trace_add, receiver_pure_event, receiver_pure_event]
  norm_num

theorem receiver_event_signal : (beta1.matrix * receiverEffect).trace = (1 / 6 : ℂ) :=
  receiver_pure_event 2

/-- No positive environmental operator can reproduce this referenced receiver event. -/
theorem no_positive_environmental_effect :
    ¬ ∃ G : CMatrix RE, G.PosSemidef ∧ (G * sigma0.matrix).trace = 0 ∧
      (G * sigma1.matrix).trace = (1 / 6 : ℂ) := by
  rintro ⟨G, hG, h0, h1⟩
  have h := cMatrix_trace_mul_le_of_le_posSemidef_left hG environment_order
  rw [h1, Matrix.mul_smul, Matrix.trace_smul, h0] at h
  norm_num at h

/-- The unit vector (|02⟩ − |11⟩)/√2 witnesses the non-PPT receiver effect. -/
def negativePTVector (x : RA) : ℂ :=
  if x.1.val = 0 ∧ x.2.val = 2 then erasureInvSqrtTwo
  else if x.1.val = 1 ∧ x.2.val = 1 then -erasureInvSqrtTwo else 0

theorem negativePTVector_trace : (rankOneMatrix negativePTVector).trace = 1 := by
  norm_num [rankOneMatrix_trace, dotProduct, negativePTVector, Fintype.sum_prod_type,
    Fin.sum_univ_succ, erasureInvSqrtTwo, inv_pow, ← pow_two,
    ← Complex.ofReal_pow, Real.sq_sqrt]

theorem negativePTVector_expectation : (star negativePTVector) ⬝ᵥ
    (partialTransposeB receiverEffect).mulVec negativePTVector = (-1 / 2 : ℂ) := by
  norm_num [negativePTVector, partialTransposeB, receiverEffect, rankOneMatrix_apply,
    phi2, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
    erasureInvSqrtTwo, inv_pow, ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt]
  ring_nf
  norm_num [← Complex.ofReal_pow, Real.sq_sqrt]

/-- The conclusive effect has a negative partial-transpose expectation, exactly −1/2.
This is a finite witness, not the finite-blocklength PPT-decoder converse. -/
theorem receiverEffect_not_ppt : ¬ (partialTransposeB receiverEffect).PosSemidef := by
  intro h
  have hp := h.dotProduct_mulVec_nonneg negativePTVector
  rw [negativePTVector_expectation] at hp
  norm_num [Complex.le_def, Complex.div_re, Complex.div_im] at hp

end
end QIT.QubitActivation
