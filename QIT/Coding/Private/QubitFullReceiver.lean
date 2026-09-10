/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitProduct
public import QIT.Coding.Private.BinaryHolevo

/-!
# The full receiver measurement and Holevo lower bound

The referenced event is embedded in the actual output of `N ⊗ E2`.
Its probabilities are exactly 0 and 1/12, including the erasure weight.
The legal binary measurement and scalar entropy bound prove the half-erasure specialization of `eq:receiver-gain`.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
namespace QIT
noncomputable section
universe u v

theorem product_erasure_transmitted
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {n : ℕ} (N : Channel a b) (X : CMatrix (Fin n × a))
    (r s : Fin n) (i j : b) :
    ((N.prod (Channel.halfErasure (n := n))).map
      (X.submatrix Prod.swap Prod.swap)) (i, Sum.inl r) (j, Sum.inl s) =
      (1 / 2 : ℂ) * (((Channel.idChannel (Fin n)).prod N).map X) (r, i) (s, j) := by
  change (MatrixMap.kron N.map Channel.halfErasure.map _ ) _ _ =
    (1 / 2 : ℂ) * (MatrixMap.kron (Channel.idChannel (Fin n)).map N.map X) _ _
  simp [MatrixMap.kron, halfErasure_apply, Matrix.submatrix_apply, Channel.idChannel,
    MatrixMap.ofKraus, Matrix.single_apply, smul_eq_mul, ite_and,
    Finset.mul_sum, mul_comm]

theorem product_erasure_erased
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {n : ℕ} (N : Channel a b) (X : CMatrix (Fin n × a))
    (f g : Fin 1) (i j : b) :
    ((N.prod (Channel.halfErasure (n := n))).map
      (X.submatrix Prod.swap Prod.swap)) (i, Sum.inr f) (j, Sum.inr g) =
      (1 / 2 : ℂ) * N.map (partialTraceA X) i j := by
  have hN := congrFun (congrFun (MatrixMap.map_eq_sum_single N.map (partialTraceA X)) i) j
  have hfg : f = g := Subsingleton.elim _ _
  subst g
  have he (r s : Fin n) :
      (Channel.halfErasure.map (Matrix.single r s (1 : ℂ)))
        (Sum.inr f) (Sum.inr f) = if r = s then (1 / 2 : ℂ) else 0 := by
    rw [halfErasure_apply]
    by_cases hrs : r = s <;> simp [hrs, Matrix.smul_apply]
  rw [hN]
  simp [Channel.prod, MatrixMap.kron, he,
    Matrix.submatrix_apply, Matrix.smul_apply, partialTraceA,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply,
    mul_assoc, mul_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp only [mul_left_comm]

namespace QubitActivation

/-- The paper's `RB ⊕ B` output order, including the erased branch. -/
def receiverRegisterEquiv : (RA ⊕ Fin 4) ≃ ProductReceiver where
  toFun := Sum.elim (fun x ↦ (x.2, Sum.inl x.1)) (fun i ↦ (i, Sum.inr 0))
  invFun y := Sum.elim (fun r ↦ Sum.inl (r, y.1)) (fun _ ↦ Sum.inr y.1) y.2
  left_inv x := by cases x <;> rfl
  right_inv y := by
    rcases y with ⟨i, r | f⟩
    · rfl
    · simp [Fin.eq_zero f]

/-- Both blocks and both zero cross blocks in `eq:outputs` at p=1/2, for every input state. -/
theorem full_receiver_outputs (rho : State RA) :
    (productChannel.applyState (rho.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).matrix.submatrix
        receiverRegisterEquiv receiverRegisterEquiv =
      (1 / 2 : ℂ) • Matrix.fromBlocks (referencedReceiver.applyState rho).matrix 0 0
        (Channel.privateN.applyState rho.marginalB).matrix := by
  ext x y
  rcases x with ⟨r, i⟩ | i <;> rcases y with ⟨s, j⟩ | j
  · change (productChannel.map (rho.matrix.submatrix Prod.swap Prod.swap))
        (i, Sum.inl r) (j, Sum.inl s) = _
    rw [show productChannel = Channel.privateN.prod Channel.erasure2 from rfl,
      product_erasure_transmitted]
    rfl
  · change (productChannel.map (rho.matrix.submatrix Prod.swap Prod.swap))
        (i, Sum.inl r) (j, Sum.inr 0) = _
    simp [productChannel, Channel.prod, MatrixMap.kron, halfErasure_apply]
  · change (productChannel.map (rho.matrix.submatrix Prod.swap Prod.swap))
        (i, Sum.inr 0) (j, Sum.inl s) = _
    simp [productChannel, Channel.prod, MatrixMap.kron, halfErasure_apply]
  · change (productChannel.map (rho.matrix.submatrix Prod.swap Prod.swap))
        (i, Sum.inr 0) (j, Sum.inr 0) = _
    rw [show productChannel = Channel.privateN.prod Channel.erasure2 from rfl,
      product_erasure_erased]
    rfl

def fullEventVector : ProductReceiver → ℂ := fun x =>
  Sum.elim (fun r => phi2 (r, x.1)) (fun _ => 0) x.2

def fullReceiverEffect : CMatrix ProductReceiver := rankOneMatrix fullEventVector

theorem fullEventVector_trace : (rankOneMatrix fullEventVector).trace = 1 := by
  have h := phi_trace 2
  change (rankOneMatrix phi2).trace = 1 at h
  simpa [rankOneMatrix, Matrix.trace, Matrix.vecMulVec_apply, fullEventVector,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Finset.sum_comm] using h

theorem fullReceiverEffect_pos : fullReceiverEffect.PosSemidef :=
  rankOneMatrix_pos fullEventVector

theorem fullReceiverEffect_le_one : fullReceiverEffect ≤ 1 := by
  apply Matrix.le_iff.mpr
  apply MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent fullReceiverEffect fullReceiverEffect_pos
  exact (PureVector.state_matrix_mul_self (ψ := ⟨fullEventVector, fullEventVector_trace⟩))

theorem full_receiver_event (rho : State RA) :
    ((productChannel.applyState (rho.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).matrix *
      fullReceiverEffect).trace =
      (1 / 2 : ℂ) * ((referencedReceiver.applyState rho).matrix * receiverEffect).trace := by
  change ((productChannel.map (rho.matrix.submatrix Prod.swap Prod.swap)) *
    rankOneMatrix fullEventVector).trace = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rankOneMatrix,
    Matrix.vecMulVec_apply, Fintype.sum_prod_type, Fintype.sum_sum_type, fullEventVector,
    receiverEffect]
  simp only [Sum.elim_inl, Sum.elim_inr, star_zero, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  simp only [productChannel, Channel.erasure2, product_erasure_transmitted]
  change _ = (1 / 2 : ℂ) *
    (∑ r, ∑ i, ∑ s, ∑ j,
      referencedReceiver.map rho.matrix (r, i) (s, j) * (phi2 (s, j) * star (phi2 (r, i))))
  simp only [Finset.mul_sum, mul_assoc, referencedReceiver]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem full_receiver_event_base :
    ((fullBobEnsemble.states false).matrix * fullReceiverEffect).trace = 0 := by
  change ((productChannel.applyState (rho0.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).matrix *
    fullReceiverEffect).trace = 0
  rw [full_receiver_event]
  change (1 / 2 : ℂ) * (beta0.matrix * receiverEffect).trace = 0
  rw [receiver_event_base, mul_zero]

theorem full_receiver_event_signal :
    ((fullBobEnsemble.states true).matrix * fullReceiverEffect).trace = (1 / 12 : ℂ) := by
  change ((productChannel.applyState (rho1.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).matrix *
    fullReceiverEffect).trace = (1 / 12 : ℂ)
  rw [full_receiver_event]
  change (1 / 2 : ℂ) * (beta1.matrix * receiverEffect).trace = (1 / 12 : ℂ)
  rw [receiver_event_signal]
  norm_num

end QubitActivation
end
end QIT

namespace QIT.QubitActivation

theorem full_receiver_holevo_lower :
    signalProbability / 12 * log2 (1 / signalProbability) ≤
      fullBobEnsemble.holevoInformation := by
  have hmeasure := Ensemble.binary_event_holevo_lower fullBobEnsemble signalProbability
    (1 / 12) rfl fullReceiverEffect fullReceiverEffect_pos fullReceiverEffect_le_one
      full_receiver_event_base (by simpa using full_receiver_event_signal)
  have hscalar := rare_event_information_lower (1 / 12) signalProbability
    (by norm_num) (by norm_num) signalProbability_pos signalProbability_lt_one.le
  convert hscalar.trans hmeasure using 1
  ring

end QIT.QubitActivation
