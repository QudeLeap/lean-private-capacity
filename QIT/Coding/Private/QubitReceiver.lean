/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitCertificates

/-! # The receiver kernel and conclusive event in the qubit encoding -/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

def referencedReceiver : Channel RA RA := (idChannel (Fin 2)).prod privateN
def receiverKraus (e : Fin 8) : CMatrix RA := Matrix.kronecker 1 (krausN e)

theorem referencedReceiver_map : referencedReceiver.map = MatrixMap.ofKraus receiverKraus := by
  change MatrixMap.kron (MatrixMap.ofKraus (fun _ : Unit => (1 : CMatrix (Fin 2))))
    (MatrixMap.ofKraus krausN) = _
  rw [kron_ofKraus]
  apply LinearMap.ext
  intro X
  change (∑ ib : Unit × Fin 8, receiverKraus ib.2 * X *
    (receiverKraus ib.2).conjTranspose) = _
  rw [Fintype.sum_prod_type, Fintype.sum_unique]
  rfl

/-- The event is the projector onto the third encoding vector. -/
def receiverEffect : CMatrix RA := rankOneMatrix phi2

/-- `(id_R ⊗ N†)(|w⟩⟨w|)`. -/
def eventPullback : CMatrix RA := MatrixMap.krausAdjoint receiverKraus receiverEffect

def pullbackAmplitude (e : Fin 8) (x : RA) : ℂ :=
  ∑ b : Fin 4, star (krausN e b x.2) * phi2 (x.1, b)

theorem eventPullback_decomposition :
    eventPullback = ∑ e : Fin 8, rankOneMatrix (pullbackAmplitude e) := by
  change (∑ e : Fin 8, (receiverKraus e).conjTranspose *
    rankOneMatrix phi2 * receiverKraus e) = _
  apply Finset.sum_congr rfl
  intro e _
  have h := rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose
    (receiverKraus e).conjTranspose phi2
  simp only [Matrix.conjTranspose_conjTranspose] at h
  rw [← h]
  congr 1
  funext x
  rcases x with ⟨r, a⟩
  fin_cases r <;> simp [pullbackAmplitude, receiverKraus, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Matrix.kronecker, Fintype.sum_prod_type, Matrix.one_apply]

/-- The exact matrix `42 H_w` in RA order, used to prove `eq:certificates`. -/
def paperKernel (x y : RA) : ℂ :=
  if x.1.val = y.1.val then
    if x.2.val = y.2.val then
      if x.1.val = 0 then
        if x.2.val = 0 then 2 else if x.2.val = 1 then 8 else if x.2.val = 2 then 6 else 5
      else
        if x.2.val = 0 then 5 else if x.2.val = 1 then 6 else if x.2.val = 2 then 8 else 2
    else 0
  else if x.1.val = 0 then
    if x.2.val = 0 ∧ y.2.val = 1 then -2 * r3
    else if x.2.val = 1 ∧ y.2.val = 2 then -1
    else if x.2.val = 2 ∧ y.2.val = 3 then -2 * r3 else 0
  else
    if x.2.val = 1 ∧ y.2.val = 0 then -2 * r3
    else if x.2.val = 2 ∧ y.2.val = 1 then -1
    else if x.2.val = 3 ∧ y.2.val = 2 then -2 * r3 else 0

private theorem pullbackAmplitude_canonical (e : Fin 8) (x : RA) :
    pullbackAmplitude e x = ∑ b : Fin 4, star (ks e b x.2) * phiCanonical 2 (x.1, b) := by
  rw [ks_eq, phiCanonical_eq]
  rfl

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 4000 in
/-- The entire eight-dimensional kernel matrix, not just the event expectation. -/
theorem receiver_kernel : (42 : ℂ) • eventPullback = paperKernel := by
  rw [eventPullback_decomposition]
  ext ⟨r, a⟩ ⟨s, b⟩
  simp only [Matrix.smul_apply, Matrix.sum_apply, rankOneMatrix_apply,
    pullbackAmplitude_canonical, smul_eq_mul]
  fin_cases r <;> fin_cases a <;> fin_cases s <;> fin_cases b <;>
    norm_num [ks, phiCanonical, paperKernel, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val, map_ofNat] <;> ring_nf
  all_goals norm_num <;> ring

end
end QIT.QubitActivation
