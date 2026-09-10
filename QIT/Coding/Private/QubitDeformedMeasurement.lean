/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedEncoding
public import QIT.Coding.Private.QubitFullReceiver
public import QIT.Coding.Private.QubitFullEnvironment

/-!
# The fixed receiver measurement for the deformed example

There are eight outcomes when the helper arrives and four when it is erased.
The flag is retained. This measurement remains valid when the two receiver
states do not commute; no simultaneous diagonalization is assumed.
-/

@[expose] public section
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section
universe u

/-- Ordered RB basis for the deformed encoding, in its stated eight-outcome order. -/
def deformedReceiverVector (j : Fin 8) (x : RA) : ℂ :=
  if j.val = 0 then phiCanonical 0 x
  else if j.val = 1 then phiCanonical 1 x
  else if j.val = 2 then
    if x.1.val = 0 ∧ x.2.val = 0 then 1 / 2
    else if x.1.val = 1 ∧ x.2.val = 1 then -r3 / 2 else 0
  else if j.val = 3 then
    if x.1.val = 0 ∧ x.2.val = 2 then r3 / 2
    else if x.1.val = 1 ∧ x.2.val = 3 then -1 / 2 else 0
  else if j.val = 4 then
    if x.1.val = 0 ∧ x.2.val = 1 then r2 / 2
    else if x.1.val = 1 ∧ x.2.val = 2 then -r2 / 2 else 0
  else if j.val = 5 then phiCanonical 2 x
  else if j.val = 6 then
    if x.1.val = 0 ∧ x.2.val = 3 then 1 else 0
  else if x.1.val = 1 ∧ x.2.val = 0 then 1 else 0

set_option maxHeartbeats 2000000 in
theorem deformedReceiverVector_inner (i j : Fin 8) :
    (∑ x : RA, deformedReceiverVector i x * star (deformedReceiverVector j x)) =
      if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [deformedReceiverVector, phiCanonical, Fintype.sum_prod_type,
      Fin.sum_univ_succ, map_ofNat] <;> ring_nf
  all_goals norm_num

set_option maxHeartbeats 2000000 in
theorem deformedReceiverVector_complete :
    (∑ j : Fin 8, rankOneMatrix (deformedReceiverVector j)) = (1 : CMatrix RA) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Matrix.sum_apply, rankOneMatrix_apply, deformedReceiverVector, phiCanonical,
      Fin.sum_univ_succ, Matrix.one_apply, map_ofNat] <;> ring_nf
  all_goals norm_num

abbrev DeformedOutcome := Fin 8 ⊕ Fin 4

def deformedFullVector (j : DeformedOutcome) (y : ProductReceiver) : ℂ :=
  match j, y.2 with
  | Sum.inl k, Sum.inl r => deformedReceiverVector k (r, y.1)
  | Sum.inr k, Sum.inr _ => if k = y.1 then 1 else 0
  | _, _ => 0

theorem deformedFullVector_complete :
    (∑ j : DeformedOutcome, rankOneMatrix (deformedFullVector j)) =
      (1 : CMatrix ProductReceiver) := by
  ext ⟨i, r⟩ ⟨j, s⟩
  cases r with
  | inl r =>
    cases s with
    | inl s =>
      have h := congrFun (congrFun deformedReceiverVector_complete (r, i)) (s, j)
      simpa [Matrix.sum_apply, rankOneMatrix_apply, deformedFullVector,
        Fintype.sum_sum_type, Matrix.one_apply, and_comm] using h
    | inr f =>
      simp [Matrix.sum_apply, rankOneMatrix_apply, deformedFullVector, Fintype.sum_sum_type]
  | inr f =>
    cases s with
    | inl s =>
      simp [Matrix.sum_apply, rankOneMatrix_apply, deformedFullVector, Fintype.sum_sum_type]
    | inr g =>
      have hfg : f = g := Subsingleton.elim _ _
      subst g
      simp [Matrix.sum_apply, rankOneMatrix_apply, deformedFullVector, Fintype.sum_sum_type,
        Matrix.one_apply, eq_comm]

/-- The exact twelve-outcome single-use measurement in the paper. -/
def deformedMeasurement : POVM DeformedOutcome ProductReceiver where
  effects j := rankOneMatrix (deformedFullVector j)
  pos _ := rankOneMatrix_pos _
  sum_eq_one := deformedFullVector_complete

def deformedMeasuredEnsemble : Ensemble Bool DeformedOutcome :=
  (Channel.measure deformedMeasurement).outputEnsemble deformedBobEnsemble

/-- Actual measured information difference, including both full Eve branches. -/
def deformedMeasuredRate : ℝ :=
  deformedMeasuredEnsemble.holevoInformation - deformedEveEnsemble.holevoInformation

/-- Data processing and the one-use ensemble bound; no numerical inequality is assumed. -/
theorem deformedMeasuredRate_le_privateCapacity :
    deformedMeasuredRate ≤
      Channel.privateCapacity.{0, 0, 0, u} productChannel productComplement := by
  have hdpi := Ensemble.holevoInformation_outputEnsemble_le
    (Channel.measure deformedMeasurement) deformedBobEnsemble
  have hgap : deformedMeasuredRate ≤
      productChannel.privateInformationWith productComplement deformedEnsemble :=
    sub_le_sub_right hdpi _
  have hcap := Channel.privateInformationWith_le_privateCapacity productChannel productComplement
    (deformedEnsemble.relabelIndex (Equiv.ulift : ULift.{u, 0} Bool ≃ Bool))
  apply hgap.trans
  simpa only [Channel.privateInformationWith, Channel.outputEnsemble_relabelIndex,
    Ensemble.relabelIndex_holevoInformation] using hcap

/-- Explicitly retain all 16 + 8 environmental coordinates for each new letter. -/
theorem deformed_full_environment (x : Bool) :
    (deformedEveEnsemble.states x).matrix.submatrix
        environmentRegisterEquiv environmentRegisterEquiv =
      (1 / 2 : ℂ) • Matrix.fromBlocks
        (referencedEnvironment.applyState (deformedLetter x)).matrix 0 0
        (Channel.complementN.applyState (deformedLetter x).marginalB).matrix :=
  full_environment_outputs_directSum _

end
end QIT.QubitActivation
