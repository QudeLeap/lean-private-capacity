/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module
public import QIT.Coding.Private.TransitionEncoding
public import QIT.Coding.Private.GeneralErasure
public import QIT.Coding.Private.ProductComplement
public import QIT.Core.POVMProbability

/-! # The actual product channel and both complete environment branches

The input order is `R × A`, as in the paper. Bob's erasure register
is signal followed by flag; Eve's is flag followed by signal.
-/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.Transition
noncomputable section
abbrev RB := (Fin 2 ⊕ Fin 1) × Fin 4
abbrev FullE := (Fin 1 ⊕ Fin 2) × Fin 8

def productChannel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Channel RA RB :=
  (Channel.erasure 2 p hp0 hp1).prod mainChannel

def productComplement (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Channel RA FullE :=
  (Channel.erasureComplement 2 p hp0 hp1).prod complement

theorem product_isComplementOf (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel.IsComplementOf (productComplement p hp0 hp1) (productChannel p hp0 hp1) :=
  (erasure_isComplementOf 2 p hp0 hp1).prod complement_isComplementOf

def referenceEmbed : Matrix FullE RE ℂ := fun y x ↦
  Sum.elim (fun _ ↦ 0) (fun r ↦ if (r, y.2) = x then 1 else 0) y.1

def erasedEmbed : Matrix FullE (Fin 8) ℂ := fun y x ↦
  Sum.elim (fun _ ↦ if y.2 = x then 1 else 0) (fun _ ↦ 0) y.1

def receiverEmbed : Matrix RB RA ℂ := fun y x ↦
  Sum.elim (fun r ↦ if (r, y.2) = x then 1 else 0) (fun _ ↦ 0) y.1

theorem referenceEmbed_isometry : referenceEmbed.conjTranspose * referenceEmbed = 1 := by
  ext ⟨r, i⟩ ⟨s, j⟩
  simp [referenceEmbed, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Prod.mk.injEq, ite_and]
  by_cases hrs : r = s <;> by_cases hij : i = j <;> simp_all [Matrix.one_apply, eq_comm]

theorem erasedEmbed_isometry : erasedEmbed.conjTranspose * erasedEmbed = 1 := by
  ext i j
  simp [erasedEmbed, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type]
  by_cases hij : i = j <;> simp_all [Matrix.one_apply, eq_comm]

theorem receiverEmbed_isometry : receiverEmbed.conjTranspose * receiverEmbed = 1 := by
  ext ⟨r, i⟩ ⟨s, j⟩
  simp [receiverEmbed, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Prod.mk.injEq, ite_and]
  by_cases hrs : r = s <;> by_cases hij : i = j <;> simp_all [Matrix.one_apply, eq_comm]

def embeddedReference (rho : State RE) : State FullE :=
  POVM.isometryLiftState rho referenceEmbed referenceEmbed_isometry

def embeddedErased (rho : State (Fin 8)) : State FullE :=
  POVM.isometryLiftState rho erasedEmbed erasedEmbed_isometry

theorem embeddedReference_entry (rho : State RE) (i j : Fin 8) (f g : Fin 1 ⊕ Fin 2) :
    (embeddedReference rho).matrix (f, i) (g, j) =
      Sum.elim (fun _ ↦ 0) (fun r ↦ Sum.elim (fun _ ↦ 0) (fun s ↦ rho.matrix (r, i) (s, j)) g) f := by
  cases f <;> cases g <;>
    simp [embeddedReference, POVM.isometryLiftState, referenceEmbed, Matrix.mul_apply,
      Matrix.conjTranspose_apply]

theorem embeddedErased_entry (rho : State (Fin 8)) (i j : Fin 8) (f g : Fin 1 ⊕ Fin 2) :
    (embeddedErased rho).matrix (f, i) (g, j) =
      Sum.elim (fun _ ↦ Sum.elim (fun _ ↦ rho.matrix i j) (fun _ ↦ 0) g) (fun _ ↦ 0) f := by
  cases f <;> cases g <;>
    simp [embeddedErased, POVM.isometryLiftState, erasedEmbed,
      Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem erasure_transmitted (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : CMatrix RA) (r s : Fin 2) (i j : Fin 4) :
    (productChannel p hp0 hp1).map X (Sum.inl r, i) (Sum.inl s, j) =
      ((1 - p : ℝ) : ℂ) * referencedReceiver.map X (r, i) (s, j) := by
  simp [productChannel, referencedReceiver, Channel.prod, MatrixMap.kron, erasure_apply,
    Channel.idChannel, MatrixMap.ofKraus, Matrix.single_apply, smul_eq_mul,
    ite_and, Finset.mul_sum, mul_assoc]
  fin_cases r <;> fin_cases s <;> simp [mul_left_comm]

theorem complement_transmitted (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : CMatrix RA) (r s : Fin 2) (i j : Fin 8) :
    (productComplement p hp0 hp1).map X (Sum.inr r, i) (Sum.inr s, j) =
      (p : ℂ) * referencedEnvironment.map X (r, i) (s, j) := by
  simp [productComplement, referencedEnvironment, Channel.prod, MatrixMap.kron, erasureComplement_apply,
    Channel.idChannel, MatrixMap.ofKraus, Matrix.single_apply, smul_eq_mul,
    ite_and, Finset.mul_sum, mul_assoc]
  fin_cases r <;> fin_cases s <;> simp [mul_left_comm]

theorem complement_erased (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : CMatrix RA) (f g : Fin 1) (i j : Fin 8) :
    (productComplement p hp0 hp1).map X (Sum.inl f, i) (Sum.inl g, j) =
      ((1 - p : ℝ) : ℂ) * complement.map (partialTraceA X) i j := by
  have hN := congrFun (congrFun (MatrixMap.map_eq_sum_single complement.map (partialTraceA X)) i) j
  have hfg : f = g := Subsingleton.elim _ _
  subst g
  have he (r s : Fin 2) :
      ((Channel.erasureComplement 2 p hp0 hp1).map (Matrix.single r s (1 : ℂ)))
        (Sum.inl f) (Sum.inl f) = if r = s then ((1 - p : ℝ) : ℂ) else 0 := by
    rw [erasureComplement_apply]
    by_cases hrs : r = s <;> simp [hrs]
  rw [hN]
  simp [productComplement, Channel.prod, MatrixMap.kron, he, Matrix.smul_apply,
    partialTraceA, smul_eq_mul, Finset.mul_sum, Matrix.sum_apply,
    mul_assoc, mul_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The complete physical output, with neither a branch nor a coherence discarded. -/
theorem full_environment (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho : State RA) :
    ((productComplement p hp0 hp1).applyState rho).matrix =
      (p : ℂ) • (embeddedReference (referencedEnvironment.applyState rho)).matrix +
      ((1 - p : ℝ) : ℂ) • (embeddedErased (complement.applyState rho.marginalB)).matrix := by
  ext ⟨f, i⟩ ⟨g, j⟩
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    embeddedReference_entry, embeddedErased_entry]
  change ((productComplement p hp0 hp1).map rho.matrix) (f, i) (g, j) = _
  cases f <;> cases g
  · rw [complement_erased]
    simp [Channel.applyState, State.marginalB]
  · simp [productComplement, Channel.prod, MatrixMap.kron, erasureComplement_apply]
  · simp [productComplement, Channel.prod, MatrixMap.kron, erasureComplement_apply]
  · rw [complement_transmitted]
    simp [Channel.applyState]

def branchConstant (b : Bool) : ℝ := if b then 205 / 9 else 4
def baseBranch (b : Bool) : State FullE := if b then embeddedReference (sigma false) else embeddedErased (epsilon false)
def signalBranch (b : Bool) : State FullE := if b then embeddedReference (sigma true) else embeddedErased (epsilon true)

theorem branchConstant_ge_three (b : Bool) : 3 ≤ branchConstant b := by
  cases b <;> norm_num [branchConstant]

private theorem lifted_order {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (base signal : State a) (q : ℂ) (hq : q • signal.matrix ≤ base.matrix)
    (V : Matrix b a ℂ) (hV : V.conjTranspose * V = 1) :
    q • (POVM.isometryLiftState signal V hV).matrix ≤ (POVM.isometryLiftState base V hV).matrix := by
  apply Matrix.le_iff.mpr
  have h := (Matrix.le_iff.mp hq).mul_mul_conjTranspose_same V
  simpa only [POVM.isometryLiftState_matrix, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul] using h

theorem environment_branches_order (b : Bool) :
    ((1 / branchConstant b : ℝ) : ℂ) • (signalBranch b).matrix ≤ (baseBranch b).matrix := by
  cases b
  · exact lifted_order _ _ _ erased_environment_order erasedEmbed erasedEmbed_isometry
  · exact lifted_order _ _ _ environment_order referenceEmbed referenceEmbed_isometry

def receiverEffect : CMatrix RB :=
  receiverEmbed * (inputState true).matrix * receiverEmbed.conjTranspose

theorem receiverEffect_pos : receiverEffect.PosSemidef :=
  (inputState true).pos.mul_mul_conjTranspose_same receiverEmbed

theorem receiverEffect_le_one : receiverEffect ≤ 1 := by
  apply Matrix.le_iff.mpr
  apply MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent _ receiverEffect_pos
  have hs : (inputState true).matrix * (inputState true).matrix = (inputState true).matrix := by
    ext x y
    simp only [Matrix.mul_apply, inputState_matrix]
    exact_mod_cast TransitionEncodingData.signal_projector x y
  change (receiverEmbed * (inputState true).matrix * receiverEmbed.conjTranspose) *
    (receiverEmbed * (inputState true).matrix * receiverEmbed.conjTranspose) = _
  calc _ = receiverEmbed * (inputState true).matrix *
      (receiverEmbed.conjTranspose * receiverEmbed) * (inputState true).matrix * receiverEmbed.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [receiverEmbed_isometry, Matrix.mul_one,
        Matrix.mul_assoc receiverEmbed (inputState true).matrix (inputState true).matrix, hs]
      rfl

theorem receiverEffect_entry (f g : Fin 2 ⊕ Fin 1) (i j : Fin 4) :
    receiverEffect (f, i) (g, j) =
      Sum.elim (fun r ↦ Sum.elim (fun s ↦ (inputState true).matrix (r, i) (s, j)) (fun _ ↦ 0) g)
        (fun _ ↦ 0) f := by
  cases f <;> cases g <;>
    simp [receiverEffect, receiverEmbed, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem full_receiver_event (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho : State RA) :
    (((productChannel p hp0 hp1).applyState rho).matrix * receiverEffect).trace =
      ((1 - p : ℝ) : ℂ) * ((referencedReceiver.applyState rho).matrix * (inputState true).matrix).trace := by
  change ((productChannel p hp0 hp1).map rho.matrix * receiverEffect).trace = _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type, receiverEffect_entry,
    Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [erasure_transmitted, Finset.mul_sum, mul_assoc, Channel.applyState]

end
end QIT.Transition
