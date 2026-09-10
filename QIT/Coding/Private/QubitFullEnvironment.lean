/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitProduct
public import QIT.Coding.Private.BinaryHolevo
public import QIT.Core.POVMProbability

/-!
# The complete environmental output and Holevo upper bound

The physical 24-dimensional complement is the equal mixture of the two
orthogonally embedded environmental branches (`eq:outputs` at p=1/2).
Their factors 28 and 4 define the classical preparation proof of the
half-erasure environment bound in Appendix B.3.
No environmental coherence is removed and no entropy bound is assumed.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder NNReal
namespace QIT
noncomputable section
universe u v

theorem product_erasureComplement_transmitted
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {n : ℕ} (N : Channel a b) (X : CMatrix (Fin n × a))
    (r s : Fin n) (i j : b) :
    ((N.prod (Channel.halfErasureComplement (n := n))).map
      (X.submatrix Prod.swap Prod.swap)) (i, Sum.inr r) (j, Sum.inr s) =
      (1 / 2 : ℂ) * (((Channel.idChannel (Fin n)).prod N).map X) (r, i) (s, j) := by
  change (MatrixMap.kron N.map Channel.halfErasureComplement.map _ ) _ _ =
    (1 / 2 : ℂ) * (MatrixMap.kron (Channel.idChannel (Fin n)).map N.map X) _ _
  simp [MatrixMap.kron, Channel.halfErasureComplement, erasureComplementMap,
    Matrix.submatrix_apply, Channel.idChannel, MatrixMap.ofKraus, Matrix.single_apply,
    smul_eq_mul, ite_and, Finset.mul_sum, mul_comm]

theorem product_erasureComplement_erased
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {n : ℕ} (N : Channel a b) (X : CMatrix (Fin n × a))
    (f g : Fin 1) (i j : b) :
    ((N.prod (Channel.halfErasureComplement (n := n))).map
      (X.submatrix Prod.swap Prod.swap)) (i, Sum.inl f) (j, Sum.inl g) =
      (1 / 2 : ℂ) * N.map (partialTraceA X) i j := by
  have hN := congrFun (congrFun (MatrixMap.map_eq_sum_single N.map (partialTraceA X)) i) j
  have hfg : f = g := Subsingleton.elim _ _
  subst g
  have he (r s : Fin n) :
      (Channel.halfErasureComplement.map (Matrix.single r s (1 : ℂ)))
        (Sum.inl f) (Sum.inl f) = if r = s then (1 / 2 : ℂ) else 0 := by
    change (1 / 2 * (Matrix.single r s (1 : ℂ)).trace) *
      (if f = f then (1 : ℂ) else 0) = _
    simp [trace_single_one]
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

def envReferenceEmbed : Matrix ProductEnvironment RE ℂ := fun y x =>
  Sum.elim (fun _ => 0) (fun r => if (r, y.1) = x then 1 else 0) y.2

def envErasedEmbed : Matrix ProductEnvironment (Fin 8) ℂ := fun y x =>
  Sum.elim (fun _ => if y.1 = x then 1 else 0) (fun _ => 0) y.2

theorem envReferenceEmbed_isometry : envReferenceEmbed.conjTranspose * envReferenceEmbed = 1 := by
  ext ⟨r, i⟩ ⟨s, j⟩
  simp [envReferenceEmbed, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Prod.mk.injEq, ite_and]
  by_cases hrs : r = s <;> by_cases hij : i = j <;>
    simp_all [Matrix.one_apply, eq_comm]

theorem envErasedEmbed_isometry : envErasedEmbed.conjTranspose * envErasedEmbed = 1 := by
  ext i j
  simp [envErasedEmbed, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type]
  by_cases hij : i = j <;> simp_all [Matrix.one_apply, eq_comm]

def embeddedReference (rho : State RE) : State ProductEnvironment :=
  POVM.isometryLiftState rho envReferenceEmbed envReferenceEmbed_isometry

def embeddedErased (rho : State (Fin 8)) : State ProductEnvironment :=
  POVM.isometryLiftState rho envErasedEmbed envErasedEmbed_isometry

theorem embeddedReference_entry (rho : State RE) (i j : Fin 8)
    (f g : Fin 1 ⊕ Fin 2) :
    (embeddedReference rho).matrix (i, f) (j, g) =
      Sum.elim (fun _ => 0) (fun r => Sum.elim (fun _ => 0)
        (fun s => rho.matrix (r, i) (s, j)) g) f := by
  cases f <;> cases g <;>
    simp [embeddedReference, POVM.isometryLiftState, envReferenceEmbed,
      Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem embeddedErased_entry (rho : State (Fin 8)) (i j : Fin 8)
    (f g : Fin 1 ⊕ Fin 2) :
    (embeddedErased rho).matrix (i, f) (j, g) =
      Sum.elim (fun _ => Sum.elim (fun _ => rho.matrix i j) (fun _ => 0) g)
        (fun _ => 0) f := by
  cases f <;> cases g <;>
    simp [embeddedErased, POVM.isometryLiftState, envErasedEmbed,
      Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem full_environment_outputs (rho : State RA) :
    (productComplement.applyState (rho.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).matrix =
      (1 / 2 : ℂ) • ((embeddedReference (referencedEnvironment.applyState rho)).matrix +
        (embeddedErased (Channel.complementN.applyState rho.marginalB)).matrix) := by
  ext ⟨i, f⟩ ⟨j, g⟩
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
    embeddedReference_entry, embeddedErased_entry]
  change (productComplement.map (rho.matrix.submatrix Prod.swap Prod.swap)) (i, f) (j, g) = _
  cases f <;> cases g
  · rw [show productComplement = Channel.complementN.prod Channel.erasure2Complement from rfl,
      product_erasureComplement_erased]
    simp [Channel.applyState, State.marginalB]
  · simp [productComplement, Channel.prod, MatrixMap.kron, Channel.halfErasureComplement,
      erasureComplementMap]
  · simp [productComplement, Channel.prod, MatrixMap.kron, Channel.halfErasureComplement,
      erasureComplementMap]
  · rw [show productComplement = Channel.complementN.prod Channel.erasure2Complement from rfl,
      product_erasureComplement_transmitted]
    simp [referencedEnvironment, Channel.applyState]

/-- The paper's `RE ⊕ E` order; reference transmission is the complement's `inr` branch. -/
def environmentRegisterEquiv : (RE ⊕ Fin 8) ≃ ProductEnvironment where
  toFun := Sum.elim (fun x ↦ (x.2, Sum.inr x.1)) (fun i ↦ (i, Sum.inl 0))
  invFun y := Sum.elim (fun _ ↦ Sum.inr y.1) (fun r ↦ Sum.inl (r, y.1)) y.2
  left_inv x := by cases x <;> rfl
  right_inv y := by
    rcases y with ⟨i, f | r⟩
    · simp [Fin.eq_zero f]
    · rfl

/-- The complete environmental direct sum in `eq:outputs` at p=1/2. -/
theorem full_environment_outputs_directSum (rho : State RA) :
    (productComplement.applyState (rho.reindex (Equiv.prodComm (Fin 2) (Fin 4)))).matrix.submatrix
        environmentRegisterEquiv environmentRegisterEquiv =
      (1 / 2 : ℂ) • Matrix.fromBlocks (referencedEnvironment.applyState rho).matrix 0 0
        (Channel.complementN.applyState rho.marginalB).matrix := by
  rw [full_environment_outputs]
  ext x y
  rcases x with ⟨r, i⟩ | i <;> rcases y with ⟨s, j⟩ | j <;>
    simp [Matrix.submatrix_apply, environmentRegisterEquiv,
      embeddedReference_entry, embeddedErased_entry]

def environmentBranches (b x : Bool) : State ProductEnvironment :=
  if b then embeddedReference (if x then sigma1 else sigma0)
  else embeddedErased (if x then epsilon1 else epsilon0)

def branchProbability (b : Bool) : ℝ := if b then 1 / 28 else 1 / 4

theorem environmentBranches_letters (x : Bool) :
    (fullEveEnsemble.states x).matrix =
      (1 / 2 : ℂ) • ((environmentBranches true x).matrix + (environmentBranches false x).matrix) := by
  cases x <;> exact full_environment_outputs _

private theorem isometryLift_order
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (rho sigma : State a) (V : Matrix b a ℂ) (hV : V.conjTranspose * V = 1)
    (p : ℝ) (horder : (p : ℂ) • rho.matrix ≤ sigma.matrix) :
    (p : ℂ) • (POVM.isometryLiftState rho V hV).matrix ≤
      (POVM.isometryLiftState sigma V hV).matrix := by
  apply Matrix.le_iff.mpr
  have h := (Matrix.le_iff.mp horder).mul_mul_conjTranspose_same V
  simpa [POVM.isometryLiftState, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul] using h

theorem environmentBranches_order (b : Bool) :
    (branchProbability b : ℂ) • (environmentBranches b true).matrix ≤
      (environmentBranches b false).matrix := by
  cases b
  · apply isometryLift_order epsilon1 epsilon0 envErasedEmbed envErasedEmbed_isometry (1 / 4)
    apply Matrix.le_iff.mpr
    have h := (Matrix.le_iff.mp erased_environment_order).smul
      (by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im] : (0 : ℂ) ≤ 1 / 4)
    convert h using 1
    module
  · apply isometryLift_order sigma1 sigma0 envReferenceEmbed envReferenceEmbed_isometry (1 / 28)
    apply Matrix.le_iff.mpr
    have h := (Matrix.le_iff.mp environment_order).smul
      (by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im] : (0 : ℂ) ≤ 1 / 28)
    convert h using 1
    module

end QubitActivation
end
end QIT

namespace QIT.QubitActivation

theorem full_environment_holevo_upper :
    fullEveEnsemble.holevoInformation ≤ signalProbability / 2 * log2 112 := by
  have hp0 : ∀ b, 0 ≤ branchProbability b := by intro b; cases b <;> norm_num [branchProbability]
  have hp1 : ∀ b, branchProbability b < 1 := by intro b; cases b <;> norm_num [branchProbability]
  have hsource := BinaryPreparation.holevo_le_source fullEveEnsemble environmentBranches
    branchProbability hp0 hp1 environmentBranches_order environmentBranches_letters
  rw [BinaryPreparation.sourceEnsemble_holevo fullEveEnsemble signalProbability rfl
    signalProbability_pos.le signalProbability_lt_one.le branchProbability hp0
      (fun b => (hp1 b).le)] at hsource
  norm_num [branchProbability] at hsource
  have h28 := binary_preparation_information_upper (1 / 28) signalProbability
    (by norm_num) (by norm_num) signalProbability_pos signalProbability_lt_one.le
  have h4 := binary_preparation_information_upper (1 / 4) signalProbability
    (by norm_num) (by norm_num) signalProbability_pos signalProbability_lt_one.le
  norm_num at h28 h4
  have hlog : log2 112 = log2 28 + log2 4 := by
    unfold log2
    rw [show (112 : ℝ) = 28 * 4 by norm_num,
      Real.log_mul (by norm_num : (28 : ℝ) ≠ 0) (by norm_num : (4 : ℝ) ≠ 0)]
    ring
  rw [hlog]
  linarith

end QIT.QubitActivation
