/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitEvent
public import QIT.Coding.Private.QubitRates

/-!
# The supported reference pair retained from the 2026-09-07 manuscript

This proves the finite state, event and order statements used in
the former `eq:finite-violation`, removed from the 2026-09-08 main manuscript. Bounds on quantum relative entropy and the class
inclusion `Z_cRE ⊊ Z_P` require additional information-theoretic proofs.
-/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
noncomputable section

private theorem reference_coefficient_nonneg : (0 : ℂ) ≤ 1 - (referenceMixture : ℂ) := by
  norm_num [referenceMixture, Complex.nonneg_iff]

private theorem reference_coefficient_pos : (0 : ℂ) < (referenceMixture : ℂ) := by
  norm_num [referenceMixture, Complex.lt_def]

def referenceInput : State RA where
  matrix := (1 - (referenceMixture : ℂ)) • rho0.matrix + (referenceMixture : ℂ) • rho1.matrix
  pos := by
    exact (rho0.pos.smul reference_coefficient_nonneg).add (rho1.pos.smul reference_coefficient_pos.le)
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      rho0.trace_eq_one, rho1.trace_eq_one]
    simp [smul_eq_mul]

theorem reference_input_support : Matrix.Supports rho1.matrix referenceInput.matrix := by
  have h := Matrix.Supports.right_of_posSemidef_add
    (rho0.pos.smul reference_coefficient_nonneg) (rho1.pos.smul reference_coefficient_pos.le)
  intro v hv
  have hscaled : (referenceMixture : ℂ) • rho1.matrix.mulVec v = 0 := by
    simpa only [Matrix.smul_mulVec] using h v hv
  exact (smul_eq_zero.mp hscaled).resolve_left reference_coefficient_pos.ne'

def referenceBeta : State RA := referencedReceiver.applyState referenceInput
def referenceSigma : State RE := referencedEnvironment.applyState referenceInput

theorem reference_beta_matrix : referenceBeta.matrix =
    (1 - (referenceMixture : ℂ)) • beta0.matrix + (referenceMixture : ℂ) • beta1.matrix := by
  change referencedReceiver.map ((1 - (referenceMixture : ℂ)) • rho0.matrix +
    (referenceMixture : ℂ) • rho1.matrix) = _
  rw [map_add, map_smul, map_smul]
  rfl

theorem reference_sigma_matrix : referenceSigma.matrix =
    (1 - (referenceMixture : ℂ)) • sigma0.matrix + (referenceMixture : ℂ) • sigma1.matrix := by
  change referencedEnvironment.map ((1 - (referenceMixture : ℂ)) • rho0.matrix +
    (referenceMixture : ℂ) • rho1.matrix) = _
  rw [map_add, map_smul, map_smul]
  rfl

theorem reference_event :
    (referenceBeta.matrix * receiverEffect).trace = (referenceMixture : ℂ) / 6 := by
  rw [reference_beta_matrix, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    receiver_event_base, receiver_event_signal]
  simp [smul_eq_mul, div_eq_mul_inv]

/-- The exact positive remainder behind `σ_t ≥ (1-t) σ₁ / 28`. -/
theorem reference_environment_remainder :
    referenceSigma.matrix - ((1 - (referenceMixture : ℂ)) / 28) • sigma1.matrix =
      ((1 - (referenceMixture : ℂ)) / 28) • ((28 : ℂ) • sigma0.matrix - sigma1.matrix) +
        (referenceMixture : ℂ) • sigma1.matrix := by
  rw [reference_sigma_matrix]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem reference_environment_order :
    ((1 - (referenceMixture : ℂ)) / 28) • sigma1.matrix ≤ referenceSigma.matrix := by
  apply Matrix.le_iff.mpr
  rw [reference_environment_remainder]
  exact ((Matrix.le_iff.mp environment_order).smul
    (div_nonneg reference_coefficient_nonneg (by norm_num [Complex.nonneg_iff]))).add
    (sigma1.pos.smul reference_coefficient_pos.le)

end
end QIT.QubitActivation
