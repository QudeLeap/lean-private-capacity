/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitCertificates

/-! # The full environmental operator bound for the qubit encoding -/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

def referencedEnvironment : Channel RA RE := (idChannel (Fin 2)).prod complementN
def sigma0 : State RE := referencedEnvironment.applyState rho0
def sigma1 : State RE := referencedEnvironment.applyState rho1

/-- The Kraus complement retains every environmental coherence. -/
theorem environment_pure (j : Fin 3) :
    referencedEnvironment.map (rankOneMatrix (phi j)) =
      ∑ b : Fin 4, rankOneMatrix (envAmplitude j b) := by
  change MatrixMap.kron (MatrixMap.ofKraus (fun _ : Unit => (1 : CMatrix (Fin 2))))
    (MatrixMap.complementOfKraus krausN) (rankOneMatrix (phi j)) = _
  rw [MatrixMap.complementOfKraus_eq_ofKraus, kron_ofKraus]
  change (∑ ib : Unit × Fin 4,
    Matrix.kronecker (1 : CMatrix (Fin 2)) (fun e a => krausN e ib.2 a) *
      rankOneMatrix (phi j) *
        (Matrix.kronecker (1 : CMatrix (Fin 2)) (fun e a => krausN e ib.2 a)).conjTranspose) = _
  rw [Fintype.sum_prod_type, Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro b _
  rw [← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  congr 1
  funext x
  simp [envAmplitude, Matrix.mulVec, dotProduct, Matrix.kronecker,
    Fintype.sum_prod_type, Matrix.one_apply]

theorem sigma0_decomposition :
    sigma0.matrix = (1 / 2 : ℂ) •
      ((∑ b : Fin 4, rankOneMatrix (envAmplitude 0 b)) +
       (∑ b : Fin 4, rankOneMatrix (envAmplitude 1 b))) := by
  change referencedEnvironment.map ((1 / 2 : ℂ) •
    (rankOneMatrix (phi 0) + rankOneMatrix (phi 1))) = _
  rw [map_smul, map_add, environment_pure, environment_pure]

theorem sigma1_decomposition :
    sigma1.matrix = ∑ b : Fin 4, rankOneMatrix (envAmplitude 2 b) :=
  environment_pure 2

private theorem rankOne_pair {ι : Type*} (v w : ι → ℂ) (a b : ℝ) :
    rankOneMatrix ((a : ℂ) • v + (b : ℂ) • w) +
      rankOneMatrix ((b : ℂ) • v - (a : ℂ) • w) =
        ((a ^ 2 + b ^ 2 : ℝ) : ℂ) • (rankOneMatrix v + rankOneMatrix w) := by
  ext i j
  simp [rankOneMatrix_apply, star_add, star_sub, star_mul]
  ring

private theorem rankOne_real_smul {ι : Type*} (v : ι → ℂ) (a : ℝ) :
    rankOneMatrix ((a : ℂ) • v) = ((a ^ 2 : ℝ) : ℂ) • rankOneMatrix v := by
  ext i j
  simp [rankOneMatrix_apply, star_mul]
  ring

/-- Orthogonal coefficient vector for the first paired amplitude identity. -/
def remainder0 : RE → ℂ :=
  (-(2 * (Real.sqrt 2 : ℂ))) • envAmplitude 0 0 - (Real.sqrt 6 : ℂ) • envAmplitude 1 2

/-- Orthogonal coefficient vector for the second paired amplitude identity. -/
def remainder1 : RE → ℂ :=
  (Real.sqrt 6 : ℂ) • envAmplitude 0 1 + (2 * (Real.sqrt 2 : ℂ)) • envAmplitude 1 3

theorem environment_pair0 :
    rankOneMatrix (envAmplitude 2 1) + rankOneMatrix remainder0 =
      (14 : ℂ) • (rankOneMatrix (envAmplitude 0 0) + rankOneMatrix (envAmplitude 1 2)) := by
  rw [envAmplitude_21]
  convert rankOne_pair (envAmplitude 0 0) (envAmplitude 1 2)
    (Real.sqrt 6) (-(2 * Real.sqrt 2)) using 1 <;>
    norm_num [remainder0, sub_eq_add_neg, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt]

theorem environment_pair1 :
    rankOneMatrix (envAmplitude 2 2) + rankOneMatrix remainder1 =
      (14 : ℂ) • (rankOneMatrix (envAmplitude 0 1) + rankOneMatrix (envAmplitude 1 3)) := by
  rw [envAmplitude_22]
  convert rankOne_pair (envAmplitude 0 1) (envAmplitude 1 3)
    (-(2 * Real.sqrt 2)) (Real.sqrt 6) using 1 <;>
    norm_num [remainder1, sub_eq_add_neg, mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt]

theorem environment_single0 :
    rankOneMatrix (envAmplitude 2 0) = (2 / 3 : ℂ) • rankOneMatrix (envAmplitude 1 1) := by
  rw [envAmplitude_20]
  convert rankOne_real_smul (envAmplitude 1 1) (-Real.sqrt (2 / 3)) using 1 <;>
    norm_num [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt]

theorem environment_single3 :
    rankOneMatrix (envAmplitude 2 3) = (2 / 3 : ℂ) • rankOneMatrix (envAmplitude 0 2) := by
  rw [envAmplitude_23]
  convert rankOne_real_smul (envAmplitude 0 2) (-Real.sqrt (2 / 3)) using 1 <;>
    norm_num [div_pow, ← Complex.ofReal_pow, Real.sq_sqrt]

/-- A sum of positive outer products for the full 16-dimensional environment. -/
theorem environment_remainder :
    (28 : ℂ) • sigma0.matrix - sigma1.matrix =
      rankOneMatrix remainder0 + rankOneMatrix remainder1 +
        (40 / 3 : ℂ) •
          (rankOneMatrix (envAmplitude 1 1) + rankOneMatrix (envAmplitude 0 2)) +
        (14 : ℂ) •
          (rankOneMatrix (envAmplitude 0 3) + rankOneMatrix (envAmplitude 1 0)) := by
  rw [sigma0_decomposition, sigma1_decomposition]
  ext i j
  have h0 := congrArg (fun M : CMatrix RE => M i j) environment_pair0
  have h1 := congrArg (fun M : CMatrix RE => M i j) environment_pair1
  have h2 := congrArg (fun M : CMatrix RE => M i j) environment_single0
  have h3 := congrArg (fun M : CMatrix RE => M i j) environment_single3
  have sum4 (f : Fin 4 → ℂ) : ∑ k, f k = f 0 + f 1 + f 2 + f 3 := by
    simp [Fin.sum_univ_succ, add_assoc]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply,
    smul_eq_mul, sum4] at h0 h1 h2 h3 ⊢
  linear_combination -h0 - h1 - h2 - h3

/-- The manuscript's factor 28, with no compression of the environment. -/
theorem environment_order : sigma1.matrix ≤ (28 : ℂ) • sigma0.matrix := by
  apply Matrix.le_iff.mpr
  rw [environment_remainder]
  exact (((rankOneMatrix_pos remainder0).add (rankOneMatrix_pos remainder1)).add
    (((rankOneMatrix_pos (envAmplitude 1 1)).add (rankOneMatrix_pos (envAmplitude 0 2))).smul
      (by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]))).add
    (((rankOneMatrix_pos (envAmplitude 0 3)).add (rankOneMatrix_pos (envAmplitude 1 0))).smul
      (by norm_num [Complex.nonneg_iff]))

/-- Support inclusion follows from the proved operator bound. -/
theorem environment_support : Matrix.Supports sigma1.matrix sigma0.matrix := by
  have h := Matrix.Supports.left_of_posSemidef_add sigma1.pos (Matrix.le_iff.mp environment_order)
  have heq : sigma1.matrix + ((28 : ℂ) • sigma0.matrix - sigma1.matrix) =
      (28 : ℂ) • sigma0.matrix := by abel
  rw [heq] at h
  intro v hv
  apply h v
  simp [Matrix.smul_mulVec, hv]

def epsilon0 : State (Fin 8) := complementN.applyState rho0.marginalB
def epsilon1 : State (Fin 8) := complementN.applyState rho1.marginalB

/-- The erased environmental branch also has a positive remainder. -/
theorem erased_environment_remainder :
    (4 : ℂ) • epsilon0.matrix - epsilon1.matrix =
      complementN.map (Matrix.diagonal ![3 / 2, 0, 0, 3 / 2]) := by
  change (4 : ℂ) • complementN.map (partialTraceA rho0.matrix) -
    complementN.map (partialTraceA rho1.matrix) = _
  rw [← map_smul, ← map_sub, marginal_remainder]

theorem erased_environment_order : epsilon1.matrix ≤ (4 : ℂ) • epsilon0.matrix := by
  apply Matrix.le_iff.mpr
  rw [erased_environment_remainder]
  apply complementN.mapsPositive
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im]

end
end QIT.QubitActivation
