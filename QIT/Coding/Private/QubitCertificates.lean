/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitEncoding
public import QIT.Coding.Private.SimulatorData
public import QIT.Coding.Private.ProductComplement

/-!
# Finite certificates for the qubit encoding

All referenced environmental amplitudes use `Fin 2 × Fin 8`, including
the full Kraus-index coherences. The four amplitude identities
give a direct finite proof of the operator order in `eq:certificates`.
The newer manuscript uses a common environmental block basis instead.
-/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
open Channel SimulatorCanonical
noncomputable section

abbrev RE := Fin 2 × Fin 8

private theorem vecCons_three {α : Type*} (x : α) (v : Fin 3 → α) :
    Matrix.vecCons x v (3 : Fin 4) = v 2 := rfl

/-- The same three vectors, expressed in the exact radical basis. -/
def phiCanonical (j : Fin 3) (x : RA) : ℂ :=
  if j.val = 0 then
    if x.1.val = 0 ∧ x.2.val = 0 then r3 / 2
    else if x.1.val = 1 ∧ x.2.val = 1 then 1 / 2 else 0
  else if j.val = 1 then
    if x.1.val = 0 ∧ x.2.val = 2 then 1 / 2
    else if x.1.val = 1 ∧ x.2.val = 3 then r3 / 2 else 0
  else
    if (x.1.val = 0 ∧ x.2.val = 1) ∨ (x.1.val = 1 ∧ x.2.val = 2)
    then r2 / 2 else 0

theorem phiCanonical_eq : phiCanonical = phi := by
  funext j x
  rcases x with ⟨r, a⟩
  fin_cases j <;> fin_cases r <;> fin_cases a <;>
    norm_num [phiCanonical, phi, phi0, phi1, phi2, r2, r3, erasureInvSqrtTwo]
  all_goals simp only [← Complex.ofReal_div, ← Complex.ofReal_inv,
    ← Complex.ofReal_ofNat, Complex.ofReal_inj]
  all_goals apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  all_goals norm_num [div_pow, inv_pow, Real.sq_sqrt]

/-- `(I_R ⊗ ⟨b|V) φ_j` in the full environment basis. -/
def envAmplitude (j : Fin 3) (b : Fin 4) (x : RE) : ℂ :=
  ∑ a : Fin 4, krausN x.2 b a * phi j (x.1, a)

private theorem sqrt_two_thirds : (Real.sqrt (2 / 3) : ℂ) = r2 * r3 / 3 := by
  simp only [r2, r3, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    ← Complex.ofReal_ofNat, Complex.ofReal_inj]
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  norm_num [mul_pow, div_pow, Real.sq_sqrt]

private theorem sqrt_six : (Real.sqrt 6 : ℂ) = r2 * r3 := by
  simp only [r2, r3, ← Complex.ofReal_mul, Complex.ofReal_inj]
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  norm_num [mul_pow, Real.sq_sqrt]

set_option maxHeartbeats 2000000 in
/-- The first single-vector identity used in the environmental amplitude proof. -/
theorem envAmplitude_20 :
    envAmplitude 2 0 = -(Real.sqrt (2 / 3) : ℂ) • envAmplitude 1 1 := by
  funext x
  rcases x with ⟨r, e⟩
  simp only [envAmplitude, ← ks_eq, ← phiCanonical_eq, sqrt_two_thirds, Pi.smul_apply,
    smul_eq_mul]
  fin_cases r <;> fin_cases e <;>
    norm_num [ks, phiCanonical, Fin.sum_univ_succ, vecCons_three, Matrix.cons_val_two,
      Matrix.cons_val, map_ofNat] <;> ring_nf
  all_goals (norm_num; ring)

set_option maxHeartbeats 2000000 in
/-- The second single-vector identity used in the environmental amplitude proof. -/
theorem envAmplitude_23 :
    envAmplitude 2 3 = -(Real.sqrt (2 / 3) : ℂ) • envAmplitude 0 2 := by
  funext x
  rcases x with ⟨r, e⟩
  simp only [envAmplitude, ← ks_eq, ← phiCanonical_eq, sqrt_two_thirds, Pi.smul_apply,
    smul_eq_mul]
  fin_cases r <;> fin_cases e <;>
    norm_num [ks, phiCanonical, Fin.sum_univ_succ, vecCons_three, Matrix.cons_val_two,
      Matrix.cons_val, map_ofNat] <;> ring_nf
  all_goals (norm_num; ring)

set_option maxHeartbeats 2000000 in
/-- The first paired identity used in the environmental amplitude proof. -/
theorem envAmplitude_21 :
    envAmplitude 2 1 = (Real.sqrt 6 : ℂ) • envAmplitude 0 0 -
      (2 * (Real.sqrt 2 : ℂ)) • envAmplitude 1 2 := by
  funext x
  rcases x with ⟨r, e⟩
  simp only [envAmplitude, ← ks_eq, ← phiCanonical_eq, sqrt_six, Pi.smul_apply,
    Pi.sub_apply, smul_eq_mul, show (Real.sqrt 2 : ℂ) = r2 from rfl]
  fin_cases r <;> fin_cases e <;>
    norm_num [ks, phiCanonical, Fin.sum_univ_succ, vecCons_three, Matrix.cons_val_two,
      Matrix.cons_val, map_ofNat] <;> ring_nf
  all_goals (norm_num; ring)

set_option maxHeartbeats 2000000 in
/-- The second paired identity used in the environmental amplitude proof. -/
theorem envAmplitude_22 :
    envAmplitude 2 2 = -(2 * (Real.sqrt 2 : ℂ)) • envAmplitude 0 1 +
      (Real.sqrt 6 : ℂ) • envAmplitude 1 3 := by
  funext x
  rcases x with ⟨r, e⟩
  simp only [envAmplitude, ← ks_eq, ← phiCanonical_eq, sqrt_six, Pi.smul_apply,
    Pi.add_apply, smul_eq_mul, show (Real.sqrt 2 : ℂ) = r2 from rfl]
  fin_cases r <;> fin_cases e <;>
    norm_num [ks, phiCanonical, Fin.sum_univ_succ, vecCons_three, Matrix.cons_val_two,
      Matrix.cons_val, map_ofNat] <;> ring_nf
  all_goals (norm_num; ring)

end
end QIT.QubitActivation
