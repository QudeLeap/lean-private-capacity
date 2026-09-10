/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitProduct

/-!
# Mixed and deformed input letters

The revised example uses two different deformations of the base state and
mixes the second with `rho1`. These are density matrices on the paper's RA
register, then explicitly swapped for the physical channel N ⊗ E₂.
The denominator form avoids introducing unnecessary square roots; the theorem
`deformedBase_normalized_vectors` identifies it with the paper's normalized kets.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
namespace QIT.QubitActivation
noncomputable section

/-- Squared norm of either unnormalized deformed ket. -/
def deformationNorm (r : ℝ) : ℝ := 1 + 3 * r ^ 2

theorem deformationNorm_pos (r : ℝ) : 0 < deformationNorm r := by
  dsimp [deformationNorm]
  positivity

def deformedKet0 (r : ℝ) (x : RA) : ℂ :=
  if x.1.val = 0 ∧ x.2.val = 0 then (Real.sqrt 3 : ℂ) * r
  else if x.1.val = 1 ∧ x.2.val = 1 then 1 else 0

def deformedKet1 (r : ℝ) (x : RA) : ℂ :=
  if x.1.val = 0 ∧ x.2.val = 2 then 1
  else if x.1.val = 1 ∧ x.2.val = 3 then (Real.sqrt 3 : ℂ) * r else 0

theorem deformedKet0_trace (r : ℝ) :
    (rankOneMatrix (deformedKet0 r)).trace = (deformationNorm r : ℂ) := by
  norm_num [rankOneMatrix_trace, dotProduct, deformedKet0, Fintype.sum_prod_type,
    Fin.sum_univ_succ, deformationNorm]
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  linear_combination (r : ℂ) ^ 2 * hs

theorem deformedKet1_trace (r : ℝ) :
    (rankOneMatrix (deformedKet1 r)).trace = (deformationNorm r : ℂ) := by
  norm_num [rankOneMatrix_trace, dotProduct, deformedKet1, Fintype.sum_prod_type,
    Fin.sum_univ_succ, deformationNorm]
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  linear_combination (r : ℂ) ^ 2 * hs

/-- The paper's η(r), valid even at r = 0. -/
def deformedBase (r : ℝ) : State RA where
  matrix := ((2 * deformationNorm r : ℝ)⁻¹ : ℂ) •
    (rankOneMatrix (deformedKet0 r) + rankOneMatrix (deformedKet1 r))
  pos := ((rankOneMatrix_pos _).add (rankOneMatrix_pos _)).smul (by
    exact_mod_cast inv_nonneg.mpr (mul_nonneg (by norm_num) (deformationNorm_pos r).le))
  trace_eq_one := by
    rw [Matrix.trace_smul, Matrix.trace_add, deformedKet0_trace, deformedKet1_trace]
    have hd : (deformationNorm r : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (deformationNorm_pos r).ne'
    push_cast
    simp only [smul_eq_mul]
    field_simp
    ring

/-- A convex mixture of two density states, with the weight on the second state. -/
def mixInput (r0 r1 : State RA) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : State RA where
  matrix := (1 - (t : ℂ)) • r0.matrix + (t : ℂ) • r1.matrix
  pos := (r0.pos.smul (by exact_mod_cast sub_nonneg.mpr ht1)).add
    (r1.pos.smul (by exact_mod_cast ht0))
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      r0.trace_eq_one, r1.trace_eq_one]
    simp [smul_eq_mul]

theorem deformedBase_helper_marginal (r : ℝ) :
    partialTraceB (deformedBase r).matrix = (1 / 2 : ℂ) • (1 : CMatrix (Fin 2)) := by
  have hd : (deformationNorm r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (deformationNorm_pos r).ne'
  have hs : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
    norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [deformedBase, partialTraceB, rankOneMatrix_apply, deformedKet0, deformedKet1,
      Fin.sum_univ_succ, Matrix.one_apply]
  all_goals field_simp [hd]
  all_goals simp only [deformationNorm, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow]
  all_goals ring_nf
  all_goals rw [hs]
  all_goals ring

theorem mixInput_helper_marginal (a b : State RA) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : partialTraceB a.matrix = (1 / 2 : ℂ) • (1 : CMatrix (Fin 2)))
    (hb : partialTraceB b.matrix = (1 / 2 : ℂ) • (1 : CMatrix (Fin 2))) :
    partialTraceB (mixInput a b t ht0 ht1).matrix =
      (1 / 2 : ℂ) • (1 : CMatrix (Fin 2)) := by
  change partialTraceB ((1 - (t : ℂ)) • a.matrix + (t : ℂ) • b.matrix) = _
  rw [partialTraceB_add, partialTraceB_smul, partialTraceB_smul, ha, hb]
  module

theorem deformedBase_one : deformedBase 1 = rho0 := by
  apply State.ext
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [deformedBase, deformationNorm, rho0, rho0Mat, rankOneMatrix_apply,
      deformedKet0, deformedKet1, phi0, phi1] <;> ring

/-- Equality with the normalized vectors v₀(r), v₁(r) in the paper. -/
theorem deformedBase_normalized_vectors (r : ℝ) :
    (deformedBase r).matrix = (1 / 2 : ℂ) •
      (rankOneMatrix (fun x ↦ deformedKet0 r x / (Real.sqrt (deformationNorm r) : ℂ)) +
       rankOneMatrix (fun x ↦ deformedKet1 r x / (Real.sqrt (deformationNorm r) : ℂ))) := by
  have hs : (Real.sqrt (deformationNorm r) : ℂ) ^ 2 = (deformationNorm r : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (deformationNorm_pos r).le]
  ext x y
  simp only [deformedBase, Matrix.smul_apply, Matrix.add_apply, rankOneMatrix_apply,
    smul_eq_mul, map_div₀, Complex.star_def, Complex.conj_ofReal,
    Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [div_mul_div_comm, div_mul_div_comm, ← pow_two, hs]
  ring

/-- The undeformed mixed signal ρₜ in the new dilution example. -/
def mixedSignal (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : State RA :=
  mixInput rho0 rho1 t ht0 ht1

def deformedR0 : ℝ := 1001 / 1000
def deformedR1 : ℝ := 999 / 1000
def deformedMixing : ℝ := 27 / 1000
def deformedProbability : ℝ := 3 / 16

def deformedLetter (x : Bool) : State RA :=
  if x then mixInput (deformedBase deformedR1) rho1 deformedMixing
    (by norm_num [deformedMixing]) (by norm_num [deformedMixing])
  else deformedBase deformedR0

theorem deformedLetter_helper_marginal (x : Bool) :
    partialTraceB (deformedLetter x).matrix = (1 / 2 : ℂ) • (1 : CMatrix (Fin 2)) := by
  cases x
  · exact deformedBase_helper_marginal _
  · exact mixInput_helper_marginal _ _ _ (by norm_num [deformedMixing])
      (by norm_num [deformedMixing]) (deformedBase_helper_marginal _) rho1_helper_marginal

def deformedEnsemble : Ensemble Bool ProductInput where
  probs := (ensemble deformedProbability (by norm_num [deformedProbability])
    (by norm_num [deformedProbability])).probs
  weights_sum := (ensemble deformedProbability (by norm_num [deformedProbability])
    (by norm_num [deformedProbability])).weights_sum
  states x := (deformedLetter x).reindex (Equiv.prodComm (Fin 2) (Fin 4))

def deformedBobEnsemble : Ensemble Bool ProductReceiver :=
  productChannel.outputEnsemble deformedEnsemble

def deformedEveEnsemble : Ensemble Bool ProductEnvironment :=
  productComplement.outputEnsemble deformedEnsemble

end
end QIT.QubitActivation
