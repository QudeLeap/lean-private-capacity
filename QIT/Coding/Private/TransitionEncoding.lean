/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module
public import QIT.Coding.Private.TransitionChannel
public import QIT.Coding.Private.TransitionEncodingData
public import QIT.Core.Pure

/-! # Actual input states, receiver event, and full environment order certificates -/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.Transition
noncomputable section
abbrev RA := Fin 2 × Fin 4
abbrev RE := Fin 2 × Fin 8
open TransitionEncodingData

/-- `false` is `(u₀u₀† + u₁u₁†)/2`; `true` is `ww†`. -/
def inputState (b : Bool) : State RA where
  matrix := fun x y ↦ (rho b x y : ℂ)
  pos := by
    cases b
    · have h := ((rankOneMatrix_pos (fun x ↦ (v0 x : ℂ))).add
        (rankOneMatrix_pos (fun x ↦ (v1 x : ℂ)))).smul (show (0 : ℂ) ≤ 1 / 10 by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im])
      convert h using 1
      ext x y
      simp [rho, rankOneMatrix_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    · have h := (rankOneMatrix_pos (fun x ↦ (vw x : ℂ))).smul
        (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im])
      convert h using 1
      ext x y
      simp [rho, rankOneMatrix_apply, Matrix.smul_apply, smul_eq_mul]
      ring
  trace_eq_one := by
    change (∑ x : RA, (rho b x x : ℂ)) = 1
    exact_mod_cast rho_trace b

theorem inputState_matrix (b : Bool) (x y : RA) :
    (inputState b).matrix x y = (rho b x y : ℂ) := rfl

theorem inputState_helper_marginal (b : Bool) :
    (inputState b).marginalA.matrix = (1 / 2 : ℂ) • (1 : CMatrix (Fin 2)) := by
  ext r s
  change (∑ i : Fin 4, (rho b (r, i) (s, i) : ℂ)) = _
  have h := congrArg (fun q : ℚ ↦ (q : ℂ)) (helper_marginal b r s)
  simpa only [Rat.cast_sum, apply_ite, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_zero, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, mul_ite,
    mul_one, mul_zero] using h

def referencedReceiver : Channel RA RA := (Channel.idChannel (Fin 2)).prod mainChannel
def referencedEnvironment : Channel RA RE := (Channel.idChannel (Fin 2)).prod complement
def sigma (b : Bool) : State RE := referencedEnvironment.applyState (inputState b)
def epsilon (b : Bool) : State (Fin 8) := complement.applyState (inputState b).marginalB

theorem epsilon_eq_marginal (b : Bool) : epsilon b = (sigma b).marginalB :=
  (State.marginalB_applyState_prod (inputState b) (Channel.idChannel (Fin 2)) complement).symm

theorem receiver_entry (b : Bool) (x y : RA) :
    (referencedReceiver.applyState (inputState b)).matrix x y = (bob b x y : ℂ) := by
  change MatrixMap.kron (Channel.idChannel (Fin 2)).map mainChannel.map
    (inputState b).matrix x y = _
  rw [MatrixMap.kron_idChannel_left_apply_slice, mainChannel_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.conjTranspose_apply, inputState_matrix, error, star_ratCast,
    bob, Rat.cast_sum, Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem sigma_entry (b : Bool) (x y : RE) :
    (sigma b).matrix x y = root x.2 * (env b x y : ℂ) * root y.2 := by
  change MatrixMap.kron (Channel.idChannel (Fin 2)).map complement.map
    (inputState b).matrix x y = _
  rw [MatrixMap.kron_idChannel_left_apply_slice,
    MatrixMap.map_eq_sum_single complement.map]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, complement_single,
    inputState_matrix, error, env, Rat.cast_sum, Rat.cast_mul,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The fixed signal projector has click probability zero or 1/7 before erasure. -/
theorem receiver_event (b : Bool) :
    ((referencedReceiver.applyState (inputState b)).matrix * (inputState true).matrix).trace =
      if b then (1 / 7 : ℂ) else 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, receiver_entry, inputState_matrix]
  have h := congrArg (fun q : ℚ ↦ (q : ℂ)) (event b)
  simpa only [Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat, Rat.cast_zero] using h

theorem signal_effect_le_one : (inputState true).matrix ≤ 1 := by
  apply Matrix.le_iff.mpr
  apply MatrixMap.posSemidef_one_sub_of_posSemidef_idempotent _ (inputState true).pos
  ext x y
  simp only [Matrix.mul_apply, inputState_matrix]
  exact_mod_cast signal_projector x y

def environmentRemainder (k : Fin 6) (x : RE) : ℂ :=
  root x.2 * (orderGramTable (envFlat x) k : ℂ)

/-- A sum of positive rank-one operators on the complete 16-dimensional environment. -/
theorem environment_remainder :
    (205 / 9 : ℂ) • (sigma false).matrix - (sigma true).matrix =
      ∑ k : Fin 6, (orderWeights k : ℂ) • rankOneMatrix (environmentRemainder k) := by
  ext x y
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sigma_entry,
    Matrix.sum_apply, rankOneMatrix_apply, environmentRemainder, star_mul',
    star_root, star_ratCast]
  have h := congrArg (fun q : ℚ ↦ (q : ℂ)) (order_gram x y)
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_sub, Rat.cast_div,
    Rat.cast_ofNat] at h
  calc (205 / 9 : ℂ) * (root x.2 * (env false x y : ℂ) * root y.2) -
      root x.2 * (env true x y : ℂ) * root y.2 =
        root x.2 * ((205 / 9 : ℂ) * (env false x y : ℂ) - (env true x y : ℂ)) * root y.2 := by ring
    _ = _ := by
      rw [h]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem environment_order : ((1 / (205 / 9) : ℝ) : ℂ) • (sigma true).matrix ≤ (sigma false).matrix := by
  have h : ((205 / 9 : ℂ) • (sigma false).matrix - (sigma true).matrix).PosSemidef := by
    rw [environment_remainder]
    apply Matrix.posSemidef_sum
    intro k _
    apply (rankOneMatrix_pos _).smul
    simp only [Complex.nonneg_iff, Complex.ratCast_re, Complex.ratCast_im, and_true]
    exact_mod_cast orderWeights_nonneg k
  apply Matrix.le_iff.mpr
  have hs := h.smul (show (0 : ℂ) ≤ 9 / 205 by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im])
  convert hs using 1
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  module

theorem epsilon_entry (b : Bool) (e f : Fin 8) :
    (epsilon b).matrix e f = if e = f then
      (TransitionData.weights e : ℂ) * (epsilonDiag b e : ℂ) else 0 := by
  rw [epsilon_eq_marginal]
  change (∑ r : Fin 2, (sigma b).matrix (r, e) (r, f)) = _
  simp only [sigma_entry, ← Finset.sum_mul, ← Finset.mul_sum]
  have h : (∑ r : Fin 2, (env b (r, e) (r, f) : ℂ)) =
      if e = f then (epsilonDiag b e : ℂ) else 0 := by
    have hr := congrArg (fun q : ℚ ↦ (q : ℂ)) (epsilon_diagonal b e f)
    by_cases hef : e = f <;> simpa [hef] using hr
  rw [h]
  by_cases hef : e = f
  · subst f
    simp only [↓reduceIte]
    rw [show root e * (epsilonDiag b e : ℂ) * root e =
      (root e * root e) * (epsilonDiag b e : ℂ) by ring, root_sq]
  · simp [hef]

theorem erased_environment_order :
    ((1 / 4 : ℝ) : ℂ) • (epsilon true).matrix ≤ (epsilon false).matrix := by
  have h : ((4 : ℂ) • (epsilon false).matrix - (epsilon true).matrix).PosSemidef := by
    have he : (4 : ℂ) • (epsilon false).matrix - (epsilon true).matrix =
        Matrix.diagonal (fun e ↦ (TransitionData.weights e : ℂ) *
          ((4 : ℂ) * (epsilonDiag false e : ℂ) - (epsilonDiag true e : ℂ))) := by
      ext e f
      by_cases hef : e = f <;> simp [epsilon_entry, hef]
      ring
    rw [he]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro e
    apply mul_nonneg
    · simp only [Complex.nonneg_iff, Complex.ratCast_re, Complex.ratCast_im, and_true]
      exact_mod_cast (TransitionData.weights_pos e).le
    · have hq : (0 : ℚ) ≤ 4 * epsilonDiag false e - epsilonDiag true e := epsilon_order e
      have hr : (0 : ℝ) ≤ 4 * (epsilonDiag false e : ℝ) - (epsilonDiag true e : ℝ) := by
        exact_mod_cast hq
      rw [Complex.nonneg_iff]
      constructor
      · simpa using hr
      · simp
  apply Matrix.le_iff.mpr
  have hs := h.smul (show (0 : ℂ) ≤ 1 / 4 by norm_num [Complex.nonneg_iff, Complex.div_re, Complex.div_im])
  convert hs using 1
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  module

end
end QIT.Transition
