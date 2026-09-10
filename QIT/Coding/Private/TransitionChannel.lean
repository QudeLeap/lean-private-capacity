/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module
public import QIT.Coding.Private.TransitionChannelData
public import QIT.Coding.Private.TransposeCriterion
public import QIT.Core.Map.ChoiCharacterization

/-! # The transition channel and its transpose simulator

The eight errors and their weights are those of `private_superactivation.tex`.
The complementary channel retains the entire Kraus register. The rational
certificate is converted to a completely positive, trace-preserving simulator.
-/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT.Transition
noncomputable section

def error (e : Fin 8) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j ↦ (TransitionData.errors e i j : ℂ)

def root (e : Fin 8) : ℂ := (Real.sqrt (TransitionData.weights e : ℝ) : ℂ)

@[simp] theorem star_root (e : Fin 8) : star (root e) = root e := by simp [root]

theorem root_sq (e : Fin 8) : root e * root e = (TransitionData.weights e : ℂ) := by
  have hp : 0 ≤ (TransitionData.weights e : ℝ) := by
    exact_mod_cast (TransitionData.weights_pos e).le
  calc root e * root e = ((Real.sqrt (TransitionData.weights e : ℝ) ^ 2 : ℝ) : ℂ) := by
        simp [root, pow_two]
    _ = _ := by rw [Real.sq_sqrt hp]; norm_cast

theorem root_ne_zero (e : Fin 8) : root e ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply (Real.sqrt_pos.mpr _).ne'
  exact_mod_cast TransitionData.weights_pos e

def kraus (e : Fin 8) : Matrix (Fin 4) (Fin 4) ℂ := root e • error e

@[simp] theorem star_error (e : Fin 8) (i j : Fin 4) :
    star (error e i j) = error e i j := by simp [error]

theorem kraus_completeness : MatrixMap.krausAdjoint kraus 1 = 1 := by
  ext i j
  simp only [MatrixMap.krausAdjoint, Matrix.mul_one, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, kraus, Matrix.smul_apply,
    smul_eq_mul, star_mul, star_root, star_error]
  have he (e : Fin 8) (k : Fin 4) :
      error e k i * root e * (root e * error e k j) =
        (TransitionData.weights e : ℂ) * (error e k i * error e k j) := by
    rw [show error e k i * root e * (root e * error e k j) =
      (root e * root e) * (error e k i * error e k j) by ring, root_sq]
  calc (∑ e : Fin 8, ∑ k : Fin 4, error e k i * root e * (root e * error e k j)) =
      ∑ e : Fin 8, (TransitionData.weights e : ℂ) * ∑ k : Fin 4, error e k i * error e k j := by
        apply Finset.sum_congr rfl
        intro e _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        exact he e k
    _ = _ := by
      simp only [error, Matrix.one_apply]
      have h := congrArg (fun q : ℚ ↦ (q : ℂ)) (TransitionData.completeness i j)
      simpa only [Rat.cast_sum, Rat.cast_mul, apply_ite, Rat.cast_one, Rat.cast_zero] using h

/-- The main channel of the new manuscript. -/
def mainChannel : Channel (Fin 4) (Fin 4) where
  map := MatrixMap.ofKraus kraus
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _ kraus_completeness
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

theorem complement_tracePreserving :
    MatrixMap.IsTracePreserving (MatrixMap.complementOfKraus kraus) := by
  intro X
  have h : (MatrixMap.complementOfKraus kraus X).trace =
      (mainChannel.map X).trace := by
    simp [Matrix.trace, mainChannel, MatrixMap.ofKraus, Matrix.sum_apply,
      MatrixMap.complementOfKraus_apply]
    rw [Finset.sum_comm]
  rw [h, mainChannel.tracePreserving]

/-- The full eight-dimensional environment in the manuscript's Kraus basis. -/
def complement : Channel (Fin 4) (Fin 8) where
  map := MatrixMap.complementOfKraus kraus
  completelyPositive := MatrixMap.complementOfKraus_completelyPositive _
  tracePreserving := complement_tracePreserving
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _
    (MatrixMap.complementOfKraus_completelyPositive _)

theorem complement_isComplementOf : Channel.IsComplementOf complement mainChannel :=
  ⟨kraus, rfl, rfl⟩

theorem mainChannel_apply (X : CMatrix (Fin 4)) :
    mainChannel.map X = ∑ e : Fin 8,
      (TransitionData.weights e : ℂ) • (error e * X * (error e).conjTranspose) := by
  change (∑ e, kraus e * X * (kraus e).conjTranspose) = _
  apply Finset.sum_congr rfl
  intro e _
  simp only [kraus, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, star_root, root_sq]

theorem mainChannel_single (i j r s : Fin 4) :
    mainChannel.map (Matrix.single i j 1) r s =
      ∑ e : Fin 8, (TransitionData.weights e : ℂ) * error e r i * error e s j := by
  rw [mainChannel_apply]
  simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single_apply, ite_and, mul_assoc]

theorem complement_single (i j : Fin 4) (e f : Fin 8) :
    complement.map (Matrix.single i j 1) e f =
      root e * root f * (∑ k : Fin 4, error f k j * error e k i) := by
  simp [complement, MatrixMap.complementOfKraus_apply, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, kraus, Matrix.smul_apply, smul_eq_mul,
    Matrix.single_apply, ite_and, Finset.mul_sum, mul_assoc, mul_comm]

def simulatorChoi : CMatrix (Fin 8 × Fin 4) :=
  fun x y ↦ (root x.1)⁻¹ * (TransitionData.h x y : ℂ) * (root y.1)⁻¹

theorem h_pos : Matrix.PosSemidef (fun x y ↦ (TransitionData.h x y : ℂ) : CMatrix (Fin 8 × Fin 4)) := by
  have h : (fun x y ↦ (TransitionData.h x y : ℂ) : CMatrix (Fin 8 × Fin 4)) =
      ∑ k : Fin 14, (TransitionData.gramWeights k : ℂ) •
        Matrix.vecMulVec (fun x ↦ (TransitionData.gram k x : ℂ))
          (star (fun x ↦ (TransitionData.gram k x : ℂ))) := by
    ext ⟨e, i⟩ ⟨f, j⟩
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, Pi.star_apply, star_ratCast]
    have he := congrArg (fun q : ℚ ↦ (q : ℂ)) (TransitionData.h_gram e f i j)
    simpa only [Rat.cast_sum, Rat.cast_mul, mul_assoc] using he
  rw [h]
  apply Matrix.posSemidef_sum
  intro k _
  apply (Matrix.posSemidef_vecMulVec_self_star _).smul
  simp only [Complex.nonneg_iff, Complex.ratCast_re, Complex.ratCast_im, and_true]
  exact_mod_cast TransitionData.gramWeights_nonneg k

theorem simulatorChoi_pos : simulatorChoi.PosSemidef := by
  have h := h_pos.mul_mul_conjTranspose_same
    (Matrix.diagonal (fun x : Fin 8 × Fin 4 ↦ (root x.1)⁻¹))
  convert h using 1
  ext x y
  simp [simulatorChoi, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]

theorem simulator_tracePreserving :
    MatrixMap.IsTracePreserving (MatrixMap.ofChoiMatrix simulatorChoi) := by
  rw [MatrixMap.isTracePreserving_iff_partialTraceB_choi,
    MatrixMap.choi_ofChoiMatrix]
  ext e f
  change (∑ i : Fin 4, (root e)⁻¹ * (TransitionData.h (e, i) (f, i) : ℂ) * (root f)⁻¹) = _
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have h : (∑ i : Fin 4, (TransitionData.h (e, i) (f, i) : ℂ)) =
      if e = f then (TransitionData.weights e : ℂ) else 0 := by
    have he := congrArg (fun q : ℚ ↦ (q : ℂ)) (TransitionData.h_partialTrace e f)
    simpa only [Rat.cast_sum, apply_ite, Rat.cast_zero] using he
  rw [h]
  by_cases hef : e = f
  · subst f
    simp only [↓reduceIte, Matrix.one_apply_eq, ← root_sq]
    field_simp [root_ne_zero]
  · simp [hef]

/-- The paper's completely positive and trace-preserving transpose simulator. -/
def simulator : Channel (Fin 8) (Fin 4) where
  map := MatrixMap.ofChoiMatrix simulatorChoi
  completelyPositive := by
    unfold MatrixMap.IsCompletelyPositive
    rw [MatrixMap.choi_ofChoiMatrix]
    exact simulatorChoi_pos
  tracePreserving := simulator_tracePreserving
  mapsPositive := MatrixMap.isCompletelyPositive_mapsPositive _ (by
    unfold MatrixMap.IsCompletelyPositive
    rw [MatrixMap.choi_ofChoiMatrix]
    exact simulatorChoi_pos)

theorem simulator_single (i j : Fin 4) :
    simulator.map (complement.map (Matrix.single i j 1)) =
      (mainChannel.map (Matrix.single i j 1)).transpose := by
  ext r s
  change (∑ e : Fin 8, ∑ f : Fin 8,
    complement.map (Matrix.single i j 1) e f * simulatorChoi (e, r) (f, s)) = _
  simp only [complement_single, simulatorChoi, Matrix.transpose_apply, mainChannel_single]
  have hc (e f : Fin 8) :
      root e * root f * (∑ k, error f k j * error e k i) *
        ((root e)⁻¹ * (TransitionData.h (e, r) (f, s) : ℂ) * (root f)⁻¹) =
      (∑ k, error f k j * error e k i) * (TransitionData.h (e, r) (f, s) : ℂ) := by
    field_simp [root_ne_zero]
  calc (∑ e : Fin 8, ∑ f : Fin 8,
      root e * root f * (∑ k, error f k j * error e k i) *
        ((root e)⁻¹ * (TransitionData.h (e, r) (f, s) : ℂ) * (root f)⁻¹)) =
      ∑ e : Fin 8, ∑ f : Fin 8,
        (∑ k, error f k j * error e k i) * (TransitionData.h (e, r) (f, s) : ℂ) := by
          apply Finset.sum_congr rfl
          intro e _
          apply Finset.sum_congr rfl
          intro f _
          exact hc e f
    _ = _ := by
      simp only [error]
      exact_mod_cast TransitionData.simulation i j r s

theorem simulator_identity (X : CMatrix (Fin 4)) :
    simulator.map (complement.map X) = (mainChannel.map X).transpose := by
  change (simulator.map.comp complement.map) X = (MatrixMap.transposeMap.comp mainChannel.map) X
  rw [MatrixMap.map_eq_sum_single _ X,
    MatrixMap.map_eq_sum_single (MatrixMap.transposeMap.comp mainChannel.map) X]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact simulator_single i j

/-- Zero regularized private capacity for the actual new main channel. -/
theorem mainChannel_privateCapacity_eq_zero :
    Channel.privateCapacity mainChannel complement = 0 :=
  Channel.privateCapacity_eq_zero_of_transpose_simulator mainChannel complement
    simulator simulator_identity

end
end QIT.Transition
