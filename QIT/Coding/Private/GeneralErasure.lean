/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module

public import QIT.Coding.Private.HalfErasure
public import QIT.Classical.Bridge

/-! # Erasure channels and their full complements at an arbitrary probability -/

@[expose] public section
open scoped ComplexOrder MatrixOrder
namespace QIT
noncomputable section
universe u v

variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b]

/-- A probabilistic mixture of channels, with the weight on the first channel. -/
def Channel.convexCombination (p : ℝ) (Phi Psi : Channel a b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Channel a b where
  map := (p : ℂ) • Phi.map + ((1 - p : ℝ) : ℂ) • Psi.map
  completelyPositive := by
    change ((p : ℂ) • MatrixMap.choi Phi.map +
      ((1 - p : ℝ) : ℂ) • MatrixMap.choi Psi.map).PosSemidef
    exact (Phi.completelyPositive.smul (by exact_mod_cast hp0)).add
      (Psi.completelyPositive.smul (by exact_mod_cast sub_nonneg.mpr hp1))
  tracePreserving := by
    intro X
    change ((p : ℂ) • Phi.map X + ((1 - p : ℝ) : ℂ) • Psi.map X).trace = _
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Phi.tracePreserving, Psi.tracePreserving]
    simp [smul_eq_mul]
    ring
  mapsPositive := by
    intro X hX
    exact ((Phi.mapsPositive X hX).smul (by exact_mod_cast hp0)).add
      ((Psi.mapsPositive X hX).smul (by exact_mod_cast sub_nonneg.mpr hp1))

namespace Erasure
variable {n : ℕ}

def signalChannel : Channel (Fin n) (Fin n ⊕ Fin 1) where
  map := MatrixMap.ofKraus (fun _ : Unit ↦ erasureEmbed (n := n))
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving := MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _ (by
    simp [MatrixMap.krausAdjoint, erasureEmbed_conjTranspose_mul_self])
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

def flagChannel (a : Type u) [Fintype a] [DecidableEq a] : Channel a (Fin n ⊕ Fin 1) :=
  Channel.prepare fun _ ↦ Classical.basisState (Sum.inr (0 : Fin 1))

theorem flagChannel_apply (X : CMatrix a) :
    (flagChannel (n := n) a).map X =
      X.trace • Matrix.single (Sum.inr (0 : Fin 1)) (Sum.inr 0) (1 : ℂ) := by
  simp only [flagChannel, Channel.prepare_map, Classical.basisState_matrix]
  rw [← Finset.sum_smul]
  rfl

theorem signalChannel_apply (X : CMatrix (Fin n)) :
    (signalChannel (n := n)).map X = Matrix.fromBlocks X 0 0 (0 : CMatrix (Fin 1)) := by
  simpa [signalChannel, MatrixMap.ofKraus] using erasureEmbed_conj_mul X

end Erasure

/-- The physical erasure channel, with erasure probability `p ∈ [0,1]`. -/
def Channel.erasure (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel (Fin n) (Fin n ⊕ Fin 1) :=
  Channel.convexCombination p (Erasure.flagChannel (Fin n)) Erasure.signalChannel hp0 hp1

theorem erasure_apply (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : CMatrix (Fin n)) :
    (Channel.erasure n p hp0 hp1).map X =
      Matrix.fromBlocks (((1 - p : ℝ) : ℂ) • X) 0 0
        (((p : ℂ) * X.trace) • (1 : CMatrix (Fin 1))) := by
  change (p : ℂ) • (Erasure.flagChannel (Fin n)).map X +
    ((1 - p : ℝ) : ℂ) • Erasure.signalChannel.map X = _
  rw [Erasure.flagChannel_apply, Erasure.signalChannel_apply]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [Fin.eq_zero]

/-- The complete erasure environment, ordered as flag followed by transmitted input. -/
def Channel.erasureComplement (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel (Fin n) (Fin 1 ⊕ Fin n) :=
  Channel.sumSwap.comp (Channel.erasure n (1 - p) (sub_nonneg.mpr hp1) (by linarith))

theorem erasureComplement_apply (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : CMatrix (Fin n)) :
    (Channel.erasureComplement n p hp0 hp1).map X =
      Matrix.fromBlocks ((((1 - p : ℝ) : ℂ) * X.trace) • (1 : CMatrix (Fin 1)))
        0 0 ((p : ℂ) • X) := by
  change Channel.sumSwap.map ((Channel.erasure n (1 - p) _ _).map X) = _
  rw [erasure_apply]
  simp only [sub_sub_cancel]
  change MatrixMap.ofKraus (fun _ : Unit ↦ sumSwapM (n := n)) _ = _
  simpa [MatrixMap.ofKraus] using
    sumSwapM_fromBlocks_conjTranspose ((p : ℂ) • X) (((1 - p : ℝ) : ℂ) * X.trace)

namespace Erasure
variable {n : ℕ}

def kraus (p : ℝ) : (Fin 1 ⊕ Fin n) → Matrix (Fin n ⊕ Fin 1) (Fin n) ℂ
  | Sum.inl _ => (Real.sqrt (1 - p) : ℂ) • erasureEmbed
  | Sum.inr k => (Real.sqrt p : ℂ) • Matrix.single (Sum.inr (0 : Fin 1)) k 1

private theorem sqrt_conjugation {i j : Type*} [Fintype i] [Fintype j]
    (w : ℝ) (hw : 0 ≤ w) (A : Matrix i j ℂ) (X : Matrix j j ℂ) :
    ((Real.sqrt w : ℂ) • A) * X * ((Real.sqrt w : ℂ) • A).conjTranspose =
      (w : ℂ) • (A * X * A.conjTranspose) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul]
  congr 1
  simp [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt hw]

theorem kraus_apply (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (X : CMatrix (Fin n)) :
    MatrixMap.ofKraus (kraus (n := n) p) X = (Channel.erasure n p hp0 hp1).map X := by
  rw [erasure_apply]
  change (∑ k : Fin 1 ⊕ Fin n, kraus p k * X * (kraus p k).conjTranspose) = _
  rw [Fintype.sum_sum_type]
  simp only [kraus, sqrt_conjugation _ (sub_nonneg.mpr hp1), sqrt_conjugation _ hp0,
    erasureEmbed_conj_mul, erasureFlag_conj_mul, Fin.sum_univ_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.trace,
    Fin.eq_zero, ← Finset.mul_sum]

end Erasure

/-- The specified environment is a Kraus complement, including at `p = 0,1`. -/
theorem erasure_isComplementOf (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel.IsComplementOf (Channel.erasureComplement n p hp0 hp1)
      (Channel.erasure n p hp0 hp1) := by
  refine ⟨Erasure.kraus p, ?_, ?_⟩
  · exact LinearMap.ext (fun X ↦ (Erasure.kraus_apply p hp0 hp1 X).symm)
  · apply LinearMap.ext
    intro X
    rw [erasureComplement_apply]
    ext i j
    change _ = ((Erasure.kraus p i) * X * (Erasure.kraus p j).conjTranspose).trace
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [Erasure.kraus, Matrix.conjTranspose_smul, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul, Matrix.trace_smul]
    · simp [← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt (sub_nonneg.mpr hp1),
        erasureEmbed_conj_mul, Matrix.trace_fromBlocks_diagonal, Fin.eq_zero]
    · simp [Matrix.trace, Matrix.mul_apply, erasureEmbed, Fintype.sum_sum_type,
        Matrix.single_apply]
    · simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, erasureEmbed,
        Fintype.sum_sum_type, Matrix.single_apply, Finset.sum_mul]
    · simp [Matrix.trace, Fin.eq_zero, ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt hp0]

/-- Retain Eve's signal with probability `(1-p)/p`; keep or prepare the erasure flag. -/
def Channel.erasureSimulator (n : ℕ) (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    Channel (Fin 1 ⊕ Fin n) (Fin n ⊕ Fin 1) :=
  (Channel.convexCombination ((1 - p) / p) (Channel.idChannel (Fin n ⊕ Fin 1))
    (Erasure.flagChannel (Fin n ⊕ Fin 1))
    (div_nonneg (sub_nonneg.mpr hp1) (by linarith))
    ((div_le_one (by linarith : 0 < p)).mpr (by linarith))).comp Channel.sumSwapInv

theorem erasure_antidegradable (n : ℕ) (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p ≤ 1)
    (X : CMatrix (Fin n)) :
    (Channel.erasureSimulator n p hp0 hp1).map
        ((Channel.erasureComplement n p (by linarith) hp1).map X) =
      (Channel.erasure n p (by linarith) hp1).map X := by
  let Y := (Channel.erasure n (1 - p) (sub_nonneg.mpr hp1) (by linarith)).map X
  have ht : Y.trace = X.trace := (Channel.erasure n (1 - p) _ _).tracePreserving X
  change (((1 - p) / p : ℝ) : ℂ) • (Channel.idChannel (Fin n ⊕ Fin 1)).map
      (Channel.sumSwapInv.map (Channel.sumSwap.map Y)) +
    ((1 - (1 - p) / p : ℝ) : ℂ) • (Erasure.flagChannel (Fin n ⊕ Fin 1)).map
      (Channel.sumSwapInv.map (Channel.sumSwap.map Y)) = _
  rw [sumSwapInv_map_sumSwap_map, Erasure.flagChannel_apply, ht]
  simp only [Channel.idChannel, MatrixMap.ofKraus, Fintype.sum_unique,
    Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  dsimp [Y]
  rw [erasure_apply, erasure_apply]
  have hpc : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp [Fin.eq_zero]
  all_goals field_simp [hpc]
  all_goals ring

/-- Zero regularized private capacity at every erasure probability at least one half. -/
theorem erasure_privateCapacity_eq_zero (n : ℕ) (p : ℝ)
    (hp0 : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    Channel.privateCapacity (Channel.erasure n p (by linarith) hp1)
      (Channel.erasureComplement n p (by linarith) hp1) = 0 :=
  Channel.privateCapacity_eq_zero_of_antidegradable _ _
    (Channel.erasureSimulator n p hp0 hp1) (erasure_antidegradable n p hp0 hp1)

end
end QIT
