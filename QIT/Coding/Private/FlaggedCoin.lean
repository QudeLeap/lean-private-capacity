/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module
public import QIT.Coding.Private.DominatedCoin

/-! # A full flagged environment prepared from two classical coins

The flag distribution is independent of the encoded letter. This retains both
physical environment branches and their different domination constants.
-/

@[expose] public section
open scoped ComplexOrder MatrixOrder NNReal
namespace QIT.FlaggedCoin
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]
open DominatedCoin

def flagState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r : Bool → ℝ) (hr0 : ∀ b, 0 ≤ r b) (hr1 : ∀ b, r b ≤ 1) : State (Bool × Bool) :=
  (Ensemble.cqState {
    probs := fun b : Bool ↦ if b then ⟨p, hp0⟩ else ⟨1 - p, sub_nonneg.mpr hp1⟩
    weights_sum := by
      rw [Fintype.sum_bool]
      apply NNReal.eq
      change p + (1 - p) = 1
      ring
    states := fun b ↦ BinaryPreparation.bernoulliState (r b) (hr0 b) (hr1 b) })

theorem flagState_matrix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r : Bool → ℝ) (hr0 : ∀ b, 0 ≤ r b) (hr1 : ∀ b, r b ≤ 1) :
    (flagState p hp0 hp1 r hr0 hr1).matrix = Matrix.diagonal
      (fun x ↦ (((if x.1 then p else 1 - p) * (if x.2 then r x.1 else 1 - r x.1) : ℝ) : ℂ)) := by
  ext ⟨b, s⟩ ⟨c, t⟩
  cases b <;> cases s <;> cases c <;> cases t <;>
    simp [flagState, Ensemble.cqState_matrix, BinaryPreparation.bernoulliState_matrix,
      Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.smul_apply,
      NNReal.smul_def, Complex.real_smul]
  all_goals first | exact Or.inl (Complex.ofReal_sub 1 p) | exact Or.inl rfl

theorem flagState_entropy (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r : Bool → ℝ) (hr0 : ∀ b, 0 ≤ r b) (hr1 : ∀ b, r b ≤ 1) :
    (flagState p hp0 hp1 r hr0 hr1).vonNeumann = binaryEntropyBits p +
      p * binaryEntropyBits (r true) + (1 - p) * binaryEntropyBits (r false) := by
  unfold flagState
  rw [State.cqState_vonNeumann]
  simp only [Fintype.sum_bool, BinaryPreparation.bernoulliState_entropy,
    Bool.false_eq_true, ↓reduceIte]
  change -(xlog2 p + xlog2 (1 - p)) +
    (p * binaryEntropyBits (r true) + (1 - p) * binaryEntropyBits (r false)) = _
  unfold binaryEntropyBits
  ring

def sourceEnsemble (E : Ensemble Bool a) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (c : Bool → ℝ) (hc : ∀ b, 3 ≤ c b) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Ensemble Bool (Bool × Bool) where
  probs := E.probs
  weights_sum := E.weights_sum
  states x := flagState p hp0 hp1 (fun b ↦ bias (c b) (if x then t else 0))
    (fun b ↦ (bias_pos (c b) (hc b) _ (by cases x <;> simp [ht0])).le)
    (fun b ↦ (bias_lt_one (c b) (hc b) _ (by cases x <;> simp [ht1])).le)

private theorem quarter_false (E : Ensemble Bool a) (hq : (E.probs true : ℝ) = 1 / 4) :
    (E.probs false : ℝ) = 3 / 4 := by
  have h := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) E.weights_sum
  simp only [Fintype.sum_bool, NNReal.coe_add, NNReal.coe_one, hq] at h
  linarith

theorem sourceEnsemble_average (E : Ensemble Bool a) (hq : (E.probs true : ℝ) = 1 / 4)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : Bool → ℝ) (hc : ∀ b, 3 ≤ c b)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (sourceEnsemble E p hp0 hp1 c hc t ht0 ht1).averageState =
      flagState p hp0 hp1 (fun b ↦ bias (c b) (t / 4))
        (fun b ↦ (bias_pos (c b) (hc b) _ (by positivity)).le)
        (fun b ↦ (bias_lt_one (c b) (hc b) _ (by linarith)).le) := by
  have hqC : (E.probs true : ℂ) = (1 / 4 : ℂ) := by
    simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) hq
  have hqC' : (E.probs false : ℂ) = (3 / 4 : ℂ) := by
    simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) (quarter_false E hq)
  apply State.ext
  rw [Ensemble.averageState_matrix, Fintype.sum_bool]
  simp only [sourceEnsemble, flagState_matrix]
  ext ⟨b, s⟩ ⟨d, v⟩
  cases b <;> cases s <;> cases d <;> cases v <;>
    simp [Matrix.smul_apply, NNReal.smul_def, Complex.real_smul, hqC, hqC', bias,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  all_goals ring

theorem sourceEnsemble_information (E : Ensemble Bool a) (hq : (E.probs true : ℝ) = 1 / 4)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (c : Bool → ℝ) (hc : ∀ b, 3 ≤ c b)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (sourceEnsemble E p hp0 hp1 c hc t ht0 ht1).holevoInformation =
      p * (binaryEntropyBits (bias (c true) (t / 4)) -
        (3 / 4) * binaryEntropyBits (bias (c true) 0) - binaryEntropyBits (bias (c true) t) / 4) +
      (1 - p) * (binaryEntropyBits (bias (c false) (t / 4)) -
        (3 / 4) * binaryEntropyBits (bias (c false) 0) - binaryEntropyBits (bias (c false) t) / 4) := by
  rw [Ensemble.holevoInformation_def, sourceEnsemble_average E hq,
    flagState_entropy, Fintype.sum_bool]
  simp only [sourceEnsemble, flagState_entropy, hq, quarter_false E hq,
    Bool.false_eq_true, ↓reduceIte]
  ring

def preparingChannel (c : Bool → ℝ) (hc : ∀ b, 3 ≤ c b) (base signal : Bool → State a)
    (horder : ∀ b, ((1 / c b : ℝ) : ℂ) • (signal b).matrix ≤ (base b).matrix) :
    Channel (Bool × Bool) a := Channel.prepare fun x ↦ if x.2 then signal x.1 else
      BinaryPreparation.residual (base x.1) (signal x.1) (1 / c x.1)
        ((div_lt_one (by linarith [hc x.1] : 0 < c x.1)).mpr (by linarith [hc x.1])) (horder x.1)

theorem preparingChannel_bias (c : Bool → ℝ) (hc : ∀ b, 3 ≤ c b) (base signal : Bool → State a)
    (horder : ∀ b, ((1 / c b : ℝ) : ℂ) • (signal b).matrix ≤ (base b).matrix)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (preparingChannel c hc base signal horder).map
      (flagState p hp0 hp1 (fun b ↦ bias (c b) s)
        (fun b ↦ (bias_pos (c b) (hc b) s hs0).le)
        (fun b ↦ (bias_lt_one (c b) (hc b) s hs1).le)).matrix =
      (p : ℂ) • (((1 - s : ℝ) : ℂ) • (base true).matrix + (s : ℂ) • (signal true).matrix) +
      ((1 - p : ℝ) : ℂ) •
        (((1 - s : ℝ) : ℂ) • (base false).matrix + (s : ℂ) • (signal false).matrix) := by
  have he : (preparingChannel c hc base signal horder).map
      (flagState p hp0 hp1 (fun b ↦ bias (c b) s)
        (fun b ↦ (bias_pos (c b) (hc b) s hs0).le)
        (fun b ↦ (bias_lt_one (c b) (hc b) s hs1).le)).matrix =
      (p : ℂ) • ((DominatedCoin.preparingChannel (c true) (hc true) (base true) (signal true) (horder true)).map
        (BinaryPreparation.bernoulliState (bias (c true) s) (bias_pos _ (hc true) _ hs0).le
          (bias_lt_one _ (hc true) _ hs1).le).matrix) +
      ((1 - p : ℝ) : ℂ) •
        ((DominatedCoin.preparingChannel (c false) (hc false) (base false) (signal false) (horder false)).map
        (BinaryPreparation.bernoulliState (bias (c false) s) (bias_pos _ (hc false) _ hs0).le
          (bias_lt_one _ (hc false) _ hs1).le).matrix) := by
    rw [flagState_matrix]
    simp only [preparingChannel, Channel.prepare_map, Matrix.diagonal_apply_eq,
      Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
      DominatedCoin.preparingChannel, BinaryPreparation.bernoulliState_matrix]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  rw [he, DominatedCoin.preparingChannel_bias (c true) (hc true) (base true) (signal true)
    (horder true) s hs0 hs1, DominatedCoin.preparingChannel_bias (c false) (hc false)
    (base false) (signal false) (horder false) s hs0 hs1]

/-- Both flagged branches are included in this bound; the output states need not commute. -/
theorem holevo_bound (E : Ensemble Bool a) (hq : (E.probs true : ℝ) = 1 / 4)
    (c : Bool → ℝ) (hc : ∀ b, 3 ≤ c b) (base signal : Bool → State a)
    (horder : ∀ b, ((1 / c b : ℝ) : ℂ) • (signal b).matrix ≤ (base b).matrix)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (h0 : (E.states false).matrix = (p : ℂ) • (base true).matrix +
      ((1 - p : ℝ) : ℂ) • (base false).matrix)
    (h1 : (E.states true).matrix =
      (p : ℂ) • (((1 - t : ℝ) : ℂ) • (base true).matrix + (t : ℂ) • (signal true).matrix) +
      ((1 - p : ℝ) : ℂ) •
        (((1 - t : ℝ) : ℂ) • (base false).matrix + (t : ℂ) • (signal false).matrix)) :
    E.holevoInformation ≤
      3 * (p * (c true - 1) + (1 - p) * (c false - 1)) * t ^ 2 / (32 * Real.log 2) := by
  have ht : t < 1 := by linarith
  let F := sourceEnsemble E p hp0 hp1 c hc t ht0 ht
  let D := preparingChannel c hc base signal horder
  have hs : ∀ x, D.applyState (F.states x) = E.states x := by
    intro x
    apply State.ext
    change D.map (F.states x).matrix = _
    dsimp [D, F, sourceEnsemble]
    rw [preparingChannel_bias c hc base signal horder p hp0 hp1 (if x then t else 0)
      (by cases x <;> simp [ht0]) (by cases x <;> simp [ht])]
    cases x
    · simpa using h0.symm
    · exact h1.symm
  have he : D.outputEnsemble F = E := by
    cases E
    simp only [Channel.outputEnsemble, F, sourceEnsemble] at hs ⊢
    simp only [hs]
  have h := Ensemble.holevoInformation_outputEnsemble_le D F
  rw [he] at h
  have hsource := sourceEnsemble_information E hq p hp0 hp1 c hc t ht0 ht
  change F.holevoInformation = _ at hsource
  rw [hsource] at h
  have hT := mul_le_mul_of_nonneg_left (entropy_bound (c true) (hc true) t ht0 ht1) hp0
  have hF := mul_le_mul_of_nonneg_left (entropy_bound (c false) (hc false) t ht0 ht1)
    (sub_nonneg.mpr hp1)
  calc E.holevoInformation ≤ _ := h
    _ ≤ _ := add_le_add hT hF
    _ = _ := by ring

end
end QIT.FlaggedCoin
