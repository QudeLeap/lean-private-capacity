/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.Basic

/-!
# Finite bounds and the one-use capacity lower bound

These lemmas justify both uses of the real supremum in paper eq:capacities.
The optimized value sets are bounded above. Tensor-power one retains a unit
register, so the one-use ensemble is transported explicitly before taking
its block rate. This is an information-formula result; no operational
private coding theorem is asserted here.
-/

@[expose] public section

namespace QIT

noncomputable section
universe u v w x
variable {a : Type u} {b : Type v} {e : Type w} {ι : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype e] [DecidableEq e] [Fintype ι] [DecidableEq ι]

/-- Holevo information is nonnegative by the cq mutual-information identity. -/
theorem Ensemble.holevoInformation_nonneg (E : Ensemble ι a) : 0 ≤ E.holevoInformation := by
  rw [Ensemble.holevoInformation_eq_mutualInformation_cqState]
  exact State.mutualInformation_nonneg E.cqState

/-- Private information cannot exceed the receiver log dimension. -/
theorem Channel.privateInformationWith_le_log_card
    (N : Channel a b) (Nc : Channel a e) (E : Ensemble ι a) :
    N.privateInformationWith Nc E ≤ log2 (Fintype.card b) := by
  exact (sub_le_self _ (Ensemble.holevoInformation_nonneg (Nc.outputEnsemble E))).trans
    (N.outputEnsemble E).holevo_le_log_card

/-- The one-use private-information value set is bounded above. -/
theorem Channel.privateInformationValues_bddAbove (N : Channel a b) (Nc : Channel a e) :
    BddAbove (Channel.privateInformationValues.{u, v, w, x} N Nc) := by
  refine ⟨log2 (Fintype.card b), ?_⟩
  rintro r ⟨ι, hF, hD, E, rfl⟩
  letI := hF
  letI := hD
  exact Channel.privateInformationWith_le_log_card N Nc E

/-- The log dimension is nonnegative, including the empty-type convention. -/
private theorem log2_card_nonneg (b : Type*) [Fintype b] : 0 ≤ log2 (Fintype.card b) := by
  by_cases h : Fintype.card b = 0
  · simp [h, log2]
  · apply div_nonneg _ (Real.log_nonneg (by norm_num))
    exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)

/-- The optimized one-use private information has a finite dimension bound. -/
theorem Channel.privateInformation_le_log_card (N : Channel a b) (Nc : Channel a e) :
    Channel.privateInformation.{u, v, w, x} N Nc ≤ log2 (Fintype.card b) := by
  apply Real.sSup_le _ (log2_card_nonneg b)
  rintro r ⟨ι, hF, hD, E, rfl⟩
  letI := hF
  letI := hD
  exact Channel.privateInformationWith_le_log_card N Nc E

/-- Dimension of the recursive tensor-power label type. -/
private theorem tensorPower_card_for_private (α : Type*) [Fintype α] (n : ℕ) :
    Fintype.card (TensorPower α n) = (Fintype.card α) ^ n := by
  induction n with
  | zero => simp [TensorPower]
  | succ n ih =>
    change Fintype.card (α × TensorPower α n) = _
    rw [Fintype.card_prod, ih, pow_succ]
    ring

/-- Every block rate is bounded by the single-use receiver log dimension. -/
theorem Channel.privateCapacityRateValues_bddAbove (N : Channel a b) (Nc : Channel a e) :
    BddAbove (Channel.privateCapacityRateValues.{u, v, w, x} N Nc) := by
  refine ⟨log2 (Fintype.card b), ?_⟩
  rintro R ⟨n, hn, rfl⟩
  apply (div_le_iff₀ (by exact_mod_cast hn)).mpr
  have h := Channel.privateInformation_le_log_card (N.tensorPower n) (Nc.tensorPower n)
  simpa only [Channel.blockPrivateInformation, tensorPower_card_for_private, Nat.cast_pow,
    log2, Real.log_pow, mul_div_assoc, mul_comm] using h

/-- Transport an ensemble to one use with the explicit unit register. -/
def Ensemble.tensorPowerOne (E : Ensemble ι a) : Ensemble ι (TensorPower a 1) where
  probs := E.probs
  weights_sum := E.weights_sum
  states := fun x ↦ (E.states x).tensorPower 1

omit [DecidableEq ι] in
/-- The unit-register transport commutes with averaging. -/
theorem Ensemble.tensorPowerOne_averageState (E : Ensemble ι a) :
    (Ensemble.tensorPowerOne E).averageState = E.averageState.tensorPower 1 := by
  apply State.ext
  ext i j
  rcases i with ⟨i, unitA⟩
  rcases j with ⟨j, unitB⟩
  change (∑ x, (E.probs x) • Matrix.kronecker (E.states x).matrix
      (1 : CMatrix PUnit.{u + 1})) (i, unitA) (j, unitB) =
    Matrix.kronecker (∑ x, (E.probs x) • (E.states x).matrix)
      (1 : CMatrix PUnit.{u + 1}) (i, unitA) (j, unitB)
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.kroneckerMap_apply,
    Matrix.kronecker, smul_mul_assoc, Finset.sum_mul]


omit [DecidableEq ι] in
/-- A unit register leaves the Holevo information unchanged. -/
theorem Ensemble.tensorPowerOne_holevoInformation (E : Ensemble ι a) :
    (Ensemble.tensorPowerOne E).holevoInformation = E.holevoInformation := by
  rw [Ensemble.holevoInformation_def, Ensemble.tensorPowerOne_averageState,
    Ensemble.holevoInformation_def]
  simp only [Ensemble.tensorPowerOne, State.vonNeumann_tensorPower, Nat.cast_one, one_mul]

/-- Applying one channel use commutes with the unit-register transport. -/
theorem Channel.outputEnsemble_tensorPowerOne (N : Channel a b) (E : Ensemble ι a) :
    (N.tensorPower 1).outputEnsemble (Ensemble.tensorPowerOne E) =
      Ensemble.tensorPowerOne (N.outputEnsemble E) := by
  have h (ρ : State a) : (N.tensorPower 1).applyState (ρ.tensorPower 1) =
      (N.applyState ρ).tensorPower 1 := by
    change (N.prod (Channel.unit : Channel PUnit.{u + 1} PUnit.{v + 1})).applyState
      (ρ.prod (State.unit : State PUnit.{u + 1})) =
        (N.applyState ρ).prod (State.unit : State PUnit.{v + 1})
    rw [Channel.applyState_prod N Channel.unit ρ State.unit]
    rfl
  unfold Channel.outputEnsemble Ensemble.tensorPowerOne
  simp only [h]

/-- Any finite one-use ensemble lower-bounds the regularized information formula. -/
theorem Channel.privateInformationWith_le_privateCapacity
    (N : Channel a b) (Nc : Channel a e) (E : Ensemble ι a) :
    N.privateInformationWith Nc E ≤ Channel.privateCapacity.{u, v, w, x} N Nc := by
  have hinfo : (N.tensorPower 1).privateInformationWith (Nc.tensorPower 1)
      (Ensemble.tensorPowerOne E) = N.privateInformationWith Nc E := by
    simp only [Channel.privateInformationWith, Channel.outputEnsemble_tensorPowerOne,
      Ensemble.tensorPowerOne_holevoInformation]
  have hle : N.privateInformationWith Nc E ≤
      Channel.blockPrivateInformation.{u, v, w, x} N Nc 1 := by
    rw [← hinfo]
    exact le_csSup (Channel.privateInformationValues_bddAbove (N.tensorPower 1) (Nc.tensorPower 1))
      ⟨ι, inferInstance, inferInstance, Ensemble.tensorPowerOne E, rfl⟩
  apply hle.trans
  apply le_csSup (Channel.privateCapacityRateValues_bddAbove N Nc)
  exact ⟨1, by omega, by simp⟩

end

end QIT
