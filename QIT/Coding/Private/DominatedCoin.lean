/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module
public import QIT.Coding.Private.BinaryHolevo

/-!
# The classical coin lemma for domination constant c ≥ 3

The prior of the weak letter is 1/4. All statements include t = 0 and t = 1/2.
The proof constructs a genuine preparation channel and does not assume commuting states.
-/

@[expose] public section
open scoped ComplexOrder MatrixOrder NNReal
namespace QIT.DominatedCoin
noncomputable section

def bias (c s : ℝ) : ℝ := (1 + (c - 1) * s) / c

theorem bias_pos (c : ℝ) (hc : 3 ≤ c) (s : ℝ) (hs : 0 ≤ s) : 0 < bias c s := by
  apply div_pos _ (by linarith)
  nlinarith [mul_nonneg (show 0 ≤ c - 1 by linarith) hs]

theorem bias_lt_one (c : ℝ) (hc : 3 ≤ c) (s : ℝ) (hs : s < 1) : bias c s < 1 := by
  apply (div_lt_one (by linarith : 0 < c)).mpr
  nlinarith [mul_pos (show 0 < c - 1 by linarith) (sub_pos.mpr hs)]

private theorem bias_deriv (c s : ℝ) : HasDerivAt (bias c) ((c - 1) / c) s := by
  convert ((hasDerivAt_id s).const_mul (c - 1) |>.const_add 1).div_const c using 1
  simp

private def corrected (c s : ℝ) : ℝ := Real.binEntropy (bias c s) + (c - 1) * s ^ 2 / 2

private def correctedDeriv (c s : ℝ) : ℝ :=
  (c - 1) / c * (Real.log (1 - bias c s) - Real.log (bias c s)) + (c - 1) * s

private theorem corrected_hasDerivAt (c : ℝ) (hc : 3 ≤ c)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt (corrected c) (correctedDeriv c s) s := by
  have hb := (Real.hasDerivAt_binEntropy (bias_pos c hc s hs0).ne'
    (bias_lt_one c hc s hs1).ne).comp s (bias_deriv c s)
  convert hb.add (((hasDerivAt_id s).pow 2).const_mul (c - 1) |>.div_const 2) using 1
  dsimp [corrected, correctedDeriv]
  ring

private theorem correctedDeriv_hasDerivAt (c : ℝ) (hc : 3 ≤ c)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt (correctedDeriv c)
      ((c - 1) - (c - 1) / ((1 + (c - 1) * s) * (1 - s))) s := by
  have h0 := (bias_pos c hc s hs0).ne'
  have h1 := (sub_pos.mpr (bias_lt_one c hc s hs1)).ne'
  have h := (((bias_deriv c s).const_sub 1).log h1).sub ((bias_deriv c s).log h0)
  convert (h.const_mul ((c - 1) / c)).add ((hasDerivAt_id s).const_mul (c - 1)) using 1
  dsimp [bias]
  have hc0 : c ≠ 0 := by linarith
  have hc1 : c - 1 ≠ 0 := by linarith
  have hd0 : 1 + (c - 1) * s ≠ 0 := by
    have := mul_nonneg (show 0 ≤ c - 1 by linarith) hs0
    linarith
  have hd1 : 1 - s ≠ 0 := (sub_pos.mpr hs1).ne'
  rw [show 1 - (1 + (c - 1) * s) / c = (c - 1) * (1 - s) / c by
    field_simp; ring]
  field_simp [hc0, hc1, hd0, hd1]
  ring

private theorem corrected_convex (c : ℝ) (hc : 3 ≤ c) :
    ConvexOn ℝ (Set.Icc 0 (1 / 2)) (corrected c) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := correctedDeriv c)
    (f'' := fun s ↦ (c - 1) - (c - 1) / ((1 + (c - 1) * s) * (1 - s))) (convex_Icc _ _)
  · exact (Real.binEntropy_continuous.comp (by unfold bias; fun_prop)).continuousOn.add
      (by fun_prop : ContinuousOn (fun s : ℝ ↦ (c - 1) * s ^ 2 / 2) _)
  · intro s hs
    rw [interior_Icc] at hs
    exact (corrected_hasDerivAt c hc s hs.1.le (by linarith [hs.2])).hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact (correctedDeriv_hasDerivAt c hc s hs.1.le (by linarith [hs.2])).hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have hi : 0 ≤ (c - 2) - (c - 1) * s := by
      nlinarith [mul_nonneg (show 0 ≤ c - 1 by linarith) (show 0 ≤ 1 / 2 - s by linarith [hs.2])]
    have hd : 1 ≤ (1 + (c - 1) * s) * (1 - s) := by
      nlinarith [mul_nonneg hs.1.le hi]
    have h := (div_le_iff₀ (by linarith : 0 < (1 + (c - 1) * s) * (1 - s))).mpr
      (show c - 1 ≤ (c - 1) * ((1 + (c - 1) * s) * (1 - s)) by
        nlinarith [mul_nonneg (show 0 ≤ c - 1 by linarith) (sub_nonneg.mpr hd)])
    linarith

/-- The weighted Jensen gap in the manuscript's classical coin lemma. -/
theorem entropy_bound (c : ℝ) (hc : 3 ≤ c) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    binaryEntropyBits (bias c (t / 4)) - (3 / 4) * binaryEntropyBits (bias c 0) -
        binaryEntropyBits (bias c t) / 4 ≤ 3 * (c - 1) * t ^ 2 / (32 * Real.log 2) := by
  have h := (corrected_convex c hc).2 (show (0 : ℝ) ∈ Set.Icc 0 (1 / 2) by norm_num)
    (show t ∈ Set.Icc 0 (1 / 2) from ⟨ht0, ht1⟩)
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (3 / 4 : ℝ) + 1 / 4 = 1)
  simp only [smul_eq_mul, mul_zero, zero_add] at h
  have hn : Real.binEntropy (bias c (t / 4)) - (3 / 4) * Real.binEntropy (bias c 0) -
      Real.binEntropy (bias c t) / 4 ≤ 3 * (c - 1) * t ^ 2 / 32 := by
    dsimp [corrected] at h
    rw [show (1 / 4 : ℝ) * t = t / 4 by ring] at h
    nlinarith
  rw [binaryEntropyBits_eq_binEntropy_div_log_two (bias_pos c hc _ (by positivity)).le
      (bias_lt_one c hc _ (by linarith)).le,
    binaryEntropyBits_eq_binEntropy_div_log_two (bias_pos c hc 0 (by norm_num)).le
      (bias_lt_one c hc 0 (by norm_num)).le,
    binaryEntropyBits_eq_binEntropy_div_log_two (bias_pos c hc t ht0).le
      (bias_lt_one c hc t (by linarith)).le]
  convert div_le_div_of_nonneg_right hn (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    using 1 <;> ring

universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

def preparingChannel (c : ℝ) (hc : 3 ≤ c) (base signal : State a)
    (horder : ((1 / c : ℝ) : ℂ) • signal.matrix ≤ base.matrix) : Channel Bool a :=
  Channel.prepare fun b ↦ if b then signal else
    BinaryPreparation.residual base signal (1 / c)
      ((div_lt_one (by linarith : 0 < c)).mpr (by linarith)) horder

theorem preparingChannel_bias (c : ℝ) (hc : 3 ≤ c) (base signal : State a)
    (horder : ((1 / c : ℝ) : ℂ) • signal.matrix ≤ base.matrix)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (preparingChannel c hc base signal horder).map
        (BinaryPreparation.bernoulliState (bias c s) (bias_pos c hc s hs0).le
          (bias_lt_one c hc s hs1).le).matrix =
      ((1 - s : ℝ) : ℂ) • base.matrix + (s : ℂ) • signal.matrix := by
  rw [BinaryPreparation.bernoulliState_matrix]
  simp only [preparingChannel, Channel.prepare_map, Matrix.diagonal_apply_eq,
    Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  have h := BinaryPreparation.residual_reconstruct base signal (1 / c)
    ((div_lt_one (by linarith : 0 < c)).mpr (by linarith)) horder
  ext i j
  have he := congrFun (congrFun h i) j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_div] at he ⊢
  simp only [bias, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_sub, Complex.ofReal_one]
  have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  linear_combination (norm := (field_simp [hcc]; ring)) (1 - (s : ℂ)) * he

def sourceEnsemble (c : ℝ) (hc : 3 ≤ c) (E : Ensemble Bool a) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Ensemble Bool Bool where
  probs := E.probs
  weights_sum := E.weights_sum
  states x := BinaryPreparation.bernoulliState (bias c (if x then t else 0))
    (bias_pos c hc _ (by cases x <;> simp [ht0])).le
    (bias_lt_one c hc _ (by cases x <;> simp [ht1])).le

private theorem quarter_false (E : Ensemble Bool a) (hq : (E.probs true : ℝ) = 1 / 4) :
    (E.probs false : ℝ) = 3 / 4 := by
  have h := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) E.weights_sum
  simp only [Fintype.sum_bool, NNReal.coe_add, NNReal.coe_one, hq] at h
  linarith

theorem sourceEnsemble_average (c : ℝ) (hc : 3 ≤ c) (E : Ensemble Bool a)
    (hq : (E.probs true : ℝ) = 1 / 4) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (sourceEnsemble c hc E t ht0 ht1).averageState =
      BinaryPreparation.bernoulliState (bias c (t / 4)) (bias_pos c hc _ (by positivity)).le
        (bias_lt_one c hc _ (by linarith)).le := by
  have hqC : (E.probs true : ℂ) = (1 / 4 : ℂ) := by
    simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) hq
  have hqC' : (E.probs false : ℂ) = (3 / 4 : ℂ) := by
    simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) (quarter_false E hq)
  apply State.ext
  rw [Ensemble.averageState_matrix, Fintype.sum_bool]
  simp only [sourceEnsemble, BinaryPreparation.bernoulliState_matrix, ↓reduceIte]
  ext b c
  cases b <;> cases c <;>
    simp [Matrix.smul_apply, NNReal.smul_def, Complex.real_smul, hqC, hqC', bias,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  all_goals ring

theorem sourceEnsemble_information (c : ℝ) (hc : 3 ≤ c) (E : Ensemble Bool a)
    (hq : (E.probs true : ℝ) = 1 / 4) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (sourceEnsemble c hc E t ht0 ht1).holevoInformation =
      binaryEntropyBits (bias c (t / 4)) - (3 / 4) * binaryEntropyBits (bias c 0) -
        binaryEntropyBits (bias c t) / 4 := by
  rw [Ensemble.holevoInformation_def, sourceEnsemble_average c hc E hq t ht0 ht1,
    BinaryPreparation.bernoulliState_entropy, Fintype.sum_bool]
  simp only [sourceEnsemble, BinaryPreparation.bernoulliState_entropy, hq,
    quarter_false E hq, Bool.false_eq_true, ↓reduceIte]
  ring

/-- Data processing from the virtual coin, without any commutativity hypothesis. -/
theorem holevo_le_source (c : ℝ) (hc : 3 ≤ c) (E : Ensemble Bool a) (base signal : State a)
    (horder : ((1 / c : ℝ) : ℂ) • signal.matrix ≤ base.matrix)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (h0 : (E.states false).matrix = base.matrix)
    (h1 : (E.states true).matrix = ((1 - t : ℝ) : ℂ) • base.matrix +
      (t : ℂ) • signal.matrix) :
    E.holevoInformation ≤ (sourceEnsemble c hc E t ht0 ht1).holevoInformation := by
  have hstates : ∀ x, (preparingChannel c hc base signal horder).applyState
      ((sourceEnsemble c hc E t ht0 ht1).states x) = E.states x := by
    intro x
    apply State.ext
    simp only [Channel.applyState, sourceEnsemble]
    rw [preparingChannel_bias c hc base signal horder (if x then t else 0)
      (by cases x <;> simp [ht0]) (by cases x <;> simp [ht1])]
    cases x
    · simpa using h0.symm
    · exact h1.symm
  have heq : (preparingChannel c hc base signal horder).outputEnsemble
      (sourceEnsemble c hc E t ht0 ht1) = E := by
    cases E
    simp only [Channel.outputEnsemble, sourceEnsemble] at hstates ⊢
    simp only [hstates]
  rw [← heq]
  exact Ensemble.holevoInformation_outputEnsemble_le _ _

/-- Full quantum leakage bound for a weak letter with prior 1/4. -/
theorem holevo_quadratic_bound (c : ℝ) (hc : 3 ≤ c) (E : Ensemble Bool a) (base signal : State a)
    (hq : (E.probs true : ℝ) = 1 / 4)
    (horder : ((1 / c : ℝ) : ℂ) • signal.matrix ≤ base.matrix)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (h0 : (E.states false).matrix = base.matrix)
    (h1 : (E.states true).matrix = ((1 - t : ℝ) : ℂ) • base.matrix +
      (t : ℂ) • signal.matrix) :
    E.holevoInformation ≤ 3 * (c - 1) * t ^ 2 / (32 * Real.log 2) := by
  have h := holevo_le_source c hc E base signal horder t ht0 (by linarith) h0 h1
  rw [sourceEnsemble_information c hc E hq] at h
  exact h.trans (entropy_bound c hc t ht0 ht1)


private theorem measured_entropy (F : CMatrix a) (hF : F.PosSemidef) (hF1 : F ≤ 1)
    (rho : State a) (c : ℝ) (hc : (rho.matrix * F).trace = (c : ℂ)) :
    ((Channel.measure (POVM.binaryOfEffect F hF hF1)).applyState rho).vonNeumann =
      binaryEntropyBits c := by
  have hd : ((Channel.measure (POVM.binaryOfEffect F hF hF1)).applyState rho).matrix =
      Matrix.diagonal (fun b : Bool ↦ ((if b then c else 1 - c : ℝ) : ℂ)) := by
    change (Channel.measure (POVM.binaryOfEffect F hF hF1)).map rho.matrix = _
    rw [Channel.measure_map_state_diagonal]
    congr 1
    funext b
    cases b <;> simp [POVM.binaryOfEffect, Matrix.mul_sub, Matrix.trace_sub, hc,
      rho.trace_eq_one]
  rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal _ _ hd]
  simp [binaryEntropyBits]
  ring

/-- The exact classical information of the fixed binary measurement for prior 1/4. -/
theorem quarter_measurement_information (E : Ensemble Bool a)
    (hq : (E.probs true : ℝ) = 1 / 4) (c : ℝ)
    (F : CMatrix a) (hF : F.PosSemidef) (hF1 : F ≤ 1)
    (h0 : ((E.states false).matrix * F).trace = 0)
    (h1 : ((E.states true).matrix * F).trace = (c : ℂ)) :
    ((Channel.measure (POVM.binaryOfEffect F hF hF1)).outputEnsemble E).holevoInformation =
      binaryEntropyBits (c / 4) - binaryEntropyBits c / 4 := by
  let D := Channel.measure (POVM.binaryOfEffect F hF hF1)
  have hm : (D.outputEnsemble E).averageState = D.applyState E.averageState := by
    apply State.ext
    change (∑ x, (E.probs x) • D.map (E.states x).matrix) =
      D.map (∑ x, (E.probs x) • (E.states x).matrix)
    simp only [NNReal.smul_def, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact ((D.map.restrictScalars ℝ).map_smul (E.probs x : ℝ) (E.states x).matrix).symm
  have hqC : (E.probs true : ℂ) = (1 / 4 : ℂ) := by
    simpa using congrArg (fun r : ℝ ↦ (r : ℂ)) hq
  have hav : (E.averageState.matrix * F).trace = ((c / 4 : ℝ) : ℂ) := by
    rw [Ensemble.averageState_matrix, Fintype.sum_bool, Matrix.add_mul, Matrix.trace_add]
    simp only [NNReal.smul_def, Complex.real_smul, Matrix.smul_mul, Matrix.trace_smul,
      h0, h1, mul_zero, add_zero, hqC, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have havEntropy : (D.outputEnsemble E).averageState.vonNeumann = binaryEntropyBits (c / 4) := by
    rw [hm]
    exact measured_entropy F hF hF1 E.averageState (c / 4) hav
  have hs0 : (D.applyState (E.states false)).vonNeumann = 0 := by
    have h := measured_entropy F hF hF1 (E.states false) 0 (by simpa using h0)
    simpa [D, binaryEntropyBits, xlog2, log2] using h
  have hs1 : (D.applyState (E.states true)).vonNeumann = binaryEntropyBits c :=
    measured_entropy F hF hF1 (E.states true) c h1
  change (D.outputEnsemble E).holevoInformation = _
  rw [Ensemble.holevoInformation_def, havEntropy, Fintype.sum_bool]
  change _ - ((E.probs true : ℝ) * (D.applyState (E.states true)).vonNeumann +
    (E.probs false : ℝ) * (D.applyState (E.states false)).vonNeumann) = _
  rw [hs0, hs1, hq]
  ring

end
end QIT.DominatedCoin
