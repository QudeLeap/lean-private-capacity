/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.RareSignal
public import QIT.Classical.Bridge
public import Mathlib.Analysis.Convex.Deriv

/-!
# Binary measurements and dominated classical preparations

`Ensemble.binary_event_holevo_lower` proves the measurement step of
`eq:receiver-gain`. `BinaryPreparation.holevo_le_source` constructs a genuine
classical preparation of two equally weighted branches from their operator
domination certificates. Together with `binary_preparation_information_upper`,
it proves the half-erasure environmental Holevo bound in Appendix B.3, using entropy
concavity and data processing instead of a separate Donald-identity theorem.
-/

@[expose] public section

open scoped ComplexOrder MatrixOrder
namespace QIT
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

private theorem binary_measure_entropy
    (F : CMatrix a) (hF : F.PosSemidef) (hF1 : F ≤ 1)
    (rho : State a) (p : ℝ) (hp : (rho.matrix * F).trace = (p : ℂ)) :
    ((Channel.measure (POVM.binaryOfEffect F hF hF1)).applyState rho).vonNeumann =
      binaryEntropyBits p := by
  have hdiag : ((Channel.measure (POVM.binaryOfEffect F hF hF1)).applyState rho).matrix =
      Matrix.diagonal (fun b : Bool => ((if b then p else 1 - p : ℝ) : ℂ)) := by
    change (Channel.measure (POVM.binaryOfEffect F hF hF1)).map rho.matrix = _
    rw [Channel.measure_map_state_diagonal]
    congr 1
    funext b
    cases b <;> simp [POVM.binaryOfEffect, Matrix.mul_sub, Matrix.trace_sub, hp,
      rho.trace_eq_one]
  rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal _ _ hdiag]
  simp [binaryEntropyBits]
  ring

theorem Ensemble.binary_event_holevo_lower
    (E : Ensemble Bool a) (q p : ℝ) (hq : (E.probs true : ℝ) = q)
    (F : CMatrix a) (hF : F.PosSemidef) (hF1 : F ≤ 1)
    (h0 : ((E.states false).matrix * F).trace = 0)
    (h1 : ((E.states true).matrix * F).trace = (p : ℂ)) :
    binaryEntropyBits (p * q) - q * binaryEntropyBits p ≤ E.holevoInformation := by
  let D := Channel.measure (POVM.binaryOfEffect F hF hF1)
  have hqC : (E.probs true : ℂ) = (q : ℂ) := by exact_mod_cast hq
  have hm : (D.outputEnsemble E).averageState = D.applyState E.averageState := by
    apply State.ext
    change (∑ x, (E.probs x) • D.map (E.states x).matrix) =
      D.map (∑ x, (E.probs x) • (E.states x).matrix)
    simp only [NNReal.smul_def, map_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact ((D.map.restrictScalars ℝ).map_smul (E.probs x : ℝ) (E.states x).matrix).symm
  have hpmean : (E.averageState.matrix * F).trace = ((p * q : ℝ) : ℂ) := by
    change ((∑ x, (E.probs x) • (E.states x).matrix) * F).trace = _
    rw [Fintype.sum_bool, Matrix.add_mul, Matrix.trace_add]
    simp only [NNReal.smul_def, Complex.real_smul, Matrix.smul_mul, Matrix.trace_smul,
      h0, h1, mul_zero, add_zero]
    rw [hqC, Complex.ofReal_mul]
    ring
  have hmean : (D.outputEnsemble E).averageState.vonNeumann = binaryEntropyBits (p * q) := by
    rw [hm]
    exact binary_measure_entropy F hF hF1 E.averageState (p * q) hpmean
  have hs0 : (D.applyState (E.states false)).vonNeumann = 0 := by
    have h := binary_measure_entropy F hF hF1 (E.states false) 0 (by simpa using h0)
    simpa [D, binaryEntropyBits, xlog2, log2] using h
  have hs1 : (D.applyState (E.states true)).vonNeumann = binaryEntropyBits p :=
    binary_measure_entropy F hF hF1 (E.states true) p h1
  have hchi : (D.outputEnsemble E).holevoInformation =
      binaryEntropyBits (p * q) - q * binaryEntropyBits p := by
    rw [Ensemble.holevoInformation_def, hmean, Fintype.sum_bool]
    change _ - ((E.probs true : ℝ) * (D.applyState (E.states true)).vonNeumann +
      (E.probs false : ℝ) * (D.applyState (E.states false)).vonNeumann) = _
    rw [hs0, hs1, hq]
    ring
  rw [← hchi]
  exact Ensemble.holevoInformation_outputEnsemble_le D E

end
end QIT

namespace QIT
noncomputable section

theorem binary_preparation_information_upper (p q : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    binaryEntropyBits (q + (1 - q) * p) - (1 - q) * binaryEntropyBits p ≤
      q * log2 (1 / p) := by
  let s := q + (1 - q) * p
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs1 : s ≤ 1 := by dsimp [s]; nlinarith
  have hps : p < s := by dsimp [s]; nlinarith
  have hslope := Real.strictConcave_binEntropy.concaveOn.slope_le_of_hasDerivAt
    (show p ∈ Set.Icc 0 1 from ⟨hp0.le, hp1.le⟩)
    (show s ∈ Set.Icc 0 1 from ⟨hs0, hs1⟩) hps
    (Real.hasDerivAt_binEntropy hp0.ne' hp1.ne)
  simp only [slope, smul_eq_mul, ← div_eq_inv_mul] at hslope
  have hn := (div_le_iff₀ (sub_pos.mpr hps)).mp hslope
  have hnat : Real.binEntropy s - (1 - q) * Real.binEntropy p ≤ q * Real.log (1 / p) := by
    simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      Real.negMulLog, one_div, Real.log_inv] at hn ⊢
    dsimp [s] at hn ⊢
    nlinarith
  rw [binaryEntropyBits_eq_binEntropy_div_log_two hs0 hs1,
    binaryEntropyBits_eq_binEntropy_div_log_two hp0.le hp1.le]
  have hb := div_le_div_of_nonneg_right hnat (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  unfold log2
  convert hb using 1 <;> ring

end
end QIT

open scoped ComplexOrder MatrixOrder NNReal
namespace QIT.BinaryPreparation
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

def bernoulliState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State Bool :=
  Classical.diagonalState
    (fun b => if b then ⟨p, hp0⟩ else ⟨1 - p, sub_nonneg.mpr hp1⟩)
    (by rw [Fintype.sum_bool]; apply NNReal.eq; change p + (1 - p) = 1; ring)

theorem bernoulliState_matrix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliState p hp0 hp1).matrix =
      Matrix.diagonal (fun b : Bool => ((if b then p else 1 - p : ℝ) : ℂ)) := by
  unfold bernoulliState
  rw [Classical.diagonalState_matrix]
  congr 1
  funext b
  cases b <;> rfl

theorem bernoulliState_entropy (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (bernoulliState p hp0 hp1).vonNeumann = binaryEntropyBits p := by
  rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal _ _ (bernoulliState_matrix p hp0 hp1)]
  simp [binaryEntropyBits]
  ring

def flagState (p : Bool → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) :
    State (Bool × Bool) :=
  (Ensemble.cqState {
    probs := fun _ : Bool => (1 / 2 : ℝ≥0)
    weights_sum := by simp
    states := fun b => bernoulliState (p b) (hp0 b) (hp1 b) })

theorem flagState_entropy (p : Bool → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) :
    (flagState p hp0 hp1).vonNeumann =
      1 + (1 / 2 : ℝ) * binaryEntropyBits (p true) +
        (1 / 2 : ℝ) * binaryEntropyBits (p false) := by
  unfold flagState
  rw [State.cqState_vonNeumann]
  simp only [Fintype.sum_bool, bernoulliState_entropy]
  have hlog : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hn : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  norm_num [xlog2, log2, hlog, hn]
  ring

theorem flagState_matrix (p : Bool → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) :
    (flagState p hp0 hp1).matrix =
      Matrix.diagonal (fun x => ((1 / 2 * (if x.2 then p x.1 else 1 - p x.1) : ℝ) : ℂ)) := by
  ext ⟨b, s⟩ ⟨c, t⟩
  cases b <;> cases s <;> cases c <;> cases t <;>
    simp [flagState, Ensemble.cqState_matrix, bernoulliState_matrix,
      Matrix.kroneckerMap_apply, Matrix.kronecker, Matrix.smul_apply,
      NNReal.smul_def, Complex.real_smul]

def sourceEnsemble (E : Ensemble Bool a) (p : Bool → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) : Ensemble Bool (Bool × Bool) where
  probs := E.probs
  weights_sum := E.weights_sum
  states x := flagState (fun b => if x then 1 else p b)
    (by intro b; cases x <;> simp [hp0 b]) (by intro b; cases x <;> simp [hp1 b])

theorem sourceEnsemble_average (E : Ensemble Bool a) (q : ℝ)
    (hq : (E.probs true : ℝ) = q) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : Bool → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) :
    (sourceEnsemble E p hp0 hp1).averageState =
      flagState (fun b => q + (1 - q) * p b)
        (by intro b; exact add_nonneg hq0 (mul_nonneg (sub_nonneg.mpr hq1) (hp0 b)))
        (by intro b; nlinarith [hp0 b, hp1 b]) := by
  have hw : (E.probs false : ℝ) = 1 - q := by
    have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) E.weights_sum
    simp only [Fintype.sum_bool, NNReal.coe_add, NNReal.coe_one, hq] at h
    linarith
  have hqC : (E.probs true : ℂ) = (q : ℂ) := by exact_mod_cast hq
  have hwC : (E.probs false : ℂ) = ((1 - q : ℝ) : ℂ) := by exact_mod_cast hw
  apply State.ext
  rw [Ensemble.averageState_matrix, Fintype.sum_bool]
  simp only [sourceEnsemble, flagState_matrix]
  ext ⟨b, s⟩ ⟨c, t⟩
  cases b <;> cases s <;> cases c <;> cases t <;>
    simp [Matrix.smul_apply, NNReal.smul_def, Complex.real_smul, hqC, hwC,
      Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_sub]
  all_goals ring

theorem sourceEnsemble_holevo (E : Ensemble Bool a) (q : ℝ)
    (hq : (E.probs true : ℝ) = q) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : Bool → ℝ) (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b ≤ 1) :
    (sourceEnsemble E p hp0 hp1).holevoInformation =
      (1 / 2 : ℝ) * (binaryEntropyBits (q + (1 - q) * p true) -
        (1 - q) * binaryEntropyBits (p true)) +
      (1 / 2 : ℝ) * (binaryEntropyBits (q + (1 - q) * p false) -
        (1 - q) * binaryEntropyBits (p false)) := by
  have hw : (E.probs false : ℝ) = 1 - q := by
    have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) E.weights_sum
    simp only [Fintype.sum_bool, NNReal.coe_add, NNReal.coe_one, hq] at h
    linarith
  rw [Ensemble.holevoInformation_def, sourceEnsemble_average E q hq hq0 hq1 p hp0 hp1,
    flagState_entropy, Fintype.sum_bool]
  simp only [sourceEnsemble, flagState_entropy, hq, hw, ↓reduceIte]
  norm_num [show binaryEntropyBits 1 = 0 by norm_num [binaryEntropyBits, xlog2, log2]]
  ring

def residual (base signal : State a) (p : ℝ) (hp1 : p < 1)
    (horder : (p : ℂ) • signal.matrix ≤ base.matrix) : State a where
  matrix := (((1 - p)⁻¹ : ℝ) : ℂ) • (base.matrix - (p : ℂ) • signal.matrix)
  pos := by
    apply (Matrix.le_iff.mp horder).smul
    exact_mod_cast (inv_nonneg.mpr (sub_pos.mpr hp1).le)
  trace_eq_one := by
    simp only [Matrix.trace_smul, Matrix.trace_sub, base.trace_eq_one,
      signal.trace_eq_one, smul_eq_mul, mul_one, Complex.ofReal_inv]
    have hpC : (1 : ℂ) - (p : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hp1).ne'
    rw [Complex.ofReal_sub, Complex.ofReal_one]
    exact inv_mul_cancel₀ hpC

theorem residual_reconstruct (base signal : State a) (p : ℝ) (hp1 : p < 1)
    (horder : (p : ℂ) • signal.matrix ≤ base.matrix) :
    (p : ℂ) • signal.matrix + ((1 - p : ℝ) : ℂ) • (residual base signal p hp1 horder).matrix =
      base.matrix := by
  change (p : ℂ) • signal.matrix + ((1 - p : ℝ) : ℂ) •
    ((((1 - p)⁻¹ : ℝ) : ℂ) • (base.matrix - (p : ℂ) • signal.matrix)) = _
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (sub_pos.mpr hp1).ne',
    Complex.ofReal_one, one_smul]
  abel

def preparingChannel (S : Bool → Bool → State a) (p : Bool → ℝ)
    (hp1 : ∀ b, p b < 1) (horder : ∀ b, (p b : ℂ) • (S b true).matrix ≤ (S b false).matrix) :
    Channel (Bool × Bool) a :=
  Channel.prepare fun x => if x.2 then S x.1 true else
    residual (S x.1 false) (S x.1 true) (p x.1) (hp1 x.1) (horder x.1)

theorem preparingChannel_letters (S : Bool → Bool → State a) (p : Bool → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b < 1)
    (horder : ∀ b, (p b : ℂ) • (S b true).matrix ≤ (S b false).matrix) (x : Bool) :
    (preparingChannel S p hp1 horder).map
      (flagState (fun b => if x then 1 else p b)
        (by intro b; cases x <;> simp [hp0 b])
        (by intro b; cases x <;> simp [(hp1 b).le])).matrix =
      (1 / 2 : ℂ) • ((S true x).matrix + (S false x).matrix) := by
  rw [flagState_matrix]
  simp only [preparingChannel, Channel.prepare_map, Matrix.diagonal_apply_eq,
    Fintype.sum_prod_type, Fintype.sum_bool]
  cases x
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have ht := residual_reconstruct (S true false) (S true true) (p true) (hp1 true) (horder true)
    have hf := residual_reconstruct (S false false) (S false true) (p false) (hp1 false) (horder false)
    ext i j
    have ht' := congrFun (congrFun ht i) j
    have hf' := congrFun (congrFun hf i) j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at ht' hf' ⊢
    linear_combination (1 / 2 : ℂ) * ht' + (1 / 2 : ℂ) * hf'
  · simp

theorem holevo_le_source (E : Ensemble Bool a) (S : Bool → Bool → State a) (p : Bool → ℝ)
    (hp0 : ∀ b, 0 ≤ p b) (hp1 : ∀ b, p b < 1)
    (horder : ∀ b, (p b : ℂ) • (S b true).matrix ≤ (S b false).matrix)
    (hletters : ∀ x, (E.states x).matrix = (1 / 2 : ℂ) • ((S true x).matrix + (S false x).matrix)) :
    E.holevoInformation ≤ (sourceEnsemble E p hp0 (fun b => (hp1 b).le)).holevoInformation := by
  have heq : (preparingChannel S p hp1 horder).outputEnsemble
      (sourceEnsemble E p hp0 (fun b => (hp1 b).le)) = E := by
    have hstates : ∀ x, (preparingChannel S p hp1 horder).applyState
        ((sourceEnsemble E p hp0 (fun b => (hp1 b).le)).states x) = E.states x := by
      intro x
      apply State.ext
      exact (preparingChannel_letters S p hp0 hp1 horder x).trans (hletters x).symm
    cases E
    simp only [Channel.outputEnsemble, sourceEnsemble] at hstates ⊢
    simp only [hstates]
  rw [← heq]
  exact Ensemble.holevoInformation_outputEnsemble_le _ _

end
end QIT.BinaryPreparation
