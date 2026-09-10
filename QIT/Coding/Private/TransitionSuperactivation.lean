/-
Copyright (c) 2026 Chengkai Zhu.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengkai Zhu
-/

module
public import QIT.Coding.Private.TransitionProduct
public import QIT.Coding.Private.FlaggedCoin
public import QIT.Coding.Private.CapacityBounds

/-! # Superactivation for the new manuscript, for every 1/2 ≤ p < 1

This proves the positive explicit rate for the actual finite-dimensional
channels and full complements. Capacity is the regularized private-information
formula; its equivalence with operational coding capacity is a separate theorem.
-/

@[expose] public section
open scoped ComplexOrder MatrixOrder NNReal
namespace QIT.Transition
noncomputable section
universe u

def mixedSignal (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : State RA where
  matrix := ((1 - t : ℝ) : ℂ) • (inputState false).matrix + (t : ℂ) • (inputState true).matrix
  pos := ((inputState false).pos.smul (by exact_mod_cast sub_nonneg.mpr ht1)).add
    ((inputState true).pos.smul (by exact_mod_cast ht0))
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      (inputState false).trace_eq_one, (inputState true).trace_eq_one]
    simp

def ensemble (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Ensemble Bool RA where
  probs x := if x then 1 / 4 else 3 / 4
  weights_sum := by norm_num [Fintype.sum_bool]
  states x := if x then mixedSignal t ht0 ht1 else inputState false

theorem mixedSignal_helper_marginal (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (mixedSignal t ht0 ht1).marginalA.matrix = (1 / 2 : ℂ) • (1 : CMatrix (Fin 2)) := by
  have hb := inputState_helper_marginal false
  have hs := inputState_helper_marginal true
  change partialTraceB (inputState false).matrix = _ at hb
  change partialTraceB (inputState true).matrix = _ at hs
  change partialTraceB
    (((1 - t : ℝ) : ℂ) • (inputState false).matrix + (t : ℂ) • (inputState true).matrix) = _
  rw [partialTraceB_add, partialTraceB_smul, partialTraceB_smul, hb, hs]
  simp only [Complex.ofReal_sub, Complex.ofReal_one]
  module

def clickCoefficient (p : ℝ) : ℝ := (1 - p) / 7
def kappa (p : ℝ) : ℝ := (27 + 169 * p) / 9
def amplitude (p : ℝ) : ℝ := 8 * clickCoefficient p * Real.log 2 / (3 * kappa p)
def certifiedRate (p : ℝ) : ℝ := 6 * Real.log 2 * (1 - p) ^ 2 / (49 * (27 + 169 * p))

theorem clickCoefficient_pos (p : ℝ) (hp : p < 1) : 0 < clickCoefficient p := by
  unfold clickCoefficient
  positivity

theorem clickCoefficient_le (p : ℝ) (hp : 1 / 2 ≤ p) : clickCoefficient p ≤ 1 / 14 := by
  unfold clickCoefficient
  linarith

theorem kappa_ge (p : ℝ) (hp : 1 / 2 ≤ p) : 12 ≤ kappa p := by
  unfold kappa
  linarith

theorem amplitude_pos (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) : 0 < amplitude p := by
  have ha := clickCoefficient_pos p hp1
  have hk := kappa_ge p hp0
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold amplitude
  positivity

theorem amplitude_le_log_div_63 (p : ℝ) (hp0 : 1 / 2 ≤ p) : amplitude p ≤ Real.log 2 / 63 := by
  have ha := clickCoefficient_le p hp0
  have hk := kappa_ge p hp0
  have hl := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have h1 := mul_nonneg (sub_nonneg.mpr ha) hl
  have h2 := mul_nonneg (sub_nonneg.mpr hk) hl
  apply (div_le_iff₀ (by linarith : 0 < 3 * kappa p)).mpr
  nlinarith

theorem amplitude_lt_half (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) : amplitude p < 1 / 2 := by
  have ha := clickCoefficient_pos p hp1
  have ha1 := clickCoefficient_le p hp0
  have hk := kappa_ge p hp0
  have hl : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmul := mul_nonneg ha.le (sub_nonneg.mpr hl)
  apply (div_lt_iff₀ (by linarith : 0 < 3 * kappa p)).mpr
  nlinarith

theorem full_input_event (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    (((productChannel p hp0 hp1).applyState (inputState b)).matrix * receiverEffect).trace =
      if b then (clickCoefficient p : ℂ) else 0 := by
  rw [full_receiver_event, receiver_event]
  cases b <;> simp [clickCoefficient]
  ring

theorem weak_input_event (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (((productChannel p hp0 hp1).applyState (mixedSignal t ht0 ht1)).matrix * receiverEffect).trace =
      ((clickCoefficient p * t : ℝ) : ℂ) := by
  change ((productChannel p hp0 hp1).map
    (((1 - t : ℝ) : ℂ) • (inputState false).matrix + (t : ℂ) • (inputState true).matrix) * receiverEffect).trace = _
  rw [map_add, map_smul, map_smul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
  have hb := full_input_event p hp0 hp1 false
  have hs := full_input_event p hp0 hp1 true
  change ((productChannel p hp0 hp1).map (inputState false).matrix * receiverEffect).trace = 0 at hb
  change ((productChannel p hp0 hp1).map (inputState true).matrix * receiverEffect).trace = _ at hs
  rw [hb, hs]
  simp
  ring

/-- Exact measured information for the paper's fixed binary POVM and prior 1/4. -/
theorem measured_information (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((Channel.measure (POVM.binaryOfEffect receiverEffect receiverEffect_pos receiverEffect_le_one)).outputEnsemble
      ((productChannel p hp0 hp1).outputEnsemble (ensemble t ht0 ht1))).holevoInformation =
      binaryEntropyBits (clickCoefficient p * t / 4) - binaryEntropyBits (clickCoefficient p * t) / 4 := by
  apply DominatedCoin.quarter_measurement_information _ rfl _ receiverEffect
    receiverEffect_pos receiverEffect_le_one
  · exact full_input_event p hp0 hp1 false
  · exact weak_input_event p hp0 hp1 t ht0 ht1

theorem rare_signal_gain (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    clickCoefficient p * t / 2 ≤ binaryEntropyBits (clickCoefficient p * t / 4) -
      binaryEntropyBits (clickCoefficient p * t) / 4 := by
  have ha := clickCoefficient_pos p hp1
  have ha1 := clickCoefficient_le p hp0
  have h := rare_event_information_lower (clickCoefficient p * t) (1 / 4)
    (mul_pos ha ht0) (by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) ht0.le])
    (by norm_num) (by norm_num)
  have hlog : log2 (1 / (1 / 4 : ℝ)) = 2 := by
    norm_num only [one_div_div, mul_one]
    unfold log2
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
    field_simp
    norm_num
  rw [hlog] at h
  convert h using 1
  · ring
  · rw [show clickCoefficient p * t * (1 / 4) = clickCoefficient p * t / 4 by ring]
    ring

theorem receiver_information_lower (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    clickCoefficient p * t / 2 ≤
      ((productChannel p (by linarith) hp1.le).outputEnsemble
        (ensemble t ht0.le (by linarith))).holevoInformation := by
  have hm := measured_information p (by linarith) hp1.le t ht0.le (by linarith)
  have hd := Ensemble.holevoInformation_outputEnsemble_le
    (Channel.measure (POVM.binaryOfEffect receiverEffect receiverEffect_pos receiverEffect_le_one))
    ((productChannel p (by linarith) hp1.le).outputEnsemble (ensemble t ht0.le (by linarith)))
  rw [hm] at hd
  exact (rare_signal_gain p hp0 hp1 t ht0 ht1).trans hd

/-- The complete environment bound, weighted by its actual erasure probability. -/
theorem environment_information_upper (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    ((productComplement p hp0 hp1).outputEnsemble (ensemble t ht0 (by linarith))).holevoInformation ≤
      3 * kappa p * t ^ 2 / (32 * Real.log 2) := by
  have h := FlaggedCoin.holevo_bound
    ((productComplement p hp0 hp1).outputEnsemble (ensemble t ht0 (by linarith))) rfl
    branchConstant branchConstant_ge_three baseBranch signalBranch environment_branches_order
    p hp0 hp1 t ht0 ht1
  have hb := full_environment p hp0 hp1 (inputState false)
  have hs := full_environment p hp0 hp1 (inputState true)
  have h0 : (((productComplement p hp0 hp1).outputEnsemble
      (ensemble t ht0 (by linarith))).states false).matrix =
      (p : ℂ) • (baseBranch true).matrix + ((1 - p : ℝ) : ℂ) • (baseBranch false).matrix := by
    simpa only [Channel.outputEnsemble, ensemble, Bool.false_eq_true, ↓reduceIte,
      baseBranch, sigma, epsilon] using hb
  have h1 : (((productComplement p hp0 hp1).outputEnsemble
      (ensemble t ht0 (by linarith))).states true).matrix =
      (p : ℂ) • (((1 - t : ℝ) : ℂ) • (baseBranch true).matrix + (t : ℂ) • (signalBranch true).matrix) +
      ((1 - p : ℝ) : ℂ) •
        (((1 - t : ℝ) : ℂ) • (baseBranch false).matrix + (t : ℂ) • (signalBranch false).matrix) := by
    change (productComplement p hp0 hp1).map
      (((1 - t : ℝ) : ℂ) • (inputState false).matrix + (t : ℂ) • (inputState true).matrix) = _
    rw [map_add, map_smul, map_smul]
    change (productComplement p hp0 hp1).map (inputState false).matrix = _ at hb
    change (productComplement p hp0 hp1).map (inputState true).matrix = _ at hs
    rw [hb, hs]
    simp only [baseBranch, signalBranch, sigma, epsilon, Bool.false_eq_true, ↓reduceIte]
    module
  have he := h h0 h1
  convert he using 1
  simp only [branchConstant, Bool.false_eq_true, ↓reduceIte, kappa]
  ring

theorem private_information_lower (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    clickCoefficient p * t / 2 - 3 * kappa p * t ^ 2 / (32 * Real.log 2) ≤
      (productChannel p (by linarith) hp1.le).privateInformationWith
        (productComplement p (by linarith) hp1.le) (ensemble t ht0.le (by linarith)) :=
  sub_le_sub (receiver_information_lower p hp0 hp1 t ht0 ht1)
    (environment_information_upper p (by linarith) hp1.le t ht0.le ht1)

theorem amplitude_rate_identity (p : ℝ) (hp0 : 1 / 2 ≤ p) :
    clickCoefficient p * amplitude p / 2 -
      3 * kappa p * amplitude p ^ 2 / (32 * Real.log 2) = certifiedRate p := by
  have hd : 27 + 169 * p ≠ 0 := by linarith
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold amplitude clickCoefficient kappa certifiedRate
  field_simp
  ring

theorem certifiedRate_pos (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) : 0 < certifiedRate p := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hs : 0 < 1 - p := sub_pos.mpr hp1
  have hd : 0 < 27 + 169 * p := by linarith
  unfold certifiedRate
  positivity

/-- Actual fixed-measurement private information, before invoking a coding theorem. -/
def measuredRate (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ℝ :=
  ((Channel.measure (POVM.binaryOfEffect receiverEffect receiverEffect_pos receiverEffect_le_one)).outputEnsemble
    ((productChannel p hp0 hp1).outputEnsemble (ensemble t ht0 ht1))).holevoInformation -
  ((productComplement p hp0 hp1).outputEnsemble (ensemble t ht0 ht1)).holevoInformation

/-- Equation (gain), for the actual fixed measurement and every allowed weak amplitude. -/
theorem measuredRate_lower (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) :
    clickCoefficient p * t / 2 - 3 * kappa p * t ^ 2 / (32 * Real.log 2) ≤
      measuredRate p (by linarith) hp1.le t ht0.le (by linarith) := by
  unfold measuredRate
  rw [measured_information]
  exact sub_le_sub (rare_signal_gain p hp0 hp1 t ht0 ht1)
    (environment_information_upper p (by linarith) hp1.le t ht0.le ht1)

theorem certifiedRate_le_measuredRate (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) :
    certifiedRate p ≤ measuredRate p (by linarith) hp1.le (amplitude p)
      (amplitude_pos p hp0 hp1).le (by linarith [amplitude_lt_half p hp0 hp1]) := by
  have h := measuredRate_lower p hp0 hp1 (amplitude p) (amplitude_pos p hp0 hp1)
    (amplitude_lt_half p hp0 hp1).le
  rw [amplitude_rate_identity p hp0] at h
  exact h

/-- The standalone zeros include the completely erased endpoint p = 1. -/
theorem individual_capacities_zero (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p ≤ 1) :
    Channel.privateCapacity.{0, 0, 0, u} mainChannel complement = 0 ∧
    Channel.privateCapacity.{0, 0, 0, u}
      (Channel.erasure 2 p (by linarith) hp1) (Channel.erasureComplement 2 p (by linarith) hp1) = 0 :=
  ⟨mainChannel_privateCapacity_eq_zero, erasure_privateCapacity_eq_zero 2 p hp0 hp1⟩

/-- The explicit lower bound on the regularized private-information capacity. -/
theorem certifiedRate_le_privateCapacity (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) :
    certifiedRate p ≤ Channel.privateCapacity.{0, 0, 0, u}
      (productChannel p (by linarith) hp1.le) (productComplement p (by linarith) hp1.le) := by
  let E := ensemble (amplitude p) (amplitude_pos p hp0 hp1).le
    (by linarith [amplitude_lt_half p hp0 hp1])
  have h := private_information_lower p hp0 hp1 (amplitude p)
    (amplitude_pos p hp0 hp1) (amplitude_lt_half p hp0 hp1).le
  rw [amplitude_rate_identity p hp0] at h
  have hc := Channel.privateInformationWith_le_privateCapacity
    (productChannel p (by linarith) hp1.le) (productComplement p (by linarith) hp1.le)
    (E.relabelIndex (Equiv.ulift : ULift.{u, 0} Bool ≃ Bool))
  simp only [Channel.privateInformationWith, Channel.outputEnsemble_relabelIndex,
    Ensemble.relabelIndex_holevoInformation] at hc
  exact h.trans hc

/-- The manuscript's core claim, for the specified actual channels and full complements. -/
theorem superactivation_main (p : ℝ) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) :
    Channel.privateCapacity.{0, 0, 0, u} mainChannel complement = 0 ∧
    Channel.privateCapacity.{0, 0, 0, u}
      (Channel.erasure 2 p (by linarith) hp1.le) (Channel.erasureComplement 2 p (by linarith) hp1.le) = 0 ∧
    0 < certifiedRate p ∧ certifiedRate p ≤ Channel.privateCapacity.{0, 0, 0, u}
      (productChannel p (by linarith) hp1.le) (productComplement p (by linarith) hp1.le) :=
  ⟨mainChannel_privateCapacity_eq_zero, erasure_privateCapacity_eq_zero 2 p hp0 hp1.le,
    certifiedRate_pos p hp0 hp1, certifiedRate_le_privateCapacity p hp0 hp1⟩

theorem half_erasure_rate : certifiedRate (1 / 2) = 3 * Real.log 2 / 10927 := by
  unfold certifiedRate
  ring

end
end QIT.Transition
