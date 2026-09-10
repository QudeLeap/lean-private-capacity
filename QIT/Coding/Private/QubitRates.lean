/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitEncoding
public import QIT.Coding.Private.CapacityBounds

/-!
# Exact scalar constants in the qubit activation proof

The private rate is the weaker certified bound retained in Appendix B.3
of the 2026-09-08 manuscript. The reference-pair constants are retained
from the 2026-09-07 manuscript (former `eq:finite-violation`). The entropy inequalities themselves are separate
proof obligations; the scalar lemmas do not assert those inequalities.
-/

@[expose] public section
namespace QIT.QubitActivation
noncomputable section

def signalProbability : ℝ := ((2 : ℝ) ^ 48)⁻¹
def referenceMixture : ℝ := ((2 : ℝ) ^ 42)⁻¹
def certifiedRate : ℝ := ((2 : ℝ) ^ 49)⁻¹ * log2 (16 / 7)

theorem signalProbability_pos : 0 < signalProbability := by
  unfold signalProbability
  positivity

theorem signalProbability_lt_one : signalProbability < 1 := by
  norm_num [signalProbability]

private theorem log2_two_pow (n : ℕ) : log2 ((2 : ℝ) ^ n) = n := by
  unfold log2
  rw [Real.log_pow]
  field_simp [(Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

theorem signal_log : log2 (1 / signalProbability) = 48 := by
  simpa [signalProbability] using log2_two_pow 48

theorem signal_half : signalProbability / 2 = ((2 : ℝ) ^ 49)⁻¹ := by
  norm_num [signalProbability]

theorem log_environment_and_rate : log2 112 + log2 (16 / 7) = 8 := by
  rw [← log2_mul (by norm_num) (by norm_num)]
  convert log2_two_pow 8 using 1
  norm_num

/-- The last equality in the manuscript's private-rate chain. -/
theorem rate_identity :
    signalProbability / 12 * log2 (1 / signalProbability) -
        signalProbability / 2 * log2 112 = certifiedRate := by
  rw [signal_log, certifiedRate, ← signal_half]
  have hlog : log2 (16 / 7) = 8 - log2 112 := by linarith [log_environment_and_rate]
  rw [hlog]
  ring

theorem log_rate_gt_one : 1 < log2 (16 / 7) := by
  unfold log2
  rw [lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2)), one_mul]
  exact Real.log_lt_log (by norm_num) (by norm_num)

theorem certifiedRate_gt : ((2 : ℝ) ^ 49)⁻¹ < certifiedRate := by
  unfold certifiedRate
  simpa using mul_lt_mul_of_pos_left log_rate_gt_one (by positivity :
    (0 : ℝ) < ((2 : ℝ) ^ 49)⁻¹)

theorem certifiedRate_pos : 0 < certifiedRate :=
  lt_trans (by positivity) certifiedRate_gt

theorem referenceMixture_pos : 0 < referenceMixture := by
  unfold referenceMixture
  positivity

theorem referenceMixture_lt_one : referenceMixture < 1 := by
  norm_num [referenceMixture]

/-- The receiver's finite-divergence lower-bound constant is exactly six. -/
theorem reference_receiver_constant : (1 / 6 : ℝ) * log2 (1 / referenceMixture) - 1 = 6 := by
  have h : log2 (1 / referenceMixture) = 42 := by
    simpa [referenceMixture] using log2_two_pow 42
  rw [h]
  norm_num

/-- The environmental scalar bound is strictly below five. -/
theorem reference_environment_constant : log2 (28 / (1 - referenceMixture)) < 5 := by
  have hpos : (0 : ℝ) < 28 / (1 - referenceMixture) := by
    exact div_pos (by norm_num) (sub_pos.mpr referenceMixture_lt_one)
  have hlt : (28 : ℝ) / (1 - referenceMixture) < 2 ^ 5 := by
    norm_num [referenceMixture]
  have hlog := Real.log_lt_log hpos hlt
  have h := div_lt_div_of_pos_right hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  change log2 (28 / (1 - referenceMixture)) < log2 ((2 : ℝ) ^ 5) at h
  simpa only [log2_two_pow, Nat.cast_ofNat] using h

end
end QIT.QubitActivation
