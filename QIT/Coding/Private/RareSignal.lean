/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! # The binary entropy inequality for a rare conclusive event -/

@[expose] public section
namespace QIT
noncomputable section

/-- The concavity step in `eq:receiver-gain`: `h₂(aq) - qh₂(a) ≥ aq log₂(1/q)`. -/
theorem rare_event_information_lower (a q : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hq0 : 0 < q) (hq1 : q ≤ 1) :
    a * q * log2 (1 / q) ≤ binaryEntropyBits (a * q) - q * binaryEntropyBits a := by
  have hg := Real.concaveOn_negMulLog.2
    (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
    (show 1 - a ∈ Set.Ici 0 from sub_nonneg.mpr ha1)
    (show 0 ≤ 1 - q from sub_nonneg.mpr hq1) hq0.le (by ring : 1 - q + q = 1)
  have heq : (1 - q) * 1 + q * (1 - a) = 1 - a * q := by ring
  simp only [smul_eq_mul, heq, Real.negMulLog_one, mul_zero, zero_add] at hg
  have hlog : Real.log (a * q) = Real.log a + Real.log q := Real.log_mul ha0.ne' hq0.ne'
  have hnat : a * q * Real.log (1 / q) ≤ Real.binEntropy (a * q) - q * Real.binEntropy a := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog, hlog, one_div, Real.log_inv] at hg ⊢
    nlinarith
  have h := div_le_div_of_nonneg_right hnat (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have haq : a * q ≤ 1 := (mul_le_of_le_one_left hq0.le ha1).trans hq1
  rw [binaryEntropyBits_eq_binEntropy_div_log_two (mul_pos ha0 hq0).le haq,
    binaryEntropyBits_eq_binEntropy_div_log_two ha0.le ha1]
  unfold log2
  convert h using 1 <;> ring

end
end QIT
