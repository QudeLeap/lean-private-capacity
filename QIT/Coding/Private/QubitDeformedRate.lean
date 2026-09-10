/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitDeformedEntropy
public import QIT.Coding.Private.QubitDeformedEnsemble
public import QIT.Coding.Private.QubitDeformedDiagonalEntropy

/-!
# The measured private-information rate of the deformed encoding

The spectral and logarithm certificates are connected to the actual channel
outputs, the fixed measurement, and both erasure-flag branches. The final
inequality has no numerical or spectral hypotheses.
-/

@[expose] public section
namespace QIT.QubitActivation
open Channel
noncomputable section

theorem deformedFullEve_entropy (k : Fin 3) :
    (productComplement.applyState
      ((deformedTestState k).reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann =
      1 + deformedNumericSigmaEntropy k / 2 +
        deformedShannon (deformedNumericE k) / 2 := by
  rw [← State.vonNeumann_reindex _ environmentRegisterEquiv.symm]
  have h := vonNeumann_half_blocks
    ((productComplement.applyState
      ((deformedTestState k).reindex (Equiv.prodComm (Fin 2) (Fin 4)))).reindex
        environmentRegisterEquiv.symm)
    (deformedSigma k) (deformedEpsilon k)
    (full_environment_outputs_directSum (deformedTestState k))
  rw [deformedSigma_entropy, deformedEpsilon_entropy] at h
  exact h

/-- Equality with the numerical expression is proved from the physical channel outputs. -/
theorem deformedMeasuredRate_eq_numeric : deformedMeasuredRate = deformedNumericRate := by
  change (((measure deformedMeasurement).comp productChannel).outputEnsemble
    deformedEnsemble).holevoInformation -
    (productComplement.outputEnsemble deformedEnsemble).holevoInformation = _
  rw [deformed_output_holevo, deformed_output_holevo]
  change
    (((measure deformedMeasurement).applyState (productChannel.applyState
      ((deformedTestState 2).reindex (Equiv.prodComm (Fin 2) (Fin 4))))).vonNeumann -
    (13 / 16) * ((measure deformedMeasurement).applyState (productChannel.applyState
      ((deformedTestState 0).reindex (Equiv.prodComm (Fin 2) (Fin 4))))).vonNeumann -
    (3 / 16) * ((measure deformedMeasurement).applyState (productChannel.applyState
      ((deformedTestState 1).reindex (Equiv.prodComm (Fin 2) (Fin 4))))).vonNeumann) -
    ((productComplement.applyState
      ((deformedTestState 2).reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann -
    (13 / 16) * (productComplement.applyState
      ((deformedTestState 0).reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann -
    (3 / 16) * (productComplement.applyState
      ((deformedTestState 1).reindex (Equiv.prodComm (Fin 2) (Fin 4)))).vonNeumann) = _
  rw [deformedFullMeasured_entropy, deformedFullMeasured_entropy,
    deformedFullMeasured_entropy, deformedFullEve_entropy,
    deformedFullEve_entropy, deformedFullEve_entropy]
  unfold deformedNumericRate deformedNumericHolevo
  ring

/-- A strict two-sided interval, sharper than the manuscript's displayed estimate. -/
theorem deformedMeasuredRate_interval :
    (45259148246 / 100000000000000 : ℝ) < deformedMeasuredRate ∧
      deformedMeasuredRate < (45259148249 / 100000000000000 : ℝ) := by
  rw [deformedMeasuredRate_eq_numeric]
  exact deformedNumericRate_interval

/-- The displayed 0.00045258 < rate < 0.00045260 estimate. -/
theorem deformedMeasuredRate_paper_interval :
    (45258 / 100000000 : ℝ) < deformedMeasuredRate ∧
      deformedMeasuredRate < (45260 / 100000000 : ℝ) := by
  have h := deformedMeasuredRate_interval
  constructor <;> linarith [h.1, h.2]

/-- Strict certified rate for r₀ = 1001/1000, r₁ = 999/1000, t = 27/1000, q = 3/16. -/
theorem deformedMeasuredRate_gt : (181 / 400000 : ℝ) < deformedMeasuredRate := by
  rw [deformedMeasuredRate_eq_numeric]
  exact deformedNumericRate_gt

end
end QIT.QubitActivation
