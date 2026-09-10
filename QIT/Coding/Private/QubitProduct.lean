/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team, Chengkai Zhu
-/

module

public import QIT.Coding.Private.QubitEvent
public import QIT.Coding.Private.QubitRates

/-!
# The actual product channel and ensemble in the half-erasure instance of the main theorem

The paper writes its encoding in RA order and its channel as N ⊗ E₂.
`inputState` explicitly swaps the input factors to AR; the complement
below is the full 24-dimensional Kraus complement.
-/

@[expose] public section
namespace QIT.QubitActivation
open Channel
noncomputable section

abbrev ProductInput := Fin 4 × Fin 2
abbrev ProductReceiver := Fin 4 × (Fin 2 ⊕ Fin 1)
abbrev ProductEnvironment := Fin 8 × (Fin 1 ⊕ Fin 2)

def productChannel : Channel ProductInput ProductReceiver := privateN.prod erasure2
def productComplement : Channel ProductInput ProductEnvironment := complementN.prod erasure2Complement

theorem product_isComplementOf : Channel.IsComplementOf productComplement productChannel :=
  complementN_isComplementOf.prod erasure2_isComplementOf

theorem product_dimensions : Fintype.card ProductInput = 8 ∧
    Fintype.card ProductReceiver = 12 ∧ Fintype.card ProductEnvironment = 24 := by
  norm_num [ProductInput, ProductReceiver, ProductEnvironment]

def inputState (x : Bool) : State ProductInput :=
  (if x then rho1 else rho0).reindex (Equiv.prodComm (Fin 2) (Fin 4))

/-- The probability remains a fixed letter probability before the coding limit. -/
def productEnsemble (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Ensemble Bool ProductInput where
  probs := (ensemble q hq0 hq1).probs
  weights_sum := (ensemble q hq0 hq1).weights_sum
  states := inputState

def fixedEnsemble : Ensemble Bool ProductInput :=
  productEnsemble signalProbability signalProbability_pos.le signalProbability_lt_one.le

def fullBobEnsemble : Ensemble Bool ProductReceiver := productChannel.outputEnsemble fixedEnsemble
def fullEveEnsemble : Ensemble Bool ProductEnvironment := productComplement.outputEnsemble fixedEnsemble

end
end QIT.QubitActivation
