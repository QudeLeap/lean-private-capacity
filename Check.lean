import QIT
import Lean.Util.CollectAxioms

-- Check the deformed half-erasure capacity conclusion with no hypotheses.
example :
    QIT.Channel.privateCapacity.{0, 0, 0, 0}
        QIT.Channel.privateN QIT.Channel.complementN = 0 ∧
      QIT.Channel.privateCapacity.{0, 0, 0, 0}
        QIT.Channel.erasure2 QIT.Channel.erasure2Complement = 0 ∧
      (181 / 400000 : Real) <
        QIT.Channel.privateCapacity.{0, 0, 0, 0}
          QIT.QubitActivation.productChannel QIT.QubitActivation.productComplement :=
  QIT.QubitActivation.deformed_superactivation_main

example :
    (45259148246 / 100000000000000 : Real) < QIT.QubitActivation.deformedMeasuredRate ∧
      QIT.QubitActivation.deformedMeasuredRate < (45259148249 / 100000000000000 : Real) :=
  QIT.QubitActivation.deformedMeasuredRate_interval

example : QIT.QubitActivation.deformedR0 = (1001 / 1000 : Real) ∧
    QIT.QubitActivation.deformedR1 = (999 / 1000 : Real) ∧
    QIT.QubitActivation.deformedMixing = (27 / 1000 : Real) ∧
    QIT.QubitActivation.deformedProbability = (3 / 16 : Real) := ⟨rfl, rfl, rfl, rfl⟩

-- Keep the physical channels and numerical bound literal and the context empty.
example :
    QIT.Channel.privateCapacity.{0, 0, 0, 0}
        QIT.Channel.privateN QIT.Channel.complementN = 0 ∧
      QIT.Channel.privateCapacity.{0, 0, 0, 0}
        QIT.Channel.erasure2 QIT.Channel.erasure2Complement = 0 ∧
      ((2 : Real) ^ 49)⁻¹ < ((2 : Real) ^ 49)⁻¹ * QIT.log2 (16 / 7) ∧
      ((2 : Real) ^ 49)⁻¹ * QIT.log2 (16 / 7) ≤
        QIT.Channel.privateCapacity.{0, 0, 0, 0}
          QIT.QubitActivation.productChannel QIT.QubitActivation.productComplement :=
  QIT.QubitActivation.superactivation_main

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let standard : List Name := [`propext, `Classical.choice, `Quot.sound]
  for mod in env.header.moduleNames do
    if (`QIT).isPrefixOf mod && mod != `QIT then
      logInfo m!"LOADED_QIT_MODULE {mod}"
  let mut names : Array Name := #[]
  for (name, idx) in env.const2ModIdx.toArray do
    let mod := env.header.moduleNames[idx.toNat]!
    if (`QIT.Coding.Private).isPrefixOf mod then
      names := names.push name
  for name in names.qsort Name.lt do
    let axioms ← collectAxioms name
    if axioms.any (fun a ↦ !standard.contains a) then
      throwError "Nonstandard axiom dependency: {name}: {axioms}"
    if (env.find? name).any (·.isUnsafe) then
      throwError "Unsafe declaration: {name}"
    logInfo m!"AUDIT {name} : {axioms.qsort Name.lt |>.toList}"
  logInfo "EXACT_ENDPOINT_WITHOUT_HYPOTHESES_PASS"
