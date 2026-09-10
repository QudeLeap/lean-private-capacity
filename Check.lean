import CurrentProof
import Lean.Util.CollectAxioms

-- Latest manuscript: actual new channels, full complements, every p in the stated interval.
example : QIT.Channel.IsComplementOf QIT.Transition.complement QIT.Transition.mainChannel :=
  QIT.Transition.complement_isComplementOf

example (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : QIT.Channel.IsComplementOf
    (QIT.Transition.productComplement p hp0 hp1) (QIT.Transition.productChannel p hp0 hp1) :=
  QIT.Transition.product_isComplementOf p hp0 hp1

example : Fintype.card QIT.Transition.RA = 8 ∧ Fintype.card QIT.Transition.RB = 12 ∧
    Fintype.card QIT.Transition.FullE = 24 := by decide

-- Only the paper's erasure-probability conditions are hypotheses; the rate is literal.
example (p : Real) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) :
    QIT.Channel.privateCapacity.{0, 0, 0, 0} QIT.Transition.mainChannel QIT.Transition.complement = 0 ∧
    QIT.Channel.privateCapacity.{0, 0, 0, 0}
      (QIT.Channel.erasure 2 p (by linarith) hp1.le)
      (QIT.Channel.erasureComplement 2 p (by linarith) hp1.le) = 0 ∧
    0 < 6 * Real.log 2 * (1 - p) ^ 2 / (49 * (27 + 169 * p)) ∧
    6 * Real.log 2 * (1 - p) ^ 2 / (49 * (27 + 169 * p)) ≤
      QIT.Channel.privateCapacity.{0, 0, 0, 0}
        (QIT.Transition.productChannel p (by linarith) hp1.le)
        (QIT.Transition.productComplement p (by linarith) hp1.le) := by
  simpa only [QIT.Transition.certifiedRate] using QIT.Transition.superactivation_main.{0} p hp0 hp1

example : QIT.Channel.privateCapacity.{0, 0, 0, 0}
    (QIT.Channel.erasure 2 1 (by norm_num) (by norm_num))
    (QIT.Channel.erasureComplement 2 1 (by norm_num) (by norm_num)) = 0 :=
  QIT.erasure_privateCapacity_eq_zero 2 1 (by norm_num) (by norm_num)

example : QIT.Transition.certifiedRate (1 / 2) = 3 * Real.log 2 / 10927 :=
  QIT.Transition.half_erasure_rate

example (p : Real) (hp0 : 1 / 2 ≤ p) (hp1 : p < 1) :
    6 * Real.log 2 * (1 - p) ^ 2 / (49 * (27 + 169 * p)) ≤
      QIT.Transition.measuredRate p (by linarith) hp1.le (QIT.Transition.amplitude p)
        (QIT.Transition.amplitude_pos p hp0 hp1).le
        (by linarith [QIT.Transition.amplitude_lt_half p hp0 hp1]) := by
  simpa only [QIT.Transition.certifiedRate] using
    QIT.Transition.certifiedRate_le_measuredRate p hp0 hp1

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
  logInfo "EXACT_ENDPOINT_WITH_ONLY_PARAMETER_CONDITIONS_PASS"
