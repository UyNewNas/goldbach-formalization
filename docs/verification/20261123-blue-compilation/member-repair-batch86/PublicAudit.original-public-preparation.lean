import ImbalancedChen.P5OriginalPrimeEndpointDivisors
import ImbalancedChen.P5ActualRoughHeathBrownWords
import ImbalancedChen.P4BSmoothRealBCompactFamily
import ImbalancedChen.P4BSmoothPrimeVariableProfile
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget
import ImbalancedChen.P4BPhysicalRampMassReserve
import ImbalancedChen.Part3RoughFiniteEulerLogDerivative
import ImbalancedChen.P2OriginalFirstIntegralEndpoint
import Lean
set_option pp.all true
set_option pp.universes true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let targets : Array Name := #[`ImbalancedChen.P5OriginalPrimeEndpointDivisors, `ImbalancedChen.P5ActualRoughHeathBrownWords, `ImbalancedChen.P4BSmoothRealBCompactFamily, `ImbalancedChen.P4BSmoothPrimeVariableProfile, `ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget, `ImbalancedChen.P4BPhysicalRampMassReserve, `ImbalancedChen.Part3RoughFiniteEulerLogDerivative, `ImbalancedChen.P2OriginalFirstIntegralEndpoint]
  let selected := env.constants.fold (init := #[]) (fun acc name info =>
    match env.getModuleIdxFor? name with
    | some index =>
      let owner := moduleNames[index.toNat]!
      if targets.contains owner && !isPrivateName name then acc.push (owner, name, info) else acc
    | none => acc)
  let entries := selected.qsort (fun a b => Name.lt a.2.1 b.2.1)
  for (owner, name, info) in entries do
    let isAxiom := match info with | .axiomInfo _ => true | _ => false
    let record := Json.mkObj [
      ("module", toJson owner.toString), ("name", toJson name.toString),
      ("type_expression", toJson (reprStr info.type)),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("is_axiom_declaration", toJson isAxiom)]
    logInfo m!"AUDIT_RECORD {record.compress}"
    elabCommand (← `(command| #check @$(mkIdent name)))
    elabCommand (← `(command| #print axioms $(mkIdent name)))
  logInfo m!"AUDIT_FINISHED {entries.size}"
