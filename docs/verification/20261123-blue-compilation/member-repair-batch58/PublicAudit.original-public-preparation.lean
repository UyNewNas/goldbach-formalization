import ImbalancedChen.ActualPrimeFineLabelSortedSelector
import ImbalancedChen.OriginalAscendingThirteenCellOwnership
import ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows
import ImbalancedChen.P1OriginalHistoricalFifthOwnCubeAffineGates
import ImbalancedChen.P1OriginalVariableFifthContinuation
import ImbalancedChen.P1OriginalVariableFourthProfileRegularity
import Lean
set_option pp.all true
set_option pp.universes true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let targets : Array Name := #[`ImbalancedChen.ActualPrimeFineLabelSortedSelector, `ImbalancedChen.OriginalAscendingThirteenCellOwnership, `ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows, `ImbalancedChen.P1OriginalHistoricalFifthOwnCubeAffineGates, `ImbalancedChen.P1OriginalVariableFifthContinuation, `ImbalancedChen.P1OriginalVariableFourthProfileRegularity]
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
