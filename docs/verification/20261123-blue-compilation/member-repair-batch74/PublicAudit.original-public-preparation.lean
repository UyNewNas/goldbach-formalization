import ImbalancedChen.Data.P5SubdivisionStoredBlock060
import ImbalancedChen.Data.P5SubdivisionStoredBlock061
import ImbalancedChen.Data.P5SubdivisionStoredBlock062
import ImbalancedChen.Data.P5SubdivisionStoredBlock063
import ImbalancedChen.Data.P5SubdivisionStoredBlock064
import ImbalancedChen.Data.P5SubdivisionStoredBlock065
import ImbalancedChen.Data.P5SubdivisionStoredBlock066
import ImbalancedChen.Data.P5SubdivisionStoredBlock067
import ImbalancedChen.Data.P5SubdivisionStoredBlock068
import ImbalancedChen.Data.P5SubdivisionStoredBlock069
import Lean
set_option pp.all true
set_option pp.universes true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let targets : Array Name := #[`ImbalancedChen.Data.P5SubdivisionStoredBlock060, `ImbalancedChen.Data.P5SubdivisionStoredBlock061, `ImbalancedChen.Data.P5SubdivisionStoredBlock062, `ImbalancedChen.Data.P5SubdivisionStoredBlock063, `ImbalancedChen.Data.P5SubdivisionStoredBlock064, `ImbalancedChen.Data.P5SubdivisionStoredBlock065, `ImbalancedChen.Data.P5SubdivisionStoredBlock066, `ImbalancedChen.Data.P5SubdivisionStoredBlock067, `ImbalancedChen.Data.P5SubdivisionStoredBlock068, `ImbalancedChen.Data.P5SubdivisionStoredBlock069]
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
