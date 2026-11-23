import ImbalancedChen.Data.P5SubdivisionStoredBlock040
import ImbalancedChen.Data.P5SubdivisionStoredBlock041
import ImbalancedChen.Data.P5SubdivisionStoredBlock042
import ImbalancedChen.Data.P5SubdivisionStoredBlock043
import ImbalancedChen.Data.P5SubdivisionStoredBlock044
import ImbalancedChen.Data.P5SubdivisionStoredBlock045
import ImbalancedChen.Data.P5SubdivisionStoredBlock046
import ImbalancedChen.Data.P5SubdivisionStoredBlock047
import ImbalancedChen.Data.P5SubdivisionStoredBlock048
import ImbalancedChen.Data.P5SubdivisionStoredBlock049
import Lean
set_option pp.all true
set_option pp.universes true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let targets : Array Name := #[`ImbalancedChen.Data.P5SubdivisionStoredBlock040, `ImbalancedChen.Data.P5SubdivisionStoredBlock041, `ImbalancedChen.Data.P5SubdivisionStoredBlock042, `ImbalancedChen.Data.P5SubdivisionStoredBlock043, `ImbalancedChen.Data.P5SubdivisionStoredBlock044, `ImbalancedChen.Data.P5SubdivisionStoredBlock045, `ImbalancedChen.Data.P5SubdivisionStoredBlock046, `ImbalancedChen.Data.P5SubdivisionStoredBlock047, `ImbalancedChen.Data.P5SubdivisionStoredBlock048, `ImbalancedChen.Data.P5SubdivisionStoredBlock049]
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
