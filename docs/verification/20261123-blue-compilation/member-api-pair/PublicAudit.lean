import ImbalancedChen.P2SavedFloorSemantics
import ImbalancedChen.P2GuardedReciprocalRounding
import Lean
set_option pp.all true
set_option pp.universes true
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[`ImbalancedChen.P2SavedFloorSemantics, `ImbalancedChen.P2GuardedReciprocalRounding]
  let selected := env.constants.fold (init := #[]) (fun acc name info =>
    match env.getModuleIdxFor? name with
    | some index =>
      if targets.contains (env.header.moduleNames[index.toNat]!) && !isPrivateName name then
        acc.push (name, info)
      else acc
    | none => acc)
  let entries := selected.qsort (fun a b => Name.lt a.1 b.1)
  for (name, info) in entries do
    let some index := env.getModuleIdxFor? name | continue
    let owner := env.header.moduleNames[index.toNat]!
    let axioms ← collectAxioms name
    let isAxiom := match info with | .axiomInfo _ => true | _ => false
    let record := Json.mkObj [
      ("module", toJson owner.toString), ("name", toJson name.toString),
      ("type_expression", toJson (reprStr info.type)),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("transitive_axioms", toJson (axioms.toList.map Name.toString)),
      ("is_axiom_declaration", toJson isAxiom)]
    logInfo m!"AUDIT_RECORD {record.compress}"
    let checkCommand ← `(command| #check @$(mkIdent name))
    elabCommand checkCommand
    let axiomCommand ← `(command| #print axioms $(mkIdent name))
    elabCommand axiomCommand
  logInfo m!"AUDIT_FINISHED {entries.size}"
