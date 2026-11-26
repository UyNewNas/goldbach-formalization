import ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge
import Lean

set_option pp.all true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.maxSteps 1000000

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let target := `ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge
  let some idx := env.getModuleIdx? target
    | throwError "Target module missing from audit environment"
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if env.getModuleIdxFor? name == some idx then
      names := names.push name
  names := names.qsort Name.quickLt
  if names.isEmpty then throwError "Target module has no owned declarations"
  liftIO <| IO.println s!"P26_CELL00_AUDIT_IMPORTS {(toJson (env.header.moduleNames.map Name.toString)).compress}"
  liftIO <| IO.println s!"P26_CELL00_AUDIT_INVENTORY {(Json.mkObj [("module", toJson target.toString), ("names", toJson (names.map Name.toString))]).compress}"
  for name in names do
    let some ci := env.find? name
      | throwError "Owned declaration disappeared: {name}"
    if ci.isUnsafe || ci.isPartial || ci.isAxiom then
      throwError "Unsafe, partial, or new axiom declaration: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden axiom {ax} for owned declaration {name}"
    let type ← liftTermElabM do return (← Meta.ppExpr ci.type).pretty
    if type.contains '⋯' then throwError "Truncated owned type: {name}"
    let record := Json.mkObj [("module", toJson target.toString), ("name", toJson name.toString),
      ("type", toJson type), ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
      ("axiom", toJson ci.isAxiom), ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"P26_CELL00_AUDIT_DECL {record.compress}"
  liftIO <| IO.println s!"P26_CELL00_AUDIT_COMPLETE {(Json.mkObj [("module", toJson target.toString), ("count", toJson names.size)]).compress}"
