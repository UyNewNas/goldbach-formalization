import ImbalancedChen.HistoricalThreeStageTelescope
import Lean.Util.CollectAxioms
set_option warningAsError true
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true

/-! Complete actual defining-module census, compiler types, transitive axioms. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ImbalancedChen.HistoricalThreeStageTelescope]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing declaration {name}"
    if info.isUnsafe then throwError "Unsafe declaration {name}"
    if info.isAxiom then throwError "New axiom {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do throwError "Forbidden axiom {ax} in {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let type ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson env.header.moduleNames[(env.getModuleIdxFor? name).get!]!.toString),
      ("kind", toJson kind),
      ("type", toJson type),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"PART1_THREE_STAGE_AUDIT_DECL {record.compress}"
  unless names.size > 0 do throwError "Three-stage module has no declarations"
  liftIO <| IO.println s!"PART1_THREE_STAGE_AUDIT_COUNT {names.size}"
