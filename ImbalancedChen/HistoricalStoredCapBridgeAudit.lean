import ImbalancedChen.HistoricalStoredCapBridge
import Lean.Util.CollectAxioms
set_option warningAsError true

/-! Compiler declaration and axiom inventory, including generated/private names. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ImbalancedChen.HistoricalStoredCapBridge]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then throwError "Unsafe declaration in audited module: {name}"
    if info.isAxiom then throwError "Unproved axiom declaration in audited module: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do throwError "Forbidden transitive axiom {ax} in {name}"
    let idx := (env.getModuleIdxFor? name).get!
    let moduleName := env.header.moduleNames[idx]!
    counts := counts.map fun (m, count) => (m, if m == moduleName then count + 1 else count)
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
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("type", toJson type),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"PART1_ROUND4_BRIDGE_AUDIT_DECL {record.compress}"
  for (m, count) in counts do
    unless count > 0 do throwError "Audited module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"PART1_ROUND4_BRIDGE_AUDIT_MODULE {record.compress}"
  liftIO <| IO.println s!"PART1_ROUND4_BRIDGE_AUDIT_COUNT {names.size}"
