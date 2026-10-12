import ImbalancedChen.CurrentChenMeanLedger
import ImbalancedChen.CurrentChenLowerScale
import ImbalancedChen.CurrentChenBuchstabRefinement
import Lean.Util.CollectAxioms

/-!
The declaration inventory comes from Lean's environment and defining-module
metadata, not a source-code regular expression or namespace filter. It includes
private declarations, structure fields and automatically generated declarations.
`collectAxioms` is the bundled Lean transitive collector also used by `#print axioms`.
The command fails if any inventoried declaration is unsafe, is an axiom,
or transitively uses anything outside the standard three-axiom allowlist.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ImbalancedChen.CurrentChenMeanLedger,
    `ImbalancedChen.CurrentChenLowerScale,
    `ImbalancedChen.CurrentChenBuchstabRefinement]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in the audited modules: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in the audited modules: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
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
    let type ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("type", toJson type),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"CHEN_P5_AUDIT_DECL {record.compress}"
  for (m, count) in counts do
    -- Every audited proof module must have a nonempty declaration inventory.
    unless count > 0 do
      throwError "Audited module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"CHEN_P5_AUDIT_MODULE {record.compress}"
  liftIO <| IO.println s!"CHEN_P5_AUDIT_COUNT {names.size}"
  -- Also print and audit the two existing count bridges used to interpret
  -- the finite scale. These imports are separate from the own-module inventory.
  let dependencyNames := #[
    `ImbalancedChen.currentChenPairedPrimeSum_le_four_D12_add_error,
    `ImbalancedChen.eventually_currentChenPairedPrimeSum_sub_normalized_error_le_four_D12]
  for name in dependencyNames do
    let some info := env.find? name | throwError "Missing imported count bridge {name}"
    if info.isUnsafe || info.isAxiom then
      throwError "Invalid imported count bridge {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in imported count bridge {name}"
    let type ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("type", toJson type),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"CHEN_P5_IMPORTED_COUNT_BRIDGE {record.compress}"
