import ImbalancedChen.P6OriginalMarkedIntegralPrices
import ImbalancedChen.P6OriginalZeroMarkedIntegralCost
import Lean.Util.CollectAxioms

set_option pp.all true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `ImbalancedChen.P6OriginalMarkedIntegralPrices,
    `ImbalancedChen.P6OriginalZeroMarkedIntegralCost]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let moduleNames := env.header.moduleNames
  let foldNames := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains moduleNames[idx.toNat]! then names.push name else names
    | none => names
  let names := foldNames.qsort Name.lt
  let inventory := Json.mkObj [("cached_fold", toJson (names.map Name.toString))]
  liftIO <| IO.println s!"P6_AUDIT_NAME_SETS {inventory.compress}"
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
    let moduleName := moduleNames[idx.toNat]!
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
    liftIO <| IO.println s!"P6_AUDIT_DECL {record.compress}"
  for (m, count) in counts do
    -- The legacy regression file uses anonymous examples, which need not persist.
    unless count > 0 do
      throwError "Audited module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"P6_AUDIT_MODULE {record.compress}"
  liftIO <| IO.println s!"P6_AUDIT_COUNT {names.size}"
