import ImbalancedChen.P1SignedExitPolicyComparison
import Lean.Util.CollectAxioms

set_option pp.all true
set_option pp.maxSteps 1000000
set_option pp.universes true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ImbalancedChen.P1SignedExitPolicyComparison]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  -- Cache this computed modules.map exactly once, outside the full constant fold.
  let moduleNames := env.header.moduleNames
  let selected := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains moduleNames[idx.toNat]! then names.push name else names
    | none => names
  let names := selected.qsort Name.lt
  let inventory := Json.mkObj [("names", toJson (names.map Name.toString))]
  liftIO <| IO.println s!"MEMBER_OWNED_NAMES {inventory.compress}"
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in names do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    let some owner := env.getModuleIdxFor? name | throwError "Missing declaration owner {name}"
    let moduleName := moduleNames[owner.toNat]!
    unless modules.contains moduleName do
      throwError "Inventoried declaration owner changed: {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in the audited roots: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in the audited roots: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
    let type ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("is_private", toJson (isPrivateName name)),
      ("type", toJson type),
      ("type_expression", toJson (reprStr info.type)),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"AUDIT_RECORD {record.compress}"
    counts := counts.map fun (m, count) => (m, if m == moduleName then count + 1 else count)
  for (m, count) in counts do
    unless count > 0 do
      throwError "Audited root module has no owned declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"MEMBER_OWNED_MODULE {record.compress}"
  liftIO <| IO.println s!"MEMBER_OWNED_COUNT {names.size}"
