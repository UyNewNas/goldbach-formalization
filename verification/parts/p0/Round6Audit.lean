import ImbalancedChen
import Lean.Util.CollectAxioms

/-! Round 6 type export after the full root build.
This reuses the verified LongSlotAudit defining-module inventory and checks.
Only the four listed modules contribute to the 69-declaration census.
The existing final bridge is printed separately with all its analytic hypotheses.
Compiling this audit does not rebuild or replay any production module. -/

set_option pp.all true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : Array (Name × Nat) := #[
    (`ImbalancedChen.HistoricalUpperFiveCellGeometry, 23),
    (`ImbalancedChen.ActualHistoricalFifthCellIntegral, 22),
    (`ImbalancedChen.ActualHistoricalFifthSavingIntegral, 15),
    (`ImbalancedChen.HistoricalFifthCutoffInvariance, 9)]
  let modules := expected.map (·.1)
  let finalBridge := `ImbalancedChen.current_theorem_1_1_of_manuscript_bounds
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in (names.push finalBridge).qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in a P0 batch module: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in a P0 batch module: {name}"
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
    let readableType ← liftTermElabM do
      withOptions (fun opts => (opts.setBool `pp.all false).setBool `pp.explicit false) do
        return (← Meta.ppExpr info.type).pretty
    if type.contains '⋯' || readableType.contains '⋯' then
      throwError "Truncated compiler type for {name}"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    if name == finalBridge then
      liftIO <| IO.println s!"P0_ROUND6_FINAL_BRIDGE {record.compress}"
    else
      liftIO <| IO.println s!"P0_ROUND6_DECL {record.compress}"
  for (m, count) in counts do
    let wanted := expected.foldl (fun n entry => if entry.1 == m then entry.2 else n) 0
    unless count == wanted do
      throwError "Round 6 declaration count mismatch for {m}: expected {wanted}, got {count}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"P0_ROUND6_MODULE {record.compress}"
  unless names.size == 69 do
    throwError "Round 6 total declaration count mismatch: expected 69, got {names.size}"
  liftIO <| IO.println s!"P0_ROUND6_COUNT {names.size}"
