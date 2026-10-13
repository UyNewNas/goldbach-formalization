import ImbalancedChen.HistoricalUpperFiveCellGeometry
import ImbalancedChen.ActualHistoricalFifthCellIntegral
import ImbalancedChen.ActualHistoricalFifthSavingIntegral
import ImbalancedChen.HistoricalFifthCutoffInvariance
import ImbalancedChen.CurrentMainTheorem
import Lean.Util.CollectAxioms

/-! Round 6 type export after the full root build.
The census contains every serialized declaration owned by the four listed modules,
including private and generated declarations. It is checked against the imported
environment, rather than an unsupported historical declaration count.
The existing final bridge is printed separately with all its analytic hypotheses.
Only these defining modules and their dependencies are loaded into this exporter;
the completed root build and the separate root replay/axiom gates remain required.
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
  liftIO do
    IO.println "P0_ROUND6_PHASE environment_ready"
    (← IO.getStdout).flush
  let moduleNames := env.header.moduleNames
  let modules := #[
    `ImbalancedChen.HistoricalUpperFiveCellGeometry,
    `ImbalancedChen.ActualHistoricalFifthCellIntegral,
    `ImbalancedChen.ActualHistoricalFifthSavingIntegral,
    `ImbalancedChen.HistoricalFifthCutoffInvariance]
  let finalBridge := `ImbalancedChen.current_theorem_1_1_of_manuscript_bounds
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut targetIndices : Array ModuleIdx := #[]
  for moduleName in modules do
    let some idx := env.getModuleIdx? moduleName |
      throwError "Missing imported audited module {moduleName}"
    targetIndices := targetIndices.push idx
  liftIO do
    IO.println "P0_ROUND6_PHASE name_index_inventory_start"
    (← IO.getStdout).flush
  -- Traverse only name/index entries for the complete imported ownership census.
  -- ConstantInfo is queried only after selecting one of the four module indices.
  -- The index also contains IR/codegen-only names; these have no ConstantInfo
  -- and are not kernel declarations. All remaining names must match constNames.
  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun names name idx =>
    if targetIndices.contains idx then
      if (env.find? name).isSome then names.push name else names
    else names
  liftIO do
    IO.println s!"P0_ROUND6_PHASE name_index_inventory_done {names.size}"
    (← IO.getStdout).flush
  let mut serializedModules : Array Name := #[]
  let mut serializedTotal := 0
  for idx in List.range env.header.modules.size do
    let imported := env.header.modules[idx]!
    if modules.contains imported.module then
      if serializedModules.contains imported.module then
        throwError "Duplicate serialized module inventory: {imported.module}"
      let data := env.header.moduleData[idx]!
      if data.isModule || !imported.importAll || !imported.hasData then
        throwError "Expected complete legacy module data for {imported.module}"
      let owned := names.filter fun name =>
        (env.getModuleIdxFor? name).map (fun i => moduleNames[i]!) ==
          some imported.module
      unless owned.size > 0 do
        throwError "Audited module has no declarations: {imported.module}"
      unless owned.qsort Name.lt == data.constNames.qsort Name.lt do
        throwError "Serialized declarations and defining-module inventory differ for {imported.module}"
      serializedModules := serializedModules.push imported.module
      serializedTotal := serializedTotal + data.constNames.size
      let record := Json.mkObj [
        ("module", toJson imported.module.toString),
        ("is_module", toJson data.isModule),
        ("import_all", toJson imported.importAll),
        ("has_data", toJson imported.hasData),
        ("serialized_constant_names", toJson (data.constNames.map Name.toString)),
        ("environment_constant_names", toJson (owned.map Name.toString)),
        ("serialized_constant_count", toJson data.constNames.size),
        ("extra_codegen_name_count", toJson data.extraConstNames.size)]
      liftIO <| IO.println s!"P0_ROUND6_SERIALIZED {record.compress}"
  unless serializedModules.qsort Name.lt == modules.qsort Name.lt do
    throwError "Missing Round 6 serialized module data"
  unless serializedTotal == names.size do
    throwError "Round 6 serialized total and environment total differ"
  if names.contains finalBridge then
    throwError "Final bridge must not be included in the owned-module census"
  liftIO do
    IO.println "P0_ROUND6_PHASE serialized_inventory_exact_match"
    (← IO.getStdout).flush
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in (names.push finalBridge).qsort Name.lt do
    liftIO do
      IO.println s!"P0_ROUND6_PHASE declaration_start {name}"
      (← IO.getStdout).flush
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in a P0 batch module: {name}"
    if info.isPartial then
      throwError "Partial declaration in a P0 batch module: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in a P0 batch module: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
    let some idx := env.getModuleIdxFor? name |
      throwError "Missing defining module for {name}"
    let moduleName := moduleNames[idx]!
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
      ("is_unsafe", toJson info.isUnsafe),
      ("is_partial", toJson info.isPartial),
      ("is_axiom", toJson info.isAxiom),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    if name == finalBridge then
      liftIO <| IO.println s!"P0_ROUND6_FINAL_BRIDGE {record.compress}"
    else
      liftIO <| IO.println s!"P0_ROUND6_DECL {record.compress}"
  for (m, count) in counts do
    unless count > 0 do
      throwError "Audited module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"P0_ROUND6_MODULE {record.compress}"
  liftIO <| IO.println s!"P0_ROUND6_COUNT {names.size}"
