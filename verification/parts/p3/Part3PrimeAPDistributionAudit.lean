import ImbalancedChen.Part3PrimeAPDistribution
import Lean.Util.CollectAxioms

/-!
Part 3 supplier audit for the exact `Part3PrimeAPDistribution` object used
before compiling `Part3PrimeAPDistribution`.  The production module is in the
legacy object format, so the complete serialized constant list is checked
against the environment's defining-module inventory.  Every owned declaration,
including private and generated declarations, receives a complete compiler type
and transitive-axiom inventory.
-/

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
  let moduleName := `ImbalancedChen.Part3PrimeAPDistribution
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for importedModule in env.header.moduleNames do
    let path ← liftIO <| Lean.findOLean importedModule
    let record := Json.mkObj [
      ("module", toJson importedModule.toString),
      ("olean", toJson path.toString)]
    liftIO <| IO.println s!"PART3_AP_IMPORT {record.compress}"
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if env.header.moduleNames[idx]! == moduleName then names.push name else names
    | none => names
  let mut foundSerialized := false
  for idx in List.range env.header.modules.size do
    let imported := env.header.modules[idx]!
    if imported.module == moduleName then
      foundSerialized := true
      let data := env.header.moduleData[idx]!
      if data.isModule || !imported.importAll || !imported.hasData then
        throwError "Expected complete legacy module data for {moduleName}"
      unless names.qsort Name.lt == data.constNames.qsort Name.lt do
        throwError "Serialized declarations and defining-module inventory differ"
      let record := Json.mkObj [
        ("module", toJson moduleName.toString),
        ("is_module", toJson data.isModule),
        ("import_all", toJson imported.importAll),
        ("has_data", toJson imported.hasData),
        ("serialized_constant_count", toJson data.constNames.size),
        ("extra_codegen_name_count", toJson data.extraConstNames.size)]
      liftIO <| IO.println s!"PART3_AP_SERIALIZED {record.compress}"
  unless foundSerialized do
    throwError "Missing serialized module record for {moduleName}"
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in the supplier module: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in the supplier module: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
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
      ("level_parameters", toJson (info.levelParams.map Name.toString)),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"PART3_AP_DECL {record.compress}"
  unless names.size > 0 do
    throwError "Supplier module has no declarations"
  let summary := Json.mkObj [
    ("module", toJson moduleName.toString),
    ("count", toJson names.size)]
  liftIO <| IO.println s!"PART3_AP_MODULE {summary.compress}"
