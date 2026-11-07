import ImbalancedChen.Part3LongSlotNormalization
import Lean.Util.CollectAxioms

/-!
Local Part 3 batch: inventory every declaration by defining module, including
private and generated declarations.  The complete Part 3 audit remains unchanged.
The production source uses Lean's legacy, non-`module` format. A legacy importer
loads complete private data automatically; `import all` syntax cannot be used
here. The inventory below is also checked against the serialized constant names.
The imported module names and Lean-resolved object paths are emitted so the
execution receipt can bind this audit to the actual production object and imports.
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
  let modules := #[`ImbalancedChen.Part3LongSlotNormalization]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for moduleName in env.header.moduleNames do
    let path ← liftIO <| Lean.findOLean moduleName
    let record := Json.mkObj [
      ("module", toJson moduleName.toString),
      ("olean", toJson path.toString)]
    liftIO <| IO.println s!"PART3_LOCAL_IMPORT {record.compress}"
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  for idx in List.range env.header.modules.size do
    let imported := env.header.modules[idx]!
    if modules.contains imported.module then
      let data := env.header.moduleData[idx]!
      if data.isModule || !imported.importAll || !imported.hasData then
        throwError "Expected complete legacy module data for {imported.module}"
      let owned := names.filter fun name =>
        (env.getModuleIdxFor? name).map (fun i => env.header.moduleNames[i]!) ==
          some imported.module
      unless owned.qsort Name.lt == data.constNames.qsort Name.lt do
        throwError "Serialized declarations and defining-module inventory differ"
      let record := Json.mkObj [
        ("module", toJson imported.module.toString),
        ("is_module", toJson data.isModule),
        ("import_all", toJson imported.importAll),
        ("has_data", toJson imported.hasData),
        ("serialized_constant_count", toJson data.constNames.size),
        ("extra_codegen_name_count", toJson data.extraConstNames.size)]
      liftIO <| IO.println s!"PART3_LOCAL_SERIALIZED {record.compress}"
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in the local Part 3 module: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in the local Part 3 module: {name}"
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
      ("level_parameters", toJson (info.levelParams.map Name.toString)),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"PART3_LOCAL_DECL {record.compress}"
  for (m, count) in counts do
    unless count > 0 do
      throwError "Audited module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"PART3_LOCAL_MODULE {record.compress}"
  liftIO <| IO.println s!"PART3_LOCAL_COUNT {names.size}"
