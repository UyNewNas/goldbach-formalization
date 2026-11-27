import ImbalancedChen.Part3AllLevelContinuedMaass
import Lean.Util.CollectAxioms

set_option pp.fullNames true
set_option pp.explicit true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames.filter fun m =>
    m.toString.startsWith "ImbalancedChen."
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  let mut serialized : Array Name := #[]
  for idx in List.range env.header.modules.size do
    let imported := env.header.modules[idx]!
    if modules.contains imported.module then
      let data := env.header.moduleData[idx]!
      if data.isModule || !imported.importAll || !imported.hasData then
        throwError "Expected complete legacy module data for {imported.module}"
      let owned := names.filter fun name =>
        match env.getModuleIdxFor? name with
        | some i => env.header.moduleNames[i]! == imported.module
        | none => false
      unless owned.qsort Name.lt == data.constNames.qsort Name.lt do
        let missing := data.constNames.filter fun n => !owned.contains n
        let extra := owned.filter fun n => !data.constNames.contains n
        throwError "Serialized and defining-module inventories differ for {imported.module}; missing={missing}; extra={extra}"
      serialized := serialized.push imported.module
  unless serialized.qsort Name.lt == modules.qsort Name.lt do
    throwError "Missing serialized module inventory"
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe || info.isAxiom then
      throwError "Unsafe or axiom declaration: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
    let moduleName := env.header.moduleNames[(env.getModuleIdxFor? name).get!]!
    counts := counts.map fun (m, n) => (m, if m == moduleName then n + 1 else n)
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
    if type.contains '⋯' then throwError "Truncated compiler type: {name}"
    let record := Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName.toString),
      ("kind", toJson kind), ("level_parameters", toJson (info.levelParams.map Name.toString)),
      ("type", toJson type), ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"PART3_AUDIT_DECL {record.compress}"
  for (m, count) in counts do
    unless count > 0 do throwError "Empty project module: {m}"
    liftIO <| IO.println s!"PART3_AUDIT_MODULE {Json.compress <| Json.mkObj [
      ("module", toJson m.toString), ("count", toJson count)]}"
  liftIO <| IO.println s!"PART3_AUDIT_COUNT {names.size}"
