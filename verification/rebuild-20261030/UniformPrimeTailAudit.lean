import ImbalancedChen.UniformPrimeTail
import Lean.Util.CollectAxioms
set_option pp.all true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.privateNames true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  liftIO <| IO.println s!"P0_QUEUE_IMPORTS {(toJson (env.header.moduleNames.map Name.toString)).compress}"
  let moduleName := `ImbalancedChen.UniformPrimeTail
  let some idx := env.getModuleIdx? moduleName | throwError "Missing target module"
  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>
    if i == idx && (env.find? n).isSome then ns.push n else ns
  let mut serialized : Array Name := #[]
  let mut found := false
  for i in List.range env.header.modules.size do
    let imported := env.header.modules[i]!
    if imported.module == moduleName then
      if found then throwError "Duplicate module"
      found := true
      let data := env.header.moduleData[i]!
      if data.isModule || !imported.importAll || !imported.hasData then
        throwError "Incomplete imported legacy data"
      serialized := data.constNames
  unless found && names.size > 0 && names.qsort Name.lt == serialized.qsort Name.lt do
    throwError "Complete serialized/environment inventory mismatch"
  liftIO <| IO.println s!"P0_QUEUE_INVENTORY {(Json.mkObj [("module", toJson moduleName.toString), ("serialized", toJson (serialized.map Name.toString)), ("environment", toJson (names.map Name.toString))]).compress}"
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration"
    if info.isUnsafe || info.isPartial || info.isAxiom then throwError "Unsafe/partial/axiom target {name}: unsafe={info.isUnsafe}, partial={info.isPartial}, axiom={info.isAxiom}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Forbidden transitive axiom {ax}"
    let type ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
    if type.contains '⋯' then throwError "Truncated type"
    let record := Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName.toString),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom),
      ("type", toJson type), ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"P0_QUEUE_DECL {record.compress}"
