import ImbalancedChen.P2OriginalCompactQ80CompleteSoundness
import ImbalancedChen.P2OriginalCompactCachedRun
import ImbalancedChen.P2OriginalCompactQ80FixedBindings
import ImbalancedChen.P4AOrdinaryRootFirstIntegral
import ImbalancedChen.Part4ActualThirdFiniteDensityReserve
import Lean.Util.CollectAxioms

/- Diagnostic only: no independent replay and no full declaration-type output.
   The original per-module audit remains required. No source options are set. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedModules : Array Name := #[
__P24_EXPECTED_MODULE_NAMES__
  ]
  unless expectedModules.size == 321 do
    throwError "Wrong symbolic diagnostic scope"
  let actualProject := env.header.moduleNames.filter fun n =>
    n.toString.startsWith "ImbalancedChen."
  unless actualProject.qsort Name.lt == expectedModules.qsort Name.lt do
    throwError "Loaded project modules differ from the fixed symbolic closure"
  liftIO <| IO.println s!"P24_FLAGS_IMPORTS {(toJson (env.header.moduleNames.map Name.toString)).compress}"
  let mut targetIndices : Std.HashMap ModuleIdx Name := {}
  for moduleName in expectedModules do
    let some idx := env.getModuleIdx? moduleName | throwError "Missing target module {moduleName}"
    if targetIndices.contains idx then
      throwError "Repeated target module/index {moduleName}"
    targetIndices := targetIndices.insert idx moduleName
  -- Same ownership criterion as the original template, evaluated in one fold.
  -- Code-generator-only extra names lacking ConstantInfo are excluded exactly
  -- as in that template; private and generated serialized names are not filtered.
  let buckets := env.const2ModIdx.fold
      (init := ({} : Std.HashMap ModuleIdx (Array Name))) fun byModule name idx =>
    if targetIndices.contains idx && (env.find? name).isSome then
      byModule.insert idx (((byModule[idx]?).getD #[]).push name)
    else byModule
  let mut totalOwned := 0
  let mut totalBad := 0
  let mut totalUnsafe := 0
  let mut totalPartial := 0
  let mut totalAxiom := 0
  let mut totalForbiddenAxiom := 0
  for moduleName in expectedModules do
    liftIO <| IO.println s!"P24_FLAGS_START {moduleName}"
    let some idx := env.getModuleIdx? moduleName | throwError "Missing target module {moduleName}"
    let names := (buckets[idx]?).getD #[]
    let mut serialized : Array Name := #[]
    let mut found := false
    for i in List.range env.header.modules.size do
      let imported := env.header.modules[i]!
      if imported.module == moduleName then
        if found then throwError "Duplicate module {moduleName}"
        found := true
        let data := env.header.moduleData[i]!
        if data.isModule || !imported.importAll || !imported.hasData then
          throwError "Incomplete imported legacy data for {moduleName}"
        serialized := data.constNames
    unless found && names.size > 0 && names.qsort Name.lt == serialized.qsort Name.lt do
      throwError "Complete serialized/environment inventory mismatch for {moduleName}"
    liftIO <| IO.println s!"P24_FLAGS_INVENTORY {(Json.mkObj [("module", toJson moduleName.toString), ("module_index", toJson idx.toNat), ("serialized", toJson (serialized.map Name.toString)), ("environment", toJson (names.map Name.toString))]).compress}"
    let mut checked := 0
    let mut bad := 0
    let mut unsafeCount := 0
    let mut partialCount := 0
    let mut axiomCount := 0
    let mut forbiddenAxiomCount := 0
    for name in names.qsort Name.lt do
      unless env.getModuleIdxFor? name == some idx do
        throwError "Declaration ownership changed for {name}"
      let some info := env.find? name | throwError "Missing inventoried declaration {name}"
      let axioms ← collectAxioms name
      let forbidden := axioms.filter fun ax =>
        !(#[`propext, `Classical.choice, `Quot.sound].contains ax)
      checked := checked + 1
      if info.isUnsafe then unsafeCount := unsafeCount + 1
      if info.isPartial then partialCount := partialCount + 1
      if info.isAxiom then axiomCount := axiomCount + 1
      if !forbidden.isEmpty then forbiddenAxiomCount := forbiddenAxiomCount + 1
      if info.isUnsafe || info.isPartial || info.isAxiom || !forbidden.isEmpty then
        bad := bad + 1
        liftIO <| IO.println s!"P24_FLAGS_BAD {(Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName.toString), ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom), ("axioms", toJson (axioms.map Name.toString)), ("forbidden_axioms", toJson (forbidden.map Name.toString))]).compress}"
    totalOwned := totalOwned + checked
    totalBad := totalBad + bad
    totalUnsafe := totalUnsafe + unsafeCount
    totalPartial := totalPartial + partialCount
    totalAxiom := totalAxiom + axiomCount
    totalForbiddenAxiom := totalForbiddenAxiom + forbiddenAxiomCount
    liftIO <| IO.println s!"P24_FLAGS_MODULE {(Json.mkObj [("module", toJson moduleName.toString), ("module_index", toJson idx.toNat), ("serialized_count", toJson serialized.size), ("environment_count", toJson names.size), ("checked", toJson checked), ("bad_declarations", toJson bad), ("unsafe_count", toJson unsafeCount), ("partial_count", toJson partialCount), ("axiom_count", toJson axiomCount), ("forbidden_axiom_declarations", toJson forbiddenAxiomCount)]).compress}"
  liftIO <| IO.println s!"P24_FLAGS_COMPLETE {(Json.mkObj [("modules", toJson expectedModules.size), ("checked", toJson totalOwned), ("bad_declarations", toJson totalBad), ("unsafe_count", toJson totalUnsafe), ("partial_count", toJson totalPartial), ("axiom_count", toJson totalAxiom), ("forbidden_axiom_declarations", toJson totalForbiddenAxiom), ("all_flags_axioms_clear", toJson (totalBad == 0)), ("diagnostic_only", toJson true), ("full_type_audit", toJson false), ("independent_replay", toJson false), ("acceptance_credit", toJson false)]).compress}"
  if totalBad > 0 then
    throwError "Aggregate owned flag/axiom diagnostic found {totalBad} declaration(s); see all P24_FLAGS_BAD records"
