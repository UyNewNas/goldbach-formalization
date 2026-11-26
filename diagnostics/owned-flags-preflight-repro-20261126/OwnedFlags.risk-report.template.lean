import ImbalancedChen.P2OriginalCompactQ80CompleteSoundness
import ImbalancedChen.P2OriginalCompactCachedRun
import ImbalancedChen.P2OriginalCompactQ80FixedBindings
import ImbalancedChen.P4AOrdinaryRootFirstIntegral
import ImbalancedChen.Part4ActualThirdFiniteDensityReserve
import Lean.Util.CollectAxioms

/- Auxiliary risk report only. Inventory mismatches are preserved and reported,
   never accepted. The unchanged original audit still requires exact equality. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedModules : Array Name := #[
__P24_EXPECTED_MODULE_NAMES__
  ]
  unless expectedModules.size == 321 do throwError "Wrong symbolic scope"
  let actualProject := env.header.moduleNames.filter fun n =>
    n.toString.startsWith "ImbalancedChen."
  unless actualProject.qsort Name.lt == expectedModules.qsort Name.lt do
    throwError "Loaded project modules differ from fixed symbolic closure"
  liftIO <| IO.println s!"P24_FLAGS_IMPORTS {(toJson (env.header.moduleNames.map Name.toString)).compress}"
  let mut targetIndices : Std.HashMap ModuleIdx Name := {}
  for moduleName in expectedModules do
    let some idx := env.getModuleIdx? moduleName | throwError "Missing module {moduleName}"
    if targetIndices.contains idx then throwError "Duplicate target module/index {moduleName}"
    targetIndices := targetIndices.insert idx moduleName
  let buckets := env.const2ModIdx.fold
      (init := ({} : Std.HashMap ModuleIdx (Array Name))) fun byModule name idx =>
    if targetIndices.contains idx && (env.find? name).isSome then
      byModule.insert idx (((byModule[idx]?).getD #[]).push name)
    else byModule
  let mut totalChecked : Nat := 0
  let mut totalCandidates : Nat := 0
  let mut totalMissing : Nat := 0
  let mut totalBad : Nat := 0
  let mut totalIssues : Nat := 0
  let mut totalMismatch : Nat := 0
  for moduleName in expectedModules do
    liftIO <| IO.println s!"P24_FLAGS_START {moduleName}"
    let some idx := env.getModuleIdx? moduleName | throwError "Missing module {moduleName}"
    let names := (buckets[idx]?).getD #[]
    let mut serialized : Array Name := #[]
    let mut entries : Array Json := #[]
    let mut legacyDataOK := true
    for i in List.range env.header.modules.size do
      let imported := env.header.modules[i]!
      if imported.module == moduleName then
        let data := env.header.moduleData[i]!
        if data.isModule || !imported.importAll || !imported.hasData then
          legacyDataOK := false
        entries := entries.push <| Json.mkObj [("module_index", toJson i),
          ("data_is_module", toJson data.isModule), ("import_all", toJson imported.importAll),
          ("has_data", toJson imported.hasData), ("serialized_count", toJson data.constNames.size)]
        serialized := serialized ++ data.constNames
    let inventoryOK := entries.size == 1 && legacyDataOK && names.size > 0 &&
      names.qsort Name.lt == serialized.qsort Name.lt
    if !inventoryOK then totalMismatch := totalMismatch + 1
    let envSet := names.foldl (init := ({} : Std.HashMap Name Unit)) fun s n => s.insert n ()
    let serSet := serialized.foldl (init := ({} : Std.HashMap Name Unit)) fun s n => s.insert n ()
    let unionSet := serialized.foldl (init := envSet) fun s n => s.insert n ()
    let candidates := (unionSet.fold (init := (#[] : Array Name)) fun ns n _ => ns.push n).qsort Name.lt
    let serializedOnly := (serialized.filter fun n => !envSet.contains n).qsort Name.lt
    let environmentOnly := (names.filter fun n => !serSet.contains n).qsort Name.lt
    liftIO <| IO.println s!"P24_FLAGS_INVENTORY {(Json.mkObj [("module", toJson moduleName.toString), ("module_index", toJson idx.toNat), ("inventory_ok", toJson inventoryOK), ("legacy_data_ok", toJson legacyDataOK), ("header_entries", toJson entries), ("serialized", toJson (serialized.map Name.toString)), ("environment", toJson (names.map Name.toString)), ("serialized_only", toJson (serializedOnly.map Name.toString)), ("environment_only", toJson (environmentOnly.map Name.toString))]).compress}"
    let mut checkedNames : Array Name := #[]
    let mut missingNames : Array Name := #[]
    let mut bad : Nat := 0
    let mut issues : Nat := 0
    let mut unsafeCount : Nat := 0
    let mut partialCount : Nat := 0
    let mut axiomCount : Nat := 0
    let mut forbiddenCount : Nat := 0
    for name in candidates do
      let owner := env.getModuleIdxFor? name
      let ownerName := owner.bind fun i => env.header.moduleNames[i]?
      let info? := env.find? name
      let inSerialized := serSet.contains name
      let inEnvironment := envSet.contains name
      let ownerOK := owner == some idx
      if !inSerialized || !inEnvironment || !ownerOK || info?.isNone then
        issues := issues + 1
        liftIO <| IO.println s!"P24_FLAGS_DECL_ISSUE {(Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName.toString), ("expected_module_index", toJson idx.toNat), ("owner_index", toJson (owner.map ModuleIdx.toNat)), ("owner_module", toJson (ownerName.map Name.toString)), ("in_serialized", toJson inSerialized), ("in_environment", toJson inEnvironment), ("owner_matches", toJson ownerOK), ("missing_constant_info", toJson info?.isNone)]).compress}"
      match info? with
      | none => missingNames := missingNames.push name
      | some info =>
        let axioms ← collectAxioms name
        let forbidden := axioms.filter fun ax =>
          !(#[`propext, `Classical.choice, `Quot.sound].contains ax)
        checkedNames := checkedNames.push name
        if info.isUnsafe then unsafeCount := unsafeCount + 1
        if info.isPartial then partialCount := partialCount + 1
        if info.isAxiom then axiomCount := axiomCount + 1
        if !forbidden.isEmpty then forbiddenCount := forbiddenCount + 1
        if info.isUnsafe || info.isPartial || info.isAxiom || !forbidden.isEmpty then
          bad := bad + 1
          liftIO <| IO.println s!"P24_FLAGS_BAD {(Json.mkObj [("name", toJson name.toString), ("module", toJson moduleName.toString), ("owner_index", toJson (owner.map ModuleIdx.toNat)), ("owner_module", toJson (ownerName.map Name.toString)), ("owner_matches", toJson ownerOK), ("in_serialized", toJson inSerialized), ("in_environment", toJson inEnvironment), ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom), ("axioms", toJson (axioms.map Name.toString)), ("forbidden_axioms", toJson (forbidden.map Name.toString))]).compress}"
    totalChecked := totalChecked + checkedNames.size
    totalCandidates := totalCandidates + candidates.size
    totalMissing := totalMissing + missingNames.size
    totalBad := totalBad + bad
    totalIssues := totalIssues + issues
    liftIO <| IO.println s!"P24_FLAGS_MODULE {(Json.mkObj [("module", toJson moduleName.toString), ("module_index", toJson idx.toNat), ("inventory_ok", toJson inventoryOK), ("candidate_count", toJson candidates.size), ("checked", toJson checkedNames.size), ("checked_names", toJson (checkedNames.map Name.toString)), ("missing", toJson missingNames.size), ("missing_names", toJson (missingNames.map Name.toString)), ("declaration_issues", toJson issues), ("bad_declarations", toJson bad), ("unsafe_count", toJson unsafeCount), ("partial_count", toJson partialCount), ("axiom_count", toJson axiomCount), ("forbidden_axiom_declarations", toJson forbiddenCount)]).compress}"
  liftIO <| IO.println s!"P24_FLAGS_COMPLETE {(Json.mkObj [("modules", toJson expectedModules.size), ("candidate_occurrences", toJson totalCandidates), ("checked_occurrences", toJson totalChecked), ("missing_occurrences", toJson totalMissing), ("bad_occurrences", toJson totalBad), ("declaration_issue_occurrences", toJson totalIssues), ("inventory_mismatch_modules", toJson totalMismatch), ("all_inventory_ok", toJson (totalMismatch == 0)), ("all_flags_axioms_clear", toJson (totalBad == 0)), ("all_candidates_examined", toJson (totalMissing == 0)), ("diagnostic_only", toJson true), ("full_type_audit", toJson false), ("independent_replay", toJson false), ("original_owned_accepted", toJson false), ("acceptance_credit", toJson false)]).compress}"
  if totalBad > 0 || totalMismatch > 0 || totalMissing > 0 || totalIssues > 0 then
    throwError "Auxiliary risk scan complete: {totalBad} bad declaration occurrences, {totalMismatch} inventory mismatches, {totalMissing} missing ConstantInfo occurrences; no original audit acceptance"
