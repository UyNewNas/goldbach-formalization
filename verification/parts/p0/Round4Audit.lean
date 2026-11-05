import ImbalancedChen
import Lean.Util.CollectAxioms

/-! Round 4 type export after the full root build.
Audit all sixteen original/split modules and every raw serialized occurrence.
The Python consumer preserves all 414 historical complete-type hashes. The 61
old module-private matcher declarations map only to the exact GeometryChecked
names; an additional complete 61-name CertificateInputs realization group is
required with the same full types, for exactly 475 current owned declarations. No type-text normalization is used.
The scope, all production source hashes, name mappings and original baseline
are frozen. Source-proof declarations are not renamed or omitted. Existing full
build, root kernel replay and axiom gates remain required. -/

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
    IO.println "P0_ROUND4_PHASE environment_ready"
    (← IO.getStdout).flush
  let moduleNames := env.header.moduleNames
  let modules := #[
    `ImbalancedChen.StoredHistoricalBoxPermit,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Data,
    `ImbalancedChen.Certificates.PairedV2Batch4To64,
    `ImbalancedChen.Certificates.PairedV2Prefix64,
    `ImbalancedChen.Certificates.PairedV2Batch4To64CertificateInputs,
    `ImbalancedChen.Certificates.PairedV2Batch4To64GeometryChecked,
    `ImbalancedChen.Certificates.PairedV2Batch4To64LowerSum,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Rows0004To0012,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Rows0012To0020,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Rows0020To0028,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Rows0028To0036,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Rows0036To0044,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Rows0044To0052,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Rows0052To0060,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Rows0060To0064,
    `ImbalancedChen.Certificates.PairedV2Batch4To64UpperSum]
  let finalBridge := `ImbalancedChen.current_theorem_1_1_of_manuscript_bounds
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut targetIndices : Array ModuleIdx := #[]
  for moduleName in modules do
    let some idx := env.getModuleIdx? moduleName |
      throwError "Missing imported audited module {moduleName}"
    targetIndices := targetIndices.push idx
  liftIO do
    IO.println "P0_ROUND4_PHASE name_index_inventory_start"
    (← IO.getStdout).flush
  -- Traverse only name/index entries for the complete imported ownership census.
  -- ConstantInfo is queried only after selecting one of the sixteen module indices.
  -- The index also contains IR/codegen-only names; these have no ConstantInfo
  -- and are not kernel declarations. These names must exactly match the owned
  -- partition of the serialized inventory, not all shared theorem occurrences.
  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun names name idx =>
    if targetIndices.contains idx then
      if (env.find? name).isSome then names.push name else names
    else names
  liftIO do
    IO.println s!"P0_ROUND4_PHASE name_index_inventory_done {names.size}"
    (← IO.getStdout).flush
  let kindOf := fun (info : ConstantInfo) => match info with
    | .thmInfo _ => "theorem"
    | .defnInfo _ => "definition"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .axiomInfo _ => "axiom"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
  let mut serializedModules : Array Name := #[]
  let mut ownedTotal := 0
  let mut occurrenceTotal := 0
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
      let serializedOwned := data.constNames.filter fun name =>
        (env.getModuleIdxFor? name).map (fun i => moduleNames[i]!) ==
          some imported.module
      let shared := data.constNames.filter fun name => !serializedOwned.contains name
      -- Retain concrete sets before any assertion, including on a failing run.
      let diagnostic := Json.mkObj [
        ("module", toJson imported.module.toString),
        ("serialized_constant_names", toJson (data.constNames.map Name.toString)),
        ("owned_constant_names", toJson (serializedOwned.map Name.toString)),
        ("shared_constant_names", toJson (shared.map Name.toString)),
        ("environment_constant_names", toJson (owned.map Name.toString)),
        ("missing_owned_names", toJson ((owned.filter fun n => !serializedOwned.contains n).map Name.toString)),
        ("unexpected_owned_names", toJson ((serializedOwned.filter fun n => !owned.contains n).map Name.toString))]
      liftIO do
        IO.println s!"P0_ROUND4_INVENTORY_DIAGNOSTIC {diagnostic.compress}"
        (← IO.getStdout).flush
      unless data.constNames == data.constants.map (·.name) do
        throwError "Serialized names and ConstantInfo entries differ for {imported.module}"
      let mut seen : Array Name := #[]
      for name in data.constNames do
        if seen.contains name then
          throwError "Duplicate serialized declaration in {imported.module}: {name}"
        seen := seen.push name
      unless owned.size > 0 do
        throwError "Audited module has no declarations: {imported.module}"
      unless owned.qsort Name.lt == serializedOwned.qsort Name.lt do
        throwError "Serialized owned declarations and defining-module inventory differ for {imported.module}"
      for info in data.constants do
        let name := info.name
        let some current := env.find? name |
          throwError "Serialized declaration absent from environment: {imported.module}: {name}"
        let some ownerIdx := env.getModuleIdxFor? name |
          throwError "Serialized declaration has no defining module: {name}"
        let owner := moduleNames[ownerIdx]!
        if info.isUnsafe || current.isUnsafe || info.isPartial || current.isPartial ||
            info.isAxiom || current.isAxiom then
          throwError "Unsafe, partial, or axiom serialized declaration: {imported.module}: {name}"
        unless info.name == current.name && info.type == current.type &&
            info.levelParams == current.levelParams &&
            kindOf info == kindOf current do
          throwError "Serialized declaration identity differs from environment: {imported.module}: {name}"
        let isShared := owner != imported.module
        let mut sharedValidation := Json.null
        if isShared then
          -- Lean 4.33 permits duplicate realized theorems with equal name, type,
          -- universe parameters and `all`; proof values need not be identical.
          -- The first module retains ownership. An IR-only name is insufficient.
          unless ownerIdx.toNat < idx do
            throwError "Shared declaration owner does not precede serialization: {name}"
          let ownerData := env.header.moduleData[ownerIdx]!
          let some original := ownerData.constants.find? (fun candidate => candidate.name == name) |
            throwError "Shared declaration absent from owner's serialized constants: {name}"
          match info, original, current with
          | .thmInfo raw, .thmInfo first, .thmInfo selected =>
            unless raw.type == first.type && raw.levelParams == first.levelParams &&
                raw.all == first.all && raw.all == selected.all do
              throwError "Shared theorem identity differs from its owner or environment: {name}"
          | _, _, _ => throwError "Shared serialized declaration is not a theorem: {name}"
          sharedValidation := Json.mkObj [
            ("owner_precedes_serialized", toJson true),
            ("owner_has_serialized_theorem", toJson true),
            ("type_matches_owner", toJson true),
            ("level_params_match_owner", toJson true),
            ("theorem_all_matches_owner_and_environment", toJson true)]
        -- Inspect this exact serialized body, not collectAxioms(name), whose
        -- imported result is indexed by the first owner. All direct type/body
        -- dependencies must exist in the kernel environment; each then retains
        -- the standard transitive axiom allowlist check. Inspect inductive
        -- constructor dependencies as well, as Lean's collector does.
        let expressions := match info with
          | .defnInfo value => #[value.type, value.value]
          | .thmInfo value => #[value.type, value.value]
          | .opaqueInfo value => #[value.type, value.value]
          | _ => #[info.type]
        let mut dependencies : Array Name := #[]
        for expression in expressions do
          for dependency in expression.getUsedConstants do
            unless dependencies.contains dependency do
              dependencies := dependencies.push dependency
        if let .inductInfo value := info then
          for ctorName in value.ctors do
            unless dependencies.contains ctorName do
              dependencies := dependencies.push ctorName
        if kindOf info == "theorem" && dependencies.contains name then
          throwError "Self-referential raw theorem dependency: {imported.module}: {name}"
        let mut rawAxioms : Array Name := #[]
        for dependency in dependencies do
          unless (env.checked.get.find? dependency).isSome do
            throwError "Missing raw serialized dependency: {name}: {dependency}"
          let dependencyAxioms ← collectAxioms dependency
          for ax in dependencyAxioms do
            unless allowed.contains ax do
              throwError "Forbidden raw serialized axiom dependency: {name}: {dependency}: {ax}"
            unless rawAxioms.contains ax do
              rawAxioms := rawAxioms.push ax
        let occurrence := Json.mkObj [
          ("serialized_module", toJson imported.module.toString),
          ("name", toJson name.toString),
          ("owner_module", toJson owner.toString),
          ("kind", toJson (kindOf info)),
          ("is_unsafe", toJson info.isUnsafe),
          ("is_partial", toJson info.isPartial),
          ("is_axiom", toJson info.isAxiom),
          ("type_matches_environment", toJson true),
          ("level_params_match_environment", toJson true),
          ("kind_matches_environment", toJson true),
          ("all_dependencies_present", toJson true),
          ("raw_dependency_names", toJson ((dependencies.qsort Name.lt).map Name.toString)),
          ("raw_dependency_axioms", toJson ((rawAxioms.qsort Name.lt).map Name.toString)),
          ("raw_expression_count", toJson expressions.size),
          ("shared", toJson isShared),
          ("shared_validation", sharedValidation)]
        liftIO <| IO.println s!"P0_ROUND4_OCCURRENCE {occurrence.compress}"
      serializedModules := serializedModules.push imported.module
      ownedTotal := ownedTotal + serializedOwned.size
      occurrenceTotal := occurrenceTotal + data.constNames.size
      let record := Json.mkObj [
        ("module", toJson imported.module.toString),
        ("is_module", toJson data.isModule),
        ("import_all", toJson imported.importAll),
        ("has_data", toJson imported.hasData),
        ("serialized_constant_names", toJson (data.constNames.map Name.toString)),
        ("owned_constant_names", toJson (serializedOwned.map Name.toString)),
        ("shared_constant_names", toJson (shared.map Name.toString)),
        ("environment_constant_names", toJson (owned.map Name.toString)),
        ("serialized_constant_count", toJson data.constNames.size),
        ("owned_constant_count", toJson serializedOwned.size),
        ("shared_constant_count", toJson shared.size),
        ("extra_codegen_name_count", toJson data.extraConstNames.size)]
      liftIO <| IO.println s!"P0_ROUND4_SERIALIZED {record.compress}"
  unless serializedModules.qsort Name.lt == modules.qsort Name.lt do
    throwError "Missing Round 4 serialized module data"
  unless ownedTotal == names.size do
    throwError "Round 4 serialized owned total and environment total differ"
  if names.contains finalBridge then
    throwError "Final bridge must not be included in the owned-module census"
  liftIO do
    IO.println s!"P0_ROUND4_PHASE serialized_occurrences_checked {occurrenceTotal}"
    IO.println "P0_ROUND4_PHASE serialized_owned_inventory_exact_match"
    (← IO.getStdout).flush
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in (names.push finalBridge).qsort Name.lt do
    liftIO do
      IO.println s!"P0_ROUND4_PHASE declaration_start {name}"
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
      liftIO <| IO.println s!"P0_ROUND4_FINAL_BRIDGE {record.compress}"
    else
      liftIO <| IO.println s!"P0_ROUND4_DECL {record.compress}"
  for (m, count) in counts do
    unless count > 0 do
      throwError "Audited module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"P0_ROUND4_MODULE {record.compress}"
  liftIO <| IO.println s!"P0_ROUND4_COUNT {names.size}"
