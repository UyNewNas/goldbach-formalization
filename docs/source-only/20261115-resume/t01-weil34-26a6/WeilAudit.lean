import LeanPool.KloostermanWeil.Stepanov.Algebra
import LeanPool.KloostermanWeil.Stepanov.Auxiliary
import LeanPool.KloostermanWeil.Stepanov.Parameters
import LeanPool.KloostermanWeil.Stepanov.CurveCount
import LeanPool.KloostermanWeil.Stepanov.Defect
import LeanPool.KloostermanWeil.Stepanov.SpecializedCurve
import LeanPool.KloostermanWeil.Carlitz.FactorData
import LeanPool.KloostermanWeil.Carlitz.DicksonFiniteAlgebra
import LeanPool.KloostermanWeil.Carlitz.CoefficientEquivalence
import LeanPool.KloostermanWeil.Carlitz.FactorWeight
import LeanPool.KloostermanWeil.Weil.PrimeFoundation
import LeanPool.KloostermanWeil.Carlitz.ExtensionDefinitions
import LeanPool.KloostermanWeil.Carlitz.MinimalPolynomialInverse
import LeanPool.KloostermanWeil.Carlitz.ClassValue
import LeanPool.KloostermanWeil.Carlitz.ConjugateDecomposition
import LeanPool.KloostermanWeil.Carlitz.ClassGhost
import LeanPool.KloostermanWeil.Carlitz.RelevantIrreducibles
import LeanPool.KloostermanWeil.Carlitz.IrreducibleGhost
import LeanPool.KloostermanWeil.Carlitz.NewtonIndex
import LeanPool.KloostermanWeil.Carlitz.NewtonSum
import LeanPool.KloostermanWeil.Carlitz.FormalAlgebra
import LeanPool.KloostermanWeil.Carlitz.GeneratingIdentity
import LeanPool.KloostermanWeil.Carlitz.RecurrencePackage
import LeanPool.KloostermanWeil.Stepanov.FiniteSum
import LeanPool.KloostermanWeil.Stepanov.ArtinSchreier
import LeanPool.KloostermanWeil.Stepanov.CurveTrace
import LeanPool.KloostermanWeil.Stepanov.ScalarExtensionSum
import LeanPool.KloostermanWeil.Stepanov.PointCountBridge
import LeanPool.KloostermanWeil.Stepanov.CarlitzRoots
import LeanPool.KloostermanWeil.Stepanov.PowerSumSpectral
import LeanPool.KloostermanWeil.Stepanov.SpectralBound
import LeanPool.KloostermanWeil.Stepanov.PrimeWeil
import LeanPool.KloostermanWeil.Stepanov.PrimeWeilBridge
import LeanPool.KloostermanWeil.Weil.PrimeKloosterman
import Lean.Util.FoldConsts
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
  for idx in List.range env.header.modules.size do
    let imported := env.header.modules[idx]!
    let selected := env.header.moduleData[idx]!
    let record := Json.mkObj [
      ("module", toJson imported.module.toString),
      ("is_module", toJson selected.isModule),
      ("has_data", toJson imported.hasData),
      ("import_all", toJson imported.importAll)]
    liftIO <| IO.println s!"WEIL34_LOADED_MODULE {record.compress}"
  let modules := #[`LeanPool.KloostermanWeil.Stepanov.Algebra,`LeanPool.KloostermanWeil.Stepanov.Auxiliary,`LeanPool.KloostermanWeil.Stepanov.Parameters,`LeanPool.KloostermanWeil.Stepanov.CurveCount,`LeanPool.KloostermanWeil.Stepanov.Defect,`LeanPool.KloostermanWeil.Stepanov.SpecializedCurve,`LeanPool.KloostermanWeil.Carlitz.FactorData,`LeanPool.KloostermanWeil.Carlitz.DicksonFiniteAlgebra,`LeanPool.KloostermanWeil.Carlitz.CoefficientEquivalence,`LeanPool.KloostermanWeil.Carlitz.FactorWeight,`LeanPool.KloostermanWeil.Weil.PrimeFoundation,`LeanPool.KloostermanWeil.Carlitz.ExtensionDefinitions,`LeanPool.KloostermanWeil.Carlitz.MinimalPolynomialInverse,`LeanPool.KloostermanWeil.Carlitz.ClassValue,`LeanPool.KloostermanWeil.Carlitz.ConjugateDecomposition,`LeanPool.KloostermanWeil.Carlitz.ClassGhost,`LeanPool.KloostermanWeil.Carlitz.RelevantIrreducibles,`LeanPool.KloostermanWeil.Carlitz.IrreducibleGhost,`LeanPool.KloostermanWeil.Carlitz.NewtonIndex,`LeanPool.KloostermanWeil.Carlitz.NewtonSum,`LeanPool.KloostermanWeil.Carlitz.FormalAlgebra,`LeanPool.KloostermanWeil.Carlitz.GeneratingIdentity,`LeanPool.KloostermanWeil.Carlitz.RecurrencePackage,`LeanPool.KloostermanWeil.Stepanov.FiniteSum,`LeanPool.KloostermanWeil.Stepanov.ArtinSchreier,`LeanPool.KloostermanWeil.Stepanov.CurveTrace,`LeanPool.KloostermanWeil.Stepanov.ScalarExtensionSum,`LeanPool.KloostermanWeil.Stepanov.PointCountBridge,`LeanPool.KloostermanWeil.Stepanov.CarlitzRoots,`LeanPool.KloostermanWeil.Stepanov.PowerSumSpectral,`LeanPool.KloostermanWeil.Stepanov.SpectralBound,`LeanPool.KloostermanWeil.Stepanov.PrimeWeil,`LeanPool.KloostermanWeil.Stepanov.PrimeWeilBridge,`LeanPool.KloostermanWeil.Weil.PrimeKloosterman]
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
  -- ConstantInfo is queried only after selecting one of the five module indices.
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
      if !data.isModule || !imported.importAll || !imported.hasData then
        throwError "Expected complete modern private module data for {imported.module}"
      let owned := names.filter fun name =>
        (env.getModuleIdxFor? name).map (fun i => moduleNames[i]!) ==
          some imported.module
      unless owned.size > 0 do
        throwError "Audited module has no declarations: {imported.module}"
      unless owned.qsort Name.lt == data.constNames.qsort Name.lt do
        -- Diagnostics only. Keep the exact original rejection below.
        let countName := fun (xs : Array Name) (n : Name) =>
          xs.foldl (fun count x => if x == n then count + 1 else count) (0 : Nat)
        let allNames := (owned ++ data.constNames).foldl
          (fun acc n => if acc.contains n then acc else acc.push n) (#[] : Array Name)
        let differentNames := allNames.filter fun n =>
          countName owned n != countName data.constNames n
        let mut differences : Array Json := #[]
        for name in differentNames.qsort Name.lt do
          let canonical := env.getModuleIdxFor? name
          let mut occurrences : Array Json := #[]
          for otherIdx in List.range env.header.modules.size do
            let otherModule := env.header.modules[otherIdx]!
            let otherData := env.header.moduleData[otherIdx]!
            let serializedCount := countName otherData.constNames name
            let extraCount := countName otherData.extraConstNames name
            if serializedCount > 0 || extraCount > 0 then
              occurrences := occurrences.push (Json.mkObj [
                ("module_data_index", toJson otherIdx),
                ("module", toJson otherModule.module.toString),
                ("serialized_count", toJson serializedCount),
                ("extra_codegen_count", toJson extraCount)])
          differences := differences.push (Json.mkObj [
            ("name", toJson name.toString),
            ("owned_count", toJson (countName owned name)),
            ("serialized_count", toJson (countName data.constNames name)),
            ("environment_has_constant", toJson (env.find? name).isSome),
            ("canonical_owner_index", toJson (canonical.map (fun i => i.toNat))),
            ("canonical_owner_module", toJson (canonical.map (fun i => moduleNames[i]!.toString))),
            ("loaded_occurrences", Json.arr occurrences)])
        let diagnostic := Json.mkObj [
          ("module_data_index", toJson idx),
          ("module", toJson imported.module.toString),
          ("owned_names", toJson (owned.map Name.toString)),
          ("serialized_names", toJson (data.constNames.map Name.toString)),
          ("extra_codegen_names", toJson (data.extraConstNames.map Name.toString)),
          ("multiplicity_differences", Json.arr differences),
          ("acceptance_rule_unchanged", toJson true)]
        liftIO do
          IO.println s!"P0_ROUND6_INVENTORY_MISMATCH {diagnostic.compress}"
          (← IO.getStdout).flush
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
  liftIO do
    IO.println "P0_ROUND6_PHASE serialized_inventory_exact_match"
    (← IO.getStdout).flush
  let mut exportFailures : Array String := #[]
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in names.qsort Name.lt do
    liftIO do
      IO.println s!"P0_ROUND6_PHASE declaration_start {name}"
      (← IO.getStdout).flush
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    let executable := info.isUnsafe || info.isPartial
    let executableKindAllowed := match info with
      | .defnInfo _ => true
      | .opaqueInfo _ => true
      | _ => false
    if executable && !executableKindAllowed then
      exportFailures := exportFailures.push s!"Unexpected unsafe/partial constant kind: {name}"
    if info.isAxiom then
      exportFailures := exportFailures.push s!"Unproved owned axiom: {name}"
    -- Exact s02 R2 direct checked type/body worklist, with complete raw edges.
    let mut pending := #[name]
    let mut seen : NameSet := {}
    let mut axioms : Array Name := #[]
    let mut unsafePartialDependencies : Array Name := #[]
    let mut dependencyRecords : Array Json := #[]
    while !pending.isEmpty do
      let current := pending.back!
      pending := pending.pop
      unless seen.contains current do
        seen := seen.insert current
        let some currentInfo := env.checked.get.find? current |
          throwError "Missing current checked dependency {current} from {name}"
        let mut used : Array Name := #[]
        for dependency in currentInfo.getUsedConstantsAsSet do
          used := used.push dependency
        let some currentOwner := env.getModuleIdxFor? current |
          throwError "Missing physical defining module for dependency {current} from {name}"
        dependencyRecords := dependencyRecords.push (Json.mkObj [
          ("owner_module", toJson moduleNames[currentOwner]!.toString),
          ("name", toJson current.toString),
          ("is_unsafe", toJson currentInfo.isUnsafe),
          ("is_partial", toJson currentInfo.isPartial),
          ("is_axiom", toJson currentInfo.isAxiom),
          ("used_constants", toJson (used.map Name.toString))])
        if currentInfo.isUnsafe || currentInfo.isPartial then
          unsafePartialDependencies := unsafePartialDependencies.push current
          unless executable do
            exportFailures := exportFailures.push s!"Unsafe/partial dependency {current} reachable from safe logical declaration {name}"
        if currentInfo.isAxiom then
          axioms := axioms.push current
        for dependency in used do
          pending := pending.push dependency
    for ax in axioms do
      unless allowed.contains ax do
        exportFailures := exportFailures.push s!"Forbidden transitive axiom {ax} in {name}"
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
      exportFailures := exportFailures.push s!"Truncated compiler type for {name}"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("is_unsafe", toJson info.isUnsafe),
      ("is_partial", toJson info.isPartial),
      ("is_axiom", toJson info.isAxiom),
      ("safety_class", toJson (if executable then "executable_implementation" else "logical_safe")),
      ("kernel_replay_required", toJson (!executable)),
      ("implementation_kernel_proof_credit", toJson false),
      ("implementation_termination_credit", toJson false),
      ("unsafe_partial_dependencies", toJson (unsafePartialDependencies.map Name.toString)),
      ("axiom_audit", toJson "fresh_current_checked_type_and_body"),
      ("axiom_visited_count", toJson seen.size),
      ("dependency_records", Json.arr dependencyRecords),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"P0_ROUND6_DECL {record.compress}"
  for (m, count) in counts do
    unless count > 0 do
      throwError "Audited module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"P0_ROUND6_MODULE {record.compress}"
  liftIO <| IO.println s!"P0_ROUND6_COUNT {names.size}"

  unless exportFailures.isEmpty do
    liftIO <| IO.println s!"WEIL34_EXPORT_FAILURES {(toJson exportFailures).compress}"
    throwError "Complete available inventory retained; safety/axiom/fulltype gate failed"
