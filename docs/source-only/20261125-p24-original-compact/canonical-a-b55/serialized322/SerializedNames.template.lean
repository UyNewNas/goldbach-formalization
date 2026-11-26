import ImbalancedChen.P2OriginalCompactQ80CompleteSoundness
import ImbalancedChen.P2OriginalCompactCachedRun
import ImbalancedChen.P2OriginalCompactQ80FixedBindings
import ImbalancedChen.P4AOrdinaryRootFirstIntegral
import ImbalancedChen.Part4ActualThirdFiniteDensityReserve
import ImbalancedChen.P2OriginalCompactArchivedTotalCandidate
import Lean.Elab.Command

/- Diagnostic only: report each imported legacy module's original serialized
   constNames, without filtering through the merged environment's single owner.
   This neither checks full types/axioms nor replaces the original owned audit. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedModules : Array Name := #[
__P24_EXPECTED_MODULE_NAMES__
  ]
  unless expectedModules.size == 322 do throwError "Wrong current compiled scope"
  let actualProject := env.header.moduleNames.filter fun n =>
    n.toString.startsWith "ImbalancedChen."
  unless actualProject.qsort Name.lt == expectedModules.qsort Name.lt do
    throwError "Loaded project modules differ from current322; B and W must not be imported"
  liftIO <| IO.println s!"P24_SERIALIZED_IMPORTS {(toJson (env.header.moduleNames.map Name.toString)).compress}"
  let mut totalOccurrences : Nat := 0
  for moduleName in expectedModules do
    let mut serialized : Array Name := #[]
    let mut found := false
    let mut headerIndex : Nat := 0
    for i in List.range env.header.modules.size do
      let imported := env.header.modules[i]!
      if imported.module == moduleName then
        if found then throwError "Duplicate module header {moduleName}"
        found := true
        headerIndex := i
        let data := env.header.moduleData[i]!
        if data.isModule || !imported.importAll || !imported.hasData then
          throwError "Incomplete imported legacy data {moduleName}"
        serialized := data.constNames
    unless found && serialized.size > 0 do
      throwError "Missing or empty serialized module {moduleName}"
    totalOccurrences := totalOccurrences + serialized.size
    liftIO <| IO.println s!"P24_SERIALIZED_MODULE {(Json.mkObj [("module", toJson moduleName.toString), ("header_index", toJson headerIndex), ("legacy_data_complete", toJson true), ("count", toJson serialized.size), ("serialized", toJson (serialized.map Name.toString))]).compress}"
  liftIO <| IO.println s!"P24_SERIALIZED_COMPLETE {(Json.mkObj [("modules", toJson expectedModules.size), ("serialized_occurrences", toJson totalOccurrences), ("diagnostic_only", toJson true), ("merged_owner_filter_used", toJson false), ("independent_replay", toJson false), ("full_types_or_axioms_audited", toJson false), ("original_owned_credit", toJson false)]).compress}"
