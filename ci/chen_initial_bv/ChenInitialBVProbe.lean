import ChenInitialBVAdapter
import Lean.Util.CollectAxioms

/- Owned audit instrumentation only. Compile and run solely in offline isolation.
   Every loaded declaration from all 38 frozen core modules and the adapter
   gets a transitive axiom check. Private/internal declaration names are
   selected by originating module, not by public namespace or spelling. -/

#print axioms ImbalancedChen.ChenInitialBVAdapter.chenPrimeAPCount_eq_supplier
#print axioms ImbalancedChen.ChenInitialBVAdapter.supplier_cutoff_eq_sqrt_level
#print axioms ImbalancedChen.ChenInitialBVAdapter.abs_chenPrimeAPCount_sub_supplier_main_le_prefixMax
#print axioms ImbalancedChen.ChenInitialBVAdapter.sum_abs_chenInitial_rem_le_supplier_add_cost
#print axioms ImbalancedChen.ChenInitialBVAdapter.sqrt_log_level_cast_le_sqrt
#print axioms ImbalancedChen.ChenInitialBVAdapter.eventually_two_mul_supplier_bound_le_half_accuracy
#print axioms ImbalancedChen.ChenInitialBVAdapter.exists_logLevel_chenInitial_rem_logAccuracy
#print axioms ImbalancedChen.ChenInitialBVAdapter.exists_logLevel_chenInitial_rem_logAccuracy_of_primitive_subset
#print axioms ImbalancedChen.ChenInitialBVAdapter.exists_logLevel_chenInitial_sieve_rem_logAccuracy

set_option pp.all true in
#check @ImbalancedChen.ChenInitialBVAdapter.exists_logLevel_chenInitial_sieve_rem_logAccuracy

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let auditedModules : List Name := [
  `ImbalancedChen.QuotientChenFourPrime,
  `ImbalancedChen.QuotientChenFourCounts,
  `ImbalancedChen.QuotientChenInitialCounts,
  `ImbalancedChen.QuotientChenSwitchGeometry,
  `ImbalancedChen.QuotientChenNinthSwitch,
  `ImbalancedChen.Counting,
  `ImbalancedChen.Multiplicity,
  `ImbalancedChen.QuotientChenWeightCases,
  `ImbalancedChen.QuotientChenPositiveBound,
  `ImbalancedChen.RoughSquareException,
  `ImbalancedChen.QuotientChenSummedBridge,
  `ImbalancedChen.QuotientChenElevenSum,
  `ImbalancedChen.RationalPowers,
  `ImbalancedChen.OrderedBad,
  `ImbalancedChen.HalfProductGeometry,
  `ImbalancedChen.BadSourceLocalization,
  `ImbalancedChen.HalfProductSource,
  `ImbalancedChen.SieveSourceCoprimality,
  `ImbalancedChen.FiniteSieveModel,
  `ImbalancedChen.CurvedRegionDiscrepancy,
  `ImbalancedChen.CoprimeRecentering,
  `ImbalancedChen.ChenInitialPrimeSource,
  `ImbalancedChen.TotientReciprocalBudget,
  `ImbalancedChen.BoundaryGridBudget,
  `ImbalancedChen.BoundaryCellContainment,
  `ImbalancedChen.MultiplicativeGridPartition,
  `ImbalancedChen.BoundaryGlobalCaps,
  `ImbalancedChen.ActualGridEnvelopes,
  `ImbalancedChen.RectangleDiscrepancyAssembly,
  `ImbalancedChen.NormalizationGrowth,
  `ImbalancedChen.SingularSeries,
  `ImbalancedChen.PowerErrorBudget,
  `ImbalancedChen.BoundaryLogMesh,
  `ImbalancedChen.LogCutoffError,
  `ImbalancedChen.CurvedDiscrepancyReduction,
  `ImbalancedChen.LogMeshGridCount,
  `ImbalancedChen.BoundaryArbitraryLog,
  `ImbalancedChen.ChenInitialCorrectionBudget,
  `ChenInitialBVAdapter]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut counts : Std.HashMap Name Nat := {}
  let mut declarations : Nat := 0
  for moduleName in env.header.moduleNames do
    logInfo m!"BV_IMPORTED_MODULE {moduleName}"
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index]!
      if auditedModules.contains moduleName then
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "Forbidden transitive axiom {axiomName} for {name} in {moduleName}"
        counts := counts.insert moduleName (counts.getD moduleName 0 + 1)
        declarations := declarations + 1
  for moduleName in auditedModules do
    unless counts.getD moduleName 0 > 0 do
      throwError "Missing declaration coverage for owned module {moduleName}"
    logInfo m!"BV_OWNED_MODULE_AUDIT {moduleName} declarations={counts.getD moduleName 0}"
  unless declarations > 0 do
    throwError "Empty owned declaration audit"
  logInfo m!"BV_OWNED_AXIOM_AUDIT_PASS declarations={declarations} modules={auditedModules.length}"
