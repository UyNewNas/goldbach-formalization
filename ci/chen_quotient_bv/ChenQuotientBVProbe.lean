import ImbalancedChen.ChenQuotientBVAdapter
import Lean.Util.CollectAxioms

/- Owned offline-only audit instrumentation. Every declaration, including private/internal
   declarations, is selected by its origin in all 46 proof modules. -/

#print axioms ImbalancedChen.ChenQuotientBVAdapter.abs_chenQuotientPrimeAPError_le_supplier
#print axioms ImbalancedChen.ChenQuotientBVAdapter.sum_chenQuotientPrimeAPError_le_supplier
#print axioms ImbalancedChen.ChenQuotientBVAdapter.four_pool_logCoefficient_le
#print axioms ImbalancedChen.ChenQuotientBVAdapter.exists_logLevel_chenUpsilon36_remainder_logAccuracy
#print axioms ImbalancedChen.chenQuotient_secondary_AP_sum_le_primitive_log
#print axioms ImbalancedChen.sum_abs_chenQuotient_rem_le_primitive_log_add_cost
#print axioms ImbalancedChen.ChenQuotientRows.subset_Icc
#print axioms ImbalancedChen.chenUpsilon36RemainderSum_le_primitive_log_add_cost
#print axioms ImbalancedChen.eventually_chenUpsilon36CentreCost_le_of_rows

set_option pp.all true in
#check @ImbalancedChen.ChenQuotientBVAdapter.exists_logLevel_chenUpsilon36_remainder_logAccuracy

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
  `ImbalancedChen.ChenQuotientPrimeSource,
  `ImbalancedChen.ChenQuotientSieveRemainders,
  `ImbalancedChen.TotientReciprocalBudget,
  `ImbalancedChen.DivisorMomentBudget,
  `ImbalancedChen.ChenPooledQuotientAP,
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
  `ImbalancedChen.ChenQuotientCentreBudget,
  `ImbalancedChen.ChenQuotientBVFinite,
  `ImbalancedChen.ChenInitialBVAdapter,
  `ImbalancedChen.ChenQuotientBVAdapter]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut counts : Std.HashMap Name Nat := {}
  let mut declarations : Nat := 0
  for moduleName in env.header.moduleNames do
    logInfo m!"QUOTIENT_BV_IMPORTED_MODULE {moduleName}"
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
    logInfo m!"QUOTIENT_BV_OWNED_MODULE_AUDIT {moduleName} declarations={counts.getD moduleName 0}"
  unless declarations > 0 do
    throwError "Empty owned declaration audit"
  logInfo m!"QUOTIENT_BV_OWNED_AXIOM_AUDIT_PASS declarations={declarations} modules={auditedModules.length}"
