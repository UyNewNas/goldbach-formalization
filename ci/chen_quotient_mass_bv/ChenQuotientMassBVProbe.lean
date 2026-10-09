import ImbalancedChen.ChenQuotientMassNormalization
import ChenQuotientBVProbe
import Lean.Util.CollectAxioms

/- Owned offline audit instrumentation. All 51 proof origins are audited;
   the retained original quotient probe is imported as audit instrumentation. -/

#print axioms ImbalancedChen.ChenQuotientMassBVAdapter.exists_logLevel_chenUpsilon36_weightedMassError_logAccuracy
#print axioms ImbalancedChen.ChenQuotientMassBVAdapter.eventually_chenUpsilon36WeightedMassError_le_logAccuracy
#print axioms ImbalancedChen.ChenQuotientMassBVAdapter.eventually_abs_chenUpsilon36WeightedMass_sub_LiMain_le_logAccuracy
#print axioms ImbalancedChen.chenQuotientBoundingSieve_massError
#print axioms ImbalancedChen.chenQuotientMassError_eq_primeAP_sub_centre
#print axioms ImbalancedChen.abs_chenQuotientMassError_le
#print axioms ImbalancedChen.sum_chenQuotientPrimeAPError_base_le_primitive
#print axioms ImbalancedChen.chenSelectedWeightedMassError_le_primitive_add_centre
#print axioms ImbalancedChen.chenSelectedWeightedMass_sub_main_eq
#print axioms ImbalancedChen.abs_chenSelectedWeightedMass_sub_main_le
#print axioms ImbalancedChen.chenUpsilon36WeightedMassError_le_primitive_add_centre
#print axioms ImbalancedChen.abs_chenUpsilon36WeightedMass_sub_main_le
#print axioms ImbalancedChen.chenUpsilon36CentreMass_le_four_log_cube
#print axioms ImbalancedChen.eventually_mul_chenUpsilon36CentreMass_le_logAccuracy

set_option pp.all true in
#check @ImbalancedChen.ChenQuotientMassBVAdapter.eventually_chenUpsilon36WeightedMassError_le_logAccuracy

set_option pp.all true in
#check @ImbalancedChen.ChenQuotientMassBVAdapter.eventually_abs_chenUpsilon36WeightedMass_sub_LiMain_le_logAccuracy

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
  `ImbalancedChen.ChenQuotientMassFinite,
  `ImbalancedChen.ChenQuotientBVFinite,
  `ImbalancedChen.ChenInitialBVAdapter,
  `ImbalancedChen.ChenQuotientBVAdapter,
  `ImbalancedChen.ChenQuotientMassBVAdapter,
  `ImbalancedChen.ChenLogLevelGeometry,
  `ImbalancedChen.ChenQuotientLevelGeometry,
  `ImbalancedChen.ChenQuotientMassNormalization]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut counts : Std.HashMap Name Nat := {}
  let mut declarations : Nat := 0
  for moduleName in env.header.moduleNames do
    logInfo m!"MASS_BV_IMPORTED_MODULE {moduleName}"
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
    logInfo m!"MASS_BV_OWNED_MODULE_AUDIT {moduleName} declarations={counts.getD moduleName 0}"
  unless declarations > 0 do
    throwError "Empty owned declaration audit"
  logInfo m!"MASS_BV_OWNED_AXIOM_AUDIT_PASS declarations={declarations} modules={auditedModules.length}"
