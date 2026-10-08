import ChenInitialNormalizationAdapter
import Lean.Util.CollectAxioms

/- Owned audit tooling. Execute only under the pinned offline wrapper.
   Audit every loaded declaration by its origin module, including private/internal
   names. All 84 selected custom modules must be loaded; only the declaration-free
   Architect import aggregator may have zero declarations. The probe itself adds
   no mathematical declaration, and is included in whole-module kernel replay. -/

#print axioms AnalyticNumberTheory.PrimeDistribution.natPrimeCountingPNT
#print axioms AnalyticNumberTheory.Mertens.primeProduct_mertens_nat
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.chenPrimePrefix_card_eq_primeCounting
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.actual_initial_mass_eq_primeCounting_sub
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_primeCounting_div_main
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_centre_prime_correction_div_main
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_actual_initial_mass_div_main
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.eventually_actual_initial_totalMass_div_main
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.powerSieveCap
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.powerMertensEndpoint
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.mem_power_sieve_primes
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.primeEulerProduct_eq_supplier_predecessor
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_powerSieveCap_atTop
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_powerMertensEndpoint_atTop
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.powerMertensEndpoint_bounds
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_powerMertensEndpoint_div_power
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_log_powerMertensEndpoint_sub_log_power
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_log_powerMertensEndpoint_div_log
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_supplier_primeProduct_mul_log
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_primeEulerProduct_power_mul_log
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_oddEulerProduct_div_full_tail_power
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.actual_density_log_normalization_eq
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_actual_density_mul_log_div_singularSeries
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.tendsto_actual_density_div_mertens_main
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.actual_initial_density_eq_product
#print axioms ImbalancedChen.ChenInitialNormalizationAdapter.exists_actual_initial_normalization_threshold

set_option pp.all true in
#check @ImbalancedChen.ChenInitialNormalizationAdapter.exists_actual_initial_normalization_threshold

open Lean in
set_option maxHeartbeats 0 in
run_cmd do
  let auditedModules : List Name := [
    `ImbalancedChen.Counting,
    `ImbalancedChen.RationalPowers,
    `ImbalancedChen.OrderedBad,
    `ImbalancedChen.HalfProductGeometry,
    `ImbalancedChen.BadSourceLocalization,
    `ImbalancedChen.HalfProductSource,
    `ImbalancedChen.SieveSourceCoprimality,
    `ImbalancedChen.FiniteSieveModel,
    `ImbalancedChen.NormalizationGrowth,
    `ImbalancedChen.SingularSeries,
    `ImbalancedChen.FiniteSieveEuler,
    `ImbalancedChen.CenterPrimeTail,
    `ImbalancedChen.PowerErrorBudget,
    `ImbalancedChen.EulerNormalizationLimit,
    `ImbalancedChen.QuotientChenFourPrime,
    `ImbalancedChen.QuotientChenFourCounts,
    `ImbalancedChen.QuotientChenInitialCounts,
    `ImbalancedChen.QuotientChenSwitchGeometry,
    `ImbalancedChen.QuotientChenNinthSwitch,
    `ImbalancedChen.Multiplicity,
    `ImbalancedChen.QuotientChenWeightCases,
    `ImbalancedChen.QuotientChenPositiveBound,
    `ImbalancedChen.RoughSquareException,
    `ImbalancedChen.QuotientChenSummedBridge,
    `ImbalancedChen.QuotientChenElevenSum,
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
    `ImbalancedChen.BoundaryLogMesh,
    `ImbalancedChen.LogCutoffError,
    `ImbalancedChen.CurvedDiscrepancyReduction,
    `ImbalancedChen.LogMeshGridCount,
    `ImbalancedChen.BoundaryArbitraryLog,
    `ImbalancedChen.ChenInitialCorrectionBudget,
    `ImbalancedChen.CenterEulerTail,
    `Architect.Basic,
    `Architect.Command,
    `Architect.Content,
    `Architect.Attribute,
    `Architect.CollectUsed,
    `Architect.Tactic,
    `Architect.Output,
    `Architect.Load,
    `Architect,
    `PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Basic,
    `PrimeNumberTheoremAnd.Sobolev,
    `PrimeNumberTheoremAnd.Fourier,
    `PrimeNumberTheoremAnd.Defs,
    `PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics,
    `PrimeNumberTheoremAnd.Mathlib.Algebra.Notation.Support,
    `PrimeNumberTheoremAnd.SmoothExistence,
    `PrimeNumberTheoremAnd.Wiener,
    `PrimeNumberTheoremAnd.Consequences,
    `PrimeNumberTheoremAnd.Auxiliary,
    `PrimeNumberTheoremAnd.MellinCalculus,
    `PrimeNumberTheoremAnd.Rectangle,
    `PrimeNumberTheoremAnd.Tactic.AdditiveCombination,
    `PrimeNumberTheoremAnd.ResidueCalcOnRectangles,
    `PrimeNumberTheoremAnd.EulerMaclaurin,
    `PrimeNumberTheoremAnd.ZetaBounds,
    `PrimeNumberTheoremAnd.ZetaConj,
    `PrimeNumberTheoremAnd.MediumPNT,
    `AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem,
    `AnalyticNumberTheory.Mertens.Basic,
    `AnalyticNumberTheory.PrimeDistribution.ChebyshevTheta,
    `AnalyticNumberTheory.Mertens.PartialSummation,
    `AnalyticNumberTheory.Mertens.AbelianRemainder,
    `AnalyticNumberTheory.Mertens.PrimeAbel,
    `AnalyticNumberTheory.Mertens.LogChange,
    `AnalyticNumberTheory.Mertens.Product,
    `AnalyticNumberTheory.Mertens.Abelian,
    `AnalyticNumberTheory.Mertens.MangoldtBridge,
    `AnalyticNumberTheory.Mertens.ConstantIdentity,
    `AnalyticNumberTheory.Mertens.GammaKernel,
    `AnalyticNumberTheory.Mertens.FinitePart,
    `AnalyticNumberTheory.Mertens.Theorems,
    `ChenInitialNormalizationAdapter]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut counts : Std.HashMap Name Nat := {}
  let mut declarations : Nat := 0
  for moduleName in env.header.moduleNames do
    logInfo m!"NORMALIZATION_IMPORTED_MODULE {moduleName}"
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
    unless env.header.moduleNames.contains moduleName do
      throwError "Audited module missing from environment: {moduleName}"
    unless moduleName == `Architect || counts.getD moduleName 0 > 0 do
      throwError "Missing declaration coverage for custom module {moduleName}"
    logInfo m!"NORMALIZATION_MODULE_AUDIT {moduleName} declarations={counts.getD moduleName 0}"
  unless declarations > 0 do
    throwError "Empty custom declaration audit"
  logInfo m!"NORMALIZATION_AXIOM_AUDIT_PASS declarations={declarations} modules={auditedModules.length}"
