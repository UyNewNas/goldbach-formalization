import ImbalancedChen.ChenPrimeHarmonicAdapter
import ImbalancedChen.ChenQuotientMovingPrimeAdapter
import ImbalancedChen.ChenPairHarmonicLimit
import Lean.Util.CollectAxioms

/- Owned audit instrumentation. No mathematical declaration is added here.
All exact owned, supplier, and Architect origins are audited, including
private/internal declarations. This probe is also a kernel replay target. -/

#print axioms MathlibNt.SieveTheory.MertensTheorem.tendsto_weightedPrimeReciprocalLogSum
#print axioms ImbalancedChen.ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeHarmonicSum
#print axioms ImbalancedChen.ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeTotientLogSum
#print axioms ImbalancedChen.ChenQuotientMovingPrimeAdapter.exists_eventually_bounded_chenSinglePrimeTotientMass
#print axioms ImbalancedChen.ChenQuotientMovingPrimeAdapter.tendsto_chenSinglePrime_moving_sieveFactor
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenPrimeTensor_sumTest
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenPrimeTensor_diagonal
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY6_log_totient_sum
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY5_log_totient_sum
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY6_manuscript_log_totient_sum
#print axioms ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY5_manuscript_log_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeHarmonicSum

set_option pp.all true in
#check @ImbalancedChen.ChenPrimeHarmonicAdapter.tendsto_chenSinglePrimeTotientLogSum

set_option pp.all true in
#check @ImbalancedChen.ChenQuotientMovingPrimeAdapter.exists_eventually_bounded_chenSinglePrimeTotientMass

set_option pp.all true in
#check @ImbalancedChen.ChenQuotientMovingPrimeAdapter.tendsto_chenSinglePrime_moving_sieveFactor

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenPrimeTensor_sumTest

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenPrimeTensor_diagonal

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY6_log_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY5_log_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY6_manuscript_log_totient_sum

set_option pp.all true in
#check @ImbalancedChen.ChenPairHarmonicLimit.tendsto_chenY5_manuscript_log_totient_sum

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
    `ImbalancedChen.ChenPrimeHarmonicFinite,
    `AnalyticNumberTheory.LargeSieve.Additive,
    `AnalyticNumberTheory.LargeSieve.GeomSum,
    `AnalyticNumberTheory.LargeSieve.Duality,
    `AnalyticNumberTheory.LargeSieve.WellSpaced,
    `AnalyticNumberTheory.LargeSieve.Multiplicative,
    `AnalyticNumberTheory.Sieve.BombieriVinogradov,
    `AnalyticNumberTheory.Sieve.WeightedPan,
    `AnalyticNumberTheory.Sieve.VaughanIdentity,
    `AnalyticNumberTheory.LargeSieve.CharacterIndicators,
    `AnalyticNumberTheory.Sieve.PanMeanValueBody,
    `AnalyticNumberTheory.LargeSieve.BombieriDavenport,
    `AnalyticNumberTheory.Mertens.Basic,
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
    `AnalyticNumberTheory.PrimeDistribution.ChebyshevTheta,
    `AnalyticNumberTheory.Mertens.PartialSummation,
    `AnalyticNumberTheory.Sieve.GoldbachDensity,
    `AnalyticNumberTheory.Sieve.PanMainTerm,
    `AnalyticNumberTheory.LargeSieve.PanTypeIAssembly,
    `AnalyticNumberTheory.LargeSieve.PanTypeIIAssembly,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean,
    `MathlibNt.AnalyticNumberTheory.LargeSieve.LcmWeightBounds,
    `AnalyticNumberTheory.Sieve.PanV1SquareMean,
    `AnalyticNumberTheory.LargeSieve.NonCoprimeDensity,
    `AnalyticNumberTheory.Mertens.Product,
    `AnalyticNumberTheory.Mertens.MangoldtBridge,
    `AnalyticNumberTheory.Mertens.Abelian,
    `AnalyticNumberTheory.Mertens.GammaKernel,
    `AnalyticNumberTheory.Mertens.PrimeAbel,
    `AnalyticNumberTheory.Mertens.LogChange,
    `AnalyticNumberTheory.Mertens.AbelianRemainder,
    `AnalyticNumberTheory.Mertens.ConstantIdentity,
    `AnalyticNumberTheory.Mertens.FinitePart,
    `AnalyticNumberTheory.Mertens.Theorems,
    `AnalyticNumberTheory.Sieve.SelbergIdentities,
    `AnalyticNumberTheory.Sieve.Distribution,
    `AnalyticNumberTheory.Sieve.LinearSieve,
    `AnalyticNumberTheory.Sieve.SelbergUpperBound,
    `AnalyticNumberTheory.Sieve.SingularSeries,
    `AnalyticNumberTheory.Sieve.PanV3SquareMean,
    `AnalyticNumberTheory.Sieve.SumTwoPowWeighted,
    `AnalyticNumberTheory.Sieve.PanAssembly,
    `AnalyticNumberTheory.Sieve.PanVaughanPointwise,
    `AnalyticNumberTheory.Sieve.W1LemmaB,
    `AnalyticNumberTheory.Sieve.W2Transfer,
    `AnalyticNumberTheory.Sieve.W1Assembly,
    `AnalyticNumberTheory,
    `MathlibNt.SieveTheory.Arithmetic.SingularSeries,
    `MathlibNt.SieveTheory.Arithmetic.MertensTheorem,
    `ImbalancedChen.ChenPrimeHarmonicAdapter,
    `ImbalancedChen.MovingWeightTransport,
    `ImbalancedChen.ChenLogLevelGeometry,
    `ImbalancedChen.ChenQuotientSieveRemainders,
    `ImbalancedChen.ChenQuotientLevelGeometry,
    `ImbalancedChen.ChenQuotientMovingWeight,
    `ImbalancedChen.ChenQuotientMovingPrimeAdapter,
    `ImbalancedChen.ChenPairHarmonicFinite,
    `ImbalancedChen.ChenPairHarmonicLimit ]
  let emptyModules : List Name := [`Architect, `AnalyticNumberTheory]
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let mut counts : Std.HashMap Name Nat := {}
  let mut declarations : Nat := 0
  for moduleName in env.header.moduleNames do
    logInfo m!"HARMONIC_IMPORTED_MODULE {moduleName}"
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
    if emptyModules.contains moduleName then
      unless counts.getD moduleName 0 == 0 do
        throwError "Unexpected declaration in pinned import-only module {moduleName}"
    else
      unless counts.getD moduleName 0 > 0 do
        throwError "Missing declaration coverage for custom module {moduleName}"
    logInfo m!"HARMONIC_MODULE_AUDIT {moduleName} declarations={counts.getD moduleName 0}"
  unless declarations > 0 do
    throwError "Empty custom declaration audit"
  logInfo m!"HARMONIC_AXIOM_AUDIT_PASS declarations={declarations} modules={auditedModules.length}"
