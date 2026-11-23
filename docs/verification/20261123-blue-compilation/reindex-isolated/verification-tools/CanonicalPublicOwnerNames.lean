import ImbalancedChen.P5OrderedFactorTupleRectangleReindex
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[
    `ImbalancedChen.ActualGridEnvelopes,
    `ImbalancedChen.ActualSieveGate,
    `ImbalancedChen.AsymptoticTransfer,
    `ImbalancedChen.BadSourceLocalization,
    `ImbalancedChen.BoundaryCellContainment,
    `ImbalancedChen.BoundaryGlobalCaps,
    `ImbalancedChen.BoundaryGridBudget,
    `ImbalancedChen.CoprimeRecentering,
    `ImbalancedChen.Counting,
    `ImbalancedChen.CurrentMainTheorem,
    `ImbalancedChen.CurrentNumericalTransfer,
    `ImbalancedChen.CurvedRegionDiscrepancy,
    `ImbalancedChen.FiniteSieveModel,
    `ImbalancedChen.HalfProductGeometry,
    `ImbalancedChen.HalfProductMassError,
    `ImbalancedChen.HalfProductMassFibres,
    `ImbalancedChen.HalfProductMassLimit,
    `ImbalancedChen.HalfProductMassSplit,
    `ImbalancedChen.HalfProductPanFinite,
    `ImbalancedChen.HalfProductSource,
    `ImbalancedChen.LogCutoffError,
    `ImbalancedChen.MassLogIntegral,
    `ImbalancedChen.MultiplicativeGridPartition,
    `ImbalancedChen.Multiplicity,
    `ImbalancedChen.NormalizationGrowth,
    `ImbalancedChen.OrderedBad,
    `ImbalancedChen.P5ActualHBChartEventualClosure,
    `ImbalancedChen.P5ActualHBDyadicOccurrenceFamily,
    `ImbalancedChen.P5ActualHBDyadicProductWindow,
    `ImbalancedChen.P5ActualHBMediumBranchPartition,
    `ImbalancedChen.P5ActualHBMediumRoleSupports,
    `ImbalancedChen.P5ActualLabelledPrimeSmoothCharts,
    `ImbalancedChen.P5ActualMultiGroupHBChartScale,
    `ImbalancedChen.P5ActualRoughHeathBrownWords,
    `ImbalancedChen.P5ExactOriginalSmoothDyadicPartition,
    `ImbalancedChen.P5HBCompleteProduct,
    `ImbalancedChen.P5HBRightClosedDyadicRoles,
    `ImbalancedChen.P5LiteralHeathBrownOccurrenceWords,
    `ImbalancedChen.P5OrderedFactorTupleRectangleReindex,
    `ImbalancedChen.P5OriginalChartRoughCutoff,
    `ImbalancedChen.P5OriginalHBMediumChartReserves,
    `ImbalancedChen.P5RealCutoffHeathBrownThree,
    `ImbalancedChen.P5RealTruncatedMobiusSupport,
    `ImbalancedChen.P5SmoothChartHBDyadicPartition,
    `ImbalancedChen.P5SmoothChartPhysicalHBBranch,
    `ImbalancedChen.PanProductAggregateBudget,
    `ImbalancedChen.PanProductGrid,
    `ImbalancedChen.PanProductGridRanges,
    `ImbalancedChen.PanProductLiuBridge,
    `ImbalancedChen.PanProductResidueBudget,
    `ImbalancedChen.PanProductStrips,
    `ImbalancedChen.Part3ActualOriginalProperPowerChartBridge,
    `ImbalancedChen.Part3DistributionTargets,
    `ImbalancedChen.Part3OriginalProperPowerChartCount,
    `ImbalancedChen.Part3RoughAuxiliarySW,
    `ImbalancedChen.Part3RoughSlotCharacterLift,
    `ImbalancedChen.PowerErrorBudget,
    `ImbalancedChen.PrimeRectanglePrefixes,
    `ImbalancedChen.RationalPowers,
    `ImbalancedChen.RealHalfProductMass,
    `ImbalancedChen.RealHalfProductMassSplit,
    `ImbalancedChen.RealHalfProductSource,
    `ImbalancedChen.RectangleDiscrepancyAssembly,
    `ImbalancedChen.ResidueSelectorBudget,
    `ImbalancedChen.RestrictedResidueScale,
    `ImbalancedChen.SelectedGridRanges,
    `ImbalancedChen.SieveSourceCoprimality,
    `ImbalancedChen.SingularSeries,
    `ImbalancedChen.TotientReciprocalBudget,
    `ImbalancedChen.UniformPrimeTail]
  let moduleNames := env.header.moduleNames
  let selected := env.constants.fold (init := (#[] : Array (Name × Name))) (fun acc name _ =>
    match env.getModuleIdxFor? name with
    | some index =>
      let owner := moduleNames[index.toNat]!
      if targets.contains owner && !isPrivateName name then acc.push (owner, name) else acc
    | none => acc)
  let entries := selected.qsort (fun a b => Name.lt a.2 b.2)
  for (owner, name) in entries do
    let record := Json.mkObj [("module", toJson owner.toString), ("name", toJson name.toString)]
    logInfo m!"CANONICAL_NAME {record.compress}"
  logInfo m!"CANONICAL_FINISHED {entries.size}"
