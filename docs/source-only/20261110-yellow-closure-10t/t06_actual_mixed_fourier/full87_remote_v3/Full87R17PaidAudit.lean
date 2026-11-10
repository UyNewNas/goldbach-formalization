import ImbalancedChen.P4AFull87PhysicalReserveFromRate
import ImbalancedChen.P4AOrderedThirdActualRoughGeometry
import ImbalancedChen.P4AOrderedThirdArithmeticCells
import ImbalancedChen.P4AOrderedThirdArithmeticOccurrence
import ImbalancedChen.P4AOrderedThirdBufferedFallbackBoxes
import ImbalancedChen.P4AOrderedThirdClippedFactorial
import ImbalancedChen.P4AOrderedThirdCommonSchedule
import ImbalancedChen.P4AOrderedThirdCompactComparison
import ImbalancedChen.P4AOrderedThirdEighthSelectionProgram
import ImbalancedChen.P4AOrderedThirdEighthTrimProgram
import ImbalancedChen.P4AOrderedThirdFixedOmegaLimit
import ImbalancedChen.P4AOrderedThirdGlobalRange
import ImbalancedChen.P4AOrderedThirdIntegratedProfile
import ImbalancedChen.P4AOrderedThirdPhysicalAtoms
import ImbalancedChen.P4AOrderedThirdPhysicalRange
import ImbalancedChen.P4AOrderedThirdPhysicalSplit
import ImbalancedChen.P4AOrderedThirdPositiveRoot
import ImbalancedChen.P4AOrderedThirdPrefixDeletion
import ImbalancedChen.P4AOrderedThirdRankReads
import ImbalancedChen.P4AOrderedThirdReachableCeiling
import ImbalancedChen.P4AOrderedThirdRectanglePayment
import ImbalancedChen.P4AOrderedThirdRectangleRate
import ImbalancedChen.P4AOrderedThirdRoughCutTransport
import ImbalancedChen.P4AOrderedThirdSameCoefficient
import ImbalancedChen.P4AOrderedThirdStaticRootPrograms
import ImbalancedChen.P4AOrderedThirdStaticSixthPrograms
import ImbalancedChen.P4AOrderedThirdTransportKernel
import ImbalancedChen.P4AOriginalFull87CompiledCounting
import ImbalancedChen.P4AOriginalFull87SourceDictionary
import ImbalancedChen.P4AOriginalFull87SourcePrimeTests
import ImbalancedChen.P4AOriginalNewFifthUnion
import ImbalancedChen.P4AOriginalNonsingletonComparison
import ImbalancedChen.P4AOriginalNonsingletonEighthParent
import ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient
import ImbalancedChen.P4AOriginalOrderedThirdFullPolicy
import ImbalancedChen.P4AOriginalR17EighthParent
import ImbalancedChen.P4AOriginalR17EighthSignedTransport
import ImbalancedChen.P4AOriginalR17Full87SavedEndpoint
import ImbalancedChen.P4AOriginalR17PaidIntegral
import ImbalancedChen.P4AOriginalR17SameCutoffPresieve
import ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger
import ImbalancedChen.P4AUpperTaggedBetaAttachment
import ImbalancedChen.P4AUpperTaggedParityCompiler
import ImbalancedChen.P5OriginalCommonPositivePresieve
import Lean.Util.CollectAxioms

/-! Actual R17 paid-I87 full types, axioms and physical definitions. Remote only. -/

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
  let names : Array Name := #[
    `ImbalancedChen.P4AOriginalR17PaidIntegral.original_signed_density_and_count,
    `ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_ordinary_source,
    `ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_ordinary_saved,
    `ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_positive_source,
    `ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_positive_saved,
    `ImbalancedChen.P4AOriginalR17SameCutoffPresieve.original_source,
    `ImbalancedChen.P4AOriginalR17SameCutoffPresieve.original_saved,
    `ImbalancedChen.P4AOrderedThirdCommonSchedule.common_schedule,
    `ImbalancedChen.P4AOrderedThirdRectanglePayment.paid,
    `ImbalancedChen.P4AOrderedThirdSameCoefficient.joined,
    `ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.count,
    `ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.upper_majorant,
    `ImbalancedChen.P4AOriginalR17EighthSignedTransport.coefficient_difference,
    `ImbalancedChen.P4AOriginalR17EighthSignedTransport.raw_difference,
    `ImbalancedChen.P4AOriginalR17EighthParent.seventeenth_tent,
    `ImbalancedChen.P4AOriginalR17EighthParent.pair17_on_overlap,
    `ImbalancedChen.P4AOrderedThirdRectanglePayment.fixed_rate,
    `ImbalancedChen.P4AOrderedThirdRectanglePayment.rough_ratio]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let some info := env.find? name | throwError "Missing exact declaration {name}"
    if info.isUnsafe || info.isAxiom then
      throwError "Unsafe or axiomatic target {name}"
    let .thmInfo _ := info | throwError "Target is not a theorem: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
    let some idx := env.getModuleIdxFor? name | throwError "No defining module for {name}"
    let moduleName := env.header.moduleNames[idx]!
    let type ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    let readableType ← liftTermElabM do
      withOptions (fun opts => (opts.setBool `pp.all false).setBool `pp.explicit false) do
        return (← Meta.ppExpr info.type).pretty
    if type.contains '⋯' || type.contains '…' || readableType.contains '⋯' || readableType.contains '…' then
      throwError "Truncated compiler type for {name}"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson "theorem"),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"FULL87_PAID_DECL {record.compress}"
  liftIO <| IO.println s!"FULL87_PAID_COUNT {names.size}"


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : Array Name := #[
    `ImbalancedChen.P4AOriginalR17PaidIntegral.integralUpper,
    `ImbalancedChen.P4AOriginalR17EighthParent.orderedSixth,
    `ImbalancedChen.P4AOriginalR17EighthParent.orderedEighth,
    `ImbalancedChen.P4AOriginalR17EighthParent.parent,
    `ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.Ordinary,
    `ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.PositivePresieve,
    `ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.coefficient,
    `ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.keep,
    `ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.alignedWidth,
    `ImbalancedChen.P4AOriginalOrderedThirdFullPolicy.policy,
    `ImbalancedChen.P4AOrderedThirdArithmeticOccurrence.fresh,
    `ImbalancedChen.P4AUpperTaggedBetaAttachment.rho,
    `ImbalancedChen.P4AUpperTaggedParityCompiler.coefficient,
    `ImbalancedChen.P4AOriginalFull87CompiledCounting.moduli,
    `ImbalancedChen.P4AOriginalFull87SourcePrimeTests.cellIntegral,
    `ImbalancedChen.P4AOriginalFull87SourceDictionary.Cell,
    `ImbalancedChen.P4AOriginalNewFifthUnion.data,
    `ImbalancedChen.P4AFull87PhysicalReserveFromRate.Paid,
    `ImbalancedChen.P4AFull87PhysicalReserveFromRate.WallRate,
    `ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger.raw,
    `ImbalancedChen.P5OriginalCommonPositivePresieve.normalize]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    let some info := env.find? name | throwError "Missing exact declaration {name}"
    if info.isUnsafe || info.isAxiom then
      throwError "Unsafe or axiomatic target {name}"
    let kind ← match info with
      | .defnInfo _ => pure "definition"
      | .inductInfo _ =>
        if name == `ImbalancedChen.P4AOriginalFull87SourceDictionary.Cell then pure "inductive"
        else throwError "Unexpected inductive target: {name}"
      | _ => throwError "Target is not a physical definition or original Cell carrier: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
    let some idx := env.getModuleIdxFor? name | throwError "No defining module for {name}"
    let moduleName := env.header.moduleNames[idx]!
    let type ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    let readableType ← liftTermElabM do
      withOptions (fun opts => (opts.setBool `pp.all false).setBool `pp.explicit false) do
        return (← Meta.ppExpr info.type).pretty
    if type.contains '⋯' || type.contains '…' || readableType.contains '⋯' || readableType.contains '…' then
      throwError "Truncated compiler type for {name}"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"FULL87_PAID_DEF {record.compress}"
  liftIO <| IO.println s!"FULL87_PAID_DEF_COUNT {names.size}"


#print axioms ImbalancedChen.P4AOriginalR17PaidIntegral.original_signed_density_and_count
#print axioms ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_ordinary_source
#print axioms ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_ordinary_saved
#print axioms ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_positive_source
#print axioms ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.original_positive_saved
#print axioms ImbalancedChen.P4AOriginalR17SameCutoffPresieve.original_source
#print axioms ImbalancedChen.P4AOriginalR17SameCutoffPresieve.original_saved
#print axioms ImbalancedChen.P4AOrderedThirdCommonSchedule.common_schedule
#print axioms ImbalancedChen.P4AOrderedThirdRectanglePayment.paid
#print axioms ImbalancedChen.P4AOrderedThirdSameCoefficient.joined
#print axioms ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.count
#print axioms ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.upper_majorant
#print axioms ImbalancedChen.P4AOriginalR17EighthSignedTransport.coefficient_difference
#print axioms ImbalancedChen.P4AOriginalR17EighthSignedTransport.raw_difference
#print axioms ImbalancedChen.P4AOriginalR17EighthParent.seventeenth_tent
#print axioms ImbalancedChen.P4AOriginalR17EighthParent.pair17_on_overlap
#print axioms ImbalancedChen.P4AOrderedThirdRectanglePayment.fixed_rate
#print axioms ImbalancedChen.P4AOrderedThirdRectanglePayment.rough_ratio
#print axioms ImbalancedChen.P4AOriginalR17PaidIntegral.integralUpper
#print axioms ImbalancedChen.P4AOriginalR17EighthParent.orderedSixth
#print axioms ImbalancedChen.P4AOriginalR17EighthParent.orderedEighth
#print axioms ImbalancedChen.P4AOriginalR17EighthParent.parent
#print axioms ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.Ordinary
#print axioms ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.PositivePresieve
#print axioms ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.coefficient
#print axioms ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.keep
#print axioms ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.alignedWidth
#print axioms ImbalancedChen.P4AOriginalOrderedThirdFullPolicy.policy
#print axioms ImbalancedChen.P4AOrderedThirdArithmeticOccurrence.fresh
#print axioms ImbalancedChen.P4AUpperTaggedBetaAttachment.rho
#print axioms ImbalancedChen.P4AUpperTaggedParityCompiler.coefficient
#print axioms ImbalancedChen.P4AOriginalFull87CompiledCounting.moduli
#print axioms ImbalancedChen.P4AOriginalFull87SourcePrimeTests.cellIntegral
#print axioms ImbalancedChen.P4AOriginalFull87SourceDictionary.Cell
#print axioms ImbalancedChen.P4AOriginalNewFifthUnion.data
#print axioms ImbalancedChen.P4AFull87PhysicalReserveFromRate.Paid
#print axioms ImbalancedChen.P4AFull87PhysicalReserveFromRate.WallRate
#print axioms ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger.raw
#print axioms ImbalancedChen.P5OriginalCommonPositivePresieve.normalize

#print ImbalancedChen.P4AOriginalR17PaidIntegral.integralUpper
#print ImbalancedChen.P4AOriginalR17EighthParent.orderedSixth
#print ImbalancedChen.P4AOriginalR17EighthParent.orderedEighth
#print ImbalancedChen.P4AOriginalR17EighthParent.parent
#print ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.Ordinary
#print ImbalancedChen.P4AOriginalR17Full87SavedEndpoint.PositivePresieve
#print ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.coefficient
#print ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.keep
#print ImbalancedChen.P4AOriginalOrderedThirdActualCoefficient.alignedWidth
#print ImbalancedChen.P4AOriginalOrderedThirdFullPolicy.policy
#print ImbalancedChen.P4AOrderedThirdArithmeticOccurrence.fresh
#print ImbalancedChen.P4AUpperTaggedBetaAttachment.rho
#print ImbalancedChen.P4AUpperTaggedParityCompiler.coefficient
#print ImbalancedChen.P4AOriginalFull87CompiledCounting.moduli
#print ImbalancedChen.P4AOriginalFull87SourcePrimeTests.cellIntegral
#print ImbalancedChen.P4AOriginalFull87SourceDictionary.Cell
#print ImbalancedChen.P4AOriginalNewFifthUnion.data
#print ImbalancedChen.P4AFull87PhysicalReserveFromRate.Paid
#print ImbalancedChen.P4AFull87PhysicalReserveFromRate.WallRate
#print ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger.raw
#print ImbalancedChen.P5OriginalCommonPositivePresieve.normalize
