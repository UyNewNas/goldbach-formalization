import ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint
import ImbalancedChen.P4AOriginalFull87SavedGain
import ImbalancedChen.P4AOriginalFull87CompiledCounting
import ImbalancedChen.P4AOriginalNewFifthPaidDensity
import ImbalancedChen.P4AFull87UnionCompilerPayment
import ImbalancedChen.P4AFull87RoughEulerRatio
import ImbalancedChen.P4AFull87UnionPhysicalSupport
import Lean.Util.CollectAxioms

/-! Full original full87, new fifth, compiler payment and original numerical endpoint type audit. Remote only. -/

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
    `ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.union_ordinary_saved_gain,
    `ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.union_positive_presieve_saved_gain,
    `ImbalancedChen.P4AOriginalFull87SavedGain.original_saved_gain_q96,
    `ImbalancedChen.P4AOriginalFull87SavedGain.original_saved_gain_le_integral,
    `ImbalancedChen.P4AOriginalFull87SavedGain.original_eight_slot_sum_le_integral,
    `ImbalancedChen.P4AOriginalFull87CompiledCounting.physical_density_eq_raw_add_signed_source,
    `ImbalancedChen.P4AOriginalFull87CompiledCounting.real_count_le_original_sources_add_distribution,
    `ImbalancedChen.P4AOriginalFull87CompiledCounting.exists_physical_density_le_paid_sources,
    `ImbalancedChen.P4AOriginalNewFifthPhysical.exists_joined_ordinary,
    `ImbalancedChen.P4AOriginalNewFifthPhysical.exists_joined_positive_presieve,
    `ImbalancedChen.P4AOriginalNewFifthPaidDensity.exists_paid_density_and_count,
    `ImbalancedChen.P4AFull87UnionCompilerPayment.union_paid,
    `ImbalancedChen.P4AFull87UnionCompilerPayment.actual_rate,
    `ImbalancedChen.P4AFull87UnionCompilerPayment.changed_seen,
    `ImbalancedChen.P4AFull87HistoricalCompilerRate.exists_actual_rate,
    `ImbalancedChen.P4AFull87PhysicalReserveFromRate.historical_paid,
    `ImbalancedChen.P4AFull87RoughEulerRatio.of_wallRate,
    `ImbalancedChen.P4AFull87UnionPhysicalSupport.data_physical_range,
    `ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.exists_ordinary_saved_gain,
    `ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.exists_positive_presieve_saved_gain,
    `ImbalancedChen.P4AOriginalFull87SavedGain.original87_archived_cell_le_integral,
    `ImbalancedChen.P4AOriginalFull87SavedGain.original87_refined_cell_le_integral,
    `ImbalancedChen.P4AOriginalFull87SavedGain.original_base87_le_integral,
    `ImbalancedChen.P4AOriginalFull87Saved86.savedGain_eq_original_eight_slots,
    `ImbalancedChen.P4AOriginalFull87UnionActualGain.original_raw_difference_eq_box,
    `ImbalancedChen.P4AOriginalFull87SourceDictionary.globalIndex_bijective,
    `ImbalancedChen.P4AOriginalFull87SourceDictionary.source_cell_count]
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
    liftIO <| IO.println s!"FULL87_DECL {record.compress}"
  liftIO <| IO.println s!"FULL87_COUNT {names.size}"

#print axioms ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.union_ordinary_saved_gain
#print axioms ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.union_positive_presieve_saved_gain
#print axioms ImbalancedChen.P4AOriginalFull87SavedGain.original_saved_gain_q96
#print axioms ImbalancedChen.P4AOriginalFull87SavedGain.original_saved_gain_le_integral
#print axioms ImbalancedChen.P4AOriginalFull87SavedGain.original_eight_slot_sum_le_integral
#print axioms ImbalancedChen.P4AOriginalFull87CompiledCounting.physical_density_eq_raw_add_signed_source
#print axioms ImbalancedChen.P4AOriginalFull87CompiledCounting.real_count_le_original_sources_add_distribution
#print axioms ImbalancedChen.P4AOriginalFull87CompiledCounting.exists_physical_density_le_paid_sources
#print axioms ImbalancedChen.P4AOriginalNewFifthPhysical.exists_joined_ordinary
#print axioms ImbalancedChen.P4AOriginalNewFifthPhysical.exists_joined_positive_presieve
#print axioms ImbalancedChen.P4AOriginalNewFifthPaidDensity.exists_paid_density_and_count
#print axioms ImbalancedChen.P4AFull87UnionCompilerPayment.union_paid
#print axioms ImbalancedChen.P4AFull87UnionCompilerPayment.actual_rate
#print axioms ImbalancedChen.P4AFull87UnionCompilerPayment.changed_seen
#print axioms ImbalancedChen.P4AFull87HistoricalCompilerRate.exists_actual_rate
#print axioms ImbalancedChen.P4AFull87PhysicalReserveFromRate.historical_paid
#print axioms ImbalancedChen.P4AFull87RoughEulerRatio.of_wallRate
#print axioms ImbalancedChen.P4AFull87UnionPhysicalSupport.data_physical_range
#print axioms ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.exists_ordinary_saved_gain
#print axioms ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.exists_positive_presieve_saved_gain
#print axioms ImbalancedChen.P4AOriginalFull87SavedGain.original87_archived_cell_le_integral
#print axioms ImbalancedChen.P4AOriginalFull87SavedGain.original87_refined_cell_le_integral
#print axioms ImbalancedChen.P4AOriginalFull87SavedGain.original_base87_le_integral
#print axioms ImbalancedChen.P4AOriginalFull87Saved86.savedGain_eq_original_eight_slots
#print axioms ImbalancedChen.P4AOriginalFull87UnionActualGain.original_raw_difference_eq_box
#print axioms ImbalancedChen.P4AOriginalFull87SourceDictionary.globalIndex_bijective
#print axioms ImbalancedChen.P4AOriginalFull87SourceDictionary.source_cell_count

#print ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.Ordinary
#print ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.PositivePresieve
#print ImbalancedChen.P4AOriginalNewFifthPhysical.Joined
#print ImbalancedChen.P4AOriginalNewFifthPhysical.beforeEight
#print ImbalancedChen.P4AOriginalNewFifthPaidDensity.upper
#print ImbalancedChen.P4AOriginalNewFifthPaidDensity.rho
#print ImbalancedChen.P4AOriginalFull87CompiledCounting.moduli
#print ImbalancedChen.P4AOriginalFull87CompiledCounting.coefficient
#print ImbalancedChen.P4AOriginalFull87CompiledCounting.signedCompilerSource
#print ImbalancedChen.P4AFull87PhysicalReserveFromRate.Paid
#print ImbalancedChen.P4AFull87PhysicalReserveFromRate.WallRate
#print ImbalancedChen.P4AFull87DataCompilerReads.tag
#print ImbalancedChen.P4AFull87DataCompilerReads.reads
#print ImbalancedChen.P4AFull87DataCompilerReads.mode
#print ImbalancedChen.P4AFull87DataCompilerReads.evaluate
#print ImbalancedChen.P4AFull87UnionCompilerPayment.keep
#print ImbalancedChen.P4AUpperTaggedBetaAttachment.rho
#print ImbalancedChen.P4AOriginalNewFifthUnion.data
#print ImbalancedChen.P4AOriginalFull87DataPolicy.policy
#print ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.Scheduled
#print ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.sixth
#print ImbalancedChen.P4AOriginalFull87ActualSavedEndpoint.eighth
#print ImbalancedChen.P4AOriginalFull87Saved86.savedGain
#print ImbalancedChen.P4AOriginalFull87UnionHistory.bank
#print ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger.raw
#print ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger.physical
#print ImbalancedChen.P5OriginalCommonPositivePresieve.normalize
