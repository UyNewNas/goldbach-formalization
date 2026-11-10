import ImbalancedChen.P5OriginalFullFifthFloorIntegral
import Lean.Util.CollectAxioms

/-! Exact eight-declaration audit requested by the frozen S25 primary review.
This adds no mathematical supplier and is executed only by root's remote CI. -/

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
    `ImbalancedChen.P5OriginalFullFifthFloorIntegral.original_stored_old_floor_le_parentIntegral,
    `ImbalancedChen.P5OriginalFullFifthFloorIntegral.each_original_stored_floor_sub_reserve,
    `ImbalancedChen.P5OriginalFullFifthFloorIntegral.full_original_stored_floor_sub_reserve,
    `ImbalancedChen.P5OriginalFullFifthFloorIntegral.original_fifth_endpoint_sub_reserve,
    `ImbalancedChen.P5OriginalFullFifthFloorIntegral.exists_original_fifth_safe_integral,
    `ImbalancedChen.P5OriginalStoredFifthEndpoint.original_stored_fifth_endpoint,
    `ImbalancedChen.P5OriginalStoredOldArchiveBinding.original_stored_old_eq_max,
    `ImbalancedChen.P5OriginalTaylorActualMidpointIntegral.original_taylorLowerQ_le_signedIntegral]
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
    liftIO <| IO.println s!"T01_FIFTH_DECL {record.compress}"
  liftIO <| IO.println s!"T01_FIFTH_COUNT {names.size}"

#print axioms ImbalancedChen.P5OriginalFullFifthFloorIntegral.original_stored_old_floor_le_parentIntegral
#print axioms ImbalancedChen.P5OriginalFullFifthFloorIntegral.each_original_stored_floor_sub_reserve
#print axioms ImbalancedChen.P5OriginalFullFifthFloorIntegral.full_original_stored_floor_sub_reserve
#print axioms ImbalancedChen.P5OriginalFullFifthFloorIntegral.original_fifth_endpoint_sub_reserve
#print axioms ImbalancedChen.P5OriginalFullFifthFloorIntegral.exists_original_fifth_safe_integral
#print axioms ImbalancedChen.P5OriginalStoredFifthEndpoint.original_stored_fifth_endpoint
#print axioms ImbalancedChen.P5OriginalStoredOldArchiveBinding.original_stored_old_eq_max
#print axioms ImbalancedChen.P5OriginalTaylorActualMidpointIntegral.original_taylorLowerQ_le_signedIntegral
