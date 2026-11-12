import ImbalancedChen.P4AOriginalFiniteAll22FineDensity
import Lean.Util.CollectAxioms
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
  let names : Array Name := #[`ImbalancedChen.P4AOriginalFiniteAll22FineDensity.exists_fine_same_rho_hdensity,`ImbalancedChen.P4AOriginalFiniteAll22FineDensity.upper_lt_currentK,`ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient.exists_fine_cofinal_same_coefficient_density_and_count,`ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient.exists_cofinal_same_coefficient_density_and_count,`ImbalancedChen.P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect,`ImbalancedChen.p4aActualPresieveCorrection_nonneg]
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
    liftIO <| IO.println s!"DENSITY_DECL {record.compress}"
  liftIO <| IO.println s!"DENSITY_COUNT {names.size}"


open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names : Array Name := #[`ImbalancedChen.P4AOriginalFiniteAll22FineDensity.modulusFamily,`ImbalancedChen.P4AOriginalFiniteAll22FineDensity.coefficientFamily,`ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient.upper,`ImbalancedChen.P4AOriginalFiniteFallbackPolicy.F,`ImbalancedChen.P4AOriginalFiniteFallbackPolicy.rho,`ImbalancedChen.physicalDensitySum,`ImbalancedChen.realPhysicalDistributionError]
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
    liftIO <| IO.println s!"DENSITY_DEF {record.compress}"
  liftIO <| IO.println s!"DENSITY_DEF_COUNT {names.size}"


run_cmd liftIO <| IO.println "DENSITY_BODY_BEGIN ImbalancedChen.P4AOriginalFiniteAll22FineDensity.modulusFamily"
#print ImbalancedChen.P4AOriginalFiniteAll22FineDensity.modulusFamily
run_cmd liftIO <| IO.println "DENSITY_BODY_END ImbalancedChen.P4AOriginalFiniteAll22FineDensity.modulusFamily"

run_cmd liftIO <| IO.println "DENSITY_BODY_BEGIN ImbalancedChen.P4AOriginalFiniteAll22FineDensity.coefficientFamily"
#print ImbalancedChen.P4AOriginalFiniteAll22FineDensity.coefficientFamily
run_cmd liftIO <| IO.println "DENSITY_BODY_END ImbalancedChen.P4AOriginalFiniteAll22FineDensity.coefficientFamily"

run_cmd liftIO <| IO.println "DENSITY_BODY_BEGIN ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient.upper"
#print ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient.upper
run_cmd liftIO <| IO.println "DENSITY_BODY_END ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient.upper"

run_cmd liftIO <| IO.println "DENSITY_BODY_BEGIN ImbalancedChen.P4AOriginalFiniteFallbackPolicy.F"
#print ImbalancedChen.P4AOriginalFiniteFallbackPolicy.F
run_cmd liftIO <| IO.println "DENSITY_BODY_END ImbalancedChen.P4AOriginalFiniteFallbackPolicy.F"

run_cmd liftIO <| IO.println "DENSITY_BODY_BEGIN ImbalancedChen.P4AOriginalFiniteFallbackPolicy.rho"
#print ImbalancedChen.P4AOriginalFiniteFallbackPolicy.rho
run_cmd liftIO <| IO.println "DENSITY_BODY_END ImbalancedChen.P4AOriginalFiniteFallbackPolicy.rho"

run_cmd liftIO <| IO.println "DENSITY_BODY_BEGIN ImbalancedChen.physicalDensitySum"
#print ImbalancedChen.physicalDensitySum
run_cmd liftIO <| IO.println "DENSITY_BODY_END ImbalancedChen.physicalDensitySum"

run_cmd liftIO <| IO.println "DENSITY_BODY_BEGIN ImbalancedChen.realPhysicalDistributionError"
#print ImbalancedChen.realPhysicalDistributionError
run_cmd liftIO <| IO.println "DENSITY_BODY_END ImbalancedChen.realPhysicalDistributionError"
