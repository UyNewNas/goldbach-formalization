import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional
import Lean.Util.CollectAxioms

/-!
Part 3 audit for the exact unconditional Bombieri--Vinogradov supplier used by
`Part3PrimeAPDistribution`.  The inventory is selected by compiler-recorded
defining module, so private and generated declarations are covered together
with the four public theorems.
-/

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
  let moduleName :=
    `MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for importedModule in env.header.moduleNames do
    let path ← liftIO <| Lean.findOLean importedModule
    let record := Json.mkObj [
      ("module", toJson importedModule.toString),
      ("olean", toJson path.toString)]
    liftIO <| IO.println s!"PART3_BV_SUPPLIER_IMPORT {record.compress}"
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if env.header.moduleNames[idx]! == moduleName then names.push name else names
    | none => names
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in the supplier module: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in the supplier module: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let type ← liftTermElabM do
      return (← Meta.ppExpr info.type).pretty
    let readableType ← liftTermElabM do
      withOptions (fun opts => (opts.setBool `pp.all false).setBool `pp.explicit false) do
        return (← Meta.ppExpr info.type).pretty
    if type.contains '⋯' || readableType.contains '⋯' then
      throwError "Truncated compiler type for {name}"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("level_parameters", toJson (info.levelParams.map Name.toString)),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"PART3_BV_SUPPLIER_DECL {record.compress}"
  unless names.size > 0 do
    throwError "Supplier module has no declarations"
  let summary := Json.mkObj [
    ("module", toJson moduleName.toString),
    ("count", toJson names.size)]
  liftIO <| IO.println s!"PART3_BV_SUPPLIER_MODULE {summary.compress}"
