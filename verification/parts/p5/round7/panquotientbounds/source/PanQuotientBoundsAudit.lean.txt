import MathlibNt.AnalyticNumberTheory.LargeSieve.PanQuotientBounds
import Lean.Util.CollectAxioms

/-! Full defining-module inventory for the P5 Pan quotient-bounds leaf. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleName := `MathlibNt.AnalyticNumberTheory.LargeSieve.PanQuotientBounds
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let publicNames := #[
    `AnalyticNumberTheory.LargeSieve.PanQuotientBounds.eventually_nat_div_quarter,
    `AnalyticNumberTheory.LargeSieve.PanQuotientBounds.eventually_quotient_parameters]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if env.header.moduleNames[idx]! == moduleName then names.push name else names
    | none => names
  unless names.size > 0 do throwError "Audited defining module has no declarations: {moduleName}"
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then throwError "Unsafe declaration: {name}"
    if info.isAxiom then throwError "Unproved axiom: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do unless allowed.contains ax do throwError "Forbidden transitive axiom {ax} in {name}"
    let kind := match info with
      | .thmInfo _ => "theorem" | .defnInfo _ => "definition" | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient" | .axiomInfo _ => "axiom" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
    let type ← liftTermElabM do return (← Meta.ppExpr info.type).pretty
    let typeExplicit ← liftTermElabM do
      withOptions (fun opts =>
          let opts := opts.setBool `pp.explicit true
          let opts := opts.setBool `pp.universes true
          let opts := opts.setBool `pp.fullNames true
          opts.setBool `pp.proofs true) do
        return (← Meta.ppExpr info.type).pretty
    let record := Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName.toString),
      ("kind", toJson kind), ("is_unsafe", toJson info.isUnsafe),
      ("is_axiom", toJson info.isAxiom),
      ("requested_public_theorem", toJson (publicNames.contains name)),
      ("type", toJson type), ("type_explicit", toJson typeExplicit),
      ("type_expr_repr", toJson (reprStr info.type)),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"CHEN_P5_PANQUOTIENT_AUDIT_DECL {record.compress}"
  for name in publicNames do
    unless names.contains name do throwError "Requested theorem absent: {name}"
    let some (.thmInfo _) := env.find? name | throwError "Requested declaration is not a theorem: {name}"
  let record := Json.mkObj [("module", toJson moduleName.toString),
    ("count", toJson names.size), ("requested_public_theorem_count", toJson publicNames.size)]
  liftIO <| IO.println s!"CHEN_P5_PANQUOTIENT_AUDIT_MODULE {record.compress}"
  liftIO <| IO.println s!"CHEN_P5_PANQUOTIENT_AUDIT_COUNT {names.size}"
