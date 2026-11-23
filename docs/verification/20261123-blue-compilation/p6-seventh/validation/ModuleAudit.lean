import ImbalancedChen.P5U7OriginalStraddlingCells
import ImbalancedChen.P5U7OriginalScalarCoefficientWidth
import ImbalancedChen.P5U7OriginalStaircaseGeometry
import ImbalancedChen.P5U7OriginalInnerNumeratorWidth
import ImbalancedChen.P5U7OriginalRationalCoverCertificate
import ImbalancedChen.P5U7OriginalGridBoundaryArea
import ImbalancedChen.P5U7OriginalBoundaryCostRate
import ImbalancedChen.P5U7OriginalInnerCellWidth
import ImbalancedChen.P5U7OriginalRationalCoverConvergence
import ImbalancedChen.P6OriginalSeventhMeshPrice
import Lean.Util.CollectAxioms

set_option pp.all true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `ImbalancedChen.P5U7OriginalStraddlingCells,
    `ImbalancedChen.P5U7OriginalScalarCoefficientWidth,
    `ImbalancedChen.P5U7OriginalStaircaseGeometry,
    `ImbalancedChen.P5U7OriginalInnerNumeratorWidth,
    `ImbalancedChen.P5U7OriginalRationalCoverCertificate,
    `ImbalancedChen.P5U7OriginalGridBoundaryArea,
    `ImbalancedChen.P5U7OriginalBoundaryCostRate,
    `ImbalancedChen.P5U7OriginalInnerCellWidth,
    `ImbalancedChen.P5U7OriginalRationalCoverConvergence,
    `ImbalancedChen.P6OriginalSeventhMeshPrice]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in the audited modules: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in the audited modules: {name}"
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Forbidden transitive axiom {ax} in {name}"
    let idx := (env.getModuleIdxFor? name).get!
    let moduleName := env.header.moduleNames[idx]!
    counts := counts.map fun (m, count) => (m, if m == moduleName then count + 1 else count)
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
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("type", toJson type),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"P6_AUDIT_DECL {record.compress}"
  for (m, count) in counts do
    -- The legacy regression file uses anonymous examples, which need not persist.
    unless count > 0 do
      throwError "Audited module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"P6_AUDIT_MODULE {record.compress}"
  liftIO <| IO.println s!"P6_AUDIT_COUNT {names.size}"
