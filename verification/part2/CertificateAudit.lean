import ImbalancedChen.Certificates.PairedFibreIntegral
import ImbalancedChen.Certificates.RationalLogCertificate
import ImbalancedChen.Certificates.PairedCertificateChecker
import ImbalancedChen.Certificates.PairedV2Data
import ImbalancedChen.Certificates.PairedV2
import Lean.Util.CollectAxioms

/-!
Inventory every declaration whose defining module belongs to Part 2, including
private declarations and generated definitions, fields, constructors and recursors.
This uses the pinned Lean environment and its transitive axiom collector. The
independent workflow checks the emitted inventory, exact module coverage, printed
types and the standard three-axiom allowlist again.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[
    `ImbalancedChen.Certificates.PairedFibreIntegral,
    `ImbalancedChen.Certificates.RationalLogCertificate,
    `ImbalancedChen.Certificates.PairedCertificateChecker,
    `ImbalancedChen.Certificates.PairedV2Data,
    `ImbalancedChen.Certificates.PairedV2]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in a Part 2 module: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in a Part 2 module: {name}"
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
    liftIO <| IO.println s!"P2_AUDIT_DECL {record.compress}"
  for (m, count) in counts do
    unless count > 0 do
      throwError "Audited Part 2 module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"P2_AUDIT_MODULE {record.compress}"
  liftIO <| IO.println s!"P2_AUDIT_COUNT {names.size}"
