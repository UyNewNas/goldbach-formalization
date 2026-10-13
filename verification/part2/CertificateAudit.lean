import ImbalancedChen.Certificates.RationalLogCertificate
import ImbalancedChen.Certificates.PairedFibreIntegral
import ImbalancedChen.Certificates.PairedCertificateChecker
import ImbalancedChen.Certificates.PairedV2Data
import ImbalancedChen.Certificates.PairedV2
import ImbalancedChen.Certificates.AboveMuSecondCoarse
import ImbalancedChen.Certificates.PairedV2Geometry
import ImbalancedChen.Certificates.PairedV2Prefix4Data
import ImbalancedChen.Certificates.PairedV2Prefix4
import ImbalancedChen.Certificates.PairedV2Batch4To64Data
import ImbalancedChen.Certificates.PairedV2Batch4To64
import ImbalancedChen.Certificates.PairedV2Prefix64
import ImbalancedChen.Certificates.PairedV2Batch64To128Data
import ImbalancedChen.Certificates.PairedV2Batch64To128
import ImbalancedChen.Certificates.PairedV2Prefix128
import ImbalancedChen.Certificates.PairedV2Batch128To192Data
import ImbalancedChen.Certificates.PairedV2Batch128To192
import ImbalancedChen.Certificates.PairedV2Prefix192
import Lean.Util.CollectAxioms

/-! Explicit Part 2 batch: defining-module inventory, including private/generated declarations.
Every inventoried declaration is checked for unsafe, axioms, and transitive axiom whitelist.
This audit covers only the modules listed below; it does not claim full-root verification. -/

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
  let modules := #[
    `ImbalancedChen.Certificates.RationalLogCertificate,
    `ImbalancedChen.Certificates.PairedFibreIntegral,
    `ImbalancedChen.Certificates.PairedCertificateChecker,
    `ImbalancedChen.Certificates.PairedV2Data,
    `ImbalancedChen.Certificates.PairedV2,
    `ImbalancedChen.Certificates.AboveMuSecondCoarse,
    `ImbalancedChen.Certificates.PairedV2Geometry,
    `ImbalancedChen.Certificates.PairedV2Prefix4Data,
    `ImbalancedChen.Certificates.PairedV2Prefix4,
    `ImbalancedChen.Certificates.PairedV2Batch4To64Data,
    `ImbalancedChen.Certificates.PairedV2Batch4To64,
    `ImbalancedChen.Certificates.PairedV2Prefix64,
    `ImbalancedChen.Certificates.PairedV2Batch64To128Data,
    `ImbalancedChen.Certificates.PairedV2Batch64To128,
    `ImbalancedChen.Certificates.PairedV2Prefix128,
    `ImbalancedChen.Certificates.PairedV2Batch128To192Data,
    `ImbalancedChen.Certificates.PairedV2Batch128To192,
    `ImbalancedChen.Certificates.PairedV2Prefix192]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  let mut counts : Array (Name × Nat) := modules.map (·, 0)
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing inventoried declaration {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration in a Part 2 batch module: {name}"
    if info.isAxiom then
      throwError "Unproved axiom declaration in a Part 2 batch module: {name}"
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
    let readableType ← liftTermElabM do
      withOptions (fun opts => (opts.setBool `pp.all false).setBool `pp.explicit false) do
        return (← Meta.ppExpr info.type).pretty
    if type.contains '⋯' || readableType.contains '⋯' then
      throwError "Truncated compiler type for {name}"
    let record := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("type", toJson type),
      ("readable_type", toJson readableType),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"P2_AUDIT_DECL {record.compress}"
  for (m, count) in counts do
    unless count > 0 do
      throwError "Audited Part 2 batch module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"P2_AUDIT_MODULE {record.compress}"
  liftIO <| IO.println s!"P2_AUDIT_COUNT {names.size}"
