import all ImbalancedChen.Part3DistributionTargets
import all ImbalancedChen.Part3PrimeAPDistribution
import all ImbalancedChen.Part3CurrentLowerDistribution
import all ImbalancedChen.Part3LongSlotDistribution
import all ImbalancedChen.Part3LongSlotNormalization
import all ImbalancedChen.Part3RoughAuxiliarySW
import all ImbalancedChen.Part3RoughAuxiliarySWNormalization
import Lean.Util.CollectAxioms

/-!
The declaration inventory comes from Lean's environment and defining-module
metadata, not a source-code regular expression or namespace filter. It includes
private declarations, structure fields and automatically generated declarations.
`import all` requests all available module-data parts, including private ones.
`collectAxioms` is the bundled Lean transitive collector also used by `#print axioms`.
The command fails if any inventoried declaration is unsafe, is an axiom,
or transitively uses anything outside the standard three-axiom allowlist.
-/

set_option pp.fullNames true
set_option pp.explicit true
set_option pp.universes true
set_option pp.maxSteps 1000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ImbalancedChen.Part3DistributionTargets,
    `ImbalancedChen.Part3PrimeAPDistribution,
    `ImbalancedChen.Part3CurrentLowerDistribution,
    `ImbalancedChen.Part3LongSlotDistribution,
    `ImbalancedChen.Part3LongSlotNormalization,
    `ImbalancedChen.Part3RoughAuxiliarySW,
    `ImbalancedChen.Part3RoughAuxiliarySWNormalization]
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
      ("level_parameters", toJson (info.levelParams.map Name.toString)),
      ("type", toJson type),
      ("axioms", toJson (axioms.map Name.toString))]
    liftIO <| IO.println s!"PART3_AUDIT_DECL {record.compress}"
  for (m, count) in counts do
    unless count > 0 do
      throwError "Audited module has no declarations: {m}"
    let record := Json.mkObj [("module", toJson m.toString), ("count", toJson count)]
    liftIO <| IO.println s!"PART3_AUDIT_MODULE {record.compress}"
  liftIO <| IO.println s!"PART3_AUDIT_COUNT {names.size}"
