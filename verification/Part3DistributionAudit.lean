import ImbalancedChen.Part3DistributionTargets
import ImbalancedChen.Part3PrimeAPDistribution
import ImbalancedChen.Part3CurrentLowerDistribution
import ImbalancedChen.Part3LongSlotDistribution
import ImbalancedChen.Part3LongSlotNormalization
import ImbalancedChen.Part3BrunWeights
import ImbalancedChen.Part3BrunBudget
import ImbalancedChen.Part3LongSlotDivisorExpansion
import ImbalancedChen.Part3LongSlotBrunTransfer
import ImbalancedChen.Part3RoughAuxiliarySW
import ImbalancedChen.Part3RoughAuxiliarySWNormalization
import ImbalancedChen.Part3RoughAuxiliarySWPrimeFactor
import ImbalancedChen.Part3RoughAuxiliarySWWeighted
import ImbalancedChen.Part3RoughAuxiliarySWMellin
import ImbalancedChen.Part3RoughAuxiliarySWChart
import ImbalancedChen.Part3LongSlotBrunNormalization
import ImbalancedChen.Part3CompletedReciprocalWeil
import ImbalancedChen.Part3ComplexDispersion
import ImbalancedChen.Part3ComplexCRTConsumer
import ImbalancedChen.Part3FactorFiberDivisor
import ImbalancedChen.Part3CommonSmoothCutoff
import ImbalancedChen.Part3CleanBetaLargeGCDMajorant
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import ImbalancedChen.Part3ActualLargeGCDBetaMass
import ImbalancedChen.Part3LichtmanSignedDifferenceMultiplicity
import ImbalancedChen.Part3CommonPoisson
import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3ActualReciprocalSquarePoissonCore
import ImbalancedChen.Part3OriginalSignedCountingNorm
import ImbalancedChen.Part3DeterminantGCD
import ImbalancedChen.Part3RoughAuxiliarySWChartBudget
import ImbalancedChen.Part3SmoothReciprocalWeil
import ImbalancedChen.Part3TwoLongBrunComparison
import ImbalancedChen.Part3TwoLongCompletion
import ImbalancedChen.Part3TwoLongSmooth
import ImbalancedChen.Part3GevreyCutoff
import ImbalancedChen.Part3E1ReciprocalPhase
import ImbalancedChen.Part3BrunDensity
import Lean.Util.CollectAxioms

/-!
The declaration inventory comes from Lean's environment and defining-module
metadata, not a source-code regular expression or namespace filter. It includes
private declarations, structure fields and automatically generated declarations.
These sources use the legacy object format. Each environment inventory is
cross-checked against the full serialized constant list before auditing.
`collectAxioms` is the bundled Lean transitive collector also used by `#print axioms`.
The command fails if any inventoried declaration is unsafe, is an axiom,
or transitively uses anything outside the standard three-axiom allowlist.
-/

set_option pp.fullNames true
set_option pp.explicit true
set_option pp.universes true
set_option pp.proofs true
set_option pp.deepTerms true
set_option pp.maxSteps 1000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules := #[`ImbalancedChen.Part3DistributionTargets,
    `ImbalancedChen.Part3PrimeAPDistribution,
    `ImbalancedChen.Part3CurrentLowerDistribution,
    `ImbalancedChen.Part3LongSlotDistribution,
    `ImbalancedChen.Part3LongSlotNormalization,
    `ImbalancedChen.Part3BrunWeights,
    `ImbalancedChen.Part3BrunBudget,
    `ImbalancedChen.Part3LongSlotDivisorExpansion,
    `ImbalancedChen.Part3LongSlotBrunTransfer,
    `ImbalancedChen.Part3RoughAuxiliarySW,
    `ImbalancedChen.Part3RoughAuxiliarySWNormalization,
    `ImbalancedChen.Part3RoughAuxiliarySWPrimeFactor,
    `ImbalancedChen.Part3RoughAuxiliarySWWeighted,
    `ImbalancedChen.Part3RoughAuxiliarySWMellin,
    `ImbalancedChen.Part3RoughAuxiliarySWChart,
    `ImbalancedChen.Part3LongSlotBrunNormalization,
    `ImbalancedChen.Part3CompletedReciprocalWeil,
    `ImbalancedChen.Part3ComplexDispersion,
    `ImbalancedChen.Part3ComplexCRTConsumer,
    `ImbalancedChen.Part3FactorFiberDivisor,
    `ImbalancedChen.Part3CommonSmoothCutoff,
    `ImbalancedChen.Part3CleanBetaLargeGCDMajorant,
    `ImbalancedChen.Part3PolynomialResidueDivisorBound,
    `ImbalancedChen.Part3ActualLargeGCDBetaMass,
    `ImbalancedChen.Part3LichtmanSignedDifferenceMultiplicity,
    `ImbalancedChen.Part3CommonPoisson,
    `ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson,
    `ImbalancedChen.Part3ActualReciprocalSquarePoissonCore,
    `ImbalancedChen.Part3OriginalSignedCountingNorm,
    `ImbalancedChen.Part3DeterminantGCD,
    `ImbalancedChen.Part3RoughAuxiliarySWChartBudget,
    `ImbalancedChen.Part3SmoothReciprocalWeil,
    `ImbalancedChen.Part3TwoLongBrunComparison,
    `ImbalancedChen.Part3TwoLongCompletion,
    `ImbalancedChen.Part3TwoLongSmooth,
    `ImbalancedChen.Part3GevreyCutoff,
    `ImbalancedChen.Part3E1ReciprocalPhase,
    `ImbalancedChen.Part3BrunDensity]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let names := env.constants.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx => if modules.contains env.header.moduleNames[idx]! then names.push name else names
    | none => names
  let mut serialized : Array Name := #[]
  for idx in List.range env.header.modules.size do
    let imported := env.header.modules[idx]!
    if modules.contains imported.module then
      let data := env.header.moduleData[idx]!
      if data.isModule || !imported.importAll || !imported.hasData then
        throwError "Expected complete legacy module data for {imported.module}"
      let owned := names.filter fun name =>
        match env.getModuleIdxFor? name with
        | some i => env.header.moduleNames[i]! == imported.module
        | none => false
      unless owned.qsort Name.lt == data.constNames.qsort Name.lt do
        throwError "Serialized and defining-module inventories differ for {imported.module}"
      serialized := serialized.push imported.module
  unless serialized.qsort Name.lt == modules.qsort Name.lt do
    throwError "Missing serialized Part 3 module inventory"
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
    if type.contains '⋯' then
      throwError "Truncated compiler type for {name}"
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
