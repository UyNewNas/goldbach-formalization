/- Diagnostic only. Complete owned inventory and flags, with transitive axioms.
No full-type or acceptance credit. Original compiled source and object remain untouched. -/
import ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector
import Lean
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleName := `ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector
  let some idx := env.getModuleIdx? moduleName
    | throwError "Missing target module"
  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>
    if i == idx && (env.find? n).isSome then ns.push n else ns
  let mut serialized : Array Name := #[]
  let mut found := false
  for i in List.range env.header.modules.size do
    let imported := env.header.modules[i]!
    if imported.module == moduleName then
      if found then throwError "Duplicate module"
      found := true
      let data := env.header.moduleData[i]!
      if data.isModule || !imported.importAll || !imported.hasData then
        throwError "Incomplete imported legacy data"
      serialized := data.constNames
  unless found && names.size > 0 && names.qsort Name.lt == serialized.qsort Name.lt do
    throwError "Complete serialized/environment inventory mismatch"
  let inventory := Json.mkObj [
    ("module", toJson moduleName.toString),
    ("serialized", toJson (serialized.map Name.toString)),
    ("environment", toJson (names.map Name.toString)),
    ("owned_count", toJson names.size),
    ("diagnostic_only", toJson true), ("acceptance_credit", toJson false)]
  liftIO <| IO.println s!"P24_FINITE_SELECTOR_FLAGS_INVENTORY {inventory.compress}"
  let mut flagged : Array Name := #[]
  let mut unsafeNames : Array Name := #[]
  let mut partialNames : Array Name := #[]
  let mut axiomNames : Array Name := #[]
  let mut emitted : Array Name := #[]
  for name in names.qsort Name.lt do
    let some info := env.find? name
      | throwError "Missing inventoried declaration {name}"
    let kind := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    let axioms ← collectAxioms name
    let forbidden := axioms.filter fun ax => !#[`propext, `Classical.choice, `Quot.sound].contains ax
    let rejected := info.isUnsafe || info.isPartial || info.isAxiom || !forbidden.isEmpty
    if rejected then flagged := flagged.push name
    if info.isUnsafe then unsafeNames := unsafeNames.push name
    if info.isPartial then partialNames := partialNames.push name
    if info.isAxiom then axiomNames := axiomNames.push name
    emitted := emitted.push name
    let record := Json.mkObj [
      ("module", toJson moduleName.toString), ("name", toJson name.toString),
      ("user_name", toJson (privateToUserName name).toString),
      ("private", toJson (isPrivateName name)), ("kind", toJson kind),
      ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
      ("axiom", toJson info.isAxiom),
      ("axioms", toJson (axioms.map Name.toString)),
      ("forbidden_axioms", toJson (forbidden.map Name.toString)),
      ("rejected_by_original_flag_rules", toJson rejected)]
    liftIO <| IO.println s!"P24_FINITE_SELECTOR_FLAGS_DECL {record.compress}"
  unless emitted == names.qsort Name.lt do
    throwError "Diagnostic output did not cover every owned declaration"
  let summary := Json.mkObj [
    ("module", toJson moduleName.toString), ("diagnostic_only", toJson true),
    ("owned_count", toJson names.size), ("emitted_count", toJson emitted.size),
    ("serialized_environment_equal", toJson true),
    ("flagged_names", toJson (flagged.map Name.toString)),
    ("unsafe_names", toJson (unsafeNames.map Name.toString)),
    ("partial_names", toJson (partialNames.map Name.toString)),
    ("axiom_names", toJson (axiomNames.map Name.toString)),
    ("original_flag_rules_satisfied", toJson flagged.isEmpty),
    ("full_types_checked", toJson false), ("transitive_axioms_checked", toJson true),
    ("compile_credit", toJson false), ("kernel_credit", toJson false),
    ("acceptance_credit", toJson false), ("full_owned_audit_credit", toJson false),
    ("finite_A_credit", toJson false), ("P2_acceptance_credit", toJson false)]
  liftIO <| IO.println s!"P24_FINITE_SELECTOR_FLAGS_SUMMARY {summary.compress}"
