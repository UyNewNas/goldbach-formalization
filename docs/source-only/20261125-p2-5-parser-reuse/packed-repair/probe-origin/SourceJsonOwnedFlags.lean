import ImbalancedChen.P2OriginalSaving19SourceJson
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleName := `ImbalancedChen.P2OriginalSaving19SourceJson
  let some idx := env.getModuleIdx? moduleName | throwError "Missing target"
  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>
    if i == idx && (env.find? n).isSome then ns.push n else ns
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing declaration"
    if info.isUnsafe || info.isPartial || info.isAxiom then
      liftIO <| IO.println ("SOURCEJSON_FLAG " ++ (Json.mkObj [("name", toJson name.toString), ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom)]).compress)
  liftIO <| IO.println s!"SOURCEJSON_COMPLETE_OWNED_COUNT {names.size}"
