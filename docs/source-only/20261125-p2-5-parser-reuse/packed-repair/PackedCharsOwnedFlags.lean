import ImbalancedChen.P2OriginalSaving19PackedChars
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let moduleName := `ImbalancedChen.P2OriginalSaving19PackedChars
  let some idx := env.getModuleIdx? moduleName | throwError "Missing target"
  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>
    if i == idx && (env.find? n).isSome then ns.push n else ns
  for name in names.qsort Name.lt do
    let some info := env.find? name | throwError "Missing declaration"
    liftIO <| IO.println ("PACKEDCHARS_FLAG " ++ (Json.mkObj [("name", toJson name.toString), ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial), ("axiom", toJson info.isAxiom)]).compress)
  liftIO <| IO.println s!"PACKEDCHARS_COMPLETE_OWNED_COUNT {names.size}"
