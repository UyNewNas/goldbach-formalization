import MathlibNt.SieveTheory.LinearSieve
import Lean.Elab.ParseImportsFast
import Lean.Elab.Command

/- Dedicated import-only audit. This is an audit utility, not a proof supplier.
No general nonempty declaration gate is modified. Python additionally requires
exact module, fixed Git blob/SHA, source-only imports, and bound closure objects. -/
open Lean Elab Command in
run_cmd do
  let target := `MathlibNt.SieveTheory.LinearSieve
  let source := ".lake/packages/goldbach/MathlibNt/SieveTheory/LinearSieve.lean"
  let text ← liftIO <| IO.FS.readFile source
  let expected ← liftIO <| Lean.parseImports' text source
  let env ← getEnv
  let some idx := env.getModuleIdx? target | throwError "Missing empty aggregator"
  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>
    if i == idx then ns.push n else ns
  unless names.isEmpty do throwError "Empty aggregator has environment declarations"
  let mut found := 0
  for i in List.range env.header.modules.size do
    let imported := env.header.modules[i]!
    if imported.module == target then
      found := found + 1
      let data := env.header.moduleData[i]!
      if data.isModule || !imported.importAll || !imported.hasData then
        throwError "Incomplete imported legacy data"
      unless data.constNames.isEmpty && data.constants.isEmpty && data.extraConstNames.isEmpty do
        throwError "Empty aggregator has serialized declarations or generated extra names"
      unless data.isModule == expected.isModule && data.imports == expected.imports do
        throwError "Source/header imports differ from serialized actual imports"
      liftIO <| IO.println s!"EMPTY_AGGREGATOR_IMPORTS {(toJson data.imports).compress}"
  unless found == 1 do throwError "Empty aggregator must appear exactly once"
  liftIO <| IO.println s!"EMPTY_AGGREGATOR_INVENTORY {(Json.mkObj [("module", toJson target.toString), ("serialized", toJson (#[] : Array String)), ("environment", toJson (#[] : Array String)), ("constants", toJson (0 : Nat)), ("extraConstNames", toJson (0 : Nat)), ("ownProofs", toJson (0 : Nat))]).compress}"
