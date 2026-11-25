import Lean
import all Lean.Compiler.ModPkgExt

open Lean System

/-
Diagnostic reconstruction of two fixed legacy objects. The input ModuleData is
read directly; its mathematical modules are never imported or elaborated.
Only the value of its existing modPkgExt entry is replaced. The resulting file
receives no acceptance until its complete SHA256 equals the historical object.
-/
def main (args : List String) : IO Unit := do
  let [moduleArg, inputName, outputName] := args
    | throw <| IO.userError
        "usage: RetagPackage MODULE input.olean output.olean"
  let moduleName : Name ← match moduleArg with
    | "ImbalancedChen.P2AffineSimplexMomentLaw" =>
      pure `ImbalancedChen.P2AffineSimplexMomentLaw
    | "ImbalancedChen.P2Winner9CompleteSeedTypes" =>
      pure `ImbalancedChen.P2Winner9CompleteSeedTypes
    | _ => throw <| IO.userError "module is outside the two fixed diagnostic cases"
  let input : FilePath := inputName
  let output : FilePath := outputName
  if input == output then
    throw <| IO.userError "input and output must differ"
  if ← output.pathExists then
    throw <| IO.userError "refusing to overwrite an existing output"
  let roundtrip : FilePath := outputName ++ ".roundtrip"
  if ← roundtrip.pathExists then
    throw <| IO.userError "refusing to overwrite an existing roundtrip"
  let (original, region) ← readModuleData input
  let entryItems := original.entries.foldl (fun n entry => n + entry.2.size) 0
  IO.println s!"INPUT module={moduleName} constants={original.constants.size} constNames={original.constNames.size} extensions={original.entries.size} entryItems={entryItems} isModule={original.isModule} bytes={region.size}"
  if original.isModule then
    throw <| IO.userError "diagnostic requires a legacy single-file object"
  unless original.constants.size == original.constNames.size do
    throw <| IO.userError "inconsistent serialized declaration inventory"
  let key := modPkgExt.name
  let matches := original.entries.filter fun entry => entry.1 == key
  unless matches.size == 1 do
    throw <| IO.userError "expected exactly one modPkgExt entry"
  unless matches[0]!.2.size == 1 do
    throw <| IO.userError "expected a singleton original package value"
  let empty ← mkEmptyEnvironment
  let packageEnv := Environment.setModulePackage (some "imbalancedChen")
    (empty.setMainModule moduleName)
  let seed ← mkModuleData packageEnv
  let some replacement := seed.entries.find? (fun entry => entry.1 == key)
    | throw <| IO.userError "core serializer omitted modPkgExt"
  unless replacement.2.size == 1 do
    throw <| IO.userError "unexpected replacement package entry shape"
  let patched := { original with entries := original.entries.map fun entry =>
    if entry.1 == key then (entry.1, replacement.2) else entry }
  saveModuleData roundtrip moduleName original
  saveModuleData output moduleName patched
  IO.println s!"OUTPUT module={moduleName} constants={patched.constants.size} constNames={patched.constNames.size} extensions={patched.entries.size} isModule={patched.isModule} changedExtension={key} package=imbalancedChen"
