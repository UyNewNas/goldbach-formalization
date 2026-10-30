import Lean.CoreM
import Lean.Replay
import Lake.Load.Manifest

/-! Executable audit utility, not a proof module. The function below is copied
byte-for-byte from pinned Lean 4.33.0-rc1 LeanChecker.lean, only enclosed in
an independent namespace. Main selects exactly one target; it does not enumerate
prefixes, schedule parallel replays, or substitute replayFromFresh. -/
namespace ExactReplay
open Lean

unsafe def replayFromImports (module : Name) : IO Unit := do
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  -- Load all module data parts (exported, server, private)
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let mut newConstants := {}
  -- Collect constants from last ("most private") part, which subsumes all prior ones
  for name in parts[parts.size-1].1.constNames, ci in parts[parts.size-1].1.constants do
    newConstants := newConstants.insert name ci
  let env' ← env.replay newConstants
  env'.freeRegions

end ExactReplay

open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [target] := args
    | throw <| IO.userError "expected exactly one module name"
  let module := target.toName
  if target.isEmpty || module.isAnonymous then
    throw <| IO.userError "expected a nonempty module name"
  initSearchPath (← findSysroot)
  IO.println s!"exact replay starting {module}"
  ExactReplay.replayFromImports module
  IO.println s!"exact replay passed {module}"
  return 0
