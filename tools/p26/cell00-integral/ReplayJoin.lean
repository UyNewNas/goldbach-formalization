import Lean.CoreM
import Lean.Replay

/-! Verification executable. The unmodified official replay API checks the
incoming declarations against the accepted parent. Shared ImportState keeps
both environments on the same mapped module data; no proof environment is
edited or synthesized by this driver. Full type/axiom auditing is separate. -/
open Lean

def literalNat (value : Expr) : IO Nat := do
  let e := value.consumeMData
  if let some n := e.rawNatLit? then return n
  let args := e.getAppArgs
  if e.getAppFn.constName? == some ``OfNat.ofNat && args.size == 3 then
    if let some n := args[1]!.rawNatLit? then return n
  throw <| IO.userError "Expected quoted natural literal"

def quotedCharacters (initial : Expr) : IO ByteArray := do
  let mut term := initial.consumeMData
  let mut bytes := ByteArray.empty
  while term.getAppFn.constName? != some ``List.nil do
    let args := term.getAppArgs
    unless term.getAppFn.constName? == some ``List.cons && args.size == 3 do
      throw <| IO.userError "Expected quoted List Char"
    let charArgs := args[1]!.getAppArgs
    unless args[1]!.getAppFn.constName? == some ``Char.ofNat && charArgs.size == 1 do
      throw <| IO.userError "Expected quoted Char"
    let n ← literalNat charArgs[0]!
    unless n < 128 do throw <| IO.userError "Unexpected non-ASCII original input"
    bytes := bytes.push n.toUInt8
    term := args[2]!.consumeMData
  return bytes

def quotedPackedCharacters (initial : Expr) : IO ByteArray := do
  let mut pending := #[initial]
  let mut bytes := ByteArray.empty
  while !pending.isEmpty do
    let term := pending.back!.consumeMData
    pending := pending.pop
    let args := term.getAppArgs
    match term.getAppFn.constName? with
    | some `ImbalancedChen.P2OriginalSaving19PackedChars.Tree.empty => pure ()
    | some `ImbalancedChen.P2OriginalSaving19PackedChars.Tree.branch =>
      unless args.size == 2 do throw <| IO.userError "Invalid quoted branch"
      pending := pending.push args[1]! |>.push args[0]!
    | some `ImbalancedChen.P2OriginalSaving19PackedChars.Tree.leaf =>
      unless args.size == 2 do throw <| IO.userError "Invalid quoted leaf"
      let n ← literalNat args[0]!
      let mut word ← literalNat args[1]!
      for _ in List.range n do
        let value := word % 4294967296
        unless value < 128 do throw <| IO.userError "Unexpected non-ASCII original input"
        bytes := bytes.push value.toUInt8
        word := word / 4294967296
      unless word == 0 do throw <| IO.userError "Unexpected high packed digits"
    | _ => throw <| IO.userError "Expected quoted packed tree"
  return bytes

def checkOriginalData (env : Environment) : IO Unit := do
  let some (.defnInfo geometry) := env.find?
      `ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic.geometryChars00
    | throw <| IO.userError "Missing original geometry character declaration"
  let geometryBytes ← quotedCharacters geometry.value
  unless geometryBytes == (← IO.FS.readBinFile "/workspace/goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json") do
    throw <| IO.userError "Embedded original geometry bytes mismatch"
  let some (.defnInfo moment) := env.find? `ImbalancedChen.P2OriginalSaving19Archive.momentPacked00
    | throw <| IO.userError "Missing original moment packed declaration"
  let momentBytes ← quotedPackedCharacters moment.value
  unless momentBytes == (← IO.FS.readBinFile "/workspace/goldbach-research/eighth-third-moment-refinement-20261009-a23-low-00.witness.json") do
    throw <| IO.userError "Embedded original moment bytes mismatch"
  IO.println s!"P26_CELL00_ORIGINAL_BYTES {(Json.mkObj [
    ("geometry_bytes", toJson geometryBytes.size), ("moment_bytes", toJson momentBytes.size),
    ("embedded_original_bytes_match", toJson true)]).compress}"
  (← IO.getStdout).flush

unsafe def main (args : List String) : IO UInt32 := do
  let [manifest] := args | throw <| IO.userError "Expected incoming module list"
  let .ok data := Json.parse (← IO.FS.readFile manifest)
    | throw <| IO.userError "Invalid module-list JSON"
  let .ok entries := data.getArr? | throw <| IO.userError "Expected module array"
  let mut wanted : NameSet := {}
  for entry in entries do
    let .ok name := entry.getStr? | throw <| IO.userError "Expected module name"
    wanted := wanted.insert name.toName
  unless wanted.size == 468 do throw <| IO.userError "Unexpected incoming module count"
  initSearchPath (← findSysroot)
  let baseImports : Array Import := #[
    { module := `ImbalancedChen.P2OriginalSaving19Cell05SourceAttachment }]
  let (_, baseState) ← (importModulesCore baseImports).run
  let base ← finalizeImport baseState baseImports {} 0 false false
  let allImports := baseImports ++ #[
    { module := `ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge },
    { module := `ImbalancedChen.P2OriginalSaving19Cell00AllRowArithmetic }]
  let (_, fullState) ← (importModulesCore allImports).run baseState
  let full ← finalizeImport fullState allImports {} 0 false false
  checkOriginalData full
  let mut newModules : NameSet := {}
  let mut external : Array String := #[]
  for name in full.header.moduleNames do
    if !base.header.moduleNames.contains name then
      newModules := newModules.insert name
      if !(`ImbalancedChen).isPrefixOf name then external := external.push name.toString
  for name in wanted do
    unless newModules.contains name do
      throw <| IO.userError s!"Missing new project module {name}"
  for name in newModules do
    if (`ImbalancedChen).isPrefixOf name && !wanted.contains name then
      throw <| IO.userError s!"Unexpected new project module {name}"
  let constants := full.const2ModIdx.fold (init := ({} : Std.HashMap Name ConstantInfo))
    fun found name idx =>
      if newModules.contains full.header.moduleNames[idx.toNat]! then
        match full.find? name with
        | some ci => found.insert name ci
        | none => found
      else found
  let mut safe : Std.HashMap Name ConstantInfo := {}
  let mut moduleMaps := Array.replicate full.header.moduleNames.size
    ({} : Std.HashMap Name ConstantInfo)
  let mut skippedExternal := 0
  for (name, ci) in constants do
    let some idx := full.getModuleIdxFor? name
      | throw <| IO.userError s!"Missing declaring module for {name}"
    let moduleName := full.header.moduleNames[idx.toNat]!
    if ci.isUnsafe || ci.isPartial then
      if wanted.contains moduleName then
        throw <| IO.userError s!"Unsafe or partial incoming project declaration {name}"
      skippedExternal := skippedExternal + 1
    else
      if ci.isAxiom && !#[`propext, `Classical.choice, `Quot.sound].contains name then
        throw <| IO.userError s!"Forbidden incoming axiom {name}"
      safe := safe.insert name ci
      moduleMaps := moduleMaps.modify idx.toNat (fun found => found.insert name ci)
  IO.println s!"P26_CELL00_JOIN_BEGIN {(Json.mkObj [
    ("project_modules", toJson wanted.size), ("new_external_modules", toJson external),
    ("declarations", toJson safe.size), ("skipped_external_execution_helpers", toJson skippedExternal)]).compress}"
  (← IO.getStdout).flush
  let mut checked := base
  let mut processed : NameSet := {}
  for name in base.header.moduleNames do processed := processed.insert name
  let mut replayed := 0
  let mut modules := 0
  for moduleName in full.header.moduleNames do
    if newModules.contains moduleName then
      let some idx := full.getModuleIdx? moduleName
        | throw <| IO.userError s!"Missing module {moduleName}"
      for dependency in full.header.moduleData[idx.toNat]!.imports do
        unless processed.contains dependency.module do
          throw <| IO.userError s!"Non-topological module order: {moduleName} before {dependency.module}"
      let additions := moduleMaps[idx.toNat]!
      checked ← checked.replay additions
      for (name, _) in additions do
        unless (checked.toKernelEnv.find? name).isSome do
          throw <| IO.userError s!"Missing module kernel declaration {name}"
      replayed := replayed + additions.size
      modules := modules + 1
      processed := processed.insert moduleName
      IO.println s!"P26_CELL00_JOIN_PROGRESS {(Json.mkObj [
        ("module", toJson moduleName.toString), ("completed_modules", toJson modules),
        ("checked_declarations", toJson replayed)]).compress}"
      (← IO.getStdout).flush
  unless replayed == safe.size do throw <| IO.userError "Incomplete replay count"
  for (name, _) in safe do
    unless (checked.toKernelEnv.find? name).isSome do
      throw <| IO.userError s!"Missing replayed declaration {name}"
  IO.println s!"P26_CELL00_JOIN_COMPLETE {(Json.mkObj [
    ("project_modules", toJson wanted.size), ("checked_declarations", toJson safe.size),
    ("new_external_modules", toJson external), ("kernel_replay_succeeded", toJson true),
    ("P2_6_complete", toJson false)]).compress}"
  (← IO.getStdout).flush
  return 0
