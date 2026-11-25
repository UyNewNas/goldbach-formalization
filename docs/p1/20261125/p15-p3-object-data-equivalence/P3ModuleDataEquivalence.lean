import Lean
import Lean.Compiler.ModPkgExt
import Lake.Build.Trace

/-
Standalone IO witness.  Its no-argument usage path reads no project objects and
creates no evidence files.

Reads two existing single-part module objects and the current object's real trace.
All generated files go to a NEW, caller-provided evidence directory.  That directory
must be outside every project source/build/cache tree.  Do not put generated objects
on LEAN_PATH.  A wrapper must bind the captured snapshots to the five SHA256 pins,
the source manifest, the original acceptance receipt, and the runtime fingerprints.

The successful result concerns complete ModuleData after removing one verified
package-assignment extension.  It is not an ABI-equivalence or cache-adoption claim.
-/

open Lean

private def packageExtensionName : Name :=
  Name.str (Name.str (Name.num `_private.Lean.Compiler.ModPkgExt 0) "Lean") "modPkgExt"

private def allowedModules : List String := [
  "ImbalancedChen.Part3OffDiagonalModuli",
  "ImbalancedChen.Part3OriginalDyadicChartPartition",
  "ImbalancedChen.Part3PrimeProductChartTransfer",
  "ImbalancedChen.Part3PrimeProductVonMangoldt",
  "ImbalancedChen.Part3ProperPrimePowerCount"
]

private def ensure (ok : Bool) (message : String) : IO Unit := do
  unless ok do
    throw (IO.userError message)

private def distinctNames (names : Array Name) : Bool := Id.run do
  let mut seen : Array Name := #[]
  for name in names do
    if seen.contains name then
      return false
    seen := seen.push name
  return true

private def withoutPackage (data : ModuleData) : ModuleData :=
  { data with entries := data.entries.filter (fun entry => entry.1 != packageExtensionName) }

private def packageBox (data : ModuleData) : ModuleData :=
  { isModule := false
    imports := #[]
    constNames := #[]
    constants := #[]
    extraConstNames := #[]
    entries := data.entries.filter (fun entry => entry.1 == packageExtensionName) }

private def checkShape (label : String) (data : ModuleData) : IO Unit := do
  ensure (!data.isModule) s!"{label}: multi-part module is outside this witness"
  ensure (data.constNames == data.constants.map ConstantInfo.name)
    s!"{label}: constNames is inconsistent with complete constants"
  ensure (distinctNames data.constNames) s!"{label}: repeated constant name"
  ensure (distinctNames (data.entries.map Prod.fst)) s!"{label}: repeated extension name"
  match (packageBox data).entries.toList with
  | [(_, entries)] =>
      ensure (entries.size == 1) s!"{label}: package extension is not a singleton"
  | _ =>
      throw (IO.userError s!"{label}: expected exactly the pinned package extension")

private def checkNoParts (path : System.FilePath) : IO Unit := do
  for part in ["server", "private"] do
    let partPath := path.addExtension part
    ensure (!(← partPath.pathExists)) s!"unexpected module part: {partPath}"

private def bytesInfo (path : System.FilePath) (bytes : ByteArray) : Json :=
  Json.mkObj [
    ("path", toJson path.toString),
    ("bytes", toJson bytes.size),
    ("lake_hash_actual_bytes", toJson (Lake.Hash.ofByteArray bytes).hex)
  ]

private def saveData (dir : System.FilePath) (stem : String) (mod : Name)
    (data : ModuleData) : IO (ByteArray × Json) := do
  let path := dir / (stem ++ ".olean")
  ensure (!(← path.pathExists)) s!"refusing to replace an evidence file: {path}"
  saveModuleData path mod data
  let bytes ← IO.FS.readBinFile path
  return (bytes, bytesInfo path bytes)

private def parseTrace (raw : ByteArray) : IO Json := do
  let some text := String.fromUTF8? raw
    | throw (IO.userError "trace is not UTF-8")
  IO.ofExcept (Json.parse text)

private def checkTrace (trace : Json) (moduleName currentLakeHash : String) : IO Unit := do
  let schema : String ← IO.ofExcept (trace.getObjValAs? String "schemaVersion")
  ensure (schema == "2025-09-10") "unexpected normal trace schema"
  let synthetic : Bool ← IO.ofExcept (trace.getObjValAs? Bool "synthetic")
  ensure (!synthetic) "synthetic trace is outside this witness"
  let outputs ← IO.ofExcept (trace.getObjVal? "outputs")
  let isModule : Bool ← IO.ofExcept (outputs.getObjValAs? Bool "m")
  let oleans : Array String ← IO.ofExcept (outputs.getObjValAs? (Array String) "o")
  ensure (!isModule) "normal trace advertises multi-part module data"
  ensure (oleans == #[currentLakeHash ++ ".olean"])
    "trace outputs.o does not bind the actual current object bytes"
  let inputs : Array (String × Json) ←
    IO.ofExcept (trace.getObjValAs? (Array (String × Json)) "inputs")
  let packageLabels := inputs.filter (fun entry => entry.1.startsWith "Package.id?:")
  ensure ((packageLabels.map Prod.fst) == #["Package.id?: (some imbalancedChen)"])
    "normal trace package assignment does not match the trusted package template"
  let moduleLabels := inputs.filter (fun entry => entry.1.startsWith "Module.name:")
  ensure ((moduleLabels.map Prod.fst) == #["Module.name: " ++ moduleName])
    "normal trace module name mismatch"
  let argLabels := inputs.filter (fun entry => entry.1.startsWith "Module.leanArgs:")
  ensure ((argLabels.map Prod.fst) == #["Module.leanArgs: #[]"])
    "normal trace module arguments differ from the observed donor context"

private def witness (moduleName : String) (current accepted out : System.FilePath) : IO Json := do
  ensure (allowedModules.contains moduleName) "module is not one of the five reviewed suppliers"
  ensure (!(← out.pathExists)) "evidence directory must not exist"
  checkNoParts current
  checkNoParts accepted
  let mod := moduleName.toName
  let currentBefore ← IO.FS.readBinFile current
  let acceptedBefore ← IO.FS.readBinFile accepted
  let tracePath := current.withExtension "trace"
  let traceBefore ← IO.FS.readBinFile tracePath
  let trace ← parseTrace traceBefore
  checkTrace trace moduleName (Lake.Hash.ofByteArray currentBefore).hex

  -- Parse only captured copies, binding the decoded data to these exact byte arrays.
  IO.FS.createDir out
  let currentSnapshot := out / "input.current.olean"
  let acceptedSnapshot := out / "input.accepted.olean"
  let traceSnapshot := out / "input.current.trace"
  IO.FS.writeBinFile currentSnapshot currentBefore
  IO.FS.writeBinFile acceptedSnapshot acceptedBefore
  IO.FS.writeBinFile traceSnapshot traceBefore
  let currentRead ← readModuleData currentSnapshot
  let acceptedRead ← readModuleData acceptedSnapshot
  let currentData := currentRead.1
  let acceptedData := acceptedRead.1
  checkShape "current" currentData
  checkShape "accepted" acceptedData
  ensure (currentData.imports == acceptedData.imports) "import names or flags differ"
  ensure (currentData.constNames == acceptedData.constNames) "constant name arrays differ"
  ensure (currentData.extraConstNames == acceptedData.extraConstNames)
    "extra constant name arrays differ"
  ensure ((currentData.entries.map Prod.fst) == (acceptedData.entries.map Prod.fst))
    "extension name order or package-entry position differs"

  -- Require byte-exact unmodified round trips before interpreting any normalization.
  let currentRoundtrip ← saveData out "roundtrip.current" mod currentData
  let acceptedRoundtrip ← saveData out "roundtrip.accepted" mod acceptedData
  ensure (currentRoundtrip.1 == currentBefore) "current unmodified round trip differs"
  ensure (acceptedRoundtrip.1 == acceptedBefore) "accepted unmodified round trip differs"

  -- Produce opaque extension payloads through the stock typed setter.  No cast or
  -- import of a project module is needed to check their exact serialized values.
  let empty ← mkEmptyEnvironment
  let noneTemplate ← mkModuleData (Environment.setModulePackage none empty)
  let someTemplate ← mkModuleData (Environment.setModulePackage (some "imbalancedChen") empty)
  checkShape "none template" noneTemplate
  checkShape "some template" someTemplate
  let templateNoneNorm ← saveData out "template.none.nonpackage" mod (withoutPackage noneTemplate)
  let templateSomeNorm ← saveData out "template.some.nonpackage" mod (withoutPackage someTemplate)
  ensure (templateNoneNorm.1 == templateSomeNorm.1)
    "trusted package setter changed data beyond the pinned package extension"
  let expectedNone ← saveData out "package.expected-none" mod (packageBox noneTemplate)
  let expectedSome ← saveData out "package.expected-some" mod (packageBox someTemplate)
  let actualCurrent ← saveData out "package.current" mod (packageBox currentData)
  let actualAccepted ← saveData out "package.accepted" mod (packageBox acceptedData)
  ensure (actualCurrent.1 == expectedSome.1)
    "current package payload is not exactly the typed some imbalancedChen template"
  ensure (actualAccepted.1 == expectedNone.1)
    "accepted package payload is not exactly the typed none template"
  ensure (expectedSome.1 != expectedNone.1) "distinct package templates serialized identically"

  -- This record update preserves every other ModuleData field and all other
  -- extension entries in their original order, including the complete constants.
  let currentNorm ← saveData out "normalized.current" mod (withoutPackage currentData)
  let acceptedNorm ← saveData out "normalized.accepted" mod (withoutPackage acceptedData)
  ensure (currentNorm.1 == acceptedNorm.1)
    "complete ModuleData differs outside the verified package extension"

  ensure ((← IO.FS.readBinFile current) == currentBefore) "current object changed during witness"
  ensure ((← IO.FS.readBinFile accepted) == acceptedBefore) "accepted object changed during witness"
  ensure ((← IO.FS.readBinFile tracePath) == traceBefore) "current trace changed during witness"
  ensure ((← IO.FS.readBinFile currentSnapshot) == currentBefore) "current snapshot changed"
  ensure ((← IO.FS.readBinFile acceptedSnapshot) == acceptedBefore) "accepted snapshot changed"
  checkNoParts current
  checkNoParts accepted

  return Json.mkObj [
    ("schema", toJson "p3_moduledata_package_equivalence_candidate_v1"),
    ("status", toJson "DATA_EQUAL_MODULO_VERIFIED_PACKAGE__EXTERNAL_PINS_REQUIRED"),
    ("module", toJson moduleName),
    ("package_extension", toJson packageExtensionName.toString),
    ("current_package", toJson "some imbalancedChen"),
    ("accepted_package", toJson "none"),
    ("input_current", bytesInfo current currentBefore),
    ("input_accepted", bytesInfo accepted acceptedBefore),
    ("input_trace", bytesInfo tracePath traceBefore),
    ("snapshot_current", bytesInfo currentSnapshot currentBefore),
    ("snapshot_accepted", bytesInfo acceptedSnapshot acceptedBefore),
    ("snapshot_trace", bytesInfo traceSnapshot traceBefore),
    ("original_byte_roundtrips_equal", toJson true),
    ("all_moduledata_except_verified_package_byte_equal", toJson true),
    ("trace_output_matches_direct_current_lake_hash", toJson true),
    ("isModule", toJson currentData.isModule),
    ("imports", toJson currentData.imports),
    ("constant_count", toJson currentData.constants.size),
    ("constant_names", toJson (currentData.constNames.map Name.toString)),
    ("extra_constant_names", toJson (currentData.extraConstNames.map Name.toString)),
    ("extension_names", toJson (currentData.entries.map (fun entry => entry.1.toString))),
    ("loaded_current_region_bytes", toJson currentRead.2.size.toNat),
    ("loaded_accepted_region_bytes", toJson acceptedRead.2.size.toNat),
    ("artifacts", toJson #[currentRoundtrip.2, acceptedRoundtrip.2,
      templateNoneNorm.2, templateSomeNorm.2, expectedNone.2, expectedSome.2,
      actualCurrent.2, actualAccepted.2, currentNorm.2, acceptedNorm.2]),
    ("scope_limit", toJson "No imported-object byte identity, native ABI equivalence, proof replay, owner acceptance, or cache adoption is inferred.")
  ]

def main (args : List String) : IO UInt32 := do
  match args with
  | [moduleName, current, accepted, out] =>
      let result ← witness moduleName current accepted out
      IO.FS.writeFile (System.FilePath.mk out / "candidate.json") (result.pretty ++ "\n")
      IO.println result.compress
      return 0
  | _ =>
      IO.eprintln "usage: P3ModuleDataEquivalence.lean MODULE CURRENT_OLEAN ACCEPTED_OLEAN NEW_EVIDENCE_DIR"
      return 2
