import Lean
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData00
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData01
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData02
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData03
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData04
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData06
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData07
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData08
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData09
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData10
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData11
import ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData00
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData01
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData02
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData03
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData04
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData05
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData06
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData07
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData08
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData09
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData10
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData11
import ImbalancedChen.P2OriginalSaving19ArchiveMomentData12

/- Read-only serialized Expr inspection. No theorem, proof replay, evaluator
   admission or concrete JSON/shape assertion is added by this IO program. -/
open Lean

private def naturalLiteral (e : Expr) : IO Nat := do
  let e := e.consumeMData
  match e with
  | .lit (.natVal n) => return n
  | _ =>
    let args := e.getAppArgs
    if e.getAppFn.isConstOf ``OfNat.ofNat && args.size == 3 &&
        args[0]!.isConstOf ``Nat then
      match args[1]!.consumeMData with
      | .lit (.natVal n) => return n
      | _ => pure ()
    let head := match e.getAppFn with
      | .const name _ => name.toString
      | _ => "nonconstant"
    throw <| IO.userError ("unrecognized quoted Nat head=" ++ head ++
      " arity=" ++ toString args.size)

private partial def writeTree (e : Expr) (out : IO.FS.Handle) : IO (Nat × Nat) := do
  let e := e.consumeMData
  let args := e.getAppArgs
  match e.getAppFn with
  | .const name _ =>
    if name == `ImbalancedChen.P2OriginalSaving19PackedChars.Tree.empty then
      unless args.isEmpty do throw <| IO.userError "empty constructor has arguments"
      return (0, 0)
    else if name == `ImbalancedChen.P2OriginalSaving19PackedChars.Tree.branch then
      unless args.size == 2 do throw <| IO.userError "branch arity mismatch"
      let (nl, ll) ← writeTree args[0]! out
      let (nr, lr) ← writeTree args[1]! out
      return (nl + nr, ll + lr)
    else if name == `ImbalancedChen.P2OriginalSaving19PackedChars.Tree.leaf then
      unless args.size == 2 do throw <| IO.userError "leaf arity mismatch"
      let count ← naturalLiteral args[0]!
      let mut word ← naturalLiteral args[1]!
      if 256 < count then throw <| IO.userError "quoted leaf exceeds original blockLimit"
      let mut chars : List Char := []
      for _ in [:count] do
        let code := word % 4294967296
        if 0x10ffff < code ∨ (0xd800 ≤ code ∧ code ≤ 0xdfff) then
          throw <| IO.userError "invalid original Unicode scalar"
        chars := Char.ofNat code :: chars
        word := word / 4294967296
      unless word == 0 do throw <| IO.userError "packed word has unaccounted high digits"
      out.putStr (String.ofList chars.reverse)
      return (count, 1)
    else throw <| IO.userError ("unexpected quoted constructor: " ++ name.toString)
  | _ => throw <| IO.userError "quoted tree head is not a constructor constant"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let outputDir : System.FilePath :=
    "/workspace/p1-complete-proof/20261128-p15-saving19-quoted-input-readback/readback-00003/decoded"
  liftIO <| IO.FS.createDirAll outputDir
  for kind in ["Geometry", "Moment"] do
    for i in [:13] do
      let suffix := (if i < 10 then "0" else "") ++ toString i
      let modName := Name.str `ImbalancedChen ("P2OriginalSaving19Archive" ++ kind ++ "Data" ++ suffix)
      let constName := Name.str `ImbalancedChen.P2OriginalSaving19Archive
        ((if kind == "Geometry" then "geometry" else "moment") ++ "Packed" ++ suffix)
      let some info := env.find? constName
        | throwError "Missing quoted definition {constName}"
      let some value := info.value?
        | throwError "Quoted input is not a definition {constName}"
      let path := outputDir / (kind ++ suffix ++ ".json")
      let (count, leaves) ← liftIO do
        let out ← IO.FS.Handle.mk path IO.FS.Mode.write
        let counts ← writeTree value out
        out.flush
        return counts
      liftIO <| IO.println <| (Json.mkObj [("module", toJson modName.toString),
        ("constant", toJson constName.toString), ("characters", toJson count),
        ("leaves", toJson leaves), ("output", toJson path.toString)]).compress
