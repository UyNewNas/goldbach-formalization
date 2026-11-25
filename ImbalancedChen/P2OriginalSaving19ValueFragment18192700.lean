import ImbalancedChen.P2OriginalSaving19SourceJson

/-! Self-delimiting original value fragment, raw candidate span [181927,183580). This owner is independent of geometryChars00; its arbitrary-tail theorem can be reused after a separately proved byte binding.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def fragment181927Acc00000 : List (String × SourceJson) := []

noncomputable def fragment181927Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment181927Field000Value00 : SourceJson := .number (String.ofList ['4', '8'])
noncomputable def fragment181927Acc00100 : List (String × SourceJson) := (fragment181927Field000Key00, fragment181927Field000Value00) :: fragment181927Acc00000
noncomputable def fragment181927Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '8', ',']

theorem object_fragment181927_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 267) (SourceJson.white (fragment181927Field000Chars00 ++ tail)) fragment181927Acc00000 =
      SourceJson.object (fuel + 266) (SourceJson.white tail) fragment181927Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_000"
  err.flush

noncomputable def fragment181927Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment181927Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment181927Acc00200 : List (String × SourceJson) := (fragment181927Field001Key00, fragment181927Field001Value00) :: fragment181927Acc00100
noncomputable def fragment181927Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment181927_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment181927Field001Chars00 ++ tail)) fragment181927Acc00100 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment181927Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_001"
  err.flush

noncomputable def fragment181927Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment181927Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '2', '7', '0', '2', '8', '0', '4', '6', '1', '6', '1', '4', '7', '2', '8', '2', '6', '7', '1', '8', '5', '8', '0', '8', '5', '6', '1', '7', '5', '6', '6', '8', '1', '7', '8', '1', '5', '5', '1', '/', '3', '0', '7', '1', '5', '5', '6', '8', '5', '5', '0', '0', '5', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment181927Acc00300 : List (String × SourceJson) := (fragment181927Field002Key00, fragment181927Field002Value00) :: fragment181927Acc00200
noncomputable def fragment181927Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '2', '7', '0', '2', '8', '0', '4', '6', '1', '6', '1', '4', '7', '2', '8', '2', '6', '7', '1', '8', '5', '8', '0', '8', '5', '6', '1', '7', '5', '6', '6', '8', '1', '7', '8', '1', '5', '5', '1', '/', '3', '0', '7', '1', '5', '5', '6', '8', '5', '5', '0', '0', '5', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment181927_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment181927Field002Chars00 ++ tail)) fragment181927Acc00200 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment181927Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_002"
  err.flush

noncomputable def fragment181927Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment181927Field003Value00 : SourceJson := .str (String.ofList ['5', '4', '6', '7', '4', '3', '/', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment181927Acc00400 : List (String × SourceJson) := (fragment181927Field003Key00, fragment181927Field003Value00) :: fragment181927Acc00300
noncomputable def fragment181927Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '4', '6', '7', '4', '3', '/', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment181927_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment181927Field003Chars00 ++ tail)) fragment181927Acc00300 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment181927Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_003"
  err.flush

noncomputable def fragment181927Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment181927Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '0', '6', '2', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '6', '6', '/', '6', '0', '9', '3', '7', '5']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment181927Acc00500 : List (String × SourceJson) := (fragment181927Field004Key00, fragment181927Field004Value00) :: fragment181927Acc00400
noncomputable def fragment181927Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '0', '6', '2', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '9', '2', '5', '9', '/', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '6', '6', '/', '6', '0', '9', '3', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment181927_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment181927Field004Chars00 ++ tail)) fragment181927Acc00400 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment181927Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_004"
  err.flush

noncomputable def fragment181927Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment181927Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '3', '6', '1', '8', '1', '7', '5', '2', '2', '0', '0', '8', '1', '/', '3', '4', '4', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '8', '6', '5', '9', '4', '8', '2', '1', '2', '8', '2', '1', '/', '3', '4', '4', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '7', '8', '7', '1', '3', '5', '8', '2', '0', '1', '0', '1', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '2', '2', '3', '6', '2', '8', '9', '1', '0', '0', '9', '/', '8', '6', '1', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '6', '8', '4', '7', '1', '8', '8', '7', '6', '3', '1', '9', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '1', '9', '0', '5', '6', '3', '7', '5', '9', '7', '3', '9', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '7', '7', '5', '0', '0', '7', '8', '3', '0', '0', '2', '1', '/', '5', '1', '6', '6', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '2', '3', '1', '8', '1', '3', '1', '9', '2', '0', '9', '1', '/', '5', '1', '6', '6', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '8', '0', '7', '6', '2', '3', '3', '5', '1', '9', '5', '3', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '8', '0', '7', '4', '8', '5', '5', '8', '5', '2', '3', '3', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment181927Acc00600 : List (String × SourceJson) := (fragment181927Field005Key00, fragment181927Field005Value00) :: fragment181927Acc00500
noncomputable def fragment181927Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '1', '8', '1', '7', '5', '2', '2', '0', '0', '8', '1', '/', '3', '4', '4', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '8', '6', '5', '9', '4', '8', '2', '1', '2', '8', '2', '1', '/', '3', '4', '4', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '7', '8', '7', '1', '3', '5', '8', '2', '0', '1', '0', '1', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '2', '2', '3', '6', '2', '8', '9', '1', '0', '0', '9', '/', '8', '6', '1', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '6', '8', '4', '7', '1', '8', '8', '7', '6', '3', '1', '9', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '1', '9', '0', '5', '6', '3', '7', '5', '9', '7', '3', '9', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '7', '5', '0', '0', '7', '8', '3', '0', '0', '2', '1', '/', '5', '1', '6', '6', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '2', '3', '1', '8', '1', '3', '1', '9', '2', '0', '9', '1', '/', '5', '1', '6', '6', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '8', '0', '7', '6', '2', '3', '3', '5', '1', '9', '5', '3', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '8', '0', '7', '4', '8', '5', '5', '8', '5', '2', '3', '3', '/', '1', '0', '3', '3', '2', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment181927_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment181927Field005Chars00 ++ tail)) fragment181927Acc00500 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment181927Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_005"
  err.flush

noncomputable def fragment181927Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment181927Field006Value00 : SourceJson := .str (String.ofList ['2', '1', '4', '4', '7', '6', '4', '8', '0', '7', '9', '8', '0', '2', '5', '1', '2', '5', '1', '6', '4', '2', '8', '1', '2', '2', '3', '4', '5', '1', '7', '0', '4', '9', '5', '8', '9', '1', '4', '8', '3', '8', '5', '5', '0', '4', '6', '8', '7', '5', '/', '8', '8', '8', '2', '6', '6', '1', '3', '1', '7', '1', '8', '3', '3', '9', '8', '7', '2', '0', '6', '7', '8', '2', '1', '7', '1', '5', '6', '0', '3', '3', '4', '2', '5', '4', '5', '4', '9', '3', '5', '2', '7', '1', '1', '3', '9', '5', '1', '5', '5', '5', '0', '3', '1', '3', '4', '3', '2', '6', '8', '8', '6', '5', '5', '3', '6'])
noncomputable def fragment181927Acc00700 : List (String × SourceJson) := (fragment181927Field006Key00, fragment181927Field006Value00) :: fragment181927Acc00600
noncomputable def fragment181927Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '4', '4', '7', '6', '4', '8', '0', '7', '9', '8', '0', '2', '5', '1', '2', '5', '1', '6', '4', '2', '8', '1', '2', '2', '3', '4', '5', '1', '7', '0', '4', '9', '5', '8', '9', '1', '4', '8', '3', '8', '5', '5', '0', '4', '6', '8', '7', '5', '/', '8', '8', '8', '2', '6', '6', '1', '3', '1', '7', '1', '8', '3', '3', '9', '8', '7', '2', '0', '6', '7', '8', '2', '1', '7', '1', '5', '6', '0', '3', '3', '4', '2', '5', '4', '5', '4', '9', '3', '5', '2', '7', '1', '1', '3', '9', '5', '1', '5', '5', '5', '0', '3', '1', '3', '4', '3', '2', '6', '8', '8', '6', '5', '5', '3', '6', '"', ',']

theorem object_fragment181927_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment181927Field006Chars00 ++ tail)) fragment181927Acc00600 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment181927Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_006"
  err.flush

noncomputable def fragment181927Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment181927Field007Value00 : SourceJson := .str (String.ofList ['2', '2', '1', '7', '4', '3', '4', '2', '0', '4', '6', '1', '5', '0', '7', '2', '7', '1', '4', '1', '1', '4', '1', '7', '3', '1', '4', '9', '9', '8', '1', '7', '4', '8', '7', '1', '6', '2', '2', '3', '7', '1', '2', '6', '6', '4', '5', '8', '7', '1', '6', '6', '8', '4', '3', '3', '9', '1', '2', '0', '6', '0', '3', '1', '1', '5', '3', '8', '3', '4', '8', '4', '1', '3', '3', '7', '7', '2', '8', '2', '0', '9', '8', '5', '6', '3', '7', '1', '2', '6', '3', '3', '5', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '7', '2', '4', '6', '3', '5', '7', '9', '1', '4', '8', '7', '3', '6', '6', '4', '5', '8', '4', '4', '3', '7', '2', '3', '8', '2', '0', '7', '1', '5', '0', '3', '5', '0', '6', '3', '3', '9', '9', '8', '7', '3', '5', '4', '8', '5', '0', '0', '4', '8', '4', '4', '2', '8', '2', '2', '7', '0', '7', '6', '7', '9', '2', '1', '4', '1', '1', '5', '7', '0', '2', '5', '5', '2', '4', '6', '7', '1', '1', '1', '0', '0', '6', '7', '1', '5', '9', '7', '0', '1', '0', '7', '6', '7', '0', '7', '0', '4', '2', '1', '7', '2', '8', '6', '4', '1', '2', '4', '5', '4', '2', '6', '5', '9', '5', '3', '9', '9', '2', '4', '9', '6', '7', '7', '3', '9', '1', '6', '4', '7', '6', '2', '0', '9', '1'])
noncomputable def fragment181927Acc00800 : List (String × SourceJson) := (fragment181927Field007Key00, fragment181927Field007Value00) :: fragment181927Acc00700
noncomputable def fragment181927Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '1', '7', '4', '3', '4', '2', '0', '4', '6', '1', '5', '0', '7', '2', '7', '1', '4', '1', '1', '4', '1', '7', '3', '1', '4', '9', '9', '8', '1', '7', '4', '8', '7', '1', '6', '2', '2', '3', '7', '1', '2', '6', '6', '4', '5', '8', '7', '1', '6', '6', '8', '4', '3', '3', '9', '1', '2', '0', '6', '0', '3', '1', '1', '5', '3', '8', '3', '4', '8', '4', '1', '3', '3', '7', '7', '2', '8', '2', '0', '9', '8', '5', '6', '3', '7', '1', '2', '6', '3', '3', '5', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '7', '2', '4', '6', '3', '5', '7', '9', '1', '4', '8', '7', '3', '6', '6', '4', '5', '8', '4', '4', '3', '7', '2', '3', '8', '2', '0', '7', '1', '5', '0', '3', '5', '0', '6', '3', '3', '9', '9', '8', '7', '3', '5', '4', '8', '5', '0', '0', '4', '8', '4', '4', '2', '8', '2', '2', '7', '0', '7', '6', '7', '9', '2', '1', '4', '1', '1', '5', '7', '0', '2', '5', '5', '2', '4', '6', '7', '1', '1', '1', '0', '0', '6', '7', '1', '5', '9', '7', '0', '1', '0', '7', '6', '7', '0', '7', '0', '4', '2', '1', '7', '2', '8', '6', '4', '1', '2', '4', '5', '4', '2', '6', '5', '9', '5', '3', '9', '9', '2', '4', '9', '6', '7', '7', '3', '9', '1', '6', '4', '7', '6', '2', '0', '9', '1', '"', ',']

theorem object_fragment181927_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment181927Field007Chars00 ++ tail)) fragment181927Acc00700 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment181927Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_007"
  err.flush

noncomputable def fragment181927Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment181927Field008Value00 : SourceJson := .str (String.ofList ['1', '9', '1', '3', '0', '0', '5', '2', '2', '1', '0', '0', '0'])
noncomputable def fragment181927Acc00900 : List (String × SourceJson) := (fragment181927Field008Key00, fragment181927Field008Value00) :: fragment181927Acc00800
noncomputable def fragment181927Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '1', '3', '0', '0', '5', '2', '2', '1', '0', '0', '0', '"', ',']

theorem object_fragment181927_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment181927Field008Chars00 ++ tail)) fragment181927Acc00800 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment181927Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_008"
  err.flush

noncomputable def fragment181927Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment181927Field009Value00 : SourceJson := .str (String.ofList ['6', '4', '4', '7', '9', '5', '3', '0', '8', '3', '3', '7', '4'])
noncomputable def fragment181927Acc01000 : List (String × SourceJson) := (fragment181927Field009Key00, fragment181927Field009Value00) :: fragment181927Acc00900
noncomputable def fragment181927Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '4', '4', '7', '9', '5', '3', '0', '8', '3', '3', '7', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment181927_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment181927Field009Chars00 ++ tail)) fragment181927Acc00900 =
      .ok (.obj (fragment181927Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_object_field_009"
  err.flush

noncomputable def fragment181927Chars00 : List Char := '{' :: (fragment181927Field000Chars00 ++ fragment181927Field001Chars00 ++ fragment181927Field002Chars00 ++ fragment181927Field003Chars00 ++ fragment181927Field004Chars00 ++ fragment181927Field005Chars00 ++ fragment181927Field006Chars00 ++ fragment181927Field007Chars00 ++ fragment181927Field008Chars00 ++ fragment181927Field009Chars00)
noncomputable def fragment181927Value00 : SourceJson := .obj (fragment181927Acc01000.reverse)

theorem value_fragment181927 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 268) (fragment181927Chars00 ++ tail) =
      .ok (fragment181927Value00, tail) := by
  have hinput : fragment181927Chars00 ++ tail = '{' :: (fragment181927Field000Chars00 ++ (fragment181927Field001Chars00 ++ (fragment181927Field002Chars00 ++ (fragment181927Field003Chars00 ++ (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment181927Chars00, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 268) (fragment181927Chars00 ++ tail) =
        SourceJson.value (fuel + 268) ('{' :: (fragment181927Field000Chars00 ++ (fragment181927Field001Chars00 ++ (fragment181927Field002Chars00 ++ (fragment181927Field003Chars00 ++ (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 268)) hinput
    _ = SourceJson.object (fuel + 267) (SourceJson.white (fragment181927Field000Chars00 ++ (fragment181927Field001Chars00 ++ (fragment181927Field002Chars00 ++ (fragment181927Field003Chars00 ++ (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))))))))))) fragment181927Acc00000 := by rfl
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment181927Field001Chars00 ++ (fragment181927Field002Chars00 ++ (fragment181927Field003Chars00 ++ (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail))))))))))) fragment181927Acc00100 := object_fragment181927_field_000 fuel (fragment181927Field001Chars00 ++ (fragment181927Field002Chars00 ++ (fragment181927Field003Chars00 ++ (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment181927Field002Chars00 ++ (fragment181927Field003Chars00 ++ (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))))))))) fragment181927Acc00200 := object_fragment181927_field_001 fuel (fragment181927Field002Chars00 ++ (fragment181927Field003Chars00 ++ (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment181927Field003Chars00 ++ (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail))))))))) fragment181927Acc00300 := object_fragment181927_field_002 fuel (fragment181927Field003Chars00 ++ (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))))))) fragment181927Acc00400 := object_fragment181927_field_003 fuel (fragment181927Field004Chars00 ++ (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail))))))) fragment181927Acc00500 := object_fragment181927_field_004 fuel (fragment181927Field005Chars00 ++ (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))))) fragment181927Acc00600 := object_fragment181927_field_005 fuel (fragment181927Field006Chars00 ++ (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail))))) fragment181927Acc00700 := object_fragment181927_field_006 fuel (fragment181927Field007Chars00 ++ (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))) fragment181927Acc00800 := object_fragment181927_field_007 fuel (fragment181927Field008Chars00 ++ (fragment181927Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment181927Field009Chars00 ++ (tail))) fragment181927Acc00900 := object_fragment181927_field_008 fuel (fragment181927Field009Chars00 ++ (tail))
    _ = .ok (fragment181927Value00, tail) := object_fragment181927_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 fragment181927_value_complete"
  err.flush

#print axioms object_fragment181927_field_000
#print axioms object_fragment181927_field_001
#print axioms object_fragment181927_field_002
#print axioms object_fragment181927_field_003
#print axioms object_fragment181927_field_004
#print axioms object_fragment181927_field_005
#print axioms object_fragment181927_field_006
#print axioms object_fragment181927_field_007
#print axioms object_fragment181927_field_008
#print axioms object_fragment181927_field_009
#print axioms value_fragment181927

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
