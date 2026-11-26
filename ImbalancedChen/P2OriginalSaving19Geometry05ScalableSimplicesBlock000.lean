import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock000

noncomputable def fragment0104503Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0104503Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0104503Field000Value00 : SourceJson := .number (String.ofList ['0'])
noncomputable def fragment0104503Acc00100 : List (String × SourceJson) := (fragment0104503Field000Key00, fragment0104503Field000Value00) :: fragment0104503Acc00000
noncomputable def fragment0104503Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '0', ',']

theorem object_fragment0104503_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0104503Field000Chars00 ++ tail)) fragment0104503Acc00000 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0104503Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_000"
  err.flush

noncomputable def fragment0104503Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0104503Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0104503Acc00200 : List (String × SourceJson) := (fragment0104503Field001Key00, fragment0104503Field001Value00) :: fragment0104503Acc00100
noncomputable def fragment0104503Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0104503_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0104503Field001Chars00 ++ tail)) fragment0104503Acc00100 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0104503Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_001"
  err.flush

noncomputable def fragment0104503Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0104503Field002Value00 : SourceJson := .str (String.ofList ['9', '0', '8', '8', '3', '4', '6', '1', '0', '4', '6', '8', '7', '8', '8', '3', '4', '3', '7', '4', '9', '5', '7', '8', '2', '5', '5', '3', '9', '6', '3', '9', '6', '9', '0', '2', '0', '1', '3', '/', '3', '5', '0', '5', '7', '7', '3', '5', '4', '5', '8', '3', '5', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0104503Acc00300 : List (String × SourceJson) := (fragment0104503Field002Key00, fragment0104503Field002Value00) :: fragment0104503Acc00200
noncomputable def fragment0104503Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '0', '8', '8', '3', '4', '6', '1', '0', '4', '6', '8', '7', '8', '8', '3', '4', '3', '7', '4', '9', '5', '7', '8', '2', '5', '5', '3', '9', '6', '3', '9', '6', '9', '0', '2', '0', '1', '3', '/', '3', '5', '0', '5', '7', '7', '3', '5', '4', '5', '8', '3', '5', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0104503_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0104503Field002Chars00 ++ tail)) fragment0104503Acc00200 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0104503Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_002"
  err.flush

noncomputable def fragment0104503Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0104503Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0104503Acc00400 : List (String × SourceJson) := (fragment0104503Field003Key00, fragment0104503Field003Value00) :: fragment0104503Acc00300
noncomputable def fragment0104503Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0104503_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0104503Field003Chars00 ++ tail)) fragment0104503Acc00300 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0104503Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_003"
  err.flush

noncomputable def fragment0104503Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0104503Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0104503Acc00500 : List (String × SourceJson) := (fragment0104503Field004Key00, fragment0104503Field004Value00) :: fragment0104503Acc00400
noncomputable def fragment0104503Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0104503_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0104503Field004Chars00 ++ tail)) fragment0104503Acc00400 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0104503Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_004"
  err.flush

noncomputable def fragment0104503Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0104503Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '6', '8', '3', '3', '7', '7', '0', '9', '7', '3', '7', '1', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '3', '7', '9', '9', '9', '1', '0', '3', '9', '0', '1', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '2', '8', '8', '5', '4', '2', '3', '4', '3', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '2', '4', '6', '0', '8', '8', '3', '8', '4', '4', '4', '3', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '2', '2', '7', '4', '2', '1', '8', '0', '6', '1', '8', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '5', '7', '3', '0', '2', '9', '7', '7', '9', '7', '/', '9', '0', '5', '9', '2', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '1', '4', '6', '6', '5', '9', '7', '2', '6', '9', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '2', '7', '7', '1', '4', '3', '8', '3', '6', '7', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '1', '9', '0', '8', '5', '3', '8', '9', '2', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '4', '7', '5', '3', '1', '3', '5', '6', '9', '3', '1', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0104503Acc00600 : List (String × SourceJson) := (fragment0104503Field005Key00, fragment0104503Field005Value00) :: fragment0104503Acc00500
noncomputable def fragment0104503Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '8', '3', '3', '7', '7', '0', '9', '7', '3', '7', '1', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '3', '7', '9', '9', '9', '1', '0', '3', '9', '0', '1', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '2', '8', '8', '5', '4', '2', '3', '4', '3', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '2', '4', '6', '0', '8', '8', '3', '8', '4', '4', '4', '3', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '2', '2', '7', '4', '2', '1', '8', '0', '6', '1', '8', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '5', '7', '3', '0', '2', '9', '7', '7', '9', '7', '/', '9', '0', '5', '9', '2', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '1', '4', '6', '6', '5', '9', '7', '2', '6', '9', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '2', '7', '7', '1', '4', '3', '8', '3', '6', '7', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '1', '9', '0', '8', '5', '3', '8', '9', '2', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '4', '7', '5', '3', '1', '3', '5', '6', '9', '3', '1', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0104503_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0104503Field005Chars00 ++ tail)) fragment0104503Acc00500 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0104503Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_005"
  err.flush

noncomputable def fragment0104503Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0104503Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '2', '4', '7', '0', '7', '2', '6', '4', '1', '2', '9', '4', '7', '4', '7', '2', '5', '8', '4', '0', '6', '8', '5', '8', '0', '4', '1', '5', '9', '8', '2', '4', '2', '5', '2', '6', '9', '3', '4', '7', '8', '9', '0', '6', '2', '5', '0', '/', '2', '2', '8', '3', '3', '4', '2', '0', '3', '4', '6', '2', '3', '8', '2', '6', '9', '0', '8', '5', '7', '1', '1', '5', '7', '5', '3', '3', '6', '7', '2', '1', '0', '7', '4', '4', '4', '8', '8', '7', '9', '1', '9', '8', '8', '7', '5', '4', '7', '1', '4', '3', '4', '3', '9', '3', '7', '5', '4', '4', '9', '7', '4', '4', '0', '7'])
noncomputable def fragment0104503Acc00700 : List (String × SourceJson) := (fragment0104503Field006Key00, fragment0104503Field006Value00) :: fragment0104503Acc00600
noncomputable def fragment0104503Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '2', '4', '7', '0', '7', '2', '6', '4', '1', '2', '9', '4', '7', '4', '7', '2', '5', '8', '4', '0', '6', '8', '5', '8', '0', '4', '1', '5', '9', '8', '2', '4', '2', '5', '2', '6', '9', '3', '4', '7', '8', '9', '0', '6', '2', '5', '0', '/', '2', '2', '8', '3', '3', '4', '2', '0', '3', '4', '6', '2', '3', '8', '2', '6', '9', '0', '8', '5', '7', '1', '1', '5', '7', '5', '3', '3', '6', '7', '2', '1', '0', '7', '4', '4', '4', '8', '8', '7', '9', '1', '9', '8', '8', '7', '5', '4', '7', '1', '4', '3', '4', '3', '9', '3', '7', '5', '4', '4', '9', '7', '4', '4', '0', '7', '"', ',']

theorem object_fragment0104503_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0104503Field006Chars00 ++ tail)) fragment0104503Acc00600 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0104503Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_006"
  err.flush

noncomputable def fragment0104503Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0104503Field007Value00 : SourceJson := .str (String.ofList ['3', '0', '2', '7', '2', '6', '0', '0', '9', '1', '0', '7', '0', '4', '8', '4', '1', '2', '8', '2', '4', '1', '6', '1', '9', '3', '5', '6', '5', '2', '5', '9', '7', '1', '4', '2', '8', '0', '6', '1', '9', '8', '2', '2', '1', '5', '5', '9', '4', '9', '3', '2', '4', '5', '7', '4', '5', '5', '2', '1', '8', '5', '6', '3', '0', '4', '0', '9', '2', '6', '6', '3', '1', '5', '7', '1', '5', '7', '7', '8', '8', '8', '4', '1', '7', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '4', '2', '4', '2', '3', '4', '4', '5', '4', '4', '2', '6', '6', '7', '3', '9', '3', '3', '9', '1', '3', '7', '3', '9', '6', '0', '5', '7', '8', '5', '6', '0', '6', '7', '9', '4', '7', '3', '8', '9', '6', '3', '0', '4', '5', '5', '8', '1', '6', '1', '8', '9', '2', '8', '3', '2', '0', '3', '2', '8', '9', '8', '6', '4', '9', '4', '0', '7', '5', '6', '9', '7', '1', '0', '6', '4', '2', '2', '5', '0', '1', '7', '4', '3', '1', '3', '8', '4', '1', '7', '0', '4', '3', '0', '1', '3', '9', '1', '4', '9', '1', '2', '7', '0', '8', '7', '4', '8', '4', '2', '1', '9', '0', '4', '4', '2', '3', '6', '6', '4', '9', '1', '0', '4', '2', '5', '7'])
noncomputable def fragment0104503Acc00800 : List (String × SourceJson) := (fragment0104503Field007Key00, fragment0104503Field007Value00) :: fragment0104503Acc00700
noncomputable def fragment0104503Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '2', '7', '2', '6', '0', '0', '9', '1', '0', '7', '0', '4', '8', '4', '1', '2', '8', '2', '4', '1', '6', '1', '9', '3', '5', '6', '5', '2', '5', '9', '7', '1', '4', '2', '8', '0', '6', '1', '9', '8', '2', '2', '1', '5', '5', '9', '4', '9', '3', '2', '4', '5', '7', '4', '5', '5', '2', '1', '8', '5', '6', '3', '0', '4', '0', '9', '2', '6', '6', '3', '1', '5', '7', '1', '5', '7', '7', '8', '8', '8', '4', '1', '7', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '4', '2', '4', '2', '3', '4', '4', '5', '4', '4', '2', '6', '6', '7', '3', '9', '3', '3', '9', '1', '3', '7', '3', '9', '6', '0', '5', '7', '8', '5', '6', '0', '6', '7', '9', '4', '7', '3', '8', '9', '6', '3', '0', '4', '5', '5', '8', '1', '6', '1', '8', '9', '2', '8', '3', '2', '0', '3', '2', '8', '9', '8', '6', '4', '9', '4', '0', '7', '5', '6', '9', '7', '1', '0', '6', '4', '2', '2', '5', '0', '1', '7', '4', '3', '1', '3', '8', '4', '1', '7', '0', '4', '3', '0', '1', '3', '9', '1', '4', '9', '1', '2', '7', '0', '8', '7', '4', '8', '4', '2', '1', '9', '0', '4', '4', '2', '3', '6', '6', '4', '9', '1', '0', '4', '2', '5', '7', '"', ',']

theorem object_fragment0104503_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0104503Field007Chars00 ++ tail)) fragment0104503Acc00700 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0104503Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_007"
  err.flush

noncomputable def fragment0104503Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0104503Field008Value00 : SourceJson := .str (String.ofList ['6', '6', '7', '8', '4', '1', '3', '3', '7', '8', '3', '9'])
noncomputable def fragment0104503Acc00900 : List (String × SourceJson) := (fragment0104503Field008Key00, fragment0104503Field008Value00) :: fragment0104503Acc00800
noncomputable def fragment0104503Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '7', '8', '4', '1', '3', '3', '7', '8', '3', '9', '"', ',']

theorem object_fragment0104503_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0104503Field008Chars00 ++ tail)) fragment0104503Acc00800 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0104503Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_008"
  err.flush

noncomputable def fragment0104503Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0104503Field009Value00 : SourceJson := .str (String.ofList ['2', '5', '4', '4', '9', '7', '3', '3', '4', '1', '1', '0', '3'])
noncomputable def fragment0104503Acc01000 : List (String × SourceJson) := (fragment0104503Field009Key00, fragment0104503Field009Value00) :: fragment0104503Acc00900
noncomputable def fragment0104503Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '4', '4', '9', '7', '3', '3', '4', '1', '1', '0', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0104503_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0104503Field009Chars00 ++ tail)) fragment0104503Acc00900 =
      .ok (.obj (fragment0104503Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0104503_object_field_009"
  err.flush

noncomputable def fragment0104503Chars : List Char := '{' :: (fragment0104503Field000Chars00 ++ fragment0104503Field001Chars00 ++ fragment0104503Field002Chars00 ++ fragment0104503Field003Chars00 ++ fragment0104503Field004Chars00 ++ fragment0104503Field005Chars00 ++ fragment0104503Field006Chars00 ++ fragment0104503Field007Chars00 ++ fragment0104503Field008Chars00 ++ fragment0104503Field009Chars00)
noncomputable def fragment0104503Value : SourceJson := .obj (fragment0104503Acc01000.reverse)

theorem value_fragment0104503 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 252) (fragment0104503Chars ++ tail) =
      .ok (fragment0104503Value, tail) := by
  have hinput : fragment0104503Chars ++ tail = '{' :: (fragment0104503Field000Chars00 ++ (fragment0104503Field001Chars00 ++ (fragment0104503Field002Chars00 ++ (fragment0104503Field003Chars00 ++ (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0104503Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 252) (fragment0104503Chars ++ tail) =
        SourceJson.value (fuel + 252) ('{' :: (fragment0104503Field000Chars00 ++ (fragment0104503Field001Chars00 ++ (fragment0104503Field002Chars00 ++ (fragment0104503Field003Chars00 ++ (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 252)) hinput
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0104503Field000Chars00 ++ (fragment0104503Field001Chars00 ++ (fragment0104503Field002Chars00 ++ (fragment0104503Field003Chars00 ++ (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))))))))))) fragment0104503Acc00000 := by rfl
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0104503Field001Chars00 ++ (fragment0104503Field002Chars00 ++ (fragment0104503Field003Chars00 ++ (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail))))))))))) fragment0104503Acc00100 := object_fragment0104503_field_000 fuel (fragment0104503Field001Chars00 ++ (fragment0104503Field002Chars00 ++ (fragment0104503Field003Chars00 ++ (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0104503Field002Chars00 ++ (fragment0104503Field003Chars00 ++ (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))))))))) fragment0104503Acc00200 := object_fragment0104503_field_001 fuel (fragment0104503Field002Chars00 ++ (fragment0104503Field003Chars00 ++ (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0104503Field003Chars00 ++ (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail))))))))) fragment0104503Acc00300 := object_fragment0104503_field_002 fuel (fragment0104503Field003Chars00 ++ (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))))))) fragment0104503Acc00400 := object_fragment0104503_field_003 fuel (fragment0104503Field004Chars00 ++ (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail))))))) fragment0104503Acc00500 := object_fragment0104503_field_004 fuel (fragment0104503Field005Chars00 ++ (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))))) fragment0104503Acc00600 := object_fragment0104503_field_005 fuel (fragment0104503Field006Chars00 ++ (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail))))) fragment0104503Acc00700 := object_fragment0104503_field_006 fuel (fragment0104503Field007Chars00 ++ (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))) fragment0104503Acc00800 := object_fragment0104503_field_007 fuel (fragment0104503Field008Chars00 ++ (fragment0104503Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0104503Field009Chars00 ++ (tail))) fragment0104503Acc00900 := object_fragment0104503_field_008 fuel (fragment0104503Field009Chars00 ++ (tail))
    _ = .ok (fragment0104503Value, tail) := object_fragment0104503_field_009 fuel (tail)

noncomputable def fragment0106132Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0106132Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0106132Field000Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0106132Acc00100 : List (String × SourceJson) := (fragment0106132Field000Key00, fragment0106132Field000Value00) :: fragment0106132Acc00000
noncomputable def fragment0106132Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', ',']

theorem object_fragment0106132_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0106132Field000Chars00 ++ tail)) fragment0106132Acc00000 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0106132Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_000"
  err.flush

noncomputable def fragment0106132Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0106132Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0106132Acc00200 : List (String × SourceJson) := (fragment0106132Field001Key00, fragment0106132Field001Value00) :: fragment0106132Acc00100
noncomputable def fragment0106132Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0106132_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0106132Field001Chars00 ++ tail)) fragment0106132Acc00100 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0106132Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_001"
  err.flush

noncomputable def fragment0106132Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0106132Field002Value00 : SourceJson := .str (String.ofList ['9', '0', '8', '8', '5', '6', '7', '7', '7', '0', '9', '9', '0', '2', '3', '4', '6', '5', '9', '1', '9', '1', '7', '5', '2', '8', '9', '0', '2', '1', '4', '2', '6', '0', '0', '6', '1', '1', '7', '/', '3', '5', '0', '5', '7', '7', '3', '5', '4', '5', '8', '3', '5', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0106132Acc00300 : List (String × SourceJson) := (fragment0106132Field002Key00, fragment0106132Field002Value00) :: fragment0106132Acc00200
noncomputable def fragment0106132Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '0', '8', '8', '5', '6', '7', '7', '7', '0', '9', '9', '0', '2', '3', '4', '6', '5', '9', '1', '9', '1', '7', '5', '2', '8', '9', '0', '2', '1', '4', '2', '6', '0', '0', '6', '1', '1', '7', '/', '3', '5', '0', '5', '7', '7', '3', '5', '4', '5', '8', '3', '5', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0106132_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0106132Field002Chars00 ++ tail)) fragment0106132Acc00200 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0106132Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_002"
  err.flush

noncomputable def fragment0106132Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0106132Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0106132Acc00400 : List (String × SourceJson) := (fragment0106132Field003Key00, fragment0106132Field003Value00) :: fragment0106132Acc00300
noncomputable def fragment0106132Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0106132_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0106132Field003Chars00 ++ tail)) fragment0106132Acc00300 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0106132Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_003"
  err.flush

noncomputable def fragment0106132Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0106132Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0106132Acc00500 : List (String × SourceJson) := (fragment0106132Field004Key00, fragment0106132Field004Value00) :: fragment0106132Acc00400
noncomputable def fragment0106132Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0106132_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0106132Field004Chars00 ++ tail)) fragment0106132Acc00400 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0106132Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_004"
  err.flush

noncomputable def fragment0106132Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0106132Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '6', '9', '8', '4', '7', '9', '4', '6', '4', '9', '2', '9', '/', '2', '8', '3', '1', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '2', '4', '2', '6', '9', '9', '3', '3', '1', '2', '3', '/', '5', '6', '6', '2', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '7', '9', '4', '8', '6', '8', '8', '9', '7', '4', '9', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '6', '7', '7', '7', '3', '8', '1', '1', '0', '4', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '5', '8', '4', '4', '0', '5', '2', '1', '9', '2', '1', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '0', '6', '9', '2', '3', '1', '5', '7', '2', '4', '3', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '0', '3', '2', '3', '2', '5', '2', '1', '4', '9', '/', '5', '6', '6', '2', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '4', '9', '4', '2', '7', '5', '3', '8', '7', '2', '3', '/', '1', '6', '9', '8', '6', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '3', '3', '8', '7', '0', '1', '3', '0', '3', '9', '3', '/', '1', '6', '9', '8', '6', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '9', '8', '3', '9', '3', '4', '3', '2', '7', '3', '/', '2', '8', '3', '1', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0106132Acc00600 : List (String × SourceJson) := (fragment0106132Field005Key00, fragment0106132Field005Value00) :: fragment0106132Acc00500
noncomputable def fragment0106132Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '9', '8', '4', '7', '9', '4', '6', '4', '9', '2', '9', '/', '2', '8', '3', '1', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '2', '4', '2', '6', '9', '9', '3', '3', '1', '2', '3', '/', '5', '6', '6', '2', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '7', '9', '4', '8', '6', '8', '8', '9', '7', '4', '9', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '0', '6', '7', '7', '7', '3', '8', '1', '1', '0', '4', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '5', '8', '4', '4', '0', '5', '2', '1', '9', '2', '1', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '0', '6', '9', '2', '3', '1', '5', '7', '2', '4', '3', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '0', '3', '2', '3', '2', '5', '2', '1', '4', '9', '/', '5', '6', '6', '2', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '4', '9', '4', '2', '7', '5', '3', '8', '7', '2', '3', '/', '1', '6', '9', '8', '6', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '3', '3', '8', '7', '0', '1', '3', '0', '3', '9', '3', '/', '1', '6', '9', '8', '6', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '9', '8', '3', '9', '3', '4', '3', '2', '7', '3', '/', '2', '8', '3', '1', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0106132_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0106132Field005Chars00 ++ tail)) fragment0106132Acc00500 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0106132Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_005"
  err.flush

noncomputable def fragment0106132Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0106132Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '2', '4', '7', '5', '4', '2', '0', '8', '0', '6', '5', '9', '6', '5', '8', '8', '2', '2', '6', '3', '4', '0', '0', '1', '4', '1', '8', '7', '9', '6', '2', '7', '7', '8', '5', '5', '9', '1', '3', '1', '0', '1', '5', '6', '2', '5', '0', '/', '2', '2', '8', '3', '3', '4', '2', '0', '3', '4', '6', '2', '3', '8', '2', '6', '9', '0', '8', '5', '7', '1', '1', '5', '7', '5', '3', '3', '6', '7', '2', '1', '0', '7', '4', '4', '4', '8', '8', '7', '9', '1', '9', '8', '8', '7', '5', '4', '7', '1', '4', '3', '4', '3', '9', '3', '7', '5', '4', '4', '9', '7', '4', '4', '0', '7'])
noncomputable def fragment0106132Acc00700 : List (String × SourceJson) := (fragment0106132Field006Key00, fragment0106132Field006Value00) :: fragment0106132Acc00600
noncomputable def fragment0106132Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '2', '4', '7', '5', '4', '2', '0', '8', '0', '6', '5', '9', '6', '5', '8', '8', '2', '2', '6', '3', '4', '0', '0', '1', '4', '1', '8', '7', '9', '6', '2', '7', '7', '8', '5', '5', '9', '1', '3', '1', '0', '1', '5', '6', '2', '5', '0', '/', '2', '2', '8', '3', '3', '4', '2', '0', '3', '4', '6', '2', '3', '8', '2', '6', '9', '0', '8', '5', '7', '1', '1', '5', '7', '5', '3', '3', '6', '7', '2', '1', '0', '7', '4', '4', '4', '8', '8', '7', '9', '1', '9', '8', '8', '7', '5', '4', '7', '1', '4', '3', '4', '3', '9', '3', '7', '5', '4', '4', '9', '7', '4', '4', '0', '7', '"', ',']

theorem object_fragment0106132_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0106132Field006Chars00 ++ tail)) fragment0106132Acc00600 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0106132Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_006"
  err.flush

noncomputable def fragment0106132Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0106132Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '9', '7', '5', '5', '6', '3', '6', '7', '3', '8', '0', '1', '6', '8', '4', '6', '9', '7', '1', '0', '3', '7', '3', '2', '7', '5', '9', '2', '8', '3', '5', '3', '6', '0', '6', '6', '2', '1', '1', '1', '8', '7', '7', '8', '7', '7', '7', '1', '6', '3', '0', '6', '8', '3', '6', '3', '5', '8', '3', '2', '4', '7', '0', '7', '4', '1', '0', '0', '8', '2', '5', '7', '4', '1', '1', '5', '5', '0', '2', '0', '5', '5', '6', '9', '6', '9', '4', '1', '0', '1', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '3', '4', '1', '7', '6', '7', '4', '9', '3', '9', '4', '7', '7', '3', '2', '5', '5', '3', '4', '7', '6', '8', '6', '5', '1', '1', '2', '3', '5', '4', '2', '3', '2', '6', '1', '9', '4', '0', '0', '2', '9', '9', '3', '5', '3', '9', '0', '7', '3', '7', '2', '6', '2', '7', '6', '9', '8', '7', '0', '5', '0', '8', '8', '5', '7', '4', '1', '7', '9', '2', '1', '6', '3', '2', '7', '4', '9', '0', '1', '1', '7', '0', '9', '1', '3', '4', '1', '2', '3', '0', '1', '0', '8', '0', '0', '9', '1', '4', '4', '9', '4', '0', '8', '3', '6', '5', '7', '9', '4', '1', '0', '0', '2', '3', '0', '1', '2', '3', '2', '9', '0', '0', '0', '4', '0', '3'])
noncomputable def fragment0106132Acc00800 : List (String × SourceJson) := (fragment0106132Field007Key00, fragment0106132Field007Value00) :: fragment0106132Acc00700
noncomputable def fragment0106132Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '9', '7', '5', '5', '6', '3', '6', '7', '3', '8', '0', '1', '6', '8', '4', '6', '9', '7', '1', '0', '3', '7', '3', '2', '7', '5', '9', '2', '8', '3', '5', '3', '6', '0', '6', '6', '2', '1', '1', '1', '8', '7', '7', '8', '7', '7', '7', '1', '6', '3', '0', '6', '8', '3', '6', '3', '5', '8', '3', '2', '4', '7', '0', '7', '4', '1', '0', '0', '8', '2', '5', '7', '4', '1', '1', '5', '5', '0', '2', '0', '5', '5', '6', '9', '6', '9', '4', '1', '0', '1', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '3', '4', '1', '7', '6', '7', '4', '9', '3', '9', '4', '7', '7', '3', '2', '5', '5', '3', '4', '7', '6', '8', '6', '5', '1', '1', '2', '3', '5', '4', '2', '3', '2', '6', '1', '9', '4', '0', '0', '2', '9', '9', '3', '5', '3', '9', '0', '7', '3', '7', '2', '6', '2', '7', '6', '9', '8', '7', '0', '5', '0', '8', '8', '5', '7', '4', '1', '7', '9', '2', '1', '6', '3', '2', '7', '4', '9', '0', '1', '1', '7', '0', '9', '1', '3', '4', '1', '2', '3', '0', '1', '0', '8', '0', '0', '9', '1', '4', '4', '9', '4', '0', '8', '3', '6', '5', '7', '9', '4', '1', '0', '0', '2', '3', '0', '1', '2', '3', '2', '9', '0', '0', '0', '4', '0', '3', '"', ',']

theorem object_fragment0106132_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0106132Field007Chars00 ++ tail)) fragment0106132Acc00700 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0106132Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_007"
  err.flush

noncomputable def fragment0106132Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0106132Field008Value00 : SourceJson := .str (String.ofList ['6', '6', '7', '8', '5', '7', '6', '2', '6', '6', '0', '2'])
noncomputable def fragment0106132Acc00900 : List (String × SourceJson) := (fragment0106132Field008Key00, fragment0106132Field008Value00) :: fragment0106132Acc00800
noncomputable def fragment0106132Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '7', '8', '5', '7', '6', '2', '6', '6', '0', '2', '"', ',']

theorem object_fragment0106132_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0106132Field008Chars00 ++ tail)) fragment0106132Acc00800 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0106132Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_008"
  err.flush

noncomputable def fragment0106132Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0106132Field009Value00 : SourceJson := .str (String.ofList ['2', '5', '3', '2', '1', '1', '7', '0', '2', '8', '0', '0', '9'])
noncomputable def fragment0106132Acc01000 : List (String × SourceJson) := (fragment0106132Field009Key00, fragment0106132Field009Value00) :: fragment0106132Acc00900
noncomputable def fragment0106132Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '3', '2', '1', '1', '7', '0', '2', '8', '0', '0', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0106132_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0106132Field009Chars00 ++ tail)) fragment0106132Acc00900 =
      .ok (.obj (fragment0106132Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0106132_object_field_009"
  err.flush

noncomputable def fragment0106132Chars : List Char := '{' :: (fragment0106132Field000Chars00 ++ fragment0106132Field001Chars00 ++ fragment0106132Field002Chars00 ++ fragment0106132Field003Chars00 ++ fragment0106132Field004Chars00 ++ fragment0106132Field005Chars00 ++ fragment0106132Field006Chars00 ++ fragment0106132Field007Chars00 ++ fragment0106132Field008Chars00 ++ fragment0106132Field009Chars00)
noncomputable def fragment0106132Value : SourceJson := .obj (fragment0106132Acc01000.reverse)

theorem value_fragment0106132 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 252) (fragment0106132Chars ++ tail) =
      .ok (fragment0106132Value, tail) := by
  have hinput : fragment0106132Chars ++ tail = '{' :: (fragment0106132Field000Chars00 ++ (fragment0106132Field001Chars00 ++ (fragment0106132Field002Chars00 ++ (fragment0106132Field003Chars00 ++ (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0106132Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 252) (fragment0106132Chars ++ tail) =
        SourceJson.value (fuel + 252) ('{' :: (fragment0106132Field000Chars00 ++ (fragment0106132Field001Chars00 ++ (fragment0106132Field002Chars00 ++ (fragment0106132Field003Chars00 ++ (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 252)) hinput
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0106132Field000Chars00 ++ (fragment0106132Field001Chars00 ++ (fragment0106132Field002Chars00 ++ (fragment0106132Field003Chars00 ++ (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))))))))))) fragment0106132Acc00000 := by rfl
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0106132Field001Chars00 ++ (fragment0106132Field002Chars00 ++ (fragment0106132Field003Chars00 ++ (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail))))))))))) fragment0106132Acc00100 := object_fragment0106132_field_000 fuel (fragment0106132Field001Chars00 ++ (fragment0106132Field002Chars00 ++ (fragment0106132Field003Chars00 ++ (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0106132Field002Chars00 ++ (fragment0106132Field003Chars00 ++ (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))))))))) fragment0106132Acc00200 := object_fragment0106132_field_001 fuel (fragment0106132Field002Chars00 ++ (fragment0106132Field003Chars00 ++ (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0106132Field003Chars00 ++ (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail))))))))) fragment0106132Acc00300 := object_fragment0106132_field_002 fuel (fragment0106132Field003Chars00 ++ (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))))))) fragment0106132Acc00400 := object_fragment0106132_field_003 fuel (fragment0106132Field004Chars00 ++ (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail))))))) fragment0106132Acc00500 := object_fragment0106132_field_004 fuel (fragment0106132Field005Chars00 ++ (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))))) fragment0106132Acc00600 := object_fragment0106132_field_005 fuel (fragment0106132Field006Chars00 ++ (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail))))) fragment0106132Acc00700 := object_fragment0106132_field_006 fuel (fragment0106132Field007Chars00 ++ (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))) fragment0106132Acc00800 := object_fragment0106132_field_007 fuel (fragment0106132Field008Chars00 ++ (fragment0106132Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0106132Field009Chars00 ++ (tail))) fragment0106132Acc00900 := object_fragment0106132_field_008 fuel (fragment0106132Field009Chars00 ++ (tail))
    _ = .ok (fragment0106132Value, tail) := object_fragment0106132_field_009 fuel (tail)

noncomputable def fragment0107755Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0107755Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0107755Field000Value00 : SourceJson := .number (String.ofList ['2'])
noncomputable def fragment0107755Acc00100 : List (String × SourceJson) := (fragment0107755Field000Key00, fragment0107755Field000Value00) :: fragment0107755Acc00000
noncomputable def fragment0107755Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', ',']

theorem object_fragment0107755_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0107755Field000Chars00 ++ tail)) fragment0107755Acc00000 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0107755Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_000"
  err.flush

noncomputable def fragment0107755Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0107755Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0107755Acc00200 : List (String × SourceJson) := (fragment0107755Field001Key00, fragment0107755Field001Value00) :: fragment0107755Acc00100
noncomputable def fragment0107755Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0107755_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0107755Field001Chars00 ++ tail)) fragment0107755Acc00100 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0107755Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_001"
  err.flush

noncomputable def fragment0107755Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0107755Field002Value00 : SourceJson := .str (String.ofList ['9', '9', '4', '1', '2', '2', '7', '0', '0', '4', '5', '2', '9', '8', '0', '9', '8', '4', '3', '6', '9', '7', '6', '7', '4', '2', '1', '8', '3', '3', '7', '2', '2', '9', '1', '3', '9', '9', '6', '1', '0', '0', '8', '7', '/', '1', '4', '9', '5', '7', '9', '6', '7', '1', '2', '8', '8', '9', '9', '0', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0107755Acc00300 : List (String × SourceJson) := (fragment0107755Field002Key00, fragment0107755Field002Value00) :: fragment0107755Acc00200
noncomputable def fragment0107755Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '9', '4', '1', '2', '2', '7', '0', '0', '4', '5', '2', '9', '8', '0', '9', '8', '4', '3', '6', '9', '7', '6', '7', '4', '2', '1', '8', '3', '3', '7', '2', '2', '9', '1', '3', '9', '9', '6', '1', '0', '0', '8', '7', '/', '1', '4', '9', '5', '7', '9', '6', '7', '1', '2', '8', '8', '9', '9', '0', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0107755_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0107755Field002Chars00 ++ tail)) fragment0107755Acc00200 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0107755Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_002"
  err.flush

noncomputable def fragment0107755Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0107755Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0107755Acc00400 : List (String × SourceJson) := (fragment0107755Field003Key00, fragment0107755Field003Value00) :: fragment0107755Acc00300
noncomputable def fragment0107755Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '8', '2', '4', '1', '6', '9', '/', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0107755_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0107755Field003Chars00 ++ tail)) fragment0107755Acc00300 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0107755Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_003"
  err.flush

noncomputable def fragment0107755Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0107755Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0107755Acc00500 : List (String × SourceJson) := (fragment0107755Field004Key00, fragment0107755Field004Value00) :: fragment0107755Acc00400
noncomputable def fragment0107755Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0107755_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0107755Field004Chars00 ++ tail)) fragment0107755Acc00400 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0107755Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_004"
  err.flush

noncomputable def fragment0107755Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0107755Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '0', '8', '2', '6', '0', '6', '4', '3', '4', '2', '5', '4', '3', '8', '4', '3', '1', '8', '2', '9', '/', '3', '2', '6', '8', '6', '2', '1', '9', '3', '9', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '5', '4', '6', '9', '1', '8', '3', '1', '8', '5', '7', '8', '5', '8', '7', '2', '1', '/', '5', '1', '0', '7', '2', '2', '1', '7', '8', '0', '1', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '5', '6', '3', '7', '5', '2', '8', '2', '9', '1', '7', '5', '0', '9', '7', '6', '2', '9', '3', '/', '2', '9', '4', '1', '7', '5', '9', '7', '4', '5', '3', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '8', '9', '3', '4', '6', '9', '1', '5', '4', '0', '0', '3', '7', '2', '6', '2', '6', '7', '/', '1', '2', '2', '5', '7', '3', '3', '2', '2', '7', '2', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '4', '8', '0', '8', '8', '7', '5', '2', '5', '4', '8', '7', '0', '2', '2', '4', '1', '/', '1', '5', '3', '2', '1', '6', '6', '5', '3', '4', '0', '3', '4', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '9', '3', '4', '1', '9', '8', '9', '5', '8', '7', '0', '2', '3', '5', '7', '0', '1', '7', '/', '7', '3', '5', '4', '3', '9', '9', '3', '6', '3', '3', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '4', '7', '6', '5', '9', '5', '2', '2', '7', '7', '6', '2', '3', '3', '1', '1', '8', '9', '/', '1', '4', '7', '0', '8', '7', '9', '8', '7', '2', '6', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '5', '4', '5', '5', '2', '3', '6', '8', '5', '7', '5', '4', '7', '3', '9', '8', '8', '0', '1', '/', '1', '4', '7', '0', '8', '7', '9', '8', '7', '2', '6', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '6', '6', '8', '5', '4', '1', '9', '2', '7', '3', '5', '1', '8', '2', '0', '0', '4', '1', '/', '1', '4', '7', '0', '8', '7', '9', '8', '7', '2', '6', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '9', '3', '1', '5', '1', '6', '6', '9', '1', '1', '6', '8', '0', '4', '5', '6', '8', '7', '/', '1', '8', '3', '8', '5', '9', '9', '8', '4', '0', '8', '4', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0107755Acc00600 : List (String × SourceJson) := (fragment0107755Field005Key00, fragment0107755Field005Value00) :: fragment0107755Acc00500
noncomputable def fragment0107755Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '8', '2', '6', '0', '6', '4', '3', '4', '2', '5', '4', '3', '8', '4', '3', '1', '8', '2', '9', '/', '3', '2', '6', '8', '6', '2', '1', '9', '3', '9', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '5', '4', '6', '9', '1', '8', '3', '1', '8', '5', '7', '8', '5', '8', '7', '2', '1', '/', '5', '1', '0', '7', '2', '2', '1', '7', '8', '0', '1', '1', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '5', '6', '3', '7', '5', '2', '8', '2', '9', '1', '7', '5', '0', '9', '7', '6', '2', '9', '3', '/', '2', '9', '4', '1', '7', '5', '9', '7', '4', '5', '3', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '8', '9', '3', '4', '6', '9', '1', '5', '4', '0', '0', '3', '7', '2', '6', '2', '6', '7', '/', '1', '2', '2', '5', '7', '3', '3', '2', '2', '7', '2', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '4', '8', '0', '8', '8', '7', '5', '2', '5', '4', '8', '7', '0', '2', '2', '4', '1', '/', '1', '5', '3', '2', '1', '6', '6', '5', '3', '4', '0', '3', '4', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '9', '3', '4', '1', '9', '8', '9', '5', '8', '7', '0', '2', '3', '5', '7', '0', '1', '7', '/', '7', '3', '5', '4', '3', '9', '9', '3', '6', '3', '3', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '6', '4', '7', '6', '5', '9', '5', '2', '2', '7', '7', '6', '2', '3', '3', '1', '1', '8', '9', '/', '1', '4', '7', '0', '8', '7', '9', '8', '7', '2', '6', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '5', '4', '5', '5', '2', '3', '6', '8', '5', '7', '5', '4', '7', '3', '9', '8', '8', '0', '1', '/', '1', '4', '7', '0', '8', '7', '9', '8', '7', '2', '6', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '6', '6', '8', '5', '4', '1', '9', '2', '7', '3', '5', '1', '8', '2', '0', '0', '4', '1', '/', '1', '4', '7', '0', '8', '7', '9', '8', '7', '2', '6', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '9', '3', '1', '5', '1', '6', '6', '9', '1', '1', '6', '8', '0', '4', '5', '6', '8', '7', '/', '1', '8', '3', '8', '5', '9', '9', '8', '4', '0', '8', '4', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0107755_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0107755Field005Chars00 ++ tail)) fragment0107755Acc00500 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0107755Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_005"
  err.flush

noncomputable def fragment0107755Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0107755Field006Value00 : SourceJson := .str (String.ofList ['2', '4', '3', '1', '6', '8', '4', '6', '8', '5', '4', '0', '4', '0', '5', '7', '9', '5', '1', '3', '2', '4', '6', '7', '2', '2', '4', '4', '7', '1', '7', '1', '2', '1', '2', '2', '4', '2', '3', '3', '7', '2', '3', '7', '8', '9', '5', '6', '2', '5', '3', '9', '0', '6', '2', '5', '/', '5', '4', '5', '5', '6', '3', '0', '0', '9', '7', '9', '6', '6', '0', '9', '9', '4', '6', '4', '3', '8', '8', '2', '0', '1', '6', '4', '7', '2', '2', '9', '0', '7', '8', '7', '6', '2', '3', '9', '2', '6', '6', '2', '7', '9', '5', '4', '1', '0', '0', '3', '8', '9', '6', '0', '5', '9', '6', '9', '1', '6', '8', '4', '1', '1', '3', '4', '0', '8'])
noncomputable def fragment0107755Acc00700 : List (String × SourceJson) := (fragment0107755Field006Key00, fragment0107755Field006Value00) :: fragment0107755Acc00600
noncomputable def fragment0107755Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '3', '1', '6', '8', '4', '6', '8', '5', '4', '0', '4', '0', '5', '7', '9', '5', '1', '3', '2', '4', '6', '7', '2', '2', '4', '4', '7', '1', '7', '1', '2', '1', '2', '2', '4', '2', '3', '3', '7', '2', '3', '7', '8', '9', '5', '6', '2', '5', '3', '9', '0', '6', '2', '5', '/', '5', '4', '5', '5', '6', '3', '0', '0', '9', '7', '9', '6', '6', '0', '9', '9', '4', '6', '4', '3', '8', '8', '2', '0', '1', '6', '4', '7', '2', '2', '9', '0', '7', '8', '7', '6', '2', '3', '9', '2', '6', '6', '2', '7', '9', '5', '4', '1', '0', '0', '3', '8', '9', '6', '0', '5', '9', '6', '9', '1', '6', '8', '4', '1', '1', '3', '4', '0', '8', '"', ',']

theorem object_fragment0107755_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0107755Field006Chars00 ++ tail)) fragment0107755Acc00600 =
      SourceJson.object (fuel + 393) (SourceJson.white tail) fragment0107755Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_006"
  err.flush

noncomputable def fragment0107755Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0107755Field007Value00 : SourceJson := .str (String.ofList ['5', '8', '3', '1', '0', '2', '8', '3', '8', '8', '2', '2', '9', '5', '8', '5', '4', '2', '2', '2', '7', '8', '9', '4', '0', '9', '3', '4', '4', '4', '5', '3', '0', '4', '4', '0', '6', '3', '8', '9', '7', '8', '7', '5', '9', '1', '2', '9', '4', '7', '7', '2', '1', '4', '1', '0', '9', '9', '7', '2', '5', '1', '4', '8', '2', '1', '0', '4', '5', '4', '6', '4', '6', '7', '2', '7', '1', '0', '6', '1', '6', '7', '8', '4', '8', '4', '7', '4', '7', '2', '1', '9', '5', '5', '4', '8', '7', '1', '3', '3', '1', '7', '9', '0', '2', '6', '4', '4', '4', '2', '6', '4', '2', '0', '6', '6', '8', '6', '5', '2', '7', '3', '9', '7', '5', '5', '3', '6', '5', '4', '3', '4', '2', '3', '6', '4', '3', '6', '3', '4', '7', '5', '2', '7', '2', '3', '7', '7', '9', '7', '3', '6', '1', '0', '4', '7', '6', '9', '2', '1', '9', '2', '8', '4', '8', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '2', '2', '5', '3', '5', '3', '5', '6', '3', '6', '4', '8', '9', '0', '8', '4', '7', '4', '4', '0', '4', '3', '3', '7', '6', '0', '1', '8', '1', '1', '4', '5', '1', '7', '1', '3', '5', '0', '4', '7', '4', '1', '1', '0', '6', '2', '3', '4', '2', '4', '5', '5', '3', '6', '3', '5', '7', '5', '1', '9', '7', '9', '3', '0', '8', '6', '9', '1', '4', '5', '1', '8', '4', '2', '4', '9', '3', '9', '4', '3', '8', '8', '1', '3', '8', '2', '6', '7', '3', '6', '1', '8', '5', '8', '2', '1', '4', '3', '2', '6', '4', '3', '5', '7', '5', '8', '4', '6', '7', '9', '5', '5', '1', '6', '2', '5', '6', '3', '3', '0', '9', '9', '1', '2', '6', '3', '3', '2', '8', '8', '2', '2', '7', '0', '7', '1', '8', '0', '5', '3', '5', '9', '5', '2', '4', '4', '7', '6', '8', '4', '6', '6', '1', '8', '7', '2', '8', '6', '6', '5', '1', '5', '5', '0', '8', '1', '7', '4', '3', '9', '6', '0', '6', '2', '7', '3', '7', '1', '1', '4', '8', '1', '9', '2', '2', '3', '2', '9', '7', '9', '4', '9', '9', '0', '8', '4', '1', '6', '9'])
noncomputable def fragment0107755Acc00800 : List (String × SourceJson) := (fragment0107755Field007Key00, fragment0107755Field007Value00) :: fragment0107755Acc00700
noncomputable def fragment0107755Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '8', '3', '1', '0', '2', '8', '3', '8', '8', '2', '2', '9', '5', '8', '5', '4', '2', '2', '2', '7', '8', '9', '4', '0', '9', '3', '4', '4', '4', '5', '3', '0', '4', '4', '0', '6', '3', '8', '9', '7', '8', '7', '5', '9', '1', '2', '9', '4', '7', '7', '2', '1', '4', '1', '0', '9', '9', '7', '2', '5', '1', '4', '8', '2', '1', '0', '4', '5', '4', '6', '4', '6', '7', '2', '7', '1', '0', '6', '1', '6', '7', '8', '4', '8', '4', '7', '4', '7', '2', '1', '9', '5', '5', '4', '8', '7', '1', '3', '3', '1', '7', '9', '0', '2', '6', '4', '4', '4', '2', '6', '4', '2', '0', '6', '6', '8', '6', '5', '2', '7', '3', '9', '7', '5', '5', '3', '6', '5', '4', '3', '4', '2', '3', '6', '4', '3', '6', '3', '4', '7', '5', '2', '7', '2', '3', '7', '7', '9', '7', '3', '6', '1', '0', '4', '7', '6', '9', '2', '1', '9', '2', '8', '4', '8', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '2', '2', '5', '3', '5', '3', '5', '6', '3', '6', '4', '8', '9', '0', '8', '4', '7', '4', '4', '0', '4', '3', '3', '7', '6', '0', '1', '8', '1', '1', '4', '5', '1', '7', '1', '3', '5', '0', '4', '7', '4', '1', '1', '0', '6', '2', '3', '4', '2', '4', '5', '5', '3', '6', '3', '5', '7', '5', '1', '9', '7', '9', '3', '0', '8', '6', '9', '1', '4', '5', '1', '8', '4', '2', '4', '9', '3', '9', '4', '3', '8', '8', '1', '3', '8', '2', '6', '7', '3', '6', '1', '8', '5', '8', '2', '1', '4', '3', '2', '6', '4', '3', '5', '7', '5', '8', '4', '6', '7', '9', '5', '5', '1', '6', '2', '5', '6', '3', '3', '0', '9', '9', '1', '2', '6', '3', '3', '2', '8', '8', '2', '2', '7', '0', '7', '1', '8', '0', '5', '3', '5', '9', '5', '2', '4', '4', '7', '6', '8', '4', '6', '6', '1', '8', '7', '2', '8', '6', '6', '5', '1', '5', '5', '0', '8', '1', '7', '4', '3', '9', '6', '0', '6', '2', '7', '3', '7', '1', '1', '4', '8', '1', '9', '2', '2', '3', '2', '9', '7', '9', '4', '9', '9', '0', '8', '4', '1', '6', '9', '"', ',']

theorem object_fragment0107755_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 393) (SourceJson.white (fragment0107755Field007Chars00 ++ tail)) fragment0107755Acc00700 =
      SourceJson.object (fuel + 392) (SourceJson.white tail) fragment0107755Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_007"
  err.flush

noncomputable def fragment0107755Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0107755Field008Value00 : SourceJson := .str (String.ofList ['3', '5', '3', '1', '3', '5', '9', '4', '5', '7', '6', '4', '4', '7', '6', '9'])
noncomputable def fragment0107755Acc00900 : List (String × SourceJson) := (fragment0107755Field008Key00, fragment0107755Field008Value00) :: fragment0107755Acc00800
noncomputable def fragment0107755Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '5', '3', '1', '3', '5', '9', '4', '5', '7', '6', '4', '4', '7', '6', '9', '"', ',']

theorem object_fragment0107755_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 392) (SourceJson.white (fragment0107755Field008Chars00 ++ tail)) fragment0107755Acc00800 =
      SourceJson.object (fuel + 391) (SourceJson.white tail) fragment0107755Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_008"
  err.flush

noncomputable def fragment0107755Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0107755Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '9', '8', '2', '2', '9', '1', '3', '9', '0', '7', '3', '6', '0', '7'])
noncomputable def fragment0107755Acc01000 : List (String × SourceJson) := (fragment0107755Field009Key00, fragment0107755Field009Value00) :: fragment0107755Acc00900
noncomputable def fragment0107755Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '4', '9', '8', '2', '2', '9', '1', '3', '9', '0', '7', '3', '6', '0', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0107755_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 391) (SourceJson.white (fragment0107755Field009Chars00 ++ tail)) fragment0107755Acc00900 =
      .ok (.obj (fragment0107755Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0107755_object_field_009"
  err.flush

noncomputable def fragment0107755Chars : List Char := '{' :: (fragment0107755Field000Chars00 ++ fragment0107755Field001Chars00 ++ fragment0107755Field002Chars00 ++ fragment0107755Field003Chars00 ++ fragment0107755Field004Chars00 ++ fragment0107755Field005Chars00 ++ fragment0107755Field006Chars00 ++ fragment0107755Field007Chars00 ++ fragment0107755Field008Chars00 ++ fragment0107755Field009Chars00)
noncomputable def fragment0107755Value : SourceJson := .obj (fragment0107755Acc01000.reverse)

theorem value_fragment0107755 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 401) (fragment0107755Chars ++ tail) =
      .ok (fragment0107755Value, tail) := by
  have hinput : fragment0107755Chars ++ tail = '{' :: (fragment0107755Field000Chars00 ++ (fragment0107755Field001Chars00 ++ (fragment0107755Field002Chars00 ++ (fragment0107755Field003Chars00 ++ (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0107755Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 401) (fragment0107755Chars ++ tail) =
        SourceJson.value (fuel + 401) ('{' :: (fragment0107755Field000Chars00 ++ (fragment0107755Field001Chars00 ++ (fragment0107755Field002Chars00 ++ (fragment0107755Field003Chars00 ++ (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 401)) hinput
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0107755Field000Chars00 ++ (fragment0107755Field001Chars00 ++ (fragment0107755Field002Chars00 ++ (fragment0107755Field003Chars00 ++ (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))))))))))) fragment0107755Acc00000 := by rfl
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0107755Field001Chars00 ++ (fragment0107755Field002Chars00 ++ (fragment0107755Field003Chars00 ++ (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail))))))))))) fragment0107755Acc00100 := object_fragment0107755_field_000 fuel (fragment0107755Field001Chars00 ++ (fragment0107755Field002Chars00 ++ (fragment0107755Field003Chars00 ++ (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0107755Field002Chars00 ++ (fragment0107755Field003Chars00 ++ (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))))))))) fragment0107755Acc00200 := object_fragment0107755_field_001 fuel (fragment0107755Field002Chars00 ++ (fragment0107755Field003Chars00 ++ (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0107755Field003Chars00 ++ (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail))))))))) fragment0107755Acc00300 := object_fragment0107755_field_002 fuel (fragment0107755Field003Chars00 ++ (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))))))) fragment0107755Acc00400 := object_fragment0107755_field_003 fuel (fragment0107755Field004Chars00 ++ (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail))))))) fragment0107755Acc00500 := object_fragment0107755_field_004 fuel (fragment0107755Field005Chars00 ++ (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))))) fragment0107755Acc00600 := object_fragment0107755_field_005 fuel (fragment0107755Field006Chars00 ++ (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 393) (SourceJson.white (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail))))) fragment0107755Acc00700 := object_fragment0107755_field_006 fuel (fragment0107755Field007Chars00 ++ (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 392) (SourceJson.white (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))) fragment0107755Acc00800 := object_fragment0107755_field_007 fuel (fragment0107755Field008Chars00 ++ (fragment0107755Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 391) (SourceJson.white (fragment0107755Field009Chars00 ++ (tail))) fragment0107755Acc00900 := object_fragment0107755_field_008 fuel (fragment0107755Field009Chars00 ++ (tail))
    _ = .ok (fragment0107755Value, tail) := object_fragment0107755_field_009 fuel (tail)

noncomputable def fragment0109704Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0109704Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0109704Field000Value00 : SourceJson := .number (String.ofList ['3'])
noncomputable def fragment0109704Acc00100 : List (String × SourceJson) := (fragment0109704Field000Key00, fragment0109704Field000Value00) :: fragment0109704Acc00000
noncomputable def fragment0109704Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', ',']

theorem object_fragment0109704_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0109704Field000Chars00 ++ tail)) fragment0109704Acc00000 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0109704Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_000"
  err.flush

noncomputable def fragment0109704Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0109704Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0109704Acc00200 : List (String × SourceJson) := (fragment0109704Field001Key00, fragment0109704Field001Value00) :: fragment0109704Acc00100
noncomputable def fragment0109704Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0109704_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0109704Field001Chars00 ++ tail)) fragment0109704Acc00100 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0109704Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_001"
  err.flush

noncomputable def fragment0109704Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0109704Field002Value00 : SourceJson := .str (String.ofList ['7', '0', '9', '9', '4', '2', '6', '5', '8', '5', '6', '8', '7', '1', '0', '9', '8', '9', '9', '1', '7', '1', '0', '8', '1', '7', '1', '2', '1', '3', '3', '3', '2', '7', '2', '7', '7', '3', '8', '6', '8', '4', '7', '/', '4', '1', '6', '3', '7', '1', '9', '8', '4', '1', '5', '5', '2', '7', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0109704Acc00300 : List (String × SourceJson) := (fragment0109704Field002Key00, fragment0109704Field002Value00) :: fragment0109704Acc00200
noncomputable def fragment0109704Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '0', '9', '9', '4', '2', '6', '5', '8', '5', '6', '8', '7', '1', '0', '9', '8', '9', '9', '1', '7', '1', '0', '8', '1', '7', '1', '2', '1', '3', '3', '3', '2', '7', '2', '7', '7', '3', '8', '6', '8', '4', '7', '/', '4', '1', '6', '3', '7', '1', '9', '8', '4', '1', '5', '5', '2', '7', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0109704_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0109704Field002Chars00 ++ tail)) fragment0109704Acc00200 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0109704Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_002"
  err.flush

noncomputable def fragment0109704Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0109704Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0109704Acc00400 : List (String × SourceJson) := (fragment0109704Field003Key00, fragment0109704Field003Value00) :: fragment0109704Acc00300
noncomputable def fragment0109704Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0109704_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0109704Field003Chars00 ++ tail)) fragment0109704Acc00300 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0109704Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_003"
  err.flush

noncomputable def fragment0109704Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0109704Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0109704Acc00500 : List (String × SourceJson) := (fragment0109704Field004Key00, fragment0109704Field004Value00) :: fragment0109704Acc00400
noncomputable def fragment0109704Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0109704_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0109704Field004Chars00 ++ tail)) fragment0109704Acc00400 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0109704Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_004"
  err.flush

noncomputable def fragment0109704Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0109704Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '8', '7', '2', '9', '5', '0', '6', '3', '2', '4', '6', '0', '9', '/', '9', '4', '1', '4', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '7', '8', '7', '5', '3', '9', '0', '1', '1', '7', '/', '2', '9', '4', '2', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '5', '9', '7', '4', '5', '9', '4', '7', '0', '6', '8', '9', '/', '8', '4', '7', '3', '0', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '8', '8', '3', '5', '4', '8', '1', '9', '4', '4', '7', '/', '3', '5', '3', '0', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '3', '7', '9', '5', '1', '2', '4', '7', '0', '1', '/', '2', '7', '5', '8', '1', '5', '3', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['3', '2', '2', '6', '5', '7', '6', '4', '8', '3', '8', '4', '9', '/', '4', '2', '3', '6', '5', '2', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '5', '7', '7', '5', '0', '8', '9', '8', '4', '8', '4', '9', '/', '4', '2', '3', '6', '5', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '2', '5', '5', '0', '7', '7', '8', '0', '8', '7', '0', '1', '/', '4', '2', '3', '6', '5', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '7', '3', '6', '1', '2', '4', '5', '0', '3', '7', '4', '1', '/', '4', '2', '3', '6', '5', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '2', '0', '9', '7', '5', '8', '4', '9', '9', '8', '3', '7', '/', '5', '2', '9', '5', '6', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0109704Acc00600 : List (String × SourceJson) := (fragment0109704Field005Key00, fragment0109704Field005Value00) :: fragment0109704Acc00500
noncomputable def fragment0109704Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '7', '2', '9', '5', '0', '6', '3', '2', '4', '6', '0', '9', '/', '9', '4', '1', '4', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '7', '8', '7', '5', '3', '9', '0', '1', '1', '7', '/', '2', '9', '4', '2', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '5', '9', '7', '4', '5', '9', '4', '7', '0', '6', '8', '9', '/', '8', '4', '7', '3', '0', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '8', '8', '3', '5', '4', '8', '1', '9', '4', '4', '7', '/', '3', '5', '3', '0', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '7', '9', '5', '1', '2', '4', '7', '0', '1', '/', '2', '7', '5', '8', '1', '5', '3', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '2', '6', '5', '7', '6', '4', '8', '3', '8', '4', '9', '/', '4', '2', '3', '6', '5', '2', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '5', '7', '7', '5', '0', '8', '9', '8', '4', '8', '4', '9', '/', '4', '2', '3', '6', '5', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '2', '5', '5', '0', '7', '7', '8', '0', '8', '7', '0', '1', '/', '4', '2', '3', '6', '5', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '7', '3', '6', '1', '2', '4', '5', '0', '3', '7', '4', '1', '/', '4', '2', '3', '6', '5', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '0', '9', '7', '5', '8', '4', '9', '9', '8', '3', '7', '/', '5', '2', '9', '5', '6', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0109704_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0109704Field005Chars00 ++ tail)) fragment0109704Acc00500 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0109704Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_005"
  err.flush

noncomputable def fragment0109704Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0109704Field006Value00 : SourceJson := .str (String.ofList ['5', '0', '4', '6', '1', '1', '2', '3', '6', '5', '0', '4', '2', '9', '9', '9', '1', '8', '9', '6', '0', '4', '2', '8', '7', '5', '3', '1', '6', '8', '3', '4', '7', '2', '4', '3', '6', '4', '3', '7', '3', '4', '4', '8', '9', '0', '2', '3', '4', '3', '7', '5', '/', '8', '5', '6', '6', '0', '4', '0', '0', '5', '2', '8', '5', '7', '1', '3', '8', '2', '0', '7', '2', '2', '6', '5', '8', '1', '0', '0', '9', '8', '3', '3', '7', '7', '8', '9', '2', '6', '1', '1', '5', '4', '1', '7', '1', '2', '5', '5', '6', '0', '8', '6', '3', '6', '5', '6', '9', '0', '7', '2', '7', '9', '2', '5', '1', '2'])
noncomputable def fragment0109704Acc00700 : List (String × SourceJson) := (fragment0109704Field006Key00, fragment0109704Field006Value00) :: fragment0109704Acc00600
noncomputable def fragment0109704Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '0', '4', '6', '1', '1', '2', '3', '6', '5', '0', '4', '2', '9', '9', '9', '1', '8', '9', '6', '0', '4', '2', '8', '7', '5', '3', '1', '6', '8', '3', '4', '7', '2', '4', '3', '6', '4', '3', '7', '3', '4', '4', '8', '9', '0', '2', '3', '4', '3', '7', '5', '/', '8', '5', '6', '6', '0', '4', '0', '0', '5', '2', '8', '5', '7', '1', '3', '8', '2', '0', '7', '2', '2', '6', '5', '8', '1', '0', '0', '9', '8', '3', '3', '7', '7', '8', '9', '2', '6', '1', '1', '5', '4', '1', '7', '1', '2', '5', '5', '6', '0', '8', '6', '3', '6', '5', '6', '9', '0', '7', '2', '7', '9', '2', '5', '1', '2', '"', ',']

theorem object_fragment0109704_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0109704Field006Chars00 ++ tail)) fragment0109704Acc00600 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0109704Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_006"
  err.flush

noncomputable def fragment0109704Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0109704Field007Value00 : SourceJson := .str (String.ofList ['2', '2', '9', '4', '0', '8', '5', '1', '6', '4', '3', '6', '0', '2', '0', '8', '5', '7', '0', '4', '8', '6', '6', '3', '5', '4', '0', '6', '5', '3', '6', '3', '8', '8', '7', '5', '2', '2', '5', '4', '2', '8', '4', '1', '2', '0', '9', '8', '0', '5', '4', '9', '7', '9', '4', '3', '3', '5', '9', '5', '1', '6', '1', '2', '6', '9', '7', '5', '7', '1', '8', '8', '9', '1', '3', '4', '4', '3', '0', '0', '9', '3', '5', '6', '7', '0', '0', '8', '1', '2', '8', '2', '5', '6', '0', '6', '5', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '2', '3', '9', '9', '6', '6', '7', '2', '7', '7', '0', '6', '2', '6', '0', '6', '0', '2', '6', '0', '5', '9', '1', '5', '2', '7', '5', '9', '8', '7', '0', '8', '0', '4', '9', '1', '0', '8', '6', '7', '6', '4', '8', '4', '8', '9', '1', '5', '7', '6', '7', '0', '5', '6', '8', '2', '3', '0', '4', '4', '7', '4', '6', '4', '8', '3', '3', '2', '5', '7', '1', '5', '8', '3', '1', '8', '8', '1', '2', '9', '7', '9', '2', '5', '6', '6', '7', '7', '0', '8', '2', '1', '0', '3', '7', '5', '4', '5', '9', '2', '8', '1', '3', '6', '2', '8', '9', '7', '7', '9', '2', '3', '5', '8', '7', '0', '0', '8', '7', '7', '8', '1', '2', '1', '8', '9', '7', '8', '2', '5', '1'])
noncomputable def fragment0109704Acc00800 : List (String × SourceJson) := (fragment0109704Field007Key00, fragment0109704Field007Value00) :: fragment0109704Acc00700
noncomputable def fragment0109704Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '9', '4', '0', '8', '5', '1', '6', '4', '3', '6', '0', '2', '0', '8', '5', '7', '0', '4', '8', '6', '6', '3', '5', '4', '0', '6', '5', '3', '6', '3', '8', '8', '7', '5', '2', '2', '5', '4', '2', '8', '4', '1', '2', '0', '9', '8', '0', '5', '4', '9', '7', '9', '4', '3', '3', '5', '9', '5', '1', '6', '1', '2', '6', '9', '7', '5', '7', '1', '8', '8', '9', '1', '3', '4', '4', '3', '0', '0', '9', '3', '5', '6', '7', '0', '0', '8', '1', '2', '8', '2', '5', '6', '0', '6', '5', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '2', '3', '9', '9', '6', '6', '7', '2', '7', '7', '0', '6', '2', '6', '0', '6', '0', '2', '6', '0', '5', '9', '1', '5', '2', '7', '5', '9', '8', '7', '0', '8', '0', '4', '9', '1', '0', '8', '6', '7', '6', '4', '8', '4', '8', '9', '1', '5', '7', '6', '7', '0', '5', '6', '8', '2', '3', '0', '4', '4', '7', '4', '6', '4', '8', '3', '3', '2', '5', '7', '1', '5', '8', '3', '1', '8', '8', '1', '2', '9', '7', '9', '2', '5', '6', '6', '7', '7', '0', '8', '2', '1', '0', '3', '7', '5', '4', '5', '9', '2', '8', '1', '3', '6', '2', '8', '9', '7', '7', '9', '2', '3', '5', '8', '7', '0', '0', '8', '7', '7', '8', '1', '2', '1', '8', '9', '7', '8', '2', '5', '1', '"', ',']

theorem object_fragment0109704_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0109704Field007Chars00 ++ tail)) fragment0109704Acc00700 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0109704Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_007"
  err.flush

noncomputable def fragment0109704Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0109704Field008Value00 : SourceJson := .str (String.ofList ['4', '6', '6', '7', '1', '9', '9', '8', '7', '3', '6', '3', '9', '5', '9', '5'])
noncomputable def fragment0109704Acc00900 : List (String × SourceJson) := (fragment0109704Field008Key00, fragment0109704Field008Value00) :: fragment0109704Acc00800
noncomputable def fragment0109704Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '6', '7', '1', '9', '9', '8', '7', '3', '6', '3', '9', '5', '9', '5', '"', ',']

theorem object_fragment0109704_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0109704Field008Chars00 ++ tail)) fragment0109704Acc00800 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0109704Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_008"
  err.flush

noncomputable def fragment0109704Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0109704Field009Value00 : SourceJson := .str (String.ofList ['1', '7', '7', '4', '9', '6', '8', '1', '9', '1', '3', '6', '8', '3', '9', '6', '7'])
noncomputable def fragment0109704Acc01000 : List (String × SourceJson) := (fragment0109704Field009Key00, fragment0109704Field009Value00) :: fragment0109704Acc00900
noncomputable def fragment0109704Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '7', '4', '9', '6', '8', '1', '9', '1', '3', '6', '8', '3', '9', '6', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0109704_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0109704Field009Chars00 ++ tail)) fragment0109704Acc00900 =
      .ok (.obj (fragment0109704Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0109704_object_field_009"
  err.flush

noncomputable def fragment0109704Chars : List Char := '{' :: (fragment0109704Field000Chars00 ++ fragment0109704Field001Chars00 ++ fragment0109704Field002Chars00 ++ fragment0109704Field003Chars00 ++ fragment0109704Field004Chars00 ++ fragment0109704Field005Chars00 ++ fragment0109704Field006Chars00 ++ fragment0109704Field007Chars00 ++ fragment0109704Field008Chars00 ++ fragment0109704Field009Chars00)
noncomputable def fragment0109704Value : SourceJson := .obj (fragment0109704Acc01000.reverse)

theorem value_fragment0109704 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 265) (fragment0109704Chars ++ tail) =
      .ok (fragment0109704Value, tail) := by
  have hinput : fragment0109704Chars ++ tail = '{' :: (fragment0109704Field000Chars00 ++ (fragment0109704Field001Chars00 ++ (fragment0109704Field002Chars00 ++ (fragment0109704Field003Chars00 ++ (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0109704Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 265) (fragment0109704Chars ++ tail) =
        SourceJson.value (fuel + 265) ('{' :: (fragment0109704Field000Chars00 ++ (fragment0109704Field001Chars00 ++ (fragment0109704Field002Chars00 ++ (fragment0109704Field003Chars00 ++ (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 265)) hinput
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0109704Field000Chars00 ++ (fragment0109704Field001Chars00 ++ (fragment0109704Field002Chars00 ++ (fragment0109704Field003Chars00 ++ (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))))))))))) fragment0109704Acc00000 := by rfl
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0109704Field001Chars00 ++ (fragment0109704Field002Chars00 ++ (fragment0109704Field003Chars00 ++ (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail))))))))))) fragment0109704Acc00100 := object_fragment0109704_field_000 fuel (fragment0109704Field001Chars00 ++ (fragment0109704Field002Chars00 ++ (fragment0109704Field003Chars00 ++ (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0109704Field002Chars00 ++ (fragment0109704Field003Chars00 ++ (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))))))))) fragment0109704Acc00200 := object_fragment0109704_field_001 fuel (fragment0109704Field002Chars00 ++ (fragment0109704Field003Chars00 ++ (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0109704Field003Chars00 ++ (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail))))))))) fragment0109704Acc00300 := object_fragment0109704_field_002 fuel (fragment0109704Field003Chars00 ++ (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))))))) fragment0109704Acc00400 := object_fragment0109704_field_003 fuel (fragment0109704Field004Chars00 ++ (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail))))))) fragment0109704Acc00500 := object_fragment0109704_field_004 fuel (fragment0109704Field005Chars00 ++ (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))))) fragment0109704Acc00600 := object_fragment0109704_field_005 fuel (fragment0109704Field006Chars00 ++ (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail))))) fragment0109704Acc00700 := object_fragment0109704_field_006 fuel (fragment0109704Field007Chars00 ++ (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))) fragment0109704Acc00800 := object_fragment0109704_field_007 fuel (fragment0109704Field008Chars00 ++ (fragment0109704Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0109704Field009Chars00 ++ (tail))) fragment0109704Acc00900 := object_fragment0109704_field_008 fuel (fragment0109704Field009Chars00 ++ (tail))
    _ = .ok (fragment0109704Value, tail) := object_fragment0109704_field_009 fuel (tail)

noncomputable def fragment0111367Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0111367Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0111367Field000Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0111367Acc00100 : List (String × SourceJson) := (fragment0111367Field000Key00, fragment0111367Field000Value00) :: fragment0111367Acc00000
noncomputable def fragment0111367Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', ',']

theorem object_fragment0111367_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0111367Field000Chars00 ++ tail)) fragment0111367Acc00000 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0111367Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_000"
  err.flush

noncomputable def fragment0111367Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0111367Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0111367Acc00200 : List (String × SourceJson) := (fragment0111367Field001Key00, fragment0111367Field001Value00) :: fragment0111367Acc00100
noncomputable def fragment0111367Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0111367_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0111367Field001Chars00 ++ tail)) fragment0111367Acc00100 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0111367Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_001"
  err.flush

noncomputable def fragment0111367Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0111367Field002Value00 : SourceJson := .str (String.ofList ['9', '0', '8', '8', '1', '2', '4', '4', '4', '3', '7', '9', '1', '8', '7', '9', '0', '5', '0', '2', '1', '5', '2', '5', '0', '7', '2', '0', '2', '0', '1', '9', '9', '3', '8', '5', '5', '5', '7', '/', '3', '5', '0', '5', '7', '7', '3', '5', '4', '5', '8', '3', '5', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0111367Acc00300 : List (String × SourceJson) := (fragment0111367Field002Key00, fragment0111367Field002Value00) :: fragment0111367Acc00200
noncomputable def fragment0111367Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '0', '8', '8', '1', '2', '4', '4', '4', '3', '7', '9', '1', '8', '7', '9', '0', '5', '0', '2', '1', '5', '2', '5', '0', '7', '2', '0', '2', '0', '1', '9', '9', '3', '8', '5', '5', '5', '7', '/', '3', '5', '0', '5', '7', '7', '3', '5', '4', '5', '8', '3', '5', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0111367_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0111367Field002Chars00 ++ tail)) fragment0111367Acc00200 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0111367Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_002"
  err.flush

noncomputable def fragment0111367Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0111367Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0111367Acc00400 : List (String × SourceJson) := (fragment0111367Field003Key00, fragment0111367Field003Value00) :: fragment0111367Acc00300
noncomputable def fragment0111367Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0111367_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0111367Field003Chars00 ++ tail)) fragment0111367Acc00300 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0111367Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_003"
  err.flush

noncomputable def fragment0111367Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0111367Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0111367Acc00500 : List (String × SourceJson) := (fragment0111367Field004Key00, fragment0111367Field004Value00) :: fragment0111367Acc00400
noncomputable def fragment0111367Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0111367_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0111367Field004Chars00 ++ tail)) fragment0111367Acc00400 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0111367Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_004"
  err.flush

noncomputable def fragment0111367Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0111367Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '6', '3', '9', '1', '6', '5', '7', '5', '3', '4', '4', '1', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '9', '3', '7', '8', '7', '7', '5', '9', '9', '7', '1', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '9', '9', '7', '6', '0', '9', '9', '6', '5', '9', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '9', '8', '0', '7', '7', '5', '0', '2', '4', '7', '0', '3', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '9', '6', '2', '1', '0', '8', '4', '4', '6', '4', '4', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '6', '0', '9', '6', '3', '9', '3', '1', '6', '6', '9', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '1', '6', '6', '9', '5', '9', '3', '3', '0', '8', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '7', '0', '6', '9', '7', '4', '1', '6', '4', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '1', '3', '8', '5', '2', '8', '4', '6', '6', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '1', '2', '8', '4', '4', '7', '1', '6', '6', '7', '1', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0111367Acc00600 : List (String × SourceJson) := (fragment0111367Field005Key00, fragment0111367Field005Value00) :: fragment0111367Acc00500
noncomputable def fragment0111367Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '3', '9', '1', '6', '5', '7', '5', '3', '4', '4', '1', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '9', '3', '7', '8', '7', '7', '5', '9', '9', '7', '1', '/', '1', '1', '3', '2', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '2', '9', '9', '7', '6', '0', '9', '9', '6', '5', '9', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '9', '8', '0', '7', '7', '5', '0', '2', '4', '7', '0', '3', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '9', '6', '2', '1', '0', '8', '4', '4', '6', '4', '4', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '0', '9', '6', '3', '9', '3', '1', '6', '6', '9', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '1', '6', '6', '9', '5', '9', '3', '3', '0', '8', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '7', '0', '6', '9', '7', '4', '1', '6', '4', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '1', '3', '8', '5', '2', '8', '4', '6', '6', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '1', '2', '8', '4', '4', '7', '1', '6', '6', '7', '1', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0111367_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0111367Field005Chars00 ++ tail)) fragment0111367Acc00500 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0111367Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_005"
  err.flush

noncomputable def fragment0111367Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0111367Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '2', '4', '6', '6', '0', '3', '2', '1', '3', '3', '7', '9', '2', '6', '2', '1', '4', '0', '6', '8', '7', '3', '2', '2', '1', '2', '9', '8', '8', '7', '4', '8', '8', '2', '9', '1', '7', '1', '4', '9', '7', '6', '5', '6', '2', '5', '0', '/', '2', '2', '8', '3', '3', '2', '6', '5', '3', '5', '7', '8', '1', '2', '0', '9', '6', '3', '3', '1', '0', '0', '0', '5', '2', '8', '5', '0', '5', '4', '9', '2', '3', '0', '5', '0', '2', '5', '3', '2', '7', '5', '4', '7', '6', '4', '6', '3', '7', '5', '1', '0', '5', '4', '5', '9', '3', '9', '4', '0', '5', '3', '0', '4', '0', '7'])
noncomputable def fragment0111367Acc00700 : List (String × SourceJson) := (fragment0111367Field006Key00, fragment0111367Field006Value00) :: fragment0111367Acc00600
noncomputable def fragment0111367Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '2', '4', '6', '6', '0', '3', '2', '1', '3', '3', '7', '9', '2', '6', '2', '1', '4', '0', '6', '8', '7', '3', '2', '2', '1', '2', '9', '8', '8', '7', '4', '8', '8', '2', '9', '1', '7', '1', '4', '9', '7', '6', '5', '6', '2', '5', '0', '/', '2', '2', '8', '3', '3', '2', '6', '5', '3', '5', '7', '8', '1', '2', '0', '9', '6', '3', '3', '1', '0', '0', '0', '5', '2', '8', '5', '0', '5', '4', '9', '2', '3', '0', '5', '0', '2', '5', '3', '2', '7', '5', '4', '7', '6', '4', '6', '3', '7', '5', '1', '0', '5', '4', '5', '9', '3', '9', '4', '0', '5', '3', '0', '4', '0', '7', '"', ',']

theorem object_fragment0111367_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0111367Field006Chars00 ++ tail)) fragment0111367Acc00600 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0111367Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_006"
  err.flush

noncomputable def fragment0111367Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0111367Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '6', '4', '9', '5', '2', '4', '4', '1', '6', '1', '6', '4', '3', '5', '6', '0', '2', '3', '7', '9', '9', '9', '1', '6', '0', '0', '2', '5', '4', '6', '6', '1', '7', '1', '6', '3', '1', '4', '6', '9', '5', '7', '1', '1', '9', '5', '7', '7', '3', '4', '0', '6', '3', '8', '1', '4', '6', '3', '0', '1', '7', '5', '2', '1', '7', '1', '2', '1', '5', '9', '3', '7', '5', '2', '4', '8', '8', '5', '4', '5', '8', '5', '8', '2', '0', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '2', '9', '5', '6', '1', '0', '9', '2', '0', '6', '8', '5', '3', '3', '4', '9', '8', '3', '6', '9', '2', '8', '7', '8', '5', '5', '5', '6', '8', '0', '2', '0', '7', '6', '9', '7', '3', '5', '1', '0', '5', '8', '7', '9', '7', '1', '6', '7', '9', '2', '9', '3', '4', '4', '8', '5', '1', '8', '3', '2', '0', '2', '8', '7', '0', '6', '0', '9', '5', '9', '6', '1', '9', '4', '0', '6', '5', '6', '1', '8', '4', '1', '8', '3', '1', '4', '2', '4', '0', '1', '2', '6', '3', '5', '6', '5', '7', '4', '3', '6', '2', '0', '3', '5', '8', '8', '6', '7', '9', '0', '5', '4', '9', '6', '3', '1', '6', '6', '8', '3', '3', '5', '8', '0', '0', '0', '1', '5', '7'])
noncomputable def fragment0111367Acc00800 : List (String × SourceJson) := (fragment0111367Field007Key00, fragment0111367Field007Value00) :: fragment0111367Acc00700
noncomputable def fragment0111367Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '6', '4', '9', '5', '2', '4', '4', '1', '6', '1', '6', '4', '3', '5', '6', '0', '2', '3', '7', '9', '9', '9', '1', '6', '0', '0', '2', '5', '4', '6', '6', '1', '7', '1', '6', '3', '1', '4', '6', '9', '5', '7', '1', '1', '9', '5', '7', '7', '3', '4', '0', '6', '3', '8', '1', '4', '6', '3', '0', '1', '7', '5', '2', '1', '7', '1', '2', '1', '5', '9', '3', '7', '5', '2', '4', '8', '8', '5', '4', '5', '8', '5', '8', '2', '0', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '2', '9', '5', '6', '1', '0', '9', '2', '0', '6', '8', '5', '3', '3', '4', '9', '8', '3', '6', '9', '2', '8', '7', '8', '5', '5', '5', '6', '8', '0', '2', '0', '7', '6', '9', '7', '3', '5', '1', '0', '5', '8', '7', '9', '7', '1', '6', '7', '9', '2', '9', '3', '4', '4', '8', '5', '1', '8', '3', '2', '0', '2', '8', '7', '0', '6', '0', '9', '5', '9', '6', '1', '9', '4', '0', '6', '5', '6', '1', '8', '4', '1', '8', '3', '1', '4', '2', '4', '0', '1', '2', '6', '3', '5', '6', '5', '7', '4', '3', '6', '2', '0', '3', '5', '8', '8', '6', '7', '9', '0', '5', '4', '9', '6', '3', '1', '6', '6', '8', '3', '3', '5', '8', '0', '0', '0', '1', '5', '7', '"', ',']

theorem object_fragment0111367_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0111367Field007Chars00 ++ tail)) fragment0111367Acc00700 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0111367Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_007"
  err.flush

noncomputable def fragment0111367Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0111367Field008Value00 : SourceJson := .str (String.ofList ['6', '6', '7', '8', '2', '9', '5', '8', '2', '5', '5', '9'])
noncomputable def fragment0111367Acc00900 : List (String × SourceJson) := (fragment0111367Field008Key00, fragment0111367Field008Value00) :: fragment0111367Acc00800
noncomputable def fragment0111367Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '7', '8', '2', '9', '5', '8', '2', '5', '5', '9', '"', ',']

theorem object_fragment0111367_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0111367Field008Chars00 ++ tail)) fragment0111367Acc00800 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0111367Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_008"
  err.flush

noncomputable def fragment0111367Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0111367Field009Value00 : SourceJson := .str (String.ofList ['2', '4', '9', '0', '9', '5', '1', '9', '3', '3', '5', '6', '5'])
noncomputable def fragment0111367Acc01000 : List (String × SourceJson) := (fragment0111367Field009Key00, fragment0111367Field009Value00) :: fragment0111367Acc00900
noncomputable def fragment0111367Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '9', '0', '9', '5', '1', '9', '3', '3', '5', '6', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0111367_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0111367Field009Chars00 ++ tail)) fragment0111367Acc00900 =
      .ok (.obj (fragment0111367Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0111367_object_field_009"
  err.flush

noncomputable def fragment0111367Chars : List Char := '{' :: (fragment0111367Field000Chars00 ++ fragment0111367Field001Chars00 ++ fragment0111367Field002Chars00 ++ fragment0111367Field003Chars00 ++ fragment0111367Field004Chars00 ++ fragment0111367Field005Chars00 ++ fragment0111367Field006Chars00 ++ fragment0111367Field007Chars00 ++ fragment0111367Field008Chars00 ++ fragment0111367Field009Chars00)
noncomputable def fragment0111367Value : SourceJson := .obj (fragment0111367Acc01000.reverse)

theorem value_fragment0111367 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 256) (fragment0111367Chars ++ tail) =
      .ok (fragment0111367Value, tail) := by
  have hinput : fragment0111367Chars ++ tail = '{' :: (fragment0111367Field000Chars00 ++ (fragment0111367Field001Chars00 ++ (fragment0111367Field002Chars00 ++ (fragment0111367Field003Chars00 ++ (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0111367Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 256) (fragment0111367Chars ++ tail) =
        SourceJson.value (fuel + 256) ('{' :: (fragment0111367Field000Chars00 ++ (fragment0111367Field001Chars00 ++ (fragment0111367Field002Chars00 ++ (fragment0111367Field003Chars00 ++ (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 256)) hinput
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0111367Field000Chars00 ++ (fragment0111367Field001Chars00 ++ (fragment0111367Field002Chars00 ++ (fragment0111367Field003Chars00 ++ (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))))))))))) fragment0111367Acc00000 := by rfl
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0111367Field001Chars00 ++ (fragment0111367Field002Chars00 ++ (fragment0111367Field003Chars00 ++ (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail))))))))))) fragment0111367Acc00100 := object_fragment0111367_field_000 fuel (fragment0111367Field001Chars00 ++ (fragment0111367Field002Chars00 ++ (fragment0111367Field003Chars00 ++ (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0111367Field002Chars00 ++ (fragment0111367Field003Chars00 ++ (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))))))))) fragment0111367Acc00200 := object_fragment0111367_field_001 fuel (fragment0111367Field002Chars00 ++ (fragment0111367Field003Chars00 ++ (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0111367Field003Chars00 ++ (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail))))))))) fragment0111367Acc00300 := object_fragment0111367_field_002 fuel (fragment0111367Field003Chars00 ++ (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))))))) fragment0111367Acc00400 := object_fragment0111367_field_003 fuel (fragment0111367Field004Chars00 ++ (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail))))))) fragment0111367Acc00500 := object_fragment0111367_field_004 fuel (fragment0111367Field005Chars00 ++ (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))))) fragment0111367Acc00600 := object_fragment0111367_field_005 fuel (fragment0111367Field006Chars00 ++ (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail))))) fragment0111367Acc00700 := object_fragment0111367_field_006 fuel (fragment0111367Field007Chars00 ++ (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))) fragment0111367Acc00800 := object_fragment0111367_field_007 fuel (fragment0111367Field008Chars00 ++ (fragment0111367Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0111367Field009Chars00 ++ (tail))) fragment0111367Acc00900 := object_fragment0111367_field_008 fuel (fragment0111367Field009Chars00 ++ (tail))
    _ = .ok (fragment0111367Value, tail) := object_fragment0111367_field_009 fuel (tail)

noncomputable def fragment0113001Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0113001Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0113001Field000Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0113001Acc00100 : List (String × SourceJson) := (fragment0113001Field000Key00, fragment0113001Field000Value00) :: fragment0113001Acc00000
noncomputable def fragment0113001Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', ',']

theorem object_fragment0113001_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0113001Field000Chars00 ++ tail)) fragment0113001Acc00000 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0113001Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_000"
  err.flush

noncomputable def fragment0113001Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0113001Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0113001Acc00200 : List (String × SourceJson) := (fragment0113001Field001Key00, fragment0113001Field001Value00) :: fragment0113001Acc00100
noncomputable def fragment0113001Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0113001_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0113001Field001Chars00 ++ tail)) fragment0113001Acc00100 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0113001Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_001"
  err.flush

noncomputable def fragment0113001Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0113001Field002Value00 : SourceJson := .str (String.ofList ['2', '9', '8', '1', '1', '3', '2', '0', '1', '5', '3', '5', '5', '0', '9', '9', '3', '7', '0', '5', '0', '0', '9', '8', '4', '8', '5', '8', '9', '9', '8', '8', '2', '7', '0', '8', '5', '1', '0', '9', '8', '1', '7', '0', '9', '/', '1', '1', '2', '1', '8', '4', '7', '5', '3', '4', '6', '6', '7', '4', '3', '1', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0113001Acc00300 : List (String × SourceJson) := (fragment0113001Field002Key00, fragment0113001Field002Value00) :: fragment0113001Acc00200
noncomputable def fragment0113001Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '9', '8', '1', '1', '3', '2', '0', '1', '5', '3', '5', '5', '0', '9', '9', '3', '7', '0', '5', '0', '0', '9', '8', '4', '8', '5', '8', '9', '9', '8', '8', '2', '7', '0', '8', '5', '1', '0', '9', '8', '1', '7', '0', '9', '/', '1', '1', '2', '1', '8', '4', '7', '5', '3', '4', '6', '6', '7', '4', '3', '1', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0113001_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0113001Field002Chars00 ++ tail)) fragment0113001Acc00200 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0113001Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_002"
  err.flush

noncomputable def fragment0113001Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0113001Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0113001Acc00400 : List (String × SourceJson) := (fragment0113001Field003Key00, fragment0113001Field003Value00) :: fragment0113001Acc00300
noncomputable def fragment0113001Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0113001_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0113001Field003Chars00 ++ tail)) fragment0113001Acc00300 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0113001Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_003"
  err.flush

noncomputable def fragment0113001Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0113001Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0113001Acc00500 : List (String × SourceJson) := (fragment0113001Field004Key00, fragment0113001Field004Value00) :: fragment0113001Acc00400
noncomputable def fragment0113001Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0113001_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0113001Field004Chars00 ++ tail)) fragment0113001Acc00400 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0113001Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_004"
  err.flush

noncomputable def fragment0113001Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0113001Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '1', '4', '4', '3', '6', '9', '6', '5', '2', '4', '7', '9', '/', '7', '5', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '8', '0', '7', '8', '4', '3', '2', '3', '4', '9', '9', '/', '7', '5', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '9', '9', '7', '6', '0', '9', '9', '6', '5', '9', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '5', '2', '8', '1', '6', '3', '8', '0', '0', '1', '3', '/', '4', '2', '4', '6', '5', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '9', '6', '2', '1', '0', '8', '4', '4', '6', '4', '4', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '6', '0', '9', '6', '3', '9', '3', '1', '6', '6', '9', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '1', '6', '6', '9', '5', '9', '3', '3', '0', '8', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '7', '0', '6', '9', '7', '4', '1', '6', '4', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '9', '3', '5', '3', '4', '2', '5', '7', '4', '5', '9', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '6', '1', '4', '0', '2', '3', '7', '7', '8', '3', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0113001Acc00600 : List (String × SourceJson) := (fragment0113001Field005Key00, fragment0113001Field005Value00) :: fragment0113001Acc00500
noncomputable def fragment0113001Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '4', '4', '3', '6', '9', '6', '5', '2', '4', '7', '9', '/', '7', '5', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '8', '0', '7', '8', '4', '3', '2', '3', '4', '9', '9', '/', '7', '5', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '2', '9', '9', '7', '6', '0', '9', '9', '6', '5', '9', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '5', '2', '8', '1', '6', '3', '8', '0', '0', '1', '3', '/', '4', '2', '4', '6', '5', '1', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '9', '6', '2', '1', '0', '8', '4', '4', '6', '4', '4', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '0', '9', '6', '3', '9', '3', '1', '6', '6', '9', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '1', '6', '6', '9', '5', '9', '3', '3', '0', '8', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '7', '0', '6', '9', '7', '4', '1', '6', '4', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '9', '3', '5', '3', '4', '2', '5', '7', '4', '5', '9', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '6', '1', '4', '0', '2', '3', '7', '7', '8', '3', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0113001_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0113001Field005Chars00 ++ tail)) fragment0113001Acc00500 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0113001Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_005"
  err.flush

noncomputable def fragment0113001Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0113001Field006Value00 : SourceJson := .str (String.ofList ['3', '4', '7', '2', '3', '5', '1', '8', '5', '4', '2', '9', '1', '5', '0', '5', '4', '9', '9', '3', '7', '3', '9', '1', '1', '7', '0', '0', '0', '5', '8', '5', '0', '2', '4', '2', '4', '5', '1', '3', '8', '6', '7', '5', '9', '7', '0', '7', '7', '7', '3', '4', '3', '7', '5', '/', '4', '0', '1', '8', '6', '5', '4', '7', '0', '2', '9', '7', '4', '9', '2', '8', '9', '5', '4', '2', '5', '6', '0', '9', '3', '0', '1', '6', '9', '6', '6', '6', '4', '5', '6', '8', '4', '4', '5', '7', '6', '4', '8', '3', '8', '5', '7', '6', '2', '0', '1', '8', '5', '6', '0', '8', '5', '3', '3', '5', '3', '3', '3', '5', '1', '6', '3', '2'])
noncomputable def fragment0113001Acc00700 : List (String × SourceJson) := (fragment0113001Field006Key00, fragment0113001Field006Value00) :: fragment0113001Acc00600
noncomputable def fragment0113001Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '7', '2', '3', '5', '1', '8', '5', '4', '2', '9', '1', '5', '0', '5', '4', '9', '9', '3', '7', '3', '9', '1', '1', '7', '0', '0', '0', '5', '8', '5', '0', '2', '4', '2', '4', '5', '1', '3', '8', '6', '7', '5', '9', '7', '0', '7', '7', '7', '3', '4', '3', '7', '5', '/', '4', '0', '1', '8', '6', '5', '4', '7', '0', '2', '9', '7', '4', '9', '2', '8', '9', '5', '4', '2', '5', '6', '0', '9', '3', '0', '1', '6', '9', '6', '6', '6', '4', '5', '6', '8', '4', '4', '5', '7', '6', '4', '8', '3', '8', '5', '7', '6', '2', '0', '1', '8', '5', '6', '0', '8', '5', '3', '3', '5', '3', '3', '3', '5', '1', '6', '3', '2', '"', ',']

theorem object_fragment0113001_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0113001Field006Chars00 ++ tail)) fragment0113001Acc00600 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0113001Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_006"
  err.flush

noncomputable def fragment0113001Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0113001Field007Value00 : SourceJson := .str (String.ofList ['1', '7', '0', '6', '7', '0', '6', '3', '2', '4', '0', '2', '0', '7', '8', '6', '6', '3', '3', '4', '2', '3', '4', '4', '5', '8', '2', '0', '7', '1', '9', '3', '1', '7', '9', '9', '9', '6', '9', '5', '3', '6', '2', '7', '9', '4', '9', '2', '5', '4', '5', '9', '1', '0', '1', '9', '8', '2', '7', '0', '1', '4', '8', '1', '0', '5', '8', '4', '0', '4', '9', '0', '1', '4', '7', '0', '3', '6', '9', '9', '8', '2', '8', '3', '3', '0', '2', '4', '0', '0', '2', '6', '0', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '1', '9', '8', '6', '5', '9', '2', '2', '4', '3', '9', '3', '2', '9', '4', '9', '2', '9', '0', '9', '0', '7', '6', '6', '9', '6', '6', '3', '4', '7', '4', '7', '3', '3', '3', '8', '3', '2', '3', '8', '6', '5', '2', '5', '1', '6', '9', '3', '1', '6', '1', '2', '7', '1', '5', '9', '7', '0', '1', '7', '8', '5', '6', '9', '3', '7', '3', '6', '4', '8', '3', '0', '0', '9', '5', '4', '8', '1', '8', '1', '0', '8', '8', '4', '5', '7', '7', '4', '8', '2', '3', '6', '9', '0', '9', '7', '2', '0', '9', '6', '8', '6', '0', '1', '1', '0', '3', '8', '2', '1', '9', '3', '3', '1', '6', '9', '8', '3', '9', '6', '7', '2', '1', '9', '9', '5', '3', '6', '7'])
noncomputable def fragment0113001Acc00800 : List (String × SourceJson) := (fragment0113001Field007Key00, fragment0113001Field007Value00) :: fragment0113001Acc00700
noncomputable def fragment0113001Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '0', '6', '7', '0', '6', '3', '2', '4', '0', '2', '0', '7', '8', '6', '6', '3', '3', '4', '2', '3', '4', '4', '5', '8', '2', '0', '7', '1', '9', '3', '1', '7', '9', '9', '9', '6', '9', '5', '3', '6', '2', '7', '9', '4', '9', '2', '5', '4', '5', '9', '1', '0', '1', '9', '8', '2', '7', '0', '1', '4', '8', '1', '0', '5', '8', '4', '0', '4', '9', '0', '1', '4', '7', '0', '3', '6', '9', '9', '8', '2', '8', '3', '3', '0', '2', '4', '0', '0', '2', '6', '0', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '1', '9', '8', '6', '5', '9', '2', '2', '4', '3', '9', '3', '2', '9', '4', '9', '2', '9', '0', '9', '0', '7', '6', '6', '9', '6', '6', '3', '4', '7', '4', '7', '3', '3', '3', '8', '3', '2', '3', '8', '6', '5', '2', '5', '1', '6', '9', '3', '1', '6', '1', '2', '7', '1', '5', '9', '7', '0', '1', '7', '8', '5', '6', '9', '3', '7', '3', '6', '4', '8', '3', '0', '0', '9', '5', '4', '8', '1', '8', '1', '0', '8', '8', '4', '5', '7', '7', '4', '8', '2', '3', '6', '9', '0', '9', '7', '2', '0', '9', '6', '8', '6', '0', '1', '1', '0', '3', '8', '2', '1', '9', '3', '3', '1', '6', '9', '8', '3', '9', '6', '7', '2', '1', '9', '9', '5', '3', '6', '7', '"', ',']

theorem object_fragment0113001_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0113001Field007Chars00 ++ tail)) fragment0113001Acc00700 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0113001Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_007"
  err.flush

noncomputable def fragment0113001Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0113001Field008Value00 : SourceJson := .str (String.ofList ['6', '8', '4', '5', '7', '7', '4', '9', '5', '0', '8', '7', '7', '4', '0', '6'])
noncomputable def fragment0113001Acc00900 : List (String × SourceJson) := (fragment0113001Field008Key00, fragment0113001Field008Value00) :: fragment0113001Acc00800
noncomputable def fragment0113001Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '8', '4', '5', '7', '7', '4', '9', '5', '0', '8', '7', '7', '4', '0', '6', '"', ',']

theorem object_fragment0113001_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0113001Field008Chars00 ++ tail)) fragment0113001Acc00800 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0113001Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_008"
  err.flush

noncomputable def fragment0113001Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0113001Field009Value00 : SourceJson := .str (String.ofList ['2', '6', '0', '1', '0', '4', '0', '0', '0', '2', '1', '8', '2', '9', '1', '3', '1'])
noncomputable def fragment0113001Acc01000 : List (String × SourceJson) := (fragment0113001Field009Key00, fragment0113001Field009Value00) :: fragment0113001Acc00900
noncomputable def fragment0113001Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '0', '1', '0', '4', '0', '0', '0', '2', '1', '8', '2', '9', '1', '3', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0113001_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0113001Field009Chars00 ++ tail)) fragment0113001Acc00900 =
      .ok (.obj (fragment0113001Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0113001_object_field_009"
  err.flush

noncomputable def fragment0113001Chars : List Char := '{' :: (fragment0113001Field000Chars00 ++ fragment0113001Field001Chars00 ++ fragment0113001Field002Chars00 ++ fragment0113001Field003Chars00 ++ fragment0113001Field004Chars00 ++ fragment0113001Field005Chars00 ++ fragment0113001Field006Chars00 ++ fragment0113001Field007Chars00 ++ fragment0113001Field008Chars00 ++ fragment0113001Field009Chars00)
noncomputable def fragment0113001Value : SourceJson := .obj (fragment0113001Acc01000.reverse)

theorem value_fragment0113001 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 260) (fragment0113001Chars ++ tail) =
      .ok (fragment0113001Value, tail) := by
  have hinput : fragment0113001Chars ++ tail = '{' :: (fragment0113001Field000Chars00 ++ (fragment0113001Field001Chars00 ++ (fragment0113001Field002Chars00 ++ (fragment0113001Field003Chars00 ++ (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0113001Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 260) (fragment0113001Chars ++ tail) =
        SourceJson.value (fuel + 260) ('{' :: (fragment0113001Field000Chars00 ++ (fragment0113001Field001Chars00 ++ (fragment0113001Field002Chars00 ++ (fragment0113001Field003Chars00 ++ (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 260)) hinput
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0113001Field000Chars00 ++ (fragment0113001Field001Chars00 ++ (fragment0113001Field002Chars00 ++ (fragment0113001Field003Chars00 ++ (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))))))))))) fragment0113001Acc00000 := by rfl
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0113001Field001Chars00 ++ (fragment0113001Field002Chars00 ++ (fragment0113001Field003Chars00 ++ (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail))))))))))) fragment0113001Acc00100 := object_fragment0113001_field_000 fuel (fragment0113001Field001Chars00 ++ (fragment0113001Field002Chars00 ++ (fragment0113001Field003Chars00 ++ (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0113001Field002Chars00 ++ (fragment0113001Field003Chars00 ++ (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))))))))) fragment0113001Acc00200 := object_fragment0113001_field_001 fuel (fragment0113001Field002Chars00 ++ (fragment0113001Field003Chars00 ++ (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0113001Field003Chars00 ++ (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail))))))))) fragment0113001Acc00300 := object_fragment0113001_field_002 fuel (fragment0113001Field003Chars00 ++ (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))))))) fragment0113001Acc00400 := object_fragment0113001_field_003 fuel (fragment0113001Field004Chars00 ++ (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail))))))) fragment0113001Acc00500 := object_fragment0113001_field_004 fuel (fragment0113001Field005Chars00 ++ (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))))) fragment0113001Acc00600 := object_fragment0113001_field_005 fuel (fragment0113001Field006Chars00 ++ (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail))))) fragment0113001Acc00700 := object_fragment0113001_field_006 fuel (fragment0113001Field007Chars00 ++ (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))) fragment0113001Acc00800 := object_fragment0113001_field_007 fuel (fragment0113001Field008Chars00 ++ (fragment0113001Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0113001Field009Chars00 ++ (tail))) fragment0113001Acc00900 := object_fragment0113001_field_008 fuel (fragment0113001Field009Chars00 ++ (tail))
    _ = .ok (fragment0113001Value, tail) := object_fragment0113001_field_009 fuel (tail)

noncomputable def fragment0114659Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0114659Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0114659Field000Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0114659Acc00100 : List (String × SourceJson) := (fragment0114659Field000Key00, fragment0114659Field000Value00) :: fragment0114659Acc00000
noncomputable def fragment0114659Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', ',']

theorem object_fragment0114659_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0114659Field000Chars00 ++ tail)) fragment0114659Acc00000 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0114659Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_000"
  err.flush

noncomputable def fragment0114659Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0114659Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0114659Acc00200 : List (String × SourceJson) := (fragment0114659Field001Key00, fragment0114659Field001Value00) :: fragment0114659Acc00100
noncomputable def fragment0114659Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0114659_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0114659Field001Chars00 ++ tail)) fragment0114659Acc00100 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0114659Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_001"
  err.flush

noncomputable def fragment0114659Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0114659Field002Value00 : SourceJson := .str (String.ofList ['9', '0', '8', '7', '6', '8', '1', '1', '3', '8', '2', '1', '8', '3', '8', '3', '3', '4', '8', '1', '1', '7', '0', '9', '9', '3', '7', '5', '2', '2', '9', '6', '1', '2', '2', '5', '7', '9', '7', '/', '4', '6', '7', '4', '3', '6', '4', '7', '2', '7', '7', '8', '0', '9', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0114659Acc00300 : List (String × SourceJson) := (fragment0114659Field002Key00, fragment0114659Field002Value00) :: fragment0114659Acc00200
noncomputable def fragment0114659Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '0', '8', '7', '6', '8', '1', '1', '3', '8', '2', '1', '8', '3', '8', '3', '3', '4', '8', '1', '1', '7', '0', '9', '9', '3', '7', '5', '2', '2', '9', '6', '1', '2', '2', '5', '7', '9', '7', '/', '4', '6', '7', '4', '3', '6', '4', '7', '2', '7', '7', '8', '0', '9', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0114659_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0114659Field002Chars00 ++ tail)) fragment0114659Acc00200 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0114659Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_002"
  err.flush

noncomputable def fragment0114659Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0114659Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0114659Acc00400 : List (String × SourceJson) := (fragment0114659Field003Key00, fragment0114659Field003Value00) :: fragment0114659Acc00300
noncomputable def fragment0114659Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0114659_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0114659Field003Chars00 ++ tail)) fragment0114659Acc00300 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0114659Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_003"
  err.flush

noncomputable def fragment0114659Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0114659Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0114659Acc00500 : List (String × SourceJson) := (fragment0114659Field004Key00, fragment0114659Field004Value00) :: fragment0114659Acc00400
noncomputable def fragment0114659Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '8', '0', '0', '9', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '0', '3', '8', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '0', '9', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0114659_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0114659Field004Chars00 ++ tail)) fragment0114659Acc00400 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0114659Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_004"
  err.flush

noncomputable def fragment0114659Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0114659Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '1', '6', '2', '3', '6', '0', '0', '7', '9', '6', '8', '7', '7', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '3', '2', '8', '4', '4', '8', '0', '9', '9', '3', '7', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '7', '8', '9', '9', '9', '8', '7', '3', '3', '9', '/', '9', '0', '5', '9', '2', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '6', '6', '4', '5', '2', '3', '1', '6', '3', '5', '9', '/', '5', '6', '6', '2', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '8', '1', '9', '2', '5', '0', '8', '9', '0', '9', '0', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '5', '1', '4', '4', '0', '0', '9', '4', '6', '3', '3', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '5', '9', '5', '5', '3', '4', '8', '8', '6', '2', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '3', '2', '6', '0', '1', '4', '9', '0', '5', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '3', '5', '5', '3', '8', '6', '7', '7', '3', '3', '/', '7', '5', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '5', '0', '6', '3', '1', '4', '0', '5', '7', '5', '9', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0114659Acc00600 : List (String × SourceJson) := (fragment0114659Field005Key00, fragment0114659Field005Value00) :: fragment0114659Acc00500
noncomputable def fragment0114659Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '6', '2', '3', '6', '0', '0', '7', '9', '6', '8', '7', '7', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '3', '2', '8', '4', '4', '8', '0', '9', '9', '3', '7', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '7', '8', '9', '9', '9', '8', '7', '3', '3', '9', '/', '9', '0', '5', '9', '2', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '6', '6', '4', '5', '2', '3', '1', '6', '3', '5', '9', '/', '5', '6', '6', '2', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '8', '1', '9', '2', '5', '0', '8', '9', '0', '9', '0', '7', '/', '6', '7', '9', '4', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '5', '1', '4', '4', '0', '0', '9', '4', '6', '3', '3', '/', '4', '5', '2', '9', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '5', '9', '5', '5', '3', '4', '8', '8', '6', '2', '9', '/', '3', '3', '9', '7', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '3', '2', '6', '0', '1', '4', '9', '0', '5', '9', '/', '3', '7', '7', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '3', '5', '5', '3', '8', '6', '7', '7', '3', '3', '/', '7', '5', '4', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '5', '0', '6', '3', '1', '4', '0', '5', '7', '5', '9', '/', '2', '2', '6', '4', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0114659_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0114659Field005Chars00 ++ tail)) fragment0114659Acc00500 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0114659Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_005"
  err.flush

noncomputable def fragment0114659Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0114659Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '6', '4', '3', '6', '2', '6', '9', '5', '7', '0', '9', '6', '7', '4', '9', '8', '3', '0', '3', '3', '4', '9', '8', '7', '1', '5', '6', '9', '3', '2', '3', '7', '5', '1', '9', '6', '1', '9', '6', '9', '4', '5', '1', '9', '5', '3', '1', '2', '5', '/', '1', '8', '4', '1', '8', '5', '1', '9', '6', '9', '1', '1', '0', '5', '1', '0', '0', '3', '5', '4', '8', '1', '9', '1', '2', '8', '0', '4', '9', '5', '7', '1', '5', '1', '0', '9', '9', '5', '7', '6', '6', '3', '7', '9', '1', '4', '6', '9', '2', '6', '6', '5', '1', '5', '1', '0', '2', '1', '6', '5', '9', '6', '6', '4', '8', '9', '1', '4'])
noncomputable def fragment0114659Acc00700 : List (String × SourceJson) := (fragment0114659Field006Key00, fragment0114659Field006Value00) :: fragment0114659Acc00600
noncomputable def fragment0114659Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '6', '4', '3', '6', '2', '6', '9', '5', '7', '0', '9', '6', '7', '4', '9', '8', '3', '0', '3', '3', '4', '9', '8', '7', '1', '5', '6', '9', '3', '2', '3', '7', '5', '1', '9', '6', '1', '9', '6', '9', '4', '5', '1', '9', '5', '3', '1', '2', '5', '/', '1', '8', '4', '1', '8', '5', '1', '9', '6', '9', '1', '1', '0', '5', '1', '0', '0', '3', '5', '4', '8', '1', '9', '1', '2', '8', '0', '4', '9', '5', '7', '1', '5', '1', '0', '9', '9', '5', '7', '6', '6', '3', '7', '9', '1', '4', '6', '9', '2', '6', '6', '5', '1', '5', '1', '0', '2', '1', '6', '5', '9', '6', '6', '4', '8', '9', '1', '4', '"', ',']

theorem object_fragment0114659_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0114659Field006Chars00 ++ tail)) fragment0114659Acc00600 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0114659Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_006"
  err.flush

noncomputable def fragment0114659Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0114659Field007Value00 : SourceJson := .str (String.ofList ['3', '3', '2', '9', '7', '4', '2', '4', '5', '5', '2', '8', '6', '0', '4', '0', '4', '3', '0', '5', '3', '5', '8', '6', '0', '9', '8', '1', '1', '9', '3', '2', '7', '0', '9', '7', '8', '4', '3', '7', '0', '3', '4', '6', '3', '1', '1', '5', '3', '9', '1', '7', '5', '4', '4', '9', '9', '9', '4', '4', '7', '3', '2', '0', '9', '9', '1', '9', '5', '4', '1', '4', '5', '6', '0', '6', '0', '0', '7', '9', '4', '0', '0', '5', '3', '6', '4', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '7', '9', '3', '2', '1', '1', '3', '4', '0', '2', '1', '0', '8', '0', '0', '2', '2', '6', '1', '5', '3', '5', '3', '1', '5', '7', '5', '8', '7', '7', '5', '7', '6', '6', '3', '5', '0', '8', '7', '1', '9', '7', '4', '6', '8', '2', '9', '3', '0', '4', '2', '6', '3', '1', '3', '8', '4', '1', '5', '3', '5', '6', '8', '2', '7', '4', '4', '6', '1', '6', '0', '6', '2', '5', '0', '3', '0', '9', '0', '6', '1', '8', '9', '8', '9', '1', '9', '8', '8', '1', '4', '4', '8', '3', '0', '5', '7', '5', '1', '5', '8', '1', '9', '6', '0', '4', '9', '0', '6', '2', '2', '0', '4', '5', '0', '4', '8', '0', '6', '2', '2', '2', '7', '6', '2', '6', '0', '7'])
noncomputable def fragment0114659Acc00800 : List (String × SourceJson) := (fragment0114659Field007Key00, fragment0114659Field007Value00) :: fragment0114659Acc00700
noncomputable def fragment0114659Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '2', '9', '7', '4', '2', '4', '5', '5', '2', '8', '6', '0', '4', '0', '4', '3', '0', '5', '3', '5', '8', '6', '0', '9', '8', '1', '1', '9', '3', '2', '7', '0', '9', '7', '8', '4', '3', '7', '0', '3', '4', '6', '3', '1', '1', '5', '3', '9', '1', '7', '5', '4', '4', '9', '9', '9', '4', '4', '7', '3', '2', '0', '9', '9', '1', '9', '5', '4', '1', '4', '5', '6', '0', '6', '0', '0', '7', '9', '4', '0', '0', '5', '3', '6', '4', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '7', '9', '3', '2', '1', '1', '3', '4', '0', '2', '1', '0', '8', '0', '0', '2', '2', '6', '1', '5', '3', '5', '3', '1', '5', '7', '5', '8', '7', '7', '5', '7', '6', '6', '3', '5', '0', '8', '7', '1', '9', '7', '4', '6', '8', '2', '9', '3', '0', '4', '2', '6', '3', '1', '3', '8', '4', '1', '5', '3', '5', '6', '8', '2', '7', '4', '4', '6', '1', '6', '0', '6', '2', '5', '0', '3', '0', '9', '0', '6', '1', '8', '9', '8', '9', '1', '9', '8', '8', '1', '4', '4', '8', '3', '0', '5', '7', '5', '1', '5', '8', '1', '9', '6', '0', '4', '9', '0', '6', '2', '2', '0', '4', '5', '0', '4', '8', '0', '6', '2', '2', '2', '7', '6', '2', '6', '0', '7', '"', ',']

theorem object_fragment0114659_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0114659Field007Chars00 ++ tail)) fragment0114659Acc00700 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0114659Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_007"
  err.flush

noncomputable def fragment0114659Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0114659Field008Value00 : SourceJson := .str (String.ofList ['5', '0', '0', '8', '5', '6', '3', '0', '3', '4', '8', '3'])
noncomputable def fragment0114659Acc00900 : List (String × SourceJson) := (fragment0114659Field008Key00, fragment0114659Field008Value00) :: fragment0114659Acc00800
noncomputable def fragment0114659Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '0', '8', '5', '6', '3', '0', '3', '4', '8', '3', '"', ',']

theorem object_fragment0114659_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0114659Field008Chars00 ++ tail)) fragment0114659Acc00800 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0114659Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_008"
  err.flush

noncomputable def fragment0114659Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0114659Field009Value00 : SourceJson := .str (String.ofList ['1', '9', '1', '2', '6', '0', '3', '0', '1', '8', '0', '4', '3'])
noncomputable def fragment0114659Acc01000 : List (String × SourceJson) := (fragment0114659Field009Key00, fragment0114659Field009Value00) :: fragment0114659Acc00900
noncomputable def fragment0114659Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '1', '2', '6', '0', '3', '0', '1', '8', '0', '4', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0114659_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0114659Field009Chars00 ++ tail)) fragment0114659Acc00900 =
      .ok (.obj (fragment0114659Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0114659_object_field_009"
  err.flush

noncomputable def fragment0114659Chars : List Char := '{' :: (fragment0114659Field000Chars00 ++ fragment0114659Field001Chars00 ++ fragment0114659Field002Chars00 ++ fragment0114659Field003Chars00 ++ fragment0114659Field004Chars00 ++ fragment0114659Field005Chars00 ++ fragment0114659Field006Chars00 ++ fragment0114659Field007Chars00 ++ fragment0114659Field008Chars00 ++ fragment0114659Field009Chars00)
noncomputable def fragment0114659Value : SourceJson := .obj (fragment0114659Acc01000.reverse)

theorem value_fragment0114659 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 255) (fragment0114659Chars ++ tail) =
      .ok (fragment0114659Value, tail) := by
  have hinput : fragment0114659Chars ++ tail = '{' :: (fragment0114659Field000Chars00 ++ (fragment0114659Field001Chars00 ++ (fragment0114659Field002Chars00 ++ (fragment0114659Field003Chars00 ++ (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0114659Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 255) (fragment0114659Chars ++ tail) =
        SourceJson.value (fuel + 255) ('{' :: (fragment0114659Field000Chars00 ++ (fragment0114659Field001Chars00 ++ (fragment0114659Field002Chars00 ++ (fragment0114659Field003Chars00 ++ (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 255)) hinput
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0114659Field000Chars00 ++ (fragment0114659Field001Chars00 ++ (fragment0114659Field002Chars00 ++ (fragment0114659Field003Chars00 ++ (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))))))))))) fragment0114659Acc00000 := by rfl
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0114659Field001Chars00 ++ (fragment0114659Field002Chars00 ++ (fragment0114659Field003Chars00 ++ (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail))))))))))) fragment0114659Acc00100 := object_fragment0114659_field_000 fuel (fragment0114659Field001Chars00 ++ (fragment0114659Field002Chars00 ++ (fragment0114659Field003Chars00 ++ (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0114659Field002Chars00 ++ (fragment0114659Field003Chars00 ++ (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))))))))) fragment0114659Acc00200 := object_fragment0114659_field_001 fuel (fragment0114659Field002Chars00 ++ (fragment0114659Field003Chars00 ++ (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0114659Field003Chars00 ++ (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail))))))))) fragment0114659Acc00300 := object_fragment0114659_field_002 fuel (fragment0114659Field003Chars00 ++ (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))))))) fragment0114659Acc00400 := object_fragment0114659_field_003 fuel (fragment0114659Field004Chars00 ++ (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail))))))) fragment0114659Acc00500 := object_fragment0114659_field_004 fuel (fragment0114659Field005Chars00 ++ (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))))) fragment0114659Acc00600 := object_fragment0114659_field_005 fuel (fragment0114659Field006Chars00 ++ (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail))))) fragment0114659Acc00700 := object_fragment0114659_field_006 fuel (fragment0114659Field007Chars00 ++ (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))) fragment0114659Acc00800 := object_fragment0114659_field_007 fuel (fragment0114659Field008Chars00 ++ (fragment0114659Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0114659Field009Chars00 ++ (tail))) fragment0114659Acc00900 := object_fragment0114659_field_008 fuel (fragment0114659Field009Chars00 ++ (tail))
    _ = .ok (fragment0114659Value, tail) := object_fragment0114659_field_009 fuel (tail)

noncomputable def fragment0116294Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0116294Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0116294Field000Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0116294Acc00100 : List (String × SourceJson) := (fragment0116294Field000Key00, fragment0116294Field000Value00) :: fragment0116294Acc00000
noncomputable def fragment0116294Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', ',']

theorem object_fragment0116294_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0116294Field000Chars00 ++ tail)) fragment0116294Acc00000 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0116294Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_000"
  err.flush

noncomputable def fragment0116294Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0116294Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0116294Acc00200 : List (String × SourceJson) := (fragment0116294Field001Key00, fragment0116294Field001Value00) :: fragment0116294Acc00100
noncomputable def fragment0116294Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0116294_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0116294Field001Chars00 ++ tail)) fragment0116294Acc00100 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0116294Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_001"
  err.flush

noncomputable def fragment0116294Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0116294Field002Value00 : SourceJson := .str (String.ofList ['5', '2', '1', '0', '7', '7', '1', '0', '7', '3', '1', '9', '4', '5', '8', '4', '7', '9', '8', '2', '6', '4', '5', '3', '7', '7', '5', '9', '0', '2', '3', '1', '4', '6', '0', '2', '7', '/', '2', '2', '1', '2', '1', '7', '6', '8', '1', '6', '7', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0116294Acc00300 : List (String × SourceJson) := (fragment0116294Field002Key00, fragment0116294Field002Value00) :: fragment0116294Acc00200
noncomputable def fragment0116294Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '2', '1', '0', '7', '7', '1', '0', '7', '3', '1', '9', '4', '5', '8', '4', '7', '9', '8', '2', '6', '4', '5', '3', '7', '7', '5', '9', '0', '2', '3', '1', '4', '6', '0', '2', '7', '/', '2', '2', '1', '2', '1', '7', '6', '8', '1', '6', '7', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0116294_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0116294Field002Chars00 ++ tail)) fragment0116294Acc00200 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0116294Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_002"
  err.flush

noncomputable def fragment0116294Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0116294Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0116294Acc00400 : List (String × SourceJson) := (fragment0116294Field003Key00, fragment0116294Field003Value00) :: fragment0116294Acc00300
noncomputable def fragment0116294Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '1', '/', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0116294_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0116294Field003Chars00 ++ tail)) fragment0116294Acc00300 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0116294Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_003"
  err.flush

noncomputable def fragment0116294Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0116294Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0116294Acc00500 : List (String × SourceJson) := (fragment0116294Field004Key00, fragment0116294Field004Value00) :: fragment0116294Acc00400
noncomputable def fragment0116294Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '0', '7', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '5', '9', '/', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0116294_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0116294Field004Chars00 ++ tail)) fragment0116294Acc00400 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0116294Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_004"
  err.flush

noncomputable def fragment0116294Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0116294Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '9', '5', '9', '1', '8', '6', '8', '1', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '2', '2', '0', '0', '0', '9', '9', '7', '1', '1', '1', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '7', '3', '2', '2', '9', '4', '8', '2', '2', '1', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '3', '8', '5', '7', '1', '6', '1', '7', '9', '7', '1', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '6', '1', '3', '1', '3', '0', '5', '0', '3', '5', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '1', '3', '5', '5', '5', '2', '0', '5', '4', '7', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '7', '7', '4', '4', '1', '3', '8', '3', '1', '3', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '0', '8', '8', '2', '6', '7', '2', '3', '1', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '3', '1', '0', '2', '8', '6', '7', '3', '3', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '9', '2', '8', '3', '9', '8', '3', '2', '2', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0116294Acc00600 : List (String × SourceJson) := (fragment0116294Field005Key00, fragment0116294Field005Value00) :: fragment0116294Acc00500
noncomputable def fragment0116294Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '9', '5', '9', '1', '8', '6', '8', '1', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '2', '0', '0', '0', '9', '9', '7', '1', '1', '1', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '7', '3', '2', '2', '9', '4', '8', '2', '2', '1', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '3', '8', '5', '7', '1', '6', '1', '7', '9', '7', '1', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '6', '1', '3', '1', '3', '0', '5', '0', '3', '5', '9', '/', '5', '2', '2', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '1', '3', '5', '5', '5', '2', '0', '5', '4', '7', '/', '1', '0', '4', '5', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '7', '7', '4', '4', '1', '3', '8', '3', '1', '3', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '0', '8', '8', '2', '6', '7', '2', '3', '1', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '3', '1', '0', '2', '8', '6', '7', '3', '3', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '9', '2', '8', '3', '9', '8', '3', '2', '2', '7', '/', '2', '6', '1', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0116294_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0116294Field005Chars00 ++ tail)) fragment0116294Acc00500 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0116294Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_005"
  err.flush

noncomputable def fragment0116294Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0116294Field006Value00 : SourceJson := .str (String.ofList ['6', '2', '1', '5', '0', '4', '7', '7', '1', '9', '1', '9', '5', '9', '8', '9', '1', '2', '1', '5', '1', '1', '1', '5', '1', '4', '5', '2', '7', '1', '7', '6', '3', '9', '7', '0', '9', '0', '9', '8', '2', '8', '0', '0', '0', '0', '0', '0', '0', '/', '8', '4', '7', '6', '1', '5', '7', '7', '5', '4', '3', '3', '9', '3', '2', '1', '5', '1', '7', '2', '0', '5', '5', '4', '3', '2', '3', '3', '3', '8', '2', '3', '4', '3', '3', '1', '3', '7', '7', '0', '7', '6', '3', '2', '3', '5', '9', '4', '9', '1', '7', '0', '6', '6', '2', '2', '7', '6', '6', '1', '6', '6', '0', '2', '4', '1'])
noncomputable def fragment0116294Acc00700 : List (String × SourceJson) := (fragment0116294Field006Key00, fragment0116294Field006Value00) :: fragment0116294Acc00600
noncomputable def fragment0116294Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '2', '1', '5', '0', '4', '7', '7', '1', '9', '1', '9', '5', '9', '8', '9', '1', '2', '1', '5', '1', '1', '1', '5', '1', '4', '5', '2', '7', '1', '7', '6', '3', '9', '7', '0', '9', '0', '9', '8', '2', '8', '0', '0', '0', '0', '0', '0', '0', '/', '8', '4', '7', '6', '1', '5', '7', '7', '5', '4', '3', '3', '9', '3', '2', '1', '5', '1', '7', '2', '0', '5', '5', '4', '3', '2', '3', '3', '3', '8', '2', '3', '4', '3', '3', '1', '3', '7', '7', '0', '7', '6', '3', '2', '3', '5', '9', '4', '9', '1', '7', '0', '6', '6', '2', '2', '7', '6', '6', '1', '6', '6', '0', '2', '4', '1', '"', ',']

theorem object_fragment0116294_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0116294Field006Chars00 ++ tail)) fragment0116294Acc00600 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0116294Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_006"
  err.flush

noncomputable def fragment0116294Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0116294Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '8', '1', '8', '0', '6', '1', '3', '5', '4', '7', '5', '8', '6', '8', '8', '6', '0', '5', '6', '8', '1', '6', '4', '3', '5', '7', '9', '3', '1', '5', '0', '6', '6', '4', '7', '8', '0', '5', '1', '6', '7', '6', '0', '2', '4', '8', '9', '1', '2', '5', '3', '7', '6', '5', '6', '7', '3', '0', '2', '9', '5', '7', '3', '9', '2', '4', '2', '0', '2', '7', '2', '5', '0', '0', '4', '4', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '1', '8', '4', '5', '6', '4', '5', '0', '3', '9', '2', '1', '7', '9', '3', '4', '1', '1', '0', '0', '0', '9', '9', '7', '1', '9', '2', '4', '4', '0', '2', '9', '8', '9', '9', '6', '1', '1', '4', '5', '7', '2', '1', '0', '7', '6', '2', '9', '3', '6', '1', '5', '0', '7', '9', '0', '2', '9', '2', '8', '6', '5', '1', '9', '2', '2', '6', '4', '2', '1', '5', '2', '9', '6', '6', '8', '3', '8', '3', '5', '0', '0', '5', '6', '5', '7', '6', '0', '4', '2', '3', '1', '8', '5', '1', '4', '4', '3', '4', '1', '3', '9', '9', '4', '7', '8', '0', '2', '4', '1', '2', '9', '3', '2', '0', '8', '5', '2', '5', '7'])
noncomputable def fragment0116294Acc00800 : List (String × SourceJson) := (fragment0116294Field007Key00, fragment0116294Field007Value00) :: fragment0116294Acc00700
noncomputable def fragment0116294Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '8', '1', '8', '0', '6', '1', '3', '5', '4', '7', '5', '8', '6', '8', '8', '6', '0', '5', '6', '8', '1', '6', '4', '3', '5', '7', '9', '3', '1', '5', '0', '6', '6', '4', '7', '8', '0', '5', '1', '6', '7', '6', '0', '2', '4', '8', '9', '1', '2', '5', '3', '7', '6', '5', '6', '7', '3', '0', '2', '9', '5', '7', '3', '9', '2', '4', '2', '0', '2', '7', '2', '5', '0', '0', '4', '4', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '1', '8', '4', '5', '6', '4', '5', '0', '3', '9', '2', '1', '7', '9', '3', '4', '1', '1', '0', '0', '0', '9', '9', '7', '1', '9', '2', '4', '4', '0', '2', '9', '8', '9', '9', '6', '1', '1', '4', '5', '7', '2', '1', '0', '7', '6', '2', '9', '3', '6', '1', '5', '0', '7', '9', '0', '2', '9', '2', '8', '6', '5', '1', '9', '2', '2', '6', '4', '2', '1', '5', '2', '9', '6', '6', '8', '3', '8', '3', '5', '0', '0', '5', '6', '5', '7', '6', '0', '4', '2', '3', '1', '8', '5', '1', '4', '4', '3', '4', '1', '3', '9', '9', '4', '7', '8', '0', '2', '4', '1', '2', '9', '3', '2', '0', '8', '5', '2', '5', '7', '"', ',']

theorem object_fragment0116294_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0116294Field007Chars00 ++ tail)) fragment0116294Acc00700 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0116294Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_007"
  err.flush

noncomputable def fragment0116294Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0116294Field008Value00 : SourceJson := .str (String.ofList ['5', '8', '0', '9', '3', '1', '6', '2', '6', '0', '9', '9'])
noncomputable def fragment0116294Acc00900 : List (String × SourceJson) := (fragment0116294Field008Key00, fragment0116294Field008Value00) :: fragment0116294Acc00800
noncomputable def fragment0116294Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '0', '9', '3', '1', '6', '2', '6', '0', '9', '9', '"', ',']

theorem object_fragment0116294_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0116294Field008Chars00 ++ tail)) fragment0116294Acc00800 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0116294Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_008"
  err.flush

noncomputable def fragment0116294Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0116294Field009Value00 : SourceJson := .str (String.ofList ['2', '4', '0', '5', '9', '9', '8', '1', '7', '8', '2', '0', '1'])
noncomputable def fragment0116294Acc01000 : List (String × SourceJson) := (fragment0116294Field009Key00, fragment0116294Field009Value00) :: fragment0116294Acc00900
noncomputable def fragment0116294Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '0', '5', '9', '9', '8', '1', '7', '8', '2', '0', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0116294_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0116294Field009Chars00 ++ tail)) fragment0116294Acc00900 =
      .ok (.obj (fragment0116294Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0116294_object_field_009"
  err.flush

noncomputable def fragment0116294Chars : List Char := '{' :: (fragment0116294Field000Chars00 ++ fragment0116294Field001Chars00 ++ fragment0116294Field002Chars00 ++ fragment0116294Field003Chars00 ++ fragment0116294Field004Chars00 ++ fragment0116294Field005Chars00 ++ fragment0116294Field006Chars00 ++ fragment0116294Field007Chars00 ++ fragment0116294Field008Chars00 ++ fragment0116294Field009Chars00)
noncomputable def fragment0116294Value : SourceJson := .obj (fragment0116294Acc01000.reverse)

theorem value_fragment0116294 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 238) (fragment0116294Chars ++ tail) =
      .ok (fragment0116294Value, tail) := by
  have hinput : fragment0116294Chars ++ tail = '{' :: (fragment0116294Field000Chars00 ++ (fragment0116294Field001Chars00 ++ (fragment0116294Field002Chars00 ++ (fragment0116294Field003Chars00 ++ (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0116294Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 238) (fragment0116294Chars ++ tail) =
        SourceJson.value (fuel + 238) ('{' :: (fragment0116294Field000Chars00 ++ (fragment0116294Field001Chars00 ++ (fragment0116294Field002Chars00 ++ (fragment0116294Field003Chars00 ++ (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 238)) hinput
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0116294Field000Chars00 ++ (fragment0116294Field001Chars00 ++ (fragment0116294Field002Chars00 ++ (fragment0116294Field003Chars00 ++ (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))))))))))) fragment0116294Acc00000 := by rfl
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0116294Field001Chars00 ++ (fragment0116294Field002Chars00 ++ (fragment0116294Field003Chars00 ++ (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail))))))))))) fragment0116294Acc00100 := object_fragment0116294_field_000 fuel (fragment0116294Field001Chars00 ++ (fragment0116294Field002Chars00 ++ (fragment0116294Field003Chars00 ++ (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0116294Field002Chars00 ++ (fragment0116294Field003Chars00 ++ (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))))))))) fragment0116294Acc00200 := object_fragment0116294_field_001 fuel (fragment0116294Field002Chars00 ++ (fragment0116294Field003Chars00 ++ (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0116294Field003Chars00 ++ (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail))))))))) fragment0116294Acc00300 := object_fragment0116294_field_002 fuel (fragment0116294Field003Chars00 ++ (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))))))) fragment0116294Acc00400 := object_fragment0116294_field_003 fuel (fragment0116294Field004Chars00 ++ (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail))))))) fragment0116294Acc00500 := object_fragment0116294_field_004 fuel (fragment0116294Field005Chars00 ++ (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))))) fragment0116294Acc00600 := object_fragment0116294_field_005 fuel (fragment0116294Field006Chars00 ++ (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail))))) fragment0116294Acc00700 := object_fragment0116294_field_006 fuel (fragment0116294Field007Chars00 ++ (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))) fragment0116294Acc00800 := object_fragment0116294_field_007 fuel (fragment0116294Field008Chars00 ++ (fragment0116294Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0116294Field009Chars00 ++ (tail))) fragment0116294Acc00900 := object_fragment0116294_field_008 fuel (fragment0116294Field009Chars00 ++ (tail))
    _ = .ok (fragment0116294Value, tail) := object_fragment0116294_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_before_reader"
  err.flush

noncomputable def chunk0000LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0000SuffixChars00 : List Char := [',']
noncomputable def chunk0000Chars00 : List Char := chunk0000LeadChars00 ++ fragment0104503Chars ++ chunk0000SuffixChars00
noncomputable def chunk0000Push00 (acc : List SourceJson) : List SourceJson := fragment0104503Value :: acc

noncomputable def chunk0000AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0000_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 473)
      (SourceJson.white (chunk0000LeadChars00 ++ (fragment0104503Chars ++ rest))) acc =
      (SourceJson.value (fuel + 472) (fragment0104503Chars ++ rest)).bind
        (chunk0000AfterValue00 (fuel + 472) acc) := by rfl

theorem array_chunk0000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 473) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 472) (SourceJson.white tail) (chunk0000Push00 acc) := by
  have hinput : chunk0000Chars00 ++ tail = chunk0000LeadChars00 ++ (fragment0104503Chars ++ (chunk0000SuffixChars00 ++ tail)) := by
    simp only [chunk0000Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 473) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 473)
          (SourceJson.white (chunk0000LeadChars00 ++ (fragment0104503Chars ++ (chunk0000SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 473) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 472) (fragment0104503Chars ++ (chunk0000SuffixChars00 ++ tail))).bind
        (chunk0000AfterValue00 (fuel + 472) acc) := array_chunk0000_head fuel (chunk0000SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0104503Value, chunk0000SuffixChars00 ++ tail)).bind
        (chunk0000AfterValue00 (fuel + 472) acc) :=
      congrArg (fun result => result.bind (chunk0000AfterValue00 (fuel + 472) acc))
        (value_fragment0104503 (fuel + 220) (chunk0000SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 472) (SourceJson.white tail) (chunk0000Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_before_reader"
  err.flush

noncomputable def chunk0001LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0001SuffixChars00 : List Char := [',']
noncomputable def chunk0001Chars00 : List Char := chunk0001LeadChars00 ++ fragment0106132Chars ++ chunk0001SuffixChars00
noncomputable def chunk0001Push00 (acc : List SourceJson) : List SourceJson := fragment0106132Value :: acc

noncomputable def chunk0001AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0001_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 472)
      (SourceJson.white (chunk0001LeadChars00 ++ (fragment0106132Chars ++ rest))) acc =
      (SourceJson.value (fuel + 471) (fragment0106132Chars ++ rest)).bind
        (chunk0001AfterValue00 (fuel + 471) acc) := by rfl

theorem array_chunk0001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 472) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 471) (SourceJson.white tail) (chunk0001Push00 acc) := by
  have hinput : chunk0001Chars00 ++ tail = chunk0001LeadChars00 ++ (fragment0106132Chars ++ (chunk0001SuffixChars00 ++ tail)) := by
    simp only [chunk0001Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 472) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 472)
          (SourceJson.white (chunk0001LeadChars00 ++ (fragment0106132Chars ++ (chunk0001SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 472) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 471) (fragment0106132Chars ++ (chunk0001SuffixChars00 ++ tail))).bind
        (chunk0001AfterValue00 (fuel + 471) acc) := array_chunk0001_head fuel (chunk0001SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0106132Value, chunk0001SuffixChars00 ++ tail)).bind
        (chunk0001AfterValue00 (fuel + 471) acc) :=
      congrArg (fun result => result.bind (chunk0001AfterValue00 (fuel + 471) acc))
        (value_fragment0106132 (fuel + 219) (chunk0001SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 471) (SourceJson.white tail) (chunk0001Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_before_reader"
  err.flush

noncomputable def chunk0002LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0002SuffixChars00 : List Char := [',']
noncomputable def chunk0002Chars00 : List Char := chunk0002LeadChars00 ++ fragment0107755Chars ++ chunk0002SuffixChars00
noncomputable def chunk0002Push00 (acc : List SourceJson) : List SourceJson := fragment0107755Value :: acc

noncomputable def chunk0002AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0002_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 471)
      (SourceJson.white (chunk0002LeadChars00 ++ (fragment0107755Chars ++ rest))) acc =
      (SourceJson.value (fuel + 470) (fragment0107755Chars ++ rest)).bind
        (chunk0002AfterValue00 (fuel + 470) acc) := by rfl

theorem array_chunk0002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 471) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 470) (SourceJson.white tail) (chunk0002Push00 acc) := by
  have hinput : chunk0002Chars00 ++ tail = chunk0002LeadChars00 ++ (fragment0107755Chars ++ (chunk0002SuffixChars00 ++ tail)) := by
    simp only [chunk0002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 471) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 471)
          (SourceJson.white (chunk0002LeadChars00 ++ (fragment0107755Chars ++ (chunk0002SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 471) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 470) (fragment0107755Chars ++ (chunk0002SuffixChars00 ++ tail))).bind
        (chunk0002AfterValue00 (fuel + 470) acc) := array_chunk0002_head fuel (chunk0002SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0107755Value, chunk0002SuffixChars00 ++ tail)).bind
        (chunk0002AfterValue00 (fuel + 470) acc) :=
      congrArg (fun result => result.bind (chunk0002AfterValue00 (fuel + 470) acc))
        (value_fragment0107755 (fuel + 69) (chunk0002SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 470) (SourceJson.white tail) (chunk0002Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_before_reader"
  err.flush

noncomputable def chunk0003LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0003SuffixChars00 : List Char := [',']
noncomputable def chunk0003Chars00 : List Char := chunk0003LeadChars00 ++ fragment0109704Chars ++ chunk0003SuffixChars00
noncomputable def chunk0003Push00 (acc : List SourceJson) : List SourceJson := fragment0109704Value :: acc

noncomputable def chunk0003AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0003_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 470)
      (SourceJson.white (chunk0003LeadChars00 ++ (fragment0109704Chars ++ rest))) acc =
      (SourceJson.value (fuel + 469) (fragment0109704Chars ++ rest)).bind
        (chunk0003AfterValue00 (fuel + 469) acc) := by rfl

theorem array_chunk0003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 470) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 469) (SourceJson.white tail) (chunk0003Push00 acc) := by
  have hinput : chunk0003Chars00 ++ tail = chunk0003LeadChars00 ++ (fragment0109704Chars ++ (chunk0003SuffixChars00 ++ tail)) := by
    simp only [chunk0003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 470) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 470)
          (SourceJson.white (chunk0003LeadChars00 ++ (fragment0109704Chars ++ (chunk0003SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 470) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 469) (fragment0109704Chars ++ (chunk0003SuffixChars00 ++ tail))).bind
        (chunk0003AfterValue00 (fuel + 469) acc) := array_chunk0003_head fuel (chunk0003SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0109704Value, chunk0003SuffixChars00 ++ tail)).bind
        (chunk0003AfterValue00 (fuel + 469) acc) :=
      congrArg (fun result => result.bind (chunk0003AfterValue00 (fuel + 469) acc))
        (value_fragment0109704 (fuel + 204) (chunk0003SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 469) (SourceJson.white tail) (chunk0003Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_before_reader"
  err.flush

noncomputable def chunk0004LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0004SuffixChars00 : List Char := [',']
noncomputable def chunk0004Chars00 : List Char := chunk0004LeadChars00 ++ fragment0111367Chars ++ chunk0004SuffixChars00
noncomputable def chunk0004Push00 (acc : List SourceJson) : List SourceJson := fragment0111367Value :: acc

noncomputable def chunk0004AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0004_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 469)
      (SourceJson.white (chunk0004LeadChars00 ++ (fragment0111367Chars ++ rest))) acc =
      (SourceJson.value (fuel + 468) (fragment0111367Chars ++ rest)).bind
        (chunk0004AfterValue00 (fuel + 468) acc) := by rfl

theorem array_chunk0004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 469) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 468) (SourceJson.white tail) (chunk0004Push00 acc) := by
  have hinput : chunk0004Chars00 ++ tail = chunk0004LeadChars00 ++ (fragment0111367Chars ++ (chunk0004SuffixChars00 ++ tail)) := by
    simp only [chunk0004Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 469) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 469)
          (SourceJson.white (chunk0004LeadChars00 ++ (fragment0111367Chars ++ (chunk0004SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 469) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 468) (fragment0111367Chars ++ (chunk0004SuffixChars00 ++ tail))).bind
        (chunk0004AfterValue00 (fuel + 468) acc) := array_chunk0004_head fuel (chunk0004SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0111367Value, chunk0004SuffixChars00 ++ tail)).bind
        (chunk0004AfterValue00 (fuel + 468) acc) :=
      congrArg (fun result => result.bind (chunk0004AfterValue00 (fuel + 468) acc))
        (value_fragment0111367 (fuel + 212) (chunk0004SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 468) (SourceJson.white tail) (chunk0004Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_before_reader"
  err.flush

noncomputable def chunk0005LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0005SuffixChars00 : List Char := [',']
noncomputable def chunk0005Chars00 : List Char := chunk0005LeadChars00 ++ fragment0113001Chars ++ chunk0005SuffixChars00
noncomputable def chunk0005Push00 (acc : List SourceJson) : List SourceJson := fragment0113001Value :: acc

noncomputable def chunk0005AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0005_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 468)
      (SourceJson.white (chunk0005LeadChars00 ++ (fragment0113001Chars ++ rest))) acc =
      (SourceJson.value (fuel + 467) (fragment0113001Chars ++ rest)).bind
        (chunk0005AfterValue00 (fuel + 467) acc) := by rfl

theorem array_chunk0005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 468) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 467) (SourceJson.white tail) (chunk0005Push00 acc) := by
  have hinput : chunk0005Chars00 ++ tail = chunk0005LeadChars00 ++ (fragment0113001Chars ++ (chunk0005SuffixChars00 ++ tail)) := by
    simp only [chunk0005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 468) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 468)
          (SourceJson.white (chunk0005LeadChars00 ++ (fragment0113001Chars ++ (chunk0005SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 468) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 467) (fragment0113001Chars ++ (chunk0005SuffixChars00 ++ tail))).bind
        (chunk0005AfterValue00 (fuel + 467) acc) := array_chunk0005_head fuel (chunk0005SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0113001Value, chunk0005SuffixChars00 ++ tail)).bind
        (chunk0005AfterValue00 (fuel + 467) acc) :=
      congrArg (fun result => result.bind (chunk0005AfterValue00 (fuel + 467) acc))
        (value_fragment0113001 (fuel + 207) (chunk0005SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 467) (SourceJson.white tail) (chunk0005Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_before_reader"
  err.flush

noncomputable def chunk0006LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0006SuffixChars00 : List Char := [',']
noncomputable def chunk0006Chars00 : List Char := chunk0006LeadChars00 ++ fragment0114659Chars ++ chunk0006SuffixChars00
noncomputable def chunk0006Push00 (acc : List SourceJson) : List SourceJson := fragment0114659Value :: acc

noncomputable def chunk0006AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0006_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 467)
      (SourceJson.white (chunk0006LeadChars00 ++ (fragment0114659Chars ++ rest))) acc =
      (SourceJson.value (fuel + 466) (fragment0114659Chars ++ rest)).bind
        (chunk0006AfterValue00 (fuel + 466) acc) := by rfl

theorem array_chunk0006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 467) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 466) (SourceJson.white tail) (chunk0006Push00 acc) := by
  have hinput : chunk0006Chars00 ++ tail = chunk0006LeadChars00 ++ (fragment0114659Chars ++ (chunk0006SuffixChars00 ++ tail)) := by
    simp only [chunk0006Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 467) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 467)
          (SourceJson.white (chunk0006LeadChars00 ++ (fragment0114659Chars ++ (chunk0006SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 467) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 466) (fragment0114659Chars ++ (chunk0006SuffixChars00 ++ tail))).bind
        (chunk0006AfterValue00 (fuel + 466) acc) := array_chunk0006_head fuel (chunk0006SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0114659Value, chunk0006SuffixChars00 ++ tail)).bind
        (chunk0006AfterValue00 (fuel + 466) acc) :=
      congrArg (fun result => result.bind (chunk0006AfterValue00 (fuel + 466) acc))
        (value_fragment0114659 (fuel + 211) (chunk0006SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 466) (SourceJson.white tail) (chunk0006Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_before_reader"
  err.flush

noncomputable def chunk0007LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0007SuffixChars00 : List Char := [',']
noncomputable def chunk0007Chars00 : List Char := chunk0007LeadChars00 ++ fragment0116294Chars ++ chunk0007SuffixChars00
noncomputable def chunk0007Push00 (acc : List SourceJson) : List SourceJson := fragment0116294Value :: acc

noncomputable def chunk0007AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0007_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 466)
      (SourceJson.white (chunk0007LeadChars00 ++ (fragment0116294Chars ++ rest))) acc =
      (SourceJson.value (fuel + 465) (fragment0116294Chars ++ rest)).bind
        (chunk0007AfterValue00 (fuel + 465) acc) := by rfl

theorem array_chunk0007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 466) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 465) (SourceJson.white tail) (chunk0007Push00 acc) := by
  have hinput : chunk0007Chars00 ++ tail = chunk0007LeadChars00 ++ (fragment0116294Chars ++ (chunk0007SuffixChars00 ++ tail)) := by
    simp only [chunk0007Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 466) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 466)
          (SourceJson.white (chunk0007LeadChars00 ++ (fragment0116294Chars ++ (chunk0007SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 466) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 465) (fragment0116294Chars ++ (chunk0007SuffixChars00 ++ tail))).bind
        (chunk0007AfterValue00 (fuel + 465) acc) := array_chunk0007_head fuel (chunk0007SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0116294Value, chunk0007SuffixChars00 ++ tail)).bind
        (chunk0007AfterValue00 (fuel + 465) acc) :=
      congrArg (fun result => result.bind (chunk0007AfterValue00 (fuel + 465) acc))
        (value_fragment0116294 (fuel + 227) (chunk0007SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 465) (SourceJson.white tail) (chunk0007Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0000Chars00 ++ chunk0001Chars00 ++ chunk0002Chars00 ++ chunk0003Chars00 ++ chunk0004Chars00 ++ chunk0005Chars00 ++ chunk0006Chars00 ++ chunk0007Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0007Push00 (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 473) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 465) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 473) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 473) (SourceJson.white (chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 473) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 472) (SourceJson.white (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))))) (chunk0000Push00 (acc)) := array_chunk0000 fuel (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 471) (SourceJson.white (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (chunk0001Push00 (chunk0000Push00 (acc))) := array_chunk0001 fuel (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0000Push00 (acc))
    _ = SourceJson.array (fuel + 470) (SourceJson.white (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))) := array_chunk0002 fuel (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0001Push00 (chunk0000Push00 (acc)))
    _ = SourceJson.array (fuel + 469) (SourceJson.white (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))) := array_chunk0003 fuel (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))
    _ = SourceJson.array (fuel + 468) (SourceJson.white (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))) := array_chunk0004 fuel (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))
    _ = SourceJson.array (fuel + 467) (SourceJson.white (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))) := array_chunk0005 fuel (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))
    _ = SourceJson.array (fuel + 466) (SourceJson.white (chunk0007Chars00 ++ (tail))) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))) := array_chunk0006 fuel (chunk0007Chars00 ++ (tail)) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))
    _ = SourceJson.array (fuel + 465) (SourceJson.white tail) (blockPush acc) := array_chunk0007 fuel (tail) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 104497).take 13385 = blockChars := by rfl

theorem block_original_split : sourceRest 104497 = blockChars ++ sourceRest 117882 := by
  calc
    sourceRest 104497 = (sourceRest 104497).take 13385 ++ (sourceRest 104497).drop 13385 :=
      (List.take_append_drop 13385 (sourceRest 104497)).symm
    _ = blockChars ++ (sourceRest 104497).drop 13385 :=
      congrArg (fun part => part ++ (sourceRest 104497).drop 13385) block_original_prefix
    _ = blockChars ++ sourceRest 117882 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 104497 13385)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 473) (SourceJson.white (sourceRest 104497)) acc =
      SourceJson.array (fuel + 465) (SourceJson.white (sourceRest 117882)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 473) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 117882) acc)

#print axioms object_fragment0104503_field_000
#print axioms object_fragment0104503_field_001
#print axioms object_fragment0104503_field_002
#print axioms object_fragment0104503_field_003
#print axioms object_fragment0104503_field_004
#print axioms object_fragment0104503_field_005
#print axioms object_fragment0104503_field_006
#print axioms object_fragment0104503_field_007
#print axioms object_fragment0104503_field_008
#print axioms object_fragment0104503_field_009
#print axioms value_fragment0104503
#print axioms object_fragment0106132_field_000
#print axioms object_fragment0106132_field_001
#print axioms object_fragment0106132_field_002
#print axioms object_fragment0106132_field_003
#print axioms object_fragment0106132_field_004
#print axioms object_fragment0106132_field_005
#print axioms object_fragment0106132_field_006
#print axioms object_fragment0106132_field_007
#print axioms object_fragment0106132_field_008
#print axioms object_fragment0106132_field_009
#print axioms value_fragment0106132
#print axioms object_fragment0107755_field_000
#print axioms object_fragment0107755_field_001
#print axioms object_fragment0107755_field_002
#print axioms object_fragment0107755_field_003
#print axioms object_fragment0107755_field_004
#print axioms object_fragment0107755_field_005
#print axioms object_fragment0107755_field_006
#print axioms object_fragment0107755_field_007
#print axioms object_fragment0107755_field_008
#print axioms object_fragment0107755_field_009
#print axioms value_fragment0107755
#print axioms object_fragment0109704_field_000
#print axioms object_fragment0109704_field_001
#print axioms object_fragment0109704_field_002
#print axioms object_fragment0109704_field_003
#print axioms object_fragment0109704_field_004
#print axioms object_fragment0109704_field_005
#print axioms object_fragment0109704_field_006
#print axioms object_fragment0109704_field_007
#print axioms object_fragment0109704_field_008
#print axioms object_fragment0109704_field_009
#print axioms value_fragment0109704
#print axioms object_fragment0111367_field_000
#print axioms object_fragment0111367_field_001
#print axioms object_fragment0111367_field_002
#print axioms object_fragment0111367_field_003
#print axioms object_fragment0111367_field_004
#print axioms object_fragment0111367_field_005
#print axioms object_fragment0111367_field_006
#print axioms object_fragment0111367_field_007
#print axioms object_fragment0111367_field_008
#print axioms object_fragment0111367_field_009
#print axioms value_fragment0111367
#print axioms object_fragment0113001_field_000
#print axioms object_fragment0113001_field_001
#print axioms object_fragment0113001_field_002
#print axioms object_fragment0113001_field_003
#print axioms object_fragment0113001_field_004
#print axioms object_fragment0113001_field_005
#print axioms object_fragment0113001_field_006
#print axioms object_fragment0113001_field_007
#print axioms object_fragment0113001_field_008
#print axioms object_fragment0113001_field_009
#print axioms value_fragment0113001
#print axioms object_fragment0114659_field_000
#print axioms object_fragment0114659_field_001
#print axioms object_fragment0114659_field_002
#print axioms object_fragment0114659_field_003
#print axioms object_fragment0114659_field_004
#print axioms object_fragment0114659_field_005
#print axioms object_fragment0114659_field_006
#print axioms object_fragment0114659_field_007
#print axioms object_fragment0114659_field_008
#print axioms object_fragment0114659_field_009
#print axioms value_fragment0114659
#print axioms object_fragment0116294_field_000
#print axioms object_fragment0116294_field_001
#print axioms object_fragment0116294_field_002
#print axioms object_fragment0116294_field_003
#print axioms object_fragment0116294_field_004
#print axioms object_fragment0116294_field_005
#print axioms object_fragment0116294_field_006
#print axioms object_fragment0116294_field_007
#print axioms object_fragment0116294_field_008
#print axioms object_fragment0116294_field_009
#print axioms value_fragment0116294
#print axioms array_chunk0000_head
#print axioms array_chunk0000
#print axioms array_chunk0001_head
#print axioms array_chunk0001
#print axioms array_chunk0002_head
#print axioms array_chunk0002
#print axioms array_chunk0003_head
#print axioms array_chunk0003
#print axioms array_chunk0004_head
#print axioms array_chunk0004
#print axioms array_chunk0005_head
#print axioms array_chunk0005
#print axioms array_chunk0006_head
#print axioms array_chunk0006
#print axioms array_chunk0007_head
#print axioms array_chunk0007
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock000

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
