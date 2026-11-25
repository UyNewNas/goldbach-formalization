import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock072

noncomputable def fragment0467147Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0467147Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0467147Field000Value00 : SourceJson := .number (String.ofList ['1', '4', '2'])
noncomputable def fragment0467147Acc00100 : List (String × SourceJson) := (fragment0467147Field000Key00, fragment0467147Field000Value00) :: fragment0467147Acc00000
noncomputable def fragment0467147Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', '2', ',']

theorem object_fragment0467147_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0467147Field000Chars00 ++ tail)) fragment0467147Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0467147Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_000"
  err.flush

noncomputable def fragment0467147Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0467147Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6'])]
noncomputable def fragment0467147Acc00200 : List (String × SourceJson) := (fragment0467147Field001Key00, fragment0467147Field001Value00) :: fragment0467147Acc00100
noncomputable def fragment0467147Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0467147_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0467147Field001Chars00 ++ tail)) fragment0467147Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0467147Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_001"
  err.flush

noncomputable def fragment0467147Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0467147Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '6', '4', '1', '4', '3', '0', '2', '6', '5', '7', '7', '7', '1', '0', '6', '7', '2', '7', '3', '9', '1', '0', '1', '7', '3', '7', '7', '0', '2', '8', '5', '2', '1', '6', '3', '1', '1', '0', '2', '7', '/', '1', '4', '7', '4', '9', '3', '7', '9', '6', '0', '5', '1', '3', '3', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0467147Acc00300 : List (String × SourceJson) := (fragment0467147Field002Key00, fragment0467147Field002Value00) :: fragment0467147Acc00200
noncomputable def fragment0467147Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '6', '4', '1', '4', '3', '0', '2', '6', '5', '7', '7', '7', '1', '0', '6', '7', '2', '7', '3', '9', '1', '0', '1', '7', '3', '7', '7', '0', '2', '8', '5', '2', '1', '6', '3', '1', '1', '0', '2', '7', '/', '1', '4', '7', '4', '9', '3', '7', '9', '6', '0', '5', '1', '3', '3', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0467147_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0467147Field002Chars00 ++ tail)) fragment0467147Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0467147Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_002"
  err.flush

noncomputable def fragment0467147Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0467147Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0467147Acc00400 : List (String × SourceJson) := (fragment0467147Field003Key00, fragment0467147Field003Value00) :: fragment0467147Acc00300
noncomputable def fragment0467147Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0467147_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0467147Field003Chars00 ++ tail)) fragment0467147Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0467147Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_003"
  err.flush

noncomputable def fragment0467147Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0467147Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '1', '5', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0467147Acc00500 : List (String × SourceJson) := (fragment0467147Field004Key00, fragment0467147Field004Value00) :: fragment0467147Acc00400
noncomputable def fragment0467147Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '1', '5', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0467147_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0467147Field004Chars00 ++ tail)) fragment0467147Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0467147Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_004"
  err.flush

noncomputable def fragment0467147Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0467147Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '9', '8', '5', '2', '8', '0', '2', '6', '3', '3', '1', '9', '/', '2', '0', '3', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '2', '3', '3', '3', '1', '5', '3', '8', '0', '4', '9', '/', '2', '0', '3', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '0', '5', '3', '8', '1', '8', '8', '2', '4', '1', '7', '9', '/', '6', '8', '7', '7', '6', '6', '2', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '4', '7', '8', '1', '6', '0', '5', '6', '2', '1', '0', '9', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '3', '1', '3', '3', '8', '7', '8', '3', '7', '8', '3', '7', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '4', '2', '5', '8', '6', '9', '6', '7', '8', '7', '3', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '6', '7', '9', '9', '2', '9', '7', '1', '5', '7', '9', '/', '4', '8', '2', '6', '4', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '5', '1', '1', '0', '3', '3', '1', '7', '5', '9', '3', '/', '4', '5', '8', '5', '1', '0', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '3', '6', '8', '8', '7', '3', '7', '6', '8', '2', '4', '9', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '3', '6', '8', '5', '0', '6', '9', '5', '9', '5', '6', '9', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0467147Acc00600 : List (String × SourceJson) := (fragment0467147Field005Key00, fragment0467147Field005Value00) :: fragment0467147Acc00500
noncomputable def fragment0467147Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '8', '5', '2', '8', '0', '2', '6', '3', '3', '1', '9', '/', '2', '0', '3', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '2', '3', '3', '3', '1', '5', '3', '8', '0', '4', '9', '/', '2', '0', '3', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '0', '5', '3', '8', '1', '8', '8', '2', '4', '1', '7', '9', '/', '6', '8', '7', '7', '6', '6', '2', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '4', '7', '8', '1', '6', '0', '5', '6', '2', '1', '0', '9', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '3', '1', '3', '3', '8', '7', '8', '3', '7', '8', '3', '7', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '4', '2', '5', '8', '6', '9', '6', '7', '8', '7', '3', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '6', '7', '9', '9', '2', '9', '7', '1', '5', '7', '9', '/', '4', '8', '2', '6', '4', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '5', '1', '1', '0', '3', '3', '1', '7', '5', '9', '3', '/', '4', '5', '8', '5', '1', '0', '8', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '3', '6', '8', '8', '7', '3', '7', '6', '8', '2', '4', '9', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '3', '6', '8', '5', '0', '6', '9', '5', '9', '5', '6', '9', '/', '1', '8', '3', '4', '0', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0467147_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0467147Field005Chars00 ++ tail)) fragment0467147Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0467147Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_005"
  err.flush

noncomputable def fragment0467147Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0467147Field006Value00 : SourceJson := .str (String.ofList ['3', '0', '7', '8', '0', '5', '1', '7', '4', '2', '2', '6', '9', '8', '5', '5', '0', '9', '5', '3', '6', '7', '0', '5', '6', '9', '0', '8', '3', '1', '8', '7', '7', '3', '1', '0', '9', '1', '3', '9', '8', '9', '1', '5', '4', '0', '8', '4', '0', '0', '0', '/', '2', '5', '6', '4', '5', '8', '4', '2', '3', '3', '0', '4', '6', '2', '7', '4', '6', '7', '0', '1', '5', '5', '6', '4', '2', '2', '8', '5', '6', '3', '0', '2', '8', '9', '7', '5', '1', '5', '7', '5', '9', '0', '6', '7', '4', '0', '7', '7', '7', '4', '2', '9', '7', '2', '0', '7', '9', '1', '3', '0', '0', '0', '7', '5', '4', '8', '3', '2', '0', '3'])
noncomputable def fragment0467147Acc00700 : List (String × SourceJson) := (fragment0467147Field006Key00, fragment0467147Field006Value00) :: fragment0467147Acc00600
noncomputable def fragment0467147Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '7', '8', '0', '5', '1', '7', '4', '2', '2', '6', '9', '8', '5', '5', '0', '9', '5', '3', '6', '7', '0', '5', '6', '9', '0', '8', '3', '1', '8', '7', '7', '3', '1', '0', '9', '1', '3', '9', '8', '9', '1', '5', '4', '0', '8', '4', '0', '0', '0', '/', '2', '5', '6', '4', '5', '8', '4', '2', '3', '3', '0', '4', '6', '2', '7', '4', '6', '7', '0', '1', '5', '5', '6', '4', '2', '2', '8', '5', '6', '3', '0', '2', '8', '9', '7', '5', '1', '5', '7', '5', '9', '0', '6', '7', '4', '0', '7', '7', '7', '4', '2', '9', '7', '2', '0', '7', '9', '1', '3', '0', '0', '0', '7', '5', '4', '8', '3', '2', '0', '3', '"', ',']

theorem object_fragment0467147_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0467147Field006Chars00 ++ tail)) fragment0467147Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0467147Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_006"
  err.flush

noncomputable def fragment0467147Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0467147Field007Value00 : SourceJson := .str (String.ofList ['8', '8', '3', '8', '1', '1', '6', '1', '0', '4', '7', '5', '0', '9', '8', '0', '5', '1', '3', '5', '3', '2', '3', '0', '4', '7', '5', '1', '0', '7', '9', '2', '2', '5', '4', '8', '7', '2', '0', '6', '6', '5', '1', '8', '9', '6', '1', '0', '0', '4', '9', '5', '1', '4', '9', '3', '3', '7', '3', '3', '2', '7', '5', '1', '2', '2', '8', '7', '0', '3', '6', '6', '5', '3', '0', '2', '8', '5', '6', '6', '8', '9', '2', '5', '6', '4', '3', '9', '5', '8', '9', '4', '8', '7', '1', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '9', '1', '6', '7', '6', '0', '9', '0', '7', '9', '5', '2', '6', '3', '4', '6', '1', '9', '8', '4', '9', '2', '1', '8', '4', '6', '3', '4', '3', '1', '3', '5', '6', '3', '5', '1', '0', '5', '7', '3', '2', '0', '1', '1', '1', '0', '9', '7', '8', '9', '8', '5', '8', '0', '7', '4', '1', '0', '0', '0', '5', '6', '6', '4', '1', '7', '8', '8', '2', '2', '2', '4', '6', '8', '7', '7', '8', '2', '5', '4', '0', '7', '4', '4', '1', '5', '5', '9', '7', '8', '1', '1', '8', '3', '1', '8', '7', '1', '5', '8', '6', '3', '7', '0', '0', '2', '0', '6', '0', '6', '2', '9', '2', '0', '6', '8', '6', '2', '0', '0', '2', '7', '4', '0', '6', '5', '7', '3', '0', '3', '9', '1'])
noncomputable def fragment0467147Acc00800 : List (String × SourceJson) := (fragment0467147Field007Key00, fragment0467147Field007Value00) :: fragment0467147Acc00700
noncomputable def fragment0467147Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '8', '3', '8', '1', '1', '6', '1', '0', '4', '7', '5', '0', '9', '8', '0', '5', '1', '3', '5', '3', '2', '3', '0', '4', '7', '5', '1', '0', '7', '9', '2', '2', '5', '4', '8', '7', '2', '0', '6', '6', '5', '1', '8', '9', '6', '1', '0', '0', '4', '9', '5', '1', '4', '9', '3', '3', '7', '3', '3', '2', '7', '5', '1', '2', '2', '8', '7', '0', '3', '6', '6', '5', '3', '0', '2', '8', '5', '6', '6', '8', '9', '2', '5', '6', '4', '3', '9', '5', '8', '9', '4', '8', '7', '1', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '9', '1', '6', '7', '6', '0', '9', '0', '7', '9', '5', '2', '6', '3', '4', '6', '1', '9', '8', '4', '9', '2', '1', '8', '4', '6', '3', '4', '3', '1', '3', '5', '6', '3', '5', '1', '0', '5', '7', '3', '2', '0', '1', '1', '1', '0', '9', '7', '8', '9', '8', '5', '8', '0', '7', '4', '1', '0', '0', '0', '5', '6', '6', '4', '1', '7', '8', '8', '2', '2', '2', '4', '6', '8', '7', '7', '8', '2', '5', '4', '0', '7', '4', '4', '1', '5', '5', '9', '7', '8', '1', '1', '8', '3', '1', '8', '7', '1', '5', '8', '6', '3', '7', '0', '0', '2', '0', '6', '0', '6', '2', '9', '2', '0', '6', '8', '6', '2', '0', '0', '2', '7', '4', '0', '6', '5', '7', '3', '0', '3', '9', '1', '"', ',']

theorem object_fragment0467147_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0467147Field007Chars00 ++ tail)) fragment0467147Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0467147Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_007"
  err.flush

noncomputable def fragment0467147Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0467147Field008Value00 : SourceJson := .str (String.ofList ['9', '5', '0', '9', '0', '8', '0', '6', '7', '3'])
noncomputable def fragment0467147Acc00900 : List (String × SourceJson) := (fragment0467147Field008Key00, fragment0467147Field008Value00) :: fragment0467147Acc00800
noncomputable def fragment0467147Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '5', '0', '9', '0', '8', '0', '6', '7', '3', '"', ',']

theorem object_fragment0467147_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0467147Field008Chars00 ++ tail)) fragment0467147Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0467147Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_008"
  err.flush

noncomputable def fragment0467147Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0467147Field009Value00 : SourceJson := .str (String.ofList ['4', '1', '3', '9', '2', '5', '3', '9', '7', '9', '3'])
noncomputable def fragment0467147Acc01000 : List (String × SourceJson) := (fragment0467147Field009Key00, fragment0467147Field009Value00) :: fragment0467147Acc00900
noncomputable def fragment0467147Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '3', '9', '2', '5', '3', '9', '7', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0467147_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0467147Field009Chars00 ++ tail)) fragment0467147Acc00900 =
      .ok (.obj (fragment0467147Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0467147_object_field_009"
  err.flush

noncomputable def fragment0467147Chars : List Char := '{' :: (fragment0467147Field000Chars00 ++ fragment0467147Field001Chars00 ++ fragment0467147Field002Chars00 ++ fragment0467147Field003Chars00 ++ fragment0467147Field004Chars00 ++ fragment0467147Field005Chars00 ++ fragment0467147Field006Chars00 ++ fragment0467147Field007Chars00 ++ fragment0467147Field008Chars00 ++ fragment0467147Field009Chars00)
noncomputable def fragment0467147Value : SourceJson := .obj (fragment0467147Acc01000.reverse)

theorem value_fragment0467147 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0467147Chars ++ tail) =
      .ok (fragment0467147Value, tail) := by
  have hinput : fragment0467147Chars ++ tail = '{' :: (fragment0467147Field000Chars00 ++ (fragment0467147Field001Chars00 ++ (fragment0467147Field002Chars00 ++ (fragment0467147Field003Chars00 ++ (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0467147Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0467147Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0467147Field000Chars00 ++ (fragment0467147Field001Chars00 ++ (fragment0467147Field002Chars00 ++ (fragment0467147Field003Chars00 ++ (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0467147Field000Chars00 ++ (fragment0467147Field001Chars00 ++ (fragment0467147Field002Chars00 ++ (fragment0467147Field003Chars00 ++ (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))))))))))) fragment0467147Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0467147Field001Chars00 ++ (fragment0467147Field002Chars00 ++ (fragment0467147Field003Chars00 ++ (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail))))))))))) fragment0467147Acc00100 := object_fragment0467147_field_000 fuel (fragment0467147Field001Chars00 ++ (fragment0467147Field002Chars00 ++ (fragment0467147Field003Chars00 ++ (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0467147Field002Chars00 ++ (fragment0467147Field003Chars00 ++ (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))))))))) fragment0467147Acc00200 := object_fragment0467147_field_001 fuel (fragment0467147Field002Chars00 ++ (fragment0467147Field003Chars00 ++ (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0467147Field003Chars00 ++ (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail))))))))) fragment0467147Acc00300 := object_fragment0467147_field_002 fuel (fragment0467147Field003Chars00 ++ (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))))))) fragment0467147Acc00400 := object_fragment0467147_field_003 fuel (fragment0467147Field004Chars00 ++ (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail))))))) fragment0467147Acc00500 := object_fragment0467147_field_004 fuel (fragment0467147Field005Chars00 ++ (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))))) fragment0467147Acc00600 := object_fragment0467147_field_005 fuel (fragment0467147Field006Chars00 ++ (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail))))) fragment0467147Acc00700 := object_fragment0467147_field_006 fuel (fragment0467147Field007Chars00 ++ (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))) fragment0467147Acc00800 := object_fragment0467147_field_007 fuel (fragment0467147Field008Chars00 ++ (fragment0467147Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0467147Field009Chars00 ++ (tail))) fragment0467147Acc00900 := object_fragment0467147_field_008 fuel (fragment0467147Field009Chars00 ++ (tail))
    _ = .ok (fragment0467147Value, tail) := object_fragment0467147_field_009 fuel (tail)

noncomputable def fragment0468823Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0468823Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0468823Field000Value00 : SourceJson := .number (String.ofList ['1', '4', '3'])
noncomputable def fragment0468823Acc00100 : List (String × SourceJson) := (fragment0468823Field000Key00, fragment0468823Field000Value00) :: fragment0468823Acc00000
noncomputable def fragment0468823Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', '3', ',']

theorem object_fragment0468823_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0468823Field000Chars00 ++ tail)) fragment0468823Acc00000 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0468823Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_000"
  err.flush

noncomputable def fragment0468823Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0468823Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6'])]
noncomputable def fragment0468823Acc00200 : List (String × SourceJson) := (fragment0468823Field001Key00, fragment0468823Field001Value00) :: fragment0468823Acc00100
noncomputable def fragment0468823Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0468823_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0468823Field001Chars00 ++ tail)) fragment0468823Acc00100 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0468823Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_001"
  err.flush

noncomputable def fragment0468823Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0468823Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '6', '3', '9', '4', '3', '6', '9', '3', '5', '5', '6', '6', '4', '6', '1', '8', '5', '2', '2', '3', '7', '9', '2', '6', '6', '5', '9', '3', '1', '4', '0', '6', '9', '9', '8', '2', '7', '8', '5', '9', '/', '1', '4', '7', '4', '9', '3', '7', '9', '6', '0', '5', '1', '3', '3', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0468823Acc00300 : List (String × SourceJson) := (fragment0468823Field002Key00, fragment0468823Field002Value00) :: fragment0468823Acc00200
noncomputable def fragment0468823Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '6', '3', '9', '4', '3', '6', '9', '3', '5', '5', '6', '6', '4', '6', '1', '8', '5', '2', '2', '3', '7', '9', '2', '6', '6', '5', '9', '3', '1', '4', '0', '6', '9', '9', '8', '2', '7', '8', '5', '9', '/', '1', '4', '7', '4', '9', '3', '7', '9', '6', '0', '5', '1', '3', '3', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0468823_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0468823Field002Chars00 ++ tail)) fragment0468823Acc00200 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0468823Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_002"
  err.flush

noncomputable def fragment0468823Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0468823Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0468823Acc00400 : List (String × SourceJson) := (fragment0468823Field003Key00, fragment0468823Field003Value00) :: fragment0468823Acc00300
noncomputable def fragment0468823Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0468823_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0468823Field003Chars00 ++ tail)) fragment0468823Acc00300 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0468823Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_003"
  err.flush

noncomputable def fragment0468823Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0468823Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '1', '5', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0468823Acc00500 : List (String × SourceJson) := (fragment0468823Field004Key00, fragment0468823Field004Value00) :: fragment0468823Acc00400
noncomputable def fragment0468823Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '1', '5', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0468823_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0468823Field004Chars00 ++ tail)) fragment0468823Acc00400 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0468823Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_004"
  err.flush

noncomputable def fragment0468823Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0468823Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '6', '7', '7', '2', '9', '1', '3', '9', '7', '5', '8', '3', '/', '3', '6', '6', '8', '0', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '7', '4', '5', '7', '8', '3', '6', '9', '2', '0', '9', '7', '/', '3', '6', '6', '8', '0', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '8', '5', '2', '3', '0', '8', '6', '2', '3', '3', '9', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '9', '8', '7', '1', '2', '5', '6', '8', '4', '4', '7', '0', '1', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '8', '1', '1', '4', '6', '5', '2', '5', '1', '0', '7', '/', '2', '0', '3', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '6', '0', '7', '1', '2', '2', '9', '6', '1', '5', '7', '/', '1', '5', '2', '8', '3', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '8', '9', '1', '7', '6', '7', '0', '2', '0', '7', '/', '1', '8', '0', '9', '9', '1', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '1', '4', '8', '6', '5', '0', '6', '3', '9', '7', '0', '1', '9', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '8', '6', '6', '0', '2', '7', '4', '7', '8', '9', '8', '9', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '8', '6', '5', '2', '9', '3', '8', '6', '1', '6', '2', '9', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0468823Acc00600 : List (String × SourceJson) := (fragment0468823Field005Key00, fragment0468823Field005Value00) :: fragment0468823Acc00500
noncomputable def fragment0468823Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '7', '7', '2', '9', '1', '3', '9', '7', '5', '8', '3', '/', '3', '6', '6', '8', '0', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '4', '5', '7', '8', '3', '6', '9', '2', '0', '9', '7', '/', '3', '6', '6', '8', '0', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '8', '5', '2', '3', '0', '8', '6', '2', '3', '3', '9', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '9', '8', '7', '1', '2', '5', '6', '8', '4', '4', '7', '0', '1', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '8', '1', '1', '4', '6', '5', '2', '5', '1', '0', '7', '/', '2', '0', '3', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '6', '0', '7', '1', '2', '2', '9', '6', '1', '5', '7', '/', '1', '5', '2', '8', '3', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '8', '9', '1', '7', '6', '7', '0', '2', '0', '7', '/', '1', '8', '0', '9', '9', '1', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '4', '8', '6', '5', '0', '6', '3', '9', '7', '0', '1', '9', '/', '2', '7', '5', '1', '0', '6', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '8', '6', '6', '0', '2', '7', '4', '7', '8', '9', '8', '9', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '8', '6', '5', '2', '9', '3', '8', '6', '1', '6', '2', '9', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0468823_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0468823Field005Chars00 ++ tail)) fragment0468823Acc00500 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0468823Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_005"
  err.flush

noncomputable def fragment0468823Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0468823Field006Value00 : SourceJson := .str (String.ofList ['3', '0', '7', '7', '5', '6', '6', '3', '8', '7', '8', '9', '1', '5', '2', '9', '3', '4', '3', '2', '3', '1', '9', '3', '0', '9', '7', '1', '9', '3', '5', '0', '5', '5', '4', '4', '8', '8', '5', '2', '5', '5', '2', '5', '6', '2', '2', '8', '0', '0', '0', '/', '2', '5', '6', '4', '5', '7', '1', '8', '4', '5', '6', '4', '0', '4', '8', '9', '7', '4', '1', '4', '8', '8', '9', '4', '4', '5', '4', '4', '3', '8', '0', '8', '9', '6', '0', '1', '4', '3', '5', '7', '4', '6', '3', '4', '5', '5', '4', '0', '0', '7', '2', '6', '1', '9', '4', '8', '1', '6', '9', '4', '2', '0', '9', '8', '8', '6', '1', '7', '1', '9'])
noncomputable def fragment0468823Acc00700 : List (String × SourceJson) := (fragment0468823Field006Key00, fragment0468823Field006Value00) :: fragment0468823Acc00600
noncomputable def fragment0468823Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '7', '7', '5', '6', '6', '3', '8', '7', '8', '9', '1', '5', '2', '9', '3', '4', '3', '2', '3', '1', '9', '3', '0', '9', '7', '1', '9', '3', '5', '0', '5', '5', '4', '4', '8', '8', '5', '2', '5', '5', '2', '5', '6', '2', '2', '8', '0', '0', '0', '/', '2', '5', '6', '4', '5', '7', '1', '8', '4', '5', '6', '4', '0', '4', '8', '9', '7', '4', '1', '4', '8', '8', '9', '4', '4', '5', '4', '4', '3', '8', '0', '8', '9', '6', '0', '1', '4', '3', '5', '7', '4', '6', '3', '4', '5', '5', '4', '0', '0', '7', '2', '6', '1', '9', '4', '8', '1', '6', '9', '4', '2', '0', '9', '8', '8', '6', '1', '7', '1', '9', '"', ',']

theorem object_fragment0468823_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0468823Field006Chars00 ++ tail)) fragment0468823Acc00600 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0468823Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_006"
  err.flush

noncomputable def fragment0468823Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0468823Field007Value00 : SourceJson := .str (String.ofList ['7', '5', '5', '5', '3', '9', '7', '7', '2', '8', '9', '4', '0', '1', '9', '9', '1', '3', '9', '6', '8', '4', '8', '3', '4', '0', '7', '8', '7', '1', '2', '1', '8', '7', '8', '0', '4', '0', '8', '1', '0', '2', '4', '1', '1', '6', '5', '9', '0', '0', '4', '4', '5', '9', '6', '2', '0', '2', '6', '6', '3', '1', '3', '9', '1', '2', '4', '9', '1', '6', '6', '0', '8', '9', '9', '5', '9', '3', '9', '6', '1', '7', '1', '0', '8', '5', '0', '3', '1', '2', '3', '5', '5', '2', '0', '8', '4', '4', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '1', '0', '3', '6', '3', '2', '2', '7', '6', '5', '3', '3', '6', '8', '3', '7', '9', '1', '5', '1', '0', '8', '9', '9', '9', '6', '0', '4', '2', '3', '7', '0', '4', '9', '6', '7', '1', '7', '5', '2', '3', '6', '9', '6', '6', '4', '6', '6', '0', '2', '0', '8', '7', '9', '7', '9', '9', '7', '5', '7', '3', '9', '5', '5', '5', '8', '6', '8', '5', '2', '2', '9', '4', '1', '6', '1', '8', '4', '9', '9', '7', '8', '1', '8', '9', '2', '2', '5', '8', '5', '4', '9', '8', '0', '2', '2', '5', '7', '4', '8', '4', '9', '6', '7', '8', '1', '1', '3', '3', '8', '8', '1', '0', '9', '7', '2', '0', '1', '7', '3', '0', '9', '4', '2', '5', '6', '1', '7', '1', '5', '5', '6', '0', '3'])
noncomputable def fragment0468823Acc00800 : List (String × SourceJson) := (fragment0468823Field007Key00, fragment0468823Field007Value00) :: fragment0468823Acc00700
noncomputable def fragment0468823Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '5', '5', '5', '3', '9', '7', '7', '2', '8', '9', '4', '0', '1', '9', '9', '1', '3', '9', '6', '8', '4', '8', '3', '4', '0', '7', '8', '7', '1', '2', '1', '8', '7', '8', '0', '4', '0', '8', '1', '0', '2', '4', '1', '1', '6', '5', '9', '0', '0', '4', '4', '5', '9', '6', '2', '0', '2', '6', '6', '3', '1', '3', '9', '1', '2', '4', '9', '1', '6', '6', '0', '8', '9', '9', '5', '9', '3', '9', '6', '1', '7', '1', '0', '8', '5', '0', '3', '1', '2', '3', '5', '5', '2', '0', '8', '4', '4', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '1', '0', '3', '6', '3', '2', '2', '7', '6', '5', '3', '3', '6', '8', '3', '7', '9', '1', '5', '1', '0', '8', '9', '9', '9', '6', '0', '4', '2', '3', '7', '0', '4', '9', '6', '7', '1', '7', '5', '2', '3', '6', '9', '6', '6', '4', '6', '6', '0', '2', '0', '8', '7', '9', '7', '9', '9', '7', '5', '7', '3', '9', '5', '5', '5', '8', '6', '8', '5', '2', '2', '9', '4', '1', '6', '1', '8', '4', '9', '9', '7', '8', '1', '8', '9', '2', '2', '5', '8', '5', '4', '9', '8', '0', '2', '2', '5', '7', '4', '8', '4', '9', '6', '7', '8', '1', '1', '3', '3', '8', '8', '1', '0', '9', '7', '2', '0', '1', '7', '3', '0', '9', '4', '2', '5', '6', '1', '7', '1', '5', '5', '6', '0', '3', '"', ',']

theorem object_fragment0468823_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0468823Field007Chars00 ++ tail)) fragment0468823Acc00700 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0468823Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_007"
  err.flush

noncomputable def fragment0468823Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0468823Field008Value00 : SourceJson := .str (String.ofList ['9', '5', '0', '7', '6', '2', '7', '1', '8', '3'])
noncomputable def fragment0468823Acc00900 : List (String × SourceJson) := (fragment0468823Field008Key00, fragment0468823Field008Value00) :: fragment0468823Acc00800
noncomputable def fragment0468823Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '5', '0', '7', '6', '2', '7', '1', '8', '3', '"', ',']

theorem object_fragment0468823_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0468823Field008Chars00 ++ tail)) fragment0468823Acc00800 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0468823Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_008"
  err.flush

noncomputable def fragment0468823Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0468823Field009Value00 : SourceJson := .str (String.ofList ['4', '2', '4', '4', '2', '9', '8', '6', '8', '4', '1'])
noncomputable def fragment0468823Acc01000 : List (String × SourceJson) := (fragment0468823Field009Key00, fragment0468823Field009Value00) :: fragment0468823Acc00900
noncomputable def fragment0468823Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '4', '4', '2', '9', '8', '6', '8', '4', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0468823_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0468823Field009Chars00 ++ tail)) fragment0468823Acc00900 =
      .ok (.obj (fragment0468823Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0468823_object_field_009"
  err.flush

noncomputable def fragment0468823Chars : List Char := '{' :: (fragment0468823Field000Chars00 ++ fragment0468823Field001Chars00 ++ fragment0468823Field002Chars00 ++ fragment0468823Field003Chars00 ++ fragment0468823Field004Chars00 ++ fragment0468823Field005Chars00 ++ fragment0468823Field006Chars00 ++ fragment0468823Field007Chars00 ++ fragment0468823Field008Chars00 ++ fragment0468823Field009Chars00)
noncomputable def fragment0468823Value : SourceJson := .obj (fragment0468823Acc01000.reverse)

theorem value_fragment0468823 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 265) (fragment0468823Chars ++ tail) =
      .ok (fragment0468823Value, tail) := by
  have hinput : fragment0468823Chars ++ tail = '{' :: (fragment0468823Field000Chars00 ++ (fragment0468823Field001Chars00 ++ (fragment0468823Field002Chars00 ++ (fragment0468823Field003Chars00 ++ (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0468823Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 265) (fragment0468823Chars ++ tail) =
        SourceJson.value (fuel + 265) ('{' :: (fragment0468823Field000Chars00 ++ (fragment0468823Field001Chars00 ++ (fragment0468823Field002Chars00 ++ (fragment0468823Field003Chars00 ++ (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 265)) hinput
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0468823Field000Chars00 ++ (fragment0468823Field001Chars00 ++ (fragment0468823Field002Chars00 ++ (fragment0468823Field003Chars00 ++ (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))))))))))) fragment0468823Acc00000 := by rfl
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0468823Field001Chars00 ++ (fragment0468823Field002Chars00 ++ (fragment0468823Field003Chars00 ++ (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail))))))))))) fragment0468823Acc00100 := object_fragment0468823_field_000 fuel (fragment0468823Field001Chars00 ++ (fragment0468823Field002Chars00 ++ (fragment0468823Field003Chars00 ++ (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0468823Field002Chars00 ++ (fragment0468823Field003Chars00 ++ (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))))))))) fragment0468823Acc00200 := object_fragment0468823_field_001 fuel (fragment0468823Field002Chars00 ++ (fragment0468823Field003Chars00 ++ (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0468823Field003Chars00 ++ (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail))))))))) fragment0468823Acc00300 := object_fragment0468823_field_002 fuel (fragment0468823Field003Chars00 ++ (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))))))) fragment0468823Acc00400 := object_fragment0468823_field_003 fuel (fragment0468823Field004Chars00 ++ (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail))))))) fragment0468823Acc00500 := object_fragment0468823_field_004 fuel (fragment0468823Field005Chars00 ++ (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))))) fragment0468823Acc00600 := object_fragment0468823_field_005 fuel (fragment0468823Field006Chars00 ++ (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail))))) fragment0468823Acc00700 := object_fragment0468823_field_006 fuel (fragment0468823Field007Chars00 ++ (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))) fragment0468823Acc00800 := object_fragment0468823_field_007 fuel (fragment0468823Field008Chars00 ++ (fragment0468823Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0468823Field009Chars00 ++ (tail))) fragment0468823Acc00900 := object_fragment0468823_field_008 fuel (fragment0468823Field009Chars00 ++ (tail))
    _ = .ok (fragment0468823Value, tail) := object_fragment0468823_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0142_before_reader"
  err.flush

noncomputable def chunk0142LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0142SuffixChars00 : List Char := [',']
noncomputable def chunk0142Chars00 : List Char := chunk0142LeadChars00 ++ fragment0467147Chars ++ chunk0142SuffixChars00
noncomputable def chunk0142Push00 (acc : List SourceJson) : List SourceJson := fragment0467147Value :: acc

noncomputable def chunk0142AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0142_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 462)
      (SourceJson.white (chunk0142LeadChars00 ++ (fragment0467147Chars ++ rest))) acc =
      (SourceJson.value (fuel + 461) (fragment0467147Chars ++ rest)).bind
        (chunk0142AfterValue00 (fuel + 461) acc) := by rfl

theorem array_chunk0142 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 462) (SourceJson.white (chunk0142Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 461) (SourceJson.white tail) (chunk0142Push00 acc) := by
  have hinput : chunk0142Chars00 ++ tail = chunk0142LeadChars00 ++ (fragment0467147Chars ++ (chunk0142SuffixChars00 ++ tail)) := by
    simp only [chunk0142Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 462) (SourceJson.white (chunk0142Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 462)
          (SourceJson.white (chunk0142LeadChars00 ++ (fragment0467147Chars ++ (chunk0142SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 462) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 461) (fragment0467147Chars ++ (chunk0142SuffixChars00 ++ tail))).bind
        (chunk0142AfterValue00 (fuel + 461) acc) := array_chunk0142_head fuel (chunk0142SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0467147Value, chunk0142SuffixChars00 ++ tail)).bind
        (chunk0142AfterValue00 (fuel + 461) acc) :=
      congrArg (fun result => result.bind (chunk0142AfterValue00 (fuel + 461) acc))
        (value_fragment0467147 (fuel + 200) (chunk0142SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 461) (SourceJson.white tail) (chunk0142Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0142_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0143_before_reader"
  err.flush

noncomputable def chunk0143LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0143SuffixChars00 : List Char := ['\r', '\n', ' ', ' ', ']']
noncomputable def chunk0143Chars00 : List Char := chunk0143LeadChars00 ++ fragment0468823Chars ++ chunk0143SuffixChars00
noncomputable def chunk0143Push00 (acc : List SourceJson) : List SourceJson := fragment0468823Value :: acc

noncomputable def chunk0143AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0143_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 461)
      (SourceJson.white (chunk0143LeadChars00 ++ (fragment0468823Chars ++ rest))) acc =
      (SourceJson.value (fuel + 460) (fragment0468823Chars ++ rest)).bind
        (chunk0143AfterValue00 (fuel + 460) acc) := by rfl

theorem array_chunk0143 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 461) (SourceJson.white (chunk0143Chars00 ++ tail)) acc =
      .ok (.arr ((chunk0143Push00 acc).reverse), tail) := by
  have hinput : chunk0143Chars00 ++ tail = chunk0143LeadChars00 ++ (fragment0468823Chars ++ (chunk0143SuffixChars00 ++ tail)) := by
    simp only [chunk0143Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 461) (SourceJson.white (chunk0143Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 461)
          (SourceJson.white (chunk0143LeadChars00 ++ (fragment0468823Chars ++ (chunk0143SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 461) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 460) (fragment0468823Chars ++ (chunk0143SuffixChars00 ++ tail))).bind
        (chunk0143AfterValue00 (fuel + 460) acc) := array_chunk0143_head fuel (chunk0143SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0468823Value, chunk0143SuffixChars00 ++ tail)).bind
        (chunk0143AfterValue00 (fuel + 460) acc) :=
      congrArg (fun result => result.bind (chunk0143AfterValue00 (fuel + 460) acc))
        (value_fragment0468823 (fuel + 195) (chunk0143SuffixChars00 ++ tail))
    _ = .ok (.arr ((chunk0143Push00 acc).reverse), tail) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0143_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0142Chars00 ++ chunk0143Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0143Push00 (chunk0142Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 462) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk0142Chars00 ++ (chunk0143Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 462) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 462) (SourceJson.white (chunk0142Chars00 ++ (chunk0143Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 462) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 461) (SourceJson.white (chunk0143Chars00 ++ (tail))) (chunk0142Push00 (acc)) := array_chunk0142 fuel (chunk0143Chars00 ++ (tail)) (acc)
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk0143 fuel (tail) (chunk0142Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 467141).take 3358 = blockChars := by rfl

theorem block_original_split : sourceRest 467141 = blockChars ++ sourceRest 470499 := by
  calc
    sourceRest 467141 = (sourceRest 467141).take 3358 ++ (sourceRest 467141).drop 3358 :=
      (List.take_append_drop 3358 (sourceRest 467141)).symm
    _ = blockChars ++ (sourceRest 467141).drop 3358 :=
      congrArg (fun part => part ++ (sourceRest 467141).drop 3358) block_original_prefix
    _ = blockChars ++ sourceRest 470499 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 467141 3358)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 462) (SourceJson.white (sourceRest 467141)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 470499) :=
  (congrArg (fun chars => SourceJson.array (fuel + 462) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 470499) acc)

#print axioms object_fragment0467147_field_000
#print axioms object_fragment0467147_field_001
#print axioms object_fragment0467147_field_002
#print axioms object_fragment0467147_field_003
#print axioms object_fragment0467147_field_004
#print axioms object_fragment0467147_field_005
#print axioms object_fragment0467147_field_006
#print axioms object_fragment0467147_field_007
#print axioms object_fragment0467147_field_008
#print axioms object_fragment0467147_field_009
#print axioms value_fragment0467147
#print axioms object_fragment0468823_field_000
#print axioms object_fragment0468823_field_001
#print axioms object_fragment0468823_field_002
#print axioms object_fragment0468823_field_003
#print axioms object_fragment0468823_field_004
#print axioms object_fragment0468823_field_005
#print axioms object_fragment0468823_field_006
#print axioms object_fragment0468823_field_007
#print axioms object_fragment0468823_field_008
#print axioms object_fragment0468823_field_009
#print axioms value_fragment0468823
#print axioms array_chunk0142_head
#print axioms array_chunk0142
#print axioms array_chunk0143_head
#print axioms array_chunk0143
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock072

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
