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

namespace SimplicesBlock025

noncomputable def fragment0310147Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0310147Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0310147Field000Value00 : SourceJson := .number (String.ofList ['4', '9'])
noncomputable def fragment0310147Acc00100 : List (String × SourceJson) := (fragment0310147Field000Key00, fragment0310147Field000Value00) :: fragment0310147Acc00000
noncomputable def fragment0310147Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '9', ',']

theorem object_fragment0310147_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 272) (SourceJson.white (fragment0310147Field000Chars00 ++ tail)) fragment0310147Acc00000 =
      SourceJson.object (fuel + 271) (SourceJson.white tail) fragment0310147Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_000"
  err.flush

noncomputable def fragment0310147Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0310147Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['6']), .number (String.ofList ['0'])]
noncomputable def fragment0310147Acc00200 : List (String × SourceJson) := (fragment0310147Field001Key00, fragment0310147Field001Value00) :: fragment0310147Acc00100
noncomputable def fragment0310147Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0310147_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 271) (SourceJson.white (fragment0310147Field001Chars00 ++ tail)) fragment0310147Acc00100 =
      SourceJson.object (fuel + 270) (SourceJson.white tail) fragment0310147Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_001"
  err.flush

noncomputable def fragment0310147Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0310147Field002Value00 : SourceJson := .str (String.ofList ['9', '0', '6', '0', '2', '1', '4', '9', '1', '5', '3', '2', '4', '1', '9', '6', '4', '4', '3', '5', '1', '7', '3', '8', '7', '2', '2', '4', '3', '1', '5', '5', '2', '4', '8', '3', '6', '2', '8', '9', '4', '8', '4', '1', '/', '9', '8', '6', '9', '1', '9', '9', '9', '3', '9', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0310147Acc00300 : List (String × SourceJson) := (fragment0310147Field002Key00, fragment0310147Field002Value00) :: fragment0310147Acc00200
noncomputable def fragment0310147Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '0', '6', '0', '2', '1', '4', '9', '1', '5', '3', '2', '4', '1', '9', '6', '4', '4', '3', '5', '1', '7', '3', '8', '7', '2', '2', '4', '3', '1', '5', '5', '2', '4', '8', '3', '6', '2', '8', '9', '4', '8', '4', '1', '/', '9', '8', '6', '9', '1', '9', '9', '9', '3', '9', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0310147_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment0310147Field002Chars00 ++ tail)) fragment0310147Acc00200 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment0310147Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_002"
  err.flush

noncomputable def fragment0310147Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0310147Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0310147Acc00400 : List (String × SourceJson) := (fragment0310147Field003Key00, fragment0310147Field003Value00) :: fragment0310147Acc00300
noncomputable def fragment0310147Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0310147_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0310147Field003Chars00 ++ tail)) fragment0310147Acc00300 =
      SourceJson.object (fuel + 268) (SourceJson.white tail) fragment0310147Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_003"
  err.flush

noncomputable def fragment0310147Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0310147Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0310147Acc00500 : List (String × SourceJson) := (fragment0310147Field004Key00, fragment0310147Field004Value00) :: fragment0310147Acc00400
noncomputable def fragment0310147Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0310147_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment0310147Field004Chars00 ++ tail)) fragment0310147Acc00400 =
      SourceJson.object (fuel + 267) (SourceJson.white tail) fragment0310147Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_004"
  err.flush

noncomputable def fragment0310147Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0310147Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '5', '6', '2', '3', '4', '6', '7', '9', '6', '4', '3', '7', '9', '/', '3', '4', '7', '5', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '9', '9', '5', '8', '2', '5', '1', '5', '7', '5', '9', '/', '3', '4', '7', '5', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '6', '7', '9', '6', '2', '2', '6', '3', '1', '5', '4', '6', '1', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '4', '0', '7', '4', '6', '9', '6', '2', '2', '8', '3', '1', '/', '5', '2', '1', '3', '3', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '7', '1', '9', '8', '1', '2', '5', '1', '9', '6', '9', '2', '9', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '3', '7', '1', '1', '8', '1', '9', '5', '6', '9', '6', '7', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '1', '1', '4', '2', '1', '6', '3', '6', '0', '3', '9', '/', '1', '6', '4', '6', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '5', '4', '6', '7', '6', '0', '3', '9', '3', '9', '6', '1', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '1', '7', '0', '8', '4', '3', '2', '6', '7', '6', '4', '3', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '1', '4', '5', '5', '4', '5', '3', '0', '0', '8', '2', '3', '/', '6', '2', '5', '6', '0', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0310147Acc00600 : List (String × SourceJson) := (fragment0310147Field005Key00, fragment0310147Field005Value00) :: fragment0310147Acc00500
noncomputable def fragment0310147Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '2', '3', '4', '6', '7', '9', '6', '4', '3', '7', '9', '/', '3', '4', '7', '5', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '9', '9', '5', '8', '2', '5', '1', '5', '7', '5', '9', '/', '3', '4', '7', '5', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '6', '7', '9', '6', '2', '2', '6', '3', '1', '5', '4', '6', '1', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '4', '0', '7', '4', '6', '9', '6', '2', '2', '8', '3', '1', '/', '5', '2', '1', '3', '3', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '1', '9', '8', '1', '2', '5', '1', '9', '6', '9', '2', '9', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '3', '7', '1', '1', '8', '1', '9', '5', '6', '9', '6', '7', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '1', '1', '4', '2', '1', '6', '3', '6', '0', '3', '9', '/', '1', '6', '4', '6', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '5', '4', '6', '7', '6', '0', '3', '9', '3', '9', '6', '1', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '1', '7', '0', '8', '4', '3', '2', '6', '7', '6', '4', '3', '/', '3', '1', '2', '8', '0', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '1', '4', '5', '5', '4', '5', '3', '0', '0', '8', '2', '3', '/', '6', '2', '5', '6', '0', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0310147_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 267) (SourceJson.white (fragment0310147Field005Chars00 ++ tail)) fragment0310147Acc00500 =
      SourceJson.object (fuel + 266) (SourceJson.white tail) fragment0310147Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_005"
  err.flush

noncomputable def fragment0310147Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0310147Field006Value00 : SourceJson := .str (String.ofList ['1', '6', '0', '8', '4', '7', '4', '6', '3', '5', '0', '8', '9', '7', '5', '3', '3', '8', '5', '9', '4', '5', '5', '5', '8', '8', '2', '9', '5', '0', '6', '9', '9', '3', '4', '0', '5', '0', '6', '2', '9', '1', '6', '8', '3', '5', '7', '5', '3', '0', '3', '5', '6', '4', '/', '2', '1', '4', '4', '2', '8', '9', '9', '9', '5', '8', '2', '7', '4', '5', '7', '4', '3', '3', '8', '7', '5', '3', '2', '9', '2', '4', '3', '2', '0', '4', '0', '5', '1', '0', '3', '0', '2', '2', '4', '5', '1', '4', '6', '8', '1', '5', '4', '3', '7', '5', '2', '3', '9', '0', '0', '5', '5', '5', '1', '2', '3', '9', '7', '0', '6', '2', '5'])
noncomputable def fragment0310147Acc00700 : List (String × SourceJson) := (fragment0310147Field006Key00, fragment0310147Field006Value00) :: fragment0310147Acc00600
noncomputable def fragment0310147Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '0', '8', '4', '7', '4', '6', '3', '5', '0', '8', '9', '7', '5', '3', '3', '8', '5', '9', '4', '5', '5', '5', '8', '8', '2', '9', '5', '0', '6', '9', '9', '3', '4', '0', '5', '0', '6', '2', '9', '1', '6', '8', '3', '5', '7', '5', '3', '0', '3', '5', '6', '4', '/', '2', '1', '4', '4', '2', '8', '9', '9', '9', '5', '8', '2', '7', '4', '5', '7', '4', '3', '3', '8', '7', '5', '3', '2', '9', '2', '4', '3', '2', '0', '4', '0', '5', '1', '0', '3', '0', '2', '2', '4', '5', '1', '4', '6', '8', '1', '5', '4', '3', '7', '5', '2', '3', '9', '0', '0', '5', '5', '5', '1', '2', '3', '9', '7', '0', '6', '2', '5', '"', ',']

theorem object_fragment0310147_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0310147Field006Chars00 ++ tail)) fragment0310147Acc00600 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0310147Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_006"
  err.flush

noncomputable def fragment0310147Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0310147Field007Value00 : SourceJson := .str (String.ofList ['2', '6', '2', '9', '5', '5', '1', '1', '5', '9', '7', '7', '9', '7', '1', '8', '8', '2', '4', '7', '7', '0', '0', '9', '1', '1', '3', '8', '6', '2', '6', '0', '1', '6', '4', '6', '2', '5', '6', '2', '5', '2', '3', '9', '4', '9', '4', '8', '1', '7', '2', '6', '5', '4', '7', '6', '4', '7', '7', '6', '2', '5', '2', '8', '4', '7', '1', '0', '6', '3', '6', '4', '6', '8', '5', '2', '1', '3', '0', '9', '9', '4', '3', '0', '6', '4', '7', '3', '5', '2', '9', '0', '1', '1', '9', '6', '9', '8', '1', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '0', '3', '5', '7', '8', '3', '1', '1', '8', '3', '3', '4', '0', '5', '6', '8', '0', '7', '2', '7', '2', '3', '0', '1', '5', '8', '0', '3', '1', '2', '8', '4', '6', '0', '0', '7', '3', '5', '0', '3', '2', '5', '8', '3', '9', '3', '3', '1', '4', '2', '3', '6', '6', '9', '5', '7', '3', '4', '5', '6', '3', '3', '3', '8', '0', '7', '7', '6', '2', '4', '9', '8', '3', '9', '5', '4', '2', '1', '5', '4', '2', '3', '9', '8', '3', '9', '3', '6', '6', '9', '4', '5', '0', '8', '8', '9', '9', '8', '9', '1', '2', '2', '0', '8', '4', '5', '9', '7', '2', '4', '0', '4', '4', '9', '9', '4', '2', '2', '5', '4', '4', '5', '6', '2', '3', '7', '9', '0', '0', '6', '3', '3', '4', '8', '5', '1'])
noncomputable def fragment0310147Acc00800 : List (String × SourceJson) := (fragment0310147Field007Key00, fragment0310147Field007Value00) :: fragment0310147Acc00700
noncomputable def fragment0310147Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '2', '9', '5', '5', '1', '1', '5', '9', '7', '7', '9', '7', '1', '8', '8', '2', '4', '7', '7', '0', '0', '9', '1', '1', '3', '8', '6', '2', '6', '0', '1', '6', '4', '6', '2', '5', '6', '2', '5', '2', '3', '9', '4', '9', '4', '8', '1', '7', '2', '6', '5', '4', '7', '6', '4', '7', '7', '6', '2', '5', '2', '8', '4', '7', '1', '0', '6', '3', '6', '4', '6', '8', '5', '2', '1', '3', '0', '9', '9', '4', '3', '0', '6', '4', '7', '3', '5', '2', '9', '0', '1', '1', '9', '6', '9', '8', '1', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '0', '3', '5', '7', '8', '3', '1', '1', '8', '3', '3', '4', '0', '5', '6', '8', '0', '7', '2', '7', '2', '3', '0', '1', '5', '8', '0', '3', '1', '2', '8', '4', '6', '0', '0', '7', '3', '5', '0', '3', '2', '5', '8', '3', '9', '3', '3', '1', '4', '2', '3', '6', '6', '9', '5', '7', '3', '4', '5', '6', '3', '3', '3', '8', '0', '7', '7', '6', '2', '4', '9', '8', '3', '9', '5', '4', '2', '1', '5', '4', '2', '3', '9', '8', '3', '9', '3', '6', '6', '9', '4', '5', '0', '8', '8', '9', '9', '8', '9', '1', '2', '2', '0', '8', '4', '5', '9', '7', '2', '4', '0', '4', '4', '9', '9', '4', '2', '2', '5', '4', '4', '5', '6', '2', '3', '7', '9', '0', '0', '6', '3', '3', '4', '8', '5', '1', '"', ',']

theorem object_fragment0310147_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0310147Field007Chars00 ++ tail)) fragment0310147Acc00700 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0310147Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_007"
  err.flush

noncomputable def fragment0310147Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0310147Field008Value00 : SourceJson := .str (String.ofList ['5', '9', '4', '3', '0', '6', '2', '2', '7', '4', '0', '8', '3', '2', '5'])
noncomputable def fragment0310147Acc00900 : List (String × SourceJson) := (fragment0310147Field008Key00, fragment0310147Field008Value00) :: fragment0310147Acc00800
noncomputable def fragment0310147Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '4', '3', '0', '6', '2', '2', '7', '4', '0', '8', '3', '2', '5', '"', ',']

theorem object_fragment0310147_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0310147Field008Chars00 ++ tail)) fragment0310147Acc00800 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0310147Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_008"
  err.flush

noncomputable def fragment0310147Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0310147Field009Value00 : SourceJson := .str (String.ofList ['5', '1', '6', '2', '1', '8', '2', '9', '1', '5', '1', '3', '6', '4', '0', '2'])
noncomputable def fragment0310147Acc01000 : List (String × SourceJson) := (fragment0310147Field009Key00, fragment0310147Field009Value00) :: fragment0310147Acc00900
noncomputable def fragment0310147Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '1', '6', '2', '1', '8', '2', '9', '1', '5', '1', '3', '6', '4', '0', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0310147_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0310147Field009Chars00 ++ tail)) fragment0310147Acc00900 =
      .ok (.obj (fragment0310147Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0310147_object_field_009"
  err.flush

noncomputable def fragment0310147Chars : List Char := '{' :: (fragment0310147Field000Chars00 ++ fragment0310147Field001Chars00 ++ fragment0310147Field002Chars00 ++ fragment0310147Field003Chars00 ++ fragment0310147Field004Chars00 ++ fragment0310147Field005Chars00 ++ fragment0310147Field006Chars00 ++ fragment0310147Field007Chars00 ++ fragment0310147Field008Chars00 ++ fragment0310147Field009Chars00)
noncomputable def fragment0310147Value : SourceJson := .obj (fragment0310147Acc01000.reverse)

theorem value_fragment0310147 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 273) (fragment0310147Chars ++ tail) =
      .ok (fragment0310147Value, tail) := by
  have hinput : fragment0310147Chars ++ tail = '{' :: (fragment0310147Field000Chars00 ++ (fragment0310147Field001Chars00 ++ (fragment0310147Field002Chars00 ++ (fragment0310147Field003Chars00 ++ (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0310147Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 273) (fragment0310147Chars ++ tail) =
        SourceJson.value (fuel + 273) ('{' :: (fragment0310147Field000Chars00 ++ (fragment0310147Field001Chars00 ++ (fragment0310147Field002Chars00 ++ (fragment0310147Field003Chars00 ++ (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 273)) hinput
    _ = SourceJson.object (fuel + 272) (SourceJson.white (fragment0310147Field000Chars00 ++ (fragment0310147Field001Chars00 ++ (fragment0310147Field002Chars00 ++ (fragment0310147Field003Chars00 ++ (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))))))))))) fragment0310147Acc00000 := by rfl
    _ = SourceJson.object (fuel + 271) (SourceJson.white (fragment0310147Field001Chars00 ++ (fragment0310147Field002Chars00 ++ (fragment0310147Field003Chars00 ++ (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail))))))))))) fragment0310147Acc00100 := object_fragment0310147_field_000 fuel (fragment0310147Field001Chars00 ++ (fragment0310147Field002Chars00 ++ (fragment0310147Field003Chars00 ++ (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment0310147Field002Chars00 ++ (fragment0310147Field003Chars00 ++ (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))))))))) fragment0310147Acc00200 := object_fragment0310147_field_001 fuel (fragment0310147Field002Chars00 ++ (fragment0310147Field003Chars00 ++ (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0310147Field003Chars00 ++ (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail))))))))) fragment0310147Acc00300 := object_fragment0310147_field_002 fuel (fragment0310147Field003Chars00 ++ (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))))))) fragment0310147Acc00400 := object_fragment0310147_field_003 fuel (fragment0310147Field004Chars00 ++ (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 267) (SourceJson.white (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail))))))) fragment0310147Acc00500 := object_fragment0310147_field_004 fuel (fragment0310147Field005Chars00 ++ (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))))) fragment0310147Acc00600 := object_fragment0310147_field_005 fuel (fragment0310147Field006Chars00 ++ (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail))))) fragment0310147Acc00700 := object_fragment0310147_field_006 fuel (fragment0310147Field007Chars00 ++ (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))) fragment0310147Acc00800 := object_fragment0310147_field_007 fuel (fragment0310147Field008Chars00 ++ (fragment0310147Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0310147Field009Chars00 ++ (tail))) fragment0310147Acc00900 := object_fragment0310147_field_008 fuel (fragment0310147Field009Chars00 ++ (tail))
    _ = .ok (fragment0310147Value, tail) := object_fragment0310147_field_009 fuel (tail)

noncomputable def fragment0311839Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0311839Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0311839Field000Value00 : SourceJson := .number (String.ofList ['5', '0'])
noncomputable def fragment0311839Acc00100 : List (String × SourceJson) := (fragment0311839Field000Key00, fragment0311839Field000Value00) :: fragment0311839Acc00000
noncomputable def fragment0311839Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '0', ',']

theorem object_fragment0311839_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 277) (SourceJson.white (fragment0311839Field000Chars00 ++ tail)) fragment0311839Acc00000 =
      SourceJson.object (fuel + 276) (SourceJson.white tail) fragment0311839Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_000"
  err.flush

noncomputable def fragment0311839Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0311839Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['0'])]
noncomputable def fragment0311839Acc00200 : List (String × SourceJson) := (fragment0311839Field001Key00, fragment0311839Field001Value00) :: fragment0311839Acc00100
noncomputable def fragment0311839Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0311839_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 276) (SourceJson.white (fragment0311839Field001Chars00 ++ tail)) fragment0311839Acc00100 =
      SourceJson.object (fuel + 275) (SourceJson.white tail) fragment0311839Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_001"
  err.flush

noncomputable def fragment0311839Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0311839Field002Value00 : SourceJson := .str (String.ofList ['3', '1', '6', '7', '6', '4', '2', '8', '6', '9', '0', '5', '7', '8', '5', '8', '0', '8', '8', '5', '1', '6', '0', '7', '2', '5', '4', '7', '4', '6', '0', '5', '9', '9', '6', '5', '3', '0', '2', '8', '2', '0', '2', '1', '/', '1', '0', '1', '5', '1', '1', '7', '7', '0', '8', '0', '5', '0', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0311839Acc00300 : List (String × SourceJson) := (fragment0311839Field002Key00, fragment0311839Field002Value00) :: fragment0311839Acc00200
noncomputable def fragment0311839Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '1', '6', '7', '6', '4', '2', '8', '6', '9', '0', '5', '7', '8', '5', '8', '0', '8', '8', '5', '1', '6', '0', '7', '2', '5', '4', '7', '4', '6', '0', '5', '9', '9', '6', '5', '3', '0', '2', '8', '2', '0', '2', '1', '/', '1', '0', '1', '5', '1', '1', '7', '7', '0', '8', '0', '5', '0', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0311839_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 275) (SourceJson.white (fragment0311839Field002Chars00 ++ tail)) fragment0311839Acc00200 =
      SourceJson.object (fuel + 274) (SourceJson.white tail) fragment0311839Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_002"
  err.flush

noncomputable def fragment0311839Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0311839Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0311839Acc00400 : List (String × SourceJson) := (fragment0311839Field003Key00, fragment0311839Field003Value00) :: fragment0311839Acc00300
noncomputable def fragment0311839Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0311839_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 274) (SourceJson.white (fragment0311839Field003Chars00 ++ tail)) fragment0311839Acc00300 =
      SourceJson.object (fuel + 273) (SourceJson.white tail) fragment0311839Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_003"
  err.flush

noncomputable def fragment0311839Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0311839Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0311839Acc00500 : List (String × SourceJson) := (fragment0311839Field004Key00, fragment0311839Field004Value00) :: fragment0311839Acc00400
noncomputable def fragment0311839Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0311839_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 273) (SourceJson.white (fragment0311839Field004Chars00 ++ tail)) fragment0311839Acc00400 =
      SourceJson.object (fuel + 272) (SourceJson.white tail) fragment0311839Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_004"
  err.flush

noncomputable def fragment0311839Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0311839Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '4', '8', '4', '6', '6', '7', '6', '3', '4', '3', '6', '8', '7', '/', '6', '2', '5', '6', '0', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '9', '8', '3', '6', '8', '2', '5', '3', '6', '1', '7', '1', '/', '6', '2', '5', '6', '0', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '0', '0', '9', '2', '2', '8', '4', '5', '4', '1', '9', '1', '/', '3', '7', '5', '3', '6', '0', '0', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '0', '7', '8', '8', '6', '3', '8', '5', '1', '5', '3', '/', '1', '3', '0', '3', '3', '3', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '4', '4', '4', '8', '6', '4', '6', '8', '5', '3', '5', '1', '9', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '0', '1', '8', '2', '6', '0', '2', '4', '4', '9', '1', '3', '7', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '3', '4', '9', '7', '3', '2', '3', '0', '6', '6', '8', '7', '/', '4', '9', '3', '8', '9', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '0', '6', '3', '4', '1', '6', '1', '7', '5', '4', '7', '1', '3', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '6', '5', '0', '6', '4', '1', '0', '3', '7', '5', '7', '5', '9', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '2', '3', '9', '1', '8', '4', '5', '4', '0', '0', '6', '7', '9', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0311839Acc00600 : List (String × SourceJson) := (fragment0311839Field005Key00, fragment0311839Field005Value00) :: fragment0311839Acc00500
noncomputable def fragment0311839Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '8', '4', '6', '6', '7', '6', '3', '4', '3', '6', '8', '7', '/', '6', '2', '5', '6', '0', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '9', '8', '3', '6', '8', '2', '5', '3', '6', '1', '7', '1', '/', '6', '2', '5', '6', '0', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '0', '0', '9', '2', '2', '8', '4', '5', '4', '1', '9', '1', '/', '3', '7', '5', '3', '6', '0', '0', '4', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '0', '7', '8', '8', '6', '3', '8', '5', '1', '5', '3', '/', '1', '3', '0', '3', '3', '3', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '4', '4', '4', '8', '6', '4', '6', '8', '5', '3', '5', '1', '9', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '0', '1', '8', '2', '6', '0', '2', '4', '4', '9', '1', '3', '7', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '3', '4', '9', '7', '3', '2', '3', '0', '6', '6', '8', '7', '/', '4', '9', '3', '8', '9', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '0', '6', '3', '4', '1', '6', '1', '7', '5', '4', '7', '1', '3', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '6', '5', '0', '6', '4', '1', '0', '3', '7', '5', '7', '5', '9', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '2', '3', '9', '1', '8', '4', '5', '4', '0', '0', '6', '7', '9', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0311839_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 272) (SourceJson.white (fragment0311839Field005Chars00 ++ tail)) fragment0311839Acc00500 =
      SourceJson.object (fuel + 271) (SourceJson.white tail) fragment0311839Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_005"
  err.flush

noncomputable def fragment0311839Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0311839Field006Value00 : SourceJson := .str (String.ofList ['5', '8', '1', '7', '4', '8', '3', '8', '4', '1', '9', '8', '9', '7', '9', '2', '0', '8', '0', '7', '6', '7', '2', '9', '3', '0', '0', '8', '2', '2', '0', '3', '7', '4', '0', '8', '5', '0', '8', '0', '4', '2', '5', '7', '1', '4', '2', '5', '8', '7', '8', '8', '/', '2', '3', '0', '8', '0', '5', '8', '3', '3', '6', '2', '4', '2', '9', '9', '5', '2', '9', '5', '3', '5', '5', '1', '5', '2', '5', '0', '5', '6', '1', '4', '5', '5', '5', '0', '7', '6', '2', '9', '1', '8', '8', '3', '7', '4', '9', '8', '8', '3', '0', '7', '6', '9', '9', '9', '8', '0', '7', '9', '2', '7', '5', '1', '8', '1', '2', '5'])
noncomputable def fragment0311839Acc00700 : List (String × SourceJson) := (fragment0311839Field006Key00, fragment0311839Field006Value00) :: fragment0311839Acc00600
noncomputable def fragment0311839Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '8', '1', '7', '4', '8', '3', '8', '4', '1', '9', '8', '9', '7', '9', '2', '0', '8', '0', '7', '6', '7', '2', '9', '3', '0', '0', '8', '2', '2', '0', '3', '7', '4', '0', '8', '5', '0', '8', '0', '4', '2', '5', '7', '1', '4', '2', '5', '8', '7', '8', '8', '/', '2', '3', '0', '8', '0', '5', '8', '3', '3', '6', '2', '4', '2', '9', '9', '5', '2', '9', '5', '3', '5', '5', '1', '5', '2', '5', '0', '5', '6', '1', '4', '5', '5', '5', '0', '7', '6', '2', '9', '1', '8', '8', '3', '7', '4', '9', '8', '8', '3', '0', '7', '6', '9', '9', '9', '8', '0', '7', '9', '2', '7', '5', '1', '8', '1', '2', '5', '"', ',']

theorem object_fragment0311839_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 271) (SourceJson.white (fragment0311839Field006Chars00 ++ tail)) fragment0311839Acc00600 =
      SourceJson.object (fuel + 270) (SourceJson.white tail) fragment0311839Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_006"
  err.flush

noncomputable def fragment0311839Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0311839Field007Value00 : SourceJson := .str (String.ofList ['9', '5', '0', '0', '1', '3', '8', '4', '1', '3', '5', '1', '5', '4', '4', '7', '6', '0', '0', '3', '6', '0', '1', '2', '8', '4', '1', '9', '4', '2', '5', '3', '9', '9', '5', '6', '6', '5', '5', '8', '4', '1', '6', '9', '4', '8', '5', '5', '1', '8', '2', '1', '0', '4', '2', '8', '6', '9', '4', '3', '8', '4', '5', '7', '2', '8', '1', '7', '5', '8', '9', '9', '7', '1', '3', '9', '6', '5', '1', '7', '7', '8', '5', '3', '9', '1', '7', '9', '1', '6', '8', '9', '0', '8', '8', '4', '1', '7', '0', '2', '5', '0', '6', '2', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '4', '5', '1', '1', '1', '3', '2', '8', '0', '5', '7', '6', '2', '7', '6', '8', '3', '2', '0', '4', '5', '9', '2', '5', '2', '3', '5', '4', '4', '7', '4', '9', '2', '0', '1', '6', '9', '5', '0', '2', '9', '8', '8', '8', '3', '3', '5', '3', '9', '3', '4', '6', '0', '3', '8', '0', '8', '9', '9', '4', '8', '0', '4', '2', '9', '4', '9', '2', '3', '1', '4', '1', '6', '4', '5', '6', '3', '3', '3', '8', '1', '2', '1', '9', '9', '1', '9', '8', '6', '6', '7', '2', '4', '4', '4', '1', '8', '4', '7', '3', '8', '0', '9', '8', '4', '0', '6', '2', '3', '9', '5', '5', '8', '6', '2', '9', '6', '4', '0', '1', '7', '1', '9', '4', '5', '0', '1', '2', '1', '1', '4', '2', '8', '0', '0', '5', '5', '3'])
noncomputable def fragment0311839Acc00800 : List (String × SourceJson) := (fragment0311839Field007Key00, fragment0311839Field007Value00) :: fragment0311839Acc00700
noncomputable def fragment0311839Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '5', '0', '0', '1', '3', '8', '4', '1', '3', '5', '1', '5', '4', '4', '7', '6', '0', '0', '3', '6', '0', '1', '2', '8', '4', '1', '9', '4', '2', '5', '3', '9', '9', '5', '6', '6', '5', '5', '8', '4', '1', '6', '9', '4', '8', '5', '5', '1', '8', '2', '1', '0', '4', '2', '8', '6', '9', '4', '3', '8', '4', '5', '7', '2', '8', '1', '7', '5', '8', '9', '9', '7', '1', '3', '9', '6', '5', '1', '7', '7', '8', '5', '3', '9', '1', '7', '9', '1', '6', '8', '9', '0', '8', '8', '4', '1', '7', '0', '2', '5', '0', '6', '2', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '4', '5', '1', '1', '1', '3', '2', '8', '0', '5', '7', '6', '2', '7', '6', '8', '3', '2', '0', '4', '5', '9', '2', '5', '2', '3', '5', '4', '4', '7', '4', '9', '2', '0', '1', '6', '9', '5', '0', '2', '9', '8', '8', '8', '3', '3', '5', '3', '9', '3', '4', '6', '0', '3', '8', '0', '8', '9', '9', '4', '8', '0', '4', '2', '9', '4', '9', '2', '3', '1', '4', '1', '6', '4', '5', '6', '3', '3', '3', '8', '1', '2', '1', '9', '9', '1', '9', '8', '6', '6', '7', '2', '4', '4', '4', '1', '8', '4', '7', '3', '8', '0', '9', '8', '4', '0', '6', '2', '3', '9', '5', '5', '8', '6', '2', '9', '6', '4', '0', '1', '7', '1', '9', '4', '5', '0', '1', '2', '1', '1', '4', '2', '8', '0', '0', '5', '5', '3', '"', ',']

theorem object_fragment0311839_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment0311839Field007Chars00 ++ tail)) fragment0311839Acc00700 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment0311839Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_007"
  err.flush

noncomputable def fragment0311839Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0311839Field008Value00 : SourceJson := .str (String.ofList ['1', '9', '9', '6', '9', '5', '3', '6', '6', '4', '5', '5', '7', '4', '1'])
noncomputable def fragment0311839Acc00900 : List (String × SourceJson) := (fragment0311839Field008Key00, fragment0311839Field008Value00) :: fragment0311839Acc00800
noncomputable def fragment0311839Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '9', '6', '9', '5', '3', '6', '6', '4', '5', '5', '7', '4', '1', '"', ',']

theorem object_fragment0311839_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0311839Field008Chars00 ++ tail)) fragment0311839Acc00800 =
      SourceJson.object (fuel + 268) (SourceJson.white tail) fragment0311839Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_008"
  err.flush

noncomputable def fragment0311839Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0311839Field009Value00 : SourceJson := .str (String.ofList ['1', '7', '3', '2', '2', '4', '2', '1', '7', '5', '8', '7', '6', '4', '7', '6'])
noncomputable def fragment0311839Acc01000 : List (String × SourceJson) := (fragment0311839Field009Key00, fragment0311839Field009Value00) :: fragment0311839Acc00900
noncomputable def fragment0311839Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '3', '2', '2', '4', '2', '1', '7', '5', '8', '7', '6', '4', '7', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0311839_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment0311839Field009Chars00 ++ tail)) fragment0311839Acc00900 =
      .ok (.obj (fragment0311839Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311839_object_field_009"
  err.flush

noncomputable def fragment0311839Chars : List Char := '{' :: (fragment0311839Field000Chars00 ++ fragment0311839Field001Chars00 ++ fragment0311839Field002Chars00 ++ fragment0311839Field003Chars00 ++ fragment0311839Field004Chars00 ++ fragment0311839Field005Chars00 ++ fragment0311839Field006Chars00 ++ fragment0311839Field007Chars00 ++ fragment0311839Field008Chars00 ++ fragment0311839Field009Chars00)
noncomputable def fragment0311839Value : SourceJson := .obj (fragment0311839Acc01000.reverse)

theorem value_fragment0311839 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 278) (fragment0311839Chars ++ tail) =
      .ok (fragment0311839Value, tail) := by
  have hinput : fragment0311839Chars ++ tail = '{' :: (fragment0311839Field000Chars00 ++ (fragment0311839Field001Chars00 ++ (fragment0311839Field002Chars00 ++ (fragment0311839Field003Chars00 ++ (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0311839Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 278) (fragment0311839Chars ++ tail) =
        SourceJson.value (fuel + 278) ('{' :: (fragment0311839Field000Chars00 ++ (fragment0311839Field001Chars00 ++ (fragment0311839Field002Chars00 ++ (fragment0311839Field003Chars00 ++ (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 278)) hinput
    _ = SourceJson.object (fuel + 277) (SourceJson.white (fragment0311839Field000Chars00 ++ (fragment0311839Field001Chars00 ++ (fragment0311839Field002Chars00 ++ (fragment0311839Field003Chars00 ++ (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))))))))))) fragment0311839Acc00000 := by rfl
    _ = SourceJson.object (fuel + 276) (SourceJson.white (fragment0311839Field001Chars00 ++ (fragment0311839Field002Chars00 ++ (fragment0311839Field003Chars00 ++ (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail))))))))))) fragment0311839Acc00100 := object_fragment0311839_field_000 fuel (fragment0311839Field001Chars00 ++ (fragment0311839Field002Chars00 ++ (fragment0311839Field003Chars00 ++ (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 275) (SourceJson.white (fragment0311839Field002Chars00 ++ (fragment0311839Field003Chars00 ++ (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))))))))) fragment0311839Acc00200 := object_fragment0311839_field_001 fuel (fragment0311839Field002Chars00 ++ (fragment0311839Field003Chars00 ++ (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 274) (SourceJson.white (fragment0311839Field003Chars00 ++ (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail))))))))) fragment0311839Acc00300 := object_fragment0311839_field_002 fuel (fragment0311839Field003Chars00 ++ (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 273) (SourceJson.white (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))))))) fragment0311839Acc00400 := object_fragment0311839_field_003 fuel (fragment0311839Field004Chars00 ++ (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 272) (SourceJson.white (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail))))))) fragment0311839Acc00500 := object_fragment0311839_field_004 fuel (fragment0311839Field005Chars00 ++ (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 271) (SourceJson.white (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))))) fragment0311839Acc00600 := object_fragment0311839_field_005 fuel (fragment0311839Field006Chars00 ++ (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail))))) fragment0311839Acc00700 := object_fragment0311839_field_006 fuel (fragment0311839Field007Chars00 ++ (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))) fragment0311839Acc00800 := object_fragment0311839_field_007 fuel (fragment0311839Field008Chars00 ++ (fragment0311839Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment0311839Field009Chars00 ++ (tail))) fragment0311839Acc00900 := object_fragment0311839_field_008 fuel (fragment0311839Field009Chars00 ++ (tail))
    _ = .ok (fragment0311839Value, tail) := object_fragment0311839_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_before_reader"
  err.flush

noncomputable def chunk0049LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0049SuffixChars00 : List Char := [',']
noncomputable def chunk0049Chars00 : List Char := chunk0049LeadChars00 ++ fragment0310147Chars ++ chunk0049SuffixChars00
noncomputable def chunk0049Push00 (acc : List SourceJson) : List SourceJson := fragment0310147Value :: acc

noncomputable def chunk0049AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0049_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 555)
      (SourceJson.white (chunk0049LeadChars00 ++ (fragment0310147Chars ++ rest))) acc =
      (SourceJson.value (fuel + 554) (fragment0310147Chars ++ rest)).bind
        (chunk0049AfterValue00 (fuel + 554) acc) := by rfl

theorem array_chunk0049 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 555) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 554) (SourceJson.white tail) (chunk0049Push00 acc) := by
  have hinput : chunk0049Chars00 ++ tail = chunk0049LeadChars00 ++ (fragment0310147Chars ++ (chunk0049SuffixChars00 ++ tail)) := by
    simp only [chunk0049Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 555) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 555)
          (SourceJson.white (chunk0049LeadChars00 ++ (fragment0310147Chars ++ (chunk0049SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 555) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 554) (fragment0310147Chars ++ (chunk0049SuffixChars00 ++ tail))).bind
        (chunk0049AfterValue00 (fuel + 554) acc) := array_chunk0049_head fuel (chunk0049SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0310147Value, chunk0049SuffixChars00 ++ tail)).bind
        (chunk0049AfterValue00 (fuel + 554) acc) :=
      congrArg (fun result => result.bind (chunk0049AfterValue00 (fuel + 554) acc))
        (value_fragment0310147 (fuel + 281) (chunk0049SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 554) (SourceJson.white tail) (chunk0049Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_before_reader"
  err.flush

noncomputable def chunk0050LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0050SuffixChars00 : List Char := [',']
noncomputable def chunk0050Chars00 : List Char := chunk0050LeadChars00 ++ fragment0311839Chars ++ chunk0050SuffixChars00
noncomputable def chunk0050Push00 (acc : List SourceJson) : List SourceJson := fragment0311839Value :: acc

noncomputable def chunk0050AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0050_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 554)
      (SourceJson.white (chunk0050LeadChars00 ++ (fragment0311839Chars ++ rest))) acc =
      (SourceJson.value (fuel + 553) (fragment0311839Chars ++ rest)).bind
        (chunk0050AfterValue00 (fuel + 553) acc) := by rfl

theorem array_chunk0050 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 554) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 553) (SourceJson.white tail) (chunk0050Push00 acc) := by
  have hinput : chunk0050Chars00 ++ tail = chunk0050LeadChars00 ++ (fragment0311839Chars ++ (chunk0050SuffixChars00 ++ tail)) := by
    simp only [chunk0050Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 554) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 554)
          (SourceJson.white (chunk0050LeadChars00 ++ (fragment0311839Chars ++ (chunk0050SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 554) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 553) (fragment0311839Chars ++ (chunk0050SuffixChars00 ++ tail))).bind
        (chunk0050AfterValue00 (fuel + 553) acc) := array_chunk0050_head fuel (chunk0050SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0311839Value, chunk0050SuffixChars00 ++ tail)).bind
        (chunk0050AfterValue00 (fuel + 553) acc) :=
      congrArg (fun result => result.bind (chunk0050AfterValue00 (fuel + 553) acc))
        (value_fragment0311839 (fuel + 275) (chunk0050SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 553) (SourceJson.white tail) (chunk0050Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0049Chars00 ++ chunk0050Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0050Push00 (chunk0049Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 555) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 553) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0049Chars00 ++ (chunk0050Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 555) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 555) (SourceJson.white (chunk0049Chars00 ++ (chunk0050Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 555) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 554) (SourceJson.white (chunk0050Chars00 ++ (tail))) (chunk0049Push00 (acc)) := array_chunk0049 fuel (chunk0050Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 553) (SourceJson.white tail) (blockPush acc) := array_chunk0050 fuel (tail) (chunk0049Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 310141).take 3388 = blockChars := by rfl

theorem block_original_split : sourceRest 310141 = blockChars ++ sourceRest 313529 := by
  calc
    sourceRest 310141 = (sourceRest 310141).take 3388 ++ (sourceRest 310141).drop 3388 :=
      (List.take_append_drop 3388 (sourceRest 310141)).symm
    _ = blockChars ++ (sourceRest 310141).drop 3388 :=
      congrArg (fun part => part ++ (sourceRest 310141).drop 3388) block_original_prefix
    _ = blockChars ++ sourceRest 313529 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 310141 3388)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 555) (SourceJson.white (sourceRest 310141)) acc =
      SourceJson.array (fuel + 553) (SourceJson.white (sourceRest 313529)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 555) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 313529) acc)

#print axioms object_fragment0310147_field_000
#print axioms object_fragment0310147_field_001
#print axioms object_fragment0310147_field_002
#print axioms object_fragment0310147_field_003
#print axioms object_fragment0310147_field_004
#print axioms object_fragment0310147_field_005
#print axioms object_fragment0310147_field_006
#print axioms object_fragment0310147_field_007
#print axioms object_fragment0310147_field_008
#print axioms object_fragment0310147_field_009
#print axioms value_fragment0310147
#print axioms object_fragment0311839_field_000
#print axioms object_fragment0311839_field_001
#print axioms object_fragment0311839_field_002
#print axioms object_fragment0311839_field_003
#print axioms object_fragment0311839_field_004
#print axioms object_fragment0311839_field_005
#print axioms object_fragment0311839_field_006
#print axioms object_fragment0311839_field_007
#print axioms object_fragment0311839_field_008
#print axioms object_fragment0311839_field_009
#print axioms value_fragment0311839
#print axioms array_chunk0049_head
#print axioms array_chunk0049
#print axioms array_chunk0050_head
#print axioms array_chunk0050
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock025

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
