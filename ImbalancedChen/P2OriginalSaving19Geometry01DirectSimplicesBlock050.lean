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

namespace SimplicesBlock050

noncomputable def fragment0394006Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0394006Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0394006Field000Value00 : SourceJson := .number (String.ofList ['9', '8'])
noncomputable def fragment0394006Acc00100 : List (String × SourceJson) := (fragment0394006Field000Key00, fragment0394006Field000Value00) :: fragment0394006Acc00000
noncomputable def fragment0394006Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '8', ',']

theorem object_fragment0394006_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0394006Field000Chars00 ++ tail)) fragment0394006Acc00000 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0394006Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_000"
  err.flush

noncomputable def fragment0394006Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0394006Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0394006Acc00200 : List (String × SourceJson) := (fragment0394006Field001Key00, fragment0394006Field001Value00) :: fragment0394006Acc00100
noncomputable def fragment0394006Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0394006_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0394006Field001Chars00 ++ tail)) fragment0394006Acc00100 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0394006Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_001"
  err.flush

noncomputable def fragment0394006Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0394006Field002Value00 : SourceJson := .str (String.ofList ['3', '9', '3', '6', '0', '9', '5', '5', '6', '3', '0', '8', '3', '2', '8', '1', '2', '8', '3', '0', '0', '2', '1', '3', '9', '4', '0', '0', '8', '2', '3', '4', '0', '2', '9', '3', '0', '6', '2', '5', '4', '3', '6', '0', '6', '7', '/', '1', '0', '4', '4', '3', '7', '0', '6', '5', '0', '1', '1', '5', '8', '0', '3', '7', '0', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0394006Acc00300 : List (String × SourceJson) := (fragment0394006Field002Key00, fragment0394006Field002Value00) :: fragment0394006Acc00200
noncomputable def fragment0394006Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '9', '3', '6', '0', '9', '5', '5', '6', '3', '0', '8', '3', '2', '8', '1', '2', '8', '3', '0', '0', '2', '1', '3', '9', '4', '0', '0', '8', '2', '3', '4', '0', '2', '9', '3', '0', '6', '2', '5', '4', '3', '6', '0', '6', '7', '/', '1', '0', '4', '4', '3', '7', '0', '6', '5', '0', '1', '1', '5', '8', '0', '3', '7', '0', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0394006_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0394006Field002Chars00 ++ tail)) fragment0394006Acc00200 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0394006Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_002"
  err.flush

noncomputable def fragment0394006Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0394006Field003Value00 : SourceJson := .str (String.ofList ['3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0'])
noncomputable def fragment0394006Acc00400 : List (String × SourceJson) := (fragment0394006Field003Key00, fragment0394006Field003Value00) :: fragment0394006Acc00300
noncomputable def fragment0394006Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0394006_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0394006Field003Chars00 ++ tail)) fragment0394006Acc00300 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0394006Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_003"
  err.flush

noncomputable def fragment0394006Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0394006Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['8', '0', '7', '/', '1', '7', '7', '9', '2'])]
noncomputable def fragment0394006Acc00500 : List (String × SourceJson) := (fragment0394006Field004Key00, fragment0394006Field004Value00) :: fragment0394006Acc00400
noncomputable def fragment0394006Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '/', '1', '7', '7', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0394006_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0394006Field004Chars00 ++ tail)) fragment0394006Acc00400 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0394006Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_004"
  err.flush

noncomputable def fragment0394006Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0394006Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '5', '0', '6', '0', '9', '2', '7', '9', '0', '7', '2', '7', '7', '6', '4', '8', '4', '7', '1', '/', '7', '6', '8', '2', '4', '7', '1', '2', '5', '2', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '2', '5', '7', '4', '7', '1', '7', '6', '6', '2', '4', '3', '2', '8', '4', '7', '9', '3', '/', '1', '0', '7', '5', '5', '4', '5', '9', '7', '5', '3', '4', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '7', '4', '5', '3', '4', '8', '4', '6', '4', '2', '4', '6', '0', '4', '9', '6', '2', '1', '9', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '6', '9', '3', '2', '2', '6', '3', '4', '4', '2', '1', '2', '8', '7', '9', '0', '1', '1', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '6', '9', '6', '1', '2', '1', '5', '3', '2', '8', '7', '2', '1', '1', '9', '3', '6', '3', '9', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '4', '8', '0', '9', '6', '5', '3', '9', '1', '6', '6', '1', '8', '8', '6', '0', '5', '7', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '7', '5', '6', '1', '1', '2', '7', '7', '2', '0', '5', '9', '7', '1', '8', '3', '/', '3', '3', '9', '6', '4', '6', '0', '9', '7', '4', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '2', '9', '5', '3', '8', '7', '2', '0', '5', '1', '6', '3', '0', '0', '9', '9', '8', '9', '/', '3', '2', '2', '6', '6', '3', '7', '9', '2', '6', '0', '4', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '4', '3', '3', '4', '9', '7', '0', '2', '2', '6', '2', '6', '0', '0', '9', '6', '8', '7', '/', '3', '2', '2', '6', '6', '3', '7', '9', '2', '6', '0', '4', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '6', '4', '9', '1', '5', '7', '3', '8', '3', '8', '0', '8', '0', '9', '6', '2', '9', '6', '1', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0394006Acc00600 : List (String × SourceJson) := (fragment0394006Field005Key00, fragment0394006Field005Value00) :: fragment0394006Acc00500
noncomputable def fragment0394006Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '0', '6', '0', '9', '2', '7', '9', '0', '7', '2', '7', '7', '6', '4', '8', '4', '7', '1', '/', '7', '6', '8', '2', '4', '7', '1', '2', '5', '2', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '2', '5', '7', '4', '7', '1', '7', '6', '6', '2', '4', '3', '2', '8', '4', '7', '9', '3', '/', '1', '0', '7', '5', '5', '4', '5', '9', '7', '5', '3', '4', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '7', '4', '5', '3', '4', '8', '4', '6', '4', '2', '4', '6', '0', '4', '9', '6', '2', '1', '9', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '6', '9', '3', '2', '2', '6', '3', '4', '4', '2', '1', '2', '8', '7', '9', '0', '1', '1', '/', '2', '6', '8', '8', '8', '6', '4', '9', '3', '8', '3', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '6', '9', '6', '1', '2', '1', '5', '3', '2', '8', '7', '2', '1', '1', '9', '3', '6', '3', '9', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '4', '8', '0', '9', '6', '5', '3', '9', '1', '6', '6', '1', '8', '8', '6', '0', '5', '7', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '7', '5', '6', '1', '1', '2', '7', '7', '2', '0', '5', '9', '7', '1', '8', '3', '/', '3', '3', '9', '6', '4', '6', '0', '9', '7', '4', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '2', '9', '5', '3', '8', '7', '2', '0', '5', '1', '6', '3', '0', '0', '9', '9', '8', '9', '/', '3', '2', '2', '6', '6', '3', '7', '9', '2', '6', '0', '4', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '4', '3', '3', '4', '9', '7', '0', '2', '2', '6', '2', '6', '0', '0', '9', '6', '8', '7', '/', '3', '2', '2', '6', '6', '3', '7', '9', '2', '6', '0', '4', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '6', '4', '9', '1', '5', '7', '3', '8', '3', '8', '0', '8', '0', '9', '6', '2', '9', '6', '1', '/', '1', '6', '1', '3', '3', '1', '8', '9', '6', '3', '0', '2', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0394006_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0394006Field005Chars00 ++ tail)) fragment0394006Acc00500 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0394006Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_005"
  err.flush

noncomputable def fragment0394006Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0394006Field006Value00 : SourceJson := .str (String.ofList ['9', '9', '1', '3', '2', '5', '3', '0', '5', '1', '0', '1', '1', '1', '5', '4', '8', '2', '9', '8', '5', '6', '1', '7', '0', '9', '5', '1', '3', '4', '6', '7', '5', '5', '9', '0', '6', '5', '5', '5', '4', '6', '3', '2', '1', '1', '0', '4', '0', '7', '3', '3', '6', '/', '4', '5', '1', '2', '6', '5', '9', '4', '0', '9', '1', '9', '5', '3', '3', '7', '1', '3', '4', '2', '8', '5', '6', '1', '6', '6', '9', '8', '1', '2', '2', '7', '8', '8', '1', '9', '0', '0', '5', '7', '4', '0', '2', '4', '7', '8', '0', '7', '5', '3', '1', '4', '8', '0', '6', '0', '8', '7', '9', '9', '7', '8', '1', '2', '5'])
noncomputable def fragment0394006Acc00700 : List (String × SourceJson) := (fragment0394006Field006Key00, fragment0394006Field006Value00) :: fragment0394006Acc00600
noncomputable def fragment0394006Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '9', '1', '3', '2', '5', '3', '0', '5', '1', '0', '1', '1', '1', '5', '4', '8', '2', '9', '8', '5', '6', '1', '7', '0', '9', '5', '1', '3', '4', '6', '7', '5', '5', '9', '0', '6', '5', '5', '5', '4', '6', '3', '2', '1', '1', '0', '4', '0', '7', '3', '3', '6', '/', '4', '5', '1', '2', '6', '5', '9', '4', '0', '9', '1', '9', '5', '3', '3', '7', '1', '3', '4', '2', '8', '5', '6', '1', '6', '6', '9', '8', '1', '2', '2', '7', '8', '8', '1', '9', '0', '0', '5', '7', '4', '0', '2', '4', '7', '8', '0', '7', '5', '3', '1', '4', '8', '0', '6', '0', '8', '7', '9', '9', '7', '8', '1', '2', '5', '"', ',']

theorem object_fragment0394006_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0394006Field006Chars00 ++ tail)) fragment0394006Acc00600 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0394006Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_006"
  err.flush

noncomputable def fragment0394006Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0394006Field007Value00 : SourceJson := .str (String.ofList ['1', '7', '7', '6', '2', '2', '1', '5', '1', '6', '9', '5', '8', '6', '4', '4', '4', '5', '2', '5', '8', '6', '3', '9', '5', '4', '2', '8', '3', '6', '4', '1', '7', '0', '2', '9', '7', '4', '3', '3', '9', '9', '4', '1', '5', '8', '6', '4', '6', '2', '3', '6', '0', '6', '3', '2', '8', '7', '0', '7', '3', '2', '1', '8', '3', '8', '0', '3', '6', '6', '0', '4', '9', '3', '4', '0', '6', '7', '1', '5', '1', '8', '8', '0', '7', '1', '7', '4', '9', '5', '0', '6', '0', '5', '7', '1', '8', '2', '6', '9', '7', '3', '0', '4', '8', '0', '7', '3', '4', '5', '2', '3', '8', '5', '3', '7', '8', '0', '0', '8', '7', '9', '1', '6', '8', '6', '1', '4', '3', '1', '9', '7', '6', '8', '2', '7', '8', '7', '6', '3', '0', '4', '1', '7', '0', '8', '1', '7', '2', '1', '6', '6', '6', '1', '5', '1', '0', '8', '9', '5', '1', '5', '8', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '0', '4', '9', '9', '1', '6', '1', '6', '5', '7', '8', '4', '1', '3', '6', '0', '8', '7', '7', '9', '2', '1', '3', '9', '2', '6', '1', '6', '3', '2', '4', '1', '2', '5', '2', '6', '8', '9', '1', '6', '2', '3', '9', '3', '4', '2', '7', '0', '7', '6', '9', '9', '7', '9', '9', '0', '3', '7', '8', '4', '9', '4', '3', '3', '9', '4', '1', '9', '0', '3', '5', '8', '5', '4', '9', '2', '9', '7', '3', '5', '3', '0', '8', '2', '8', '6', '0', '7', '1', '3', '3', '8', '1', '7', '4', '3', '8', '7', '3', '2', '5', '5', '1', '1', '7', '0', '4', '8', '1', '6', '8', '0', '8', '0', '9', '8', '9', '6', '7', '9', '3', '0', '6', '7', '4', '3', '5', '2', '0', '6', '5', '9', '6', '5', '1', '8', '5', '5', '1', '6', '9', '0', '3', '4', '8', '5', '0', '5', '1', '2', '3', '1', '3', '1', '1', '2', '1', '6', '2', '4', '5', '7', '9', '0', '5', '7', '2', '5', '7', '9', '7', '9', '5', '1', '1', '7', '9', '0', '6', '4', '9', '9', '6', '9', '0', '7', '9', '7', '7', '0', '3', '0', '3', '5', '9', '8', '9', '3', '1'])
noncomputable def fragment0394006Acc00800 : List (String × SourceJson) := (fragment0394006Field007Key00, fragment0394006Field007Value00) :: fragment0394006Acc00700
noncomputable def fragment0394006Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '7', '6', '2', '2', '1', '5', '1', '6', '9', '5', '8', '6', '4', '4', '4', '5', '2', '5', '8', '6', '3', '9', '5', '4', '2', '8', '3', '6', '4', '1', '7', '0', '2', '9', '7', '4', '3', '3', '9', '9', '4', '1', '5', '8', '6', '4', '6', '2', '3', '6', '0', '6', '3', '2', '8', '7', '0', '7', '3', '2', '1', '8', '3', '8', '0', '3', '6', '6', '0', '4', '9', '3', '4', '0', '6', '7', '1', '5', '1', '8', '8', '0', '7', '1', '7', '4', '9', '5', '0', '6', '0', '5', '7', '1', '8', '2', '6', '9', '7', '3', '0', '4', '8', '0', '7', '3', '4', '5', '2', '3', '8', '5', '3', '7', '8', '0', '0', '8', '7', '9', '1', '6', '8', '6', '1', '4', '3', '1', '9', '7', '6', '8', '2', '7', '8', '7', '6', '3', '0', '4', '1', '7', '0', '8', '1', '7', '2', '1', '6', '6', '6', '1', '5', '1', '0', '8', '9', '5', '1', '5', '8', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '0', '4', '9', '9', '1', '6', '1', '6', '5', '7', '8', '4', '1', '3', '6', '0', '8', '7', '7', '9', '2', '1', '3', '9', '2', '6', '1', '6', '3', '2', '4', '1', '2', '5', '2', '6', '8', '9', '1', '6', '2', '3', '9', '3', '4', '2', '7', '0', '7', '6', '9', '9', '7', '9', '9', '0', '3', '7', '8', '4', '9', '4', '3', '3', '9', '4', '1', '9', '0', '3', '5', '8', '5', '4', '9', '2', '9', '7', '3', '5', '3', '0', '8', '2', '8', '6', '0', '7', '1', '3', '3', '8', '1', '7', '4', '3', '8', '7', '3', '2', '5', '5', '1', '1', '7', '0', '4', '8', '1', '6', '8', '0', '8', '0', '9', '8', '9', '6', '7', '9', '3', '0', '6', '7', '4', '3', '5', '2', '0', '6', '5', '9', '6', '5', '1', '8', '5', '5', '1', '6', '9', '0', '3', '4', '8', '5', '0', '5', '1', '2', '3', '1', '3', '1', '1', '2', '1', '6', '2', '4', '5', '7', '9', '0', '5', '7', '2', '5', '7', '9', '7', '9', '5', '1', '1', '7', '9', '0', '6', '4', '9', '9', '6', '9', '0', '7', '9', '7', '7', '0', '3', '0', '3', '5', '9', '8', '9', '3', '1', '"', ',']

theorem object_fragment0394006_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0394006Field007Chars00 ++ tail)) fragment0394006Acc00700 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0394006Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_007"
  err.flush

noncomputable def fragment0394006Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0394006Field008Value00 : SourceJson := .str (String.ofList ['1', '7', '4', '0', '4', '5', '6', '6', '8', '5', '4', '0', '8', '4', '5', '3', '2', '8'])
noncomputable def fragment0394006Acc00900 : List (String × SourceJson) := (fragment0394006Field008Key00, fragment0394006Field008Value00) :: fragment0394006Acc00800
noncomputable def fragment0394006Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '4', '0', '4', '5', '6', '6', '8', '5', '4', '0', '8', '4', '5', '3', '2', '8', '"', ',']

theorem object_fragment0394006_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0394006Field008Chars00 ++ tail)) fragment0394006Acc00800 =
      SourceJson.object (fuel + 393) (SourceJson.white tail) fragment0394006Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_008"
  err.flush

noncomputable def fragment0394006Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0394006Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '7', '3', '5', '5', '5', '0', '6', '4', '9', '9', '3', '9', '8', '1', '3', '9', '9'])
noncomputable def fragment0394006Acc01000 : List (String × SourceJson) := (fragment0394006Field009Key00, fragment0394006Field009Value00) :: fragment0394006Acc00900
noncomputable def fragment0394006Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '7', '3', '5', '5', '5', '0', '6', '4', '9', '9', '3', '9', '8', '1', '3', '9', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0394006_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 393) (SourceJson.white (fragment0394006Field009Chars00 ++ tail)) fragment0394006Acc00900 =
      .ok (.obj (fragment0394006Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0394006_object_field_009"
  err.flush

noncomputable def fragment0394006Chars : List Char := '{' :: (fragment0394006Field000Chars00 ++ fragment0394006Field001Chars00 ++ fragment0394006Field002Chars00 ++ fragment0394006Field003Chars00 ++ fragment0394006Field004Chars00 ++ fragment0394006Field005Chars00 ++ fragment0394006Field006Chars00 ++ fragment0394006Field007Chars00 ++ fragment0394006Field008Chars00 ++ fragment0394006Field009Chars00)
noncomputable def fragment0394006Value : SourceJson := .obj (fragment0394006Acc01000.reverse)

theorem value_fragment0394006 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 403) (fragment0394006Chars ++ tail) =
      .ok (fragment0394006Value, tail) := by
  have hinput : fragment0394006Chars ++ tail = '{' :: (fragment0394006Field000Chars00 ++ (fragment0394006Field001Chars00 ++ (fragment0394006Field002Chars00 ++ (fragment0394006Field003Chars00 ++ (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0394006Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 403) (fragment0394006Chars ++ tail) =
        SourceJson.value (fuel + 403) ('{' :: (fragment0394006Field000Chars00 ++ (fragment0394006Field001Chars00 ++ (fragment0394006Field002Chars00 ++ (fragment0394006Field003Chars00 ++ (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 403)) hinput
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0394006Field000Chars00 ++ (fragment0394006Field001Chars00 ++ (fragment0394006Field002Chars00 ++ (fragment0394006Field003Chars00 ++ (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))))))))))) fragment0394006Acc00000 := by rfl
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0394006Field001Chars00 ++ (fragment0394006Field002Chars00 ++ (fragment0394006Field003Chars00 ++ (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail))))))))))) fragment0394006Acc00100 := object_fragment0394006_field_000 fuel (fragment0394006Field001Chars00 ++ (fragment0394006Field002Chars00 ++ (fragment0394006Field003Chars00 ++ (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0394006Field002Chars00 ++ (fragment0394006Field003Chars00 ++ (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))))))))) fragment0394006Acc00200 := object_fragment0394006_field_001 fuel (fragment0394006Field002Chars00 ++ (fragment0394006Field003Chars00 ++ (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0394006Field003Chars00 ++ (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail))))))))) fragment0394006Acc00300 := object_fragment0394006_field_002 fuel (fragment0394006Field003Chars00 ++ (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))))))) fragment0394006Acc00400 := object_fragment0394006_field_003 fuel (fragment0394006Field004Chars00 ++ (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail))))))) fragment0394006Acc00500 := object_fragment0394006_field_004 fuel (fragment0394006Field005Chars00 ++ (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))))) fragment0394006Acc00600 := object_fragment0394006_field_005 fuel (fragment0394006Field006Chars00 ++ (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail))))) fragment0394006Acc00700 := object_fragment0394006_field_006 fuel (fragment0394006Field007Chars00 ++ (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))) fragment0394006Acc00800 := object_fragment0394006_field_007 fuel (fragment0394006Field008Chars00 ++ (fragment0394006Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 393) (SourceJson.white (fragment0394006Field009Chars00 ++ (tail))) fragment0394006Acc00900 := object_fragment0394006_field_008 fuel (fragment0394006Field009Chars00 ++ (tail))
    _ = .ok (fragment0394006Value, tail) := object_fragment0394006_field_009 fuel (tail)

noncomputable def fragment0395957Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0395957Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0395957Field000Value00 : SourceJson := .number (String.ofList ['9', '9'])
noncomputable def fragment0395957Acc00100 : List (String × SourceJson) := (fragment0395957Field000Key00, fragment0395957Field000Value00) :: fragment0395957Acc00000
noncomputable def fragment0395957Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '9', ',']

theorem object_fragment0395957_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0395957Field000Chars00 ++ tail)) fragment0395957Acc00000 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0395957Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_000"
  err.flush

noncomputable def fragment0395957Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0395957Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['0'])]
noncomputable def fragment0395957Acc00200 : List (String × SourceJson) := (fragment0395957Field001Key00, fragment0395957Field001Value00) :: fragment0395957Acc00100
noncomputable def fragment0395957Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0395957_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0395957Field001Chars00 ++ tail)) fragment0395957Acc00100 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0395957Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_001"
  err.flush

noncomputable def fragment0395957Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0395957Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '1', '1', '6', '4', '6', '7', '5', '0', '5', '8', '0', '7', '2', '5', '6', '7', '0', '1', '5', '0', '3', '1', '7', '6', '9', '4', '3', '5', '3', '8', '3', '3', '3', '6', '7', '9', '3', '9', '0', '1', '8', '3', '7', '/', '1', '4', '8', '1', '3', '0', '1', '2', '2', '8', '2', '2', '5', '4', '7', '6', '6', '8', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0395957Acc00300 : List (String × SourceJson) := (fragment0395957Field002Key00, fragment0395957Field002Value00) :: fragment0395957Acc00200
noncomputable def fragment0395957Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '3', '1', '1', '6', '4', '6', '7', '5', '0', '5', '8', '0', '7', '2', '5', '6', '7', '0', '1', '5', '0', '3', '1', '7', '6', '9', '4', '3', '5', '3', '8', '3', '3', '3', '6', '7', '9', '3', '9', '0', '1', '8', '3', '7', '/', '1', '4', '8', '1', '3', '0', '1', '2', '2', '8', '2', '2', '5', '4', '7', '6', '6', '8', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0395957_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0395957Field002Chars00 ++ tail)) fragment0395957Acc00200 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0395957Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_002"
  err.flush

noncomputable def fragment0395957Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0395957Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0395957Acc00400 : List (String × SourceJson) := (fragment0395957Field003Key00, fragment0395957Field003Value00) :: fragment0395957Acc00300
noncomputable def fragment0395957Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0395957_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0395957Field003Chars00 ++ tail)) fragment0395957Acc00300 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0395957Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_003"
  err.flush

noncomputable def fragment0395957Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0395957Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['8', '0', '7', '/', '1', '7', '7', '9', '2'])]
noncomputable def fragment0395957Acc00500 : List (String × SourceJson) := (fragment0395957Field004Key00, fragment0395957Field004Value00) :: fragment0395957Acc00400
noncomputable def fragment0395957Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '/', '1', '7', '7', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0395957_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0395957Field004Chars00 ++ tail)) fragment0395957Acc00400 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0395957Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_004"
  err.flush

noncomputable def fragment0395957Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0395957Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '1', '5', '6', '7', '2', '1', '6', '1', '0', '1', '/', '1', '3', '8', '6', '5', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '7', '4', '8', '3', '4', '5', '8', '3', '0', '9', '/', '5', '5', '4', '6', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '2', '7', '7', '6', '9', '2', '4', '6', '0', '8', '7', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '0', '6', '7', '9', '9', '3', '2', '3', '5', '3', '/', '2', '7', '7', '3', '0', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '7', '6', '7', '9', '7', '9', '0', '9', '9', '9', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '8', '6', '8', '0', '3', '9', '7', '0', '4', '1', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '4', '1', '0', '5', '5', '4', '4', '3', '/', '8', '7', '5', '7', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '5', '8', '3', '2', '4', '4', '3', '9', '7', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '1', '3', '8', '8', '7', '3', '8', '9', '8', '1', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '1', '0', '1', '0', '4', '9', '1', '9', '9', '9', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0395957Acc00600 : List (String × SourceJson) := (fragment0395957Field005Key00, fragment0395957Field005Value00) :: fragment0395957Acc00500
noncomputable def fragment0395957Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '5', '6', '7', '2', '1', '6', '1', '0', '1', '/', '1', '3', '8', '6', '5', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '7', '4', '8', '3', '4', '5', '8', '3', '0', '9', '/', '5', '5', '4', '6', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '2', '7', '7', '6', '9', '2', '4', '6', '0', '8', '7', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '0', '6', '7', '9', '9', '3', '2', '3', '5', '3', '/', '2', '7', '7', '3', '0', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '7', '6', '7', '9', '7', '9', '0', '9', '9', '9', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '8', '6', '8', '0', '3', '9', '7', '0', '4', '1', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '4', '1', '0', '5', '5', '4', '4', '3', '/', '8', '7', '5', '7', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '5', '8', '3', '2', '4', '4', '3', '9', '7', '/', '3', '3', '2', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '1', '3', '8', '8', '7', '3', '8', '9', '8', '1', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '1', '0', '1', '0', '4', '9', '1', '9', '9', '9', '/', '1', '6', '6', '3', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0395957_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0395957Field005Chars00 ++ tail)) fragment0395957Acc00500 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0395957Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_005"
  err.flush

noncomputable def fragment0395957Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0395957Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '0', '4', '4', '6', '8', '2', '3', '4', '0', '8', '6', '6', '8', '9', '0', '9', '1', '4', '8', '4', '0', '3', '9', '4', '0', '2', '9', '3', '7', '4', '0', '9', '0', '3', '6', '3', '5', '7', '6', '4', '2', '4', '3', '6', '0', '0', '0', '8', '0', '4', '8', '/', '1', '4', '2', '3', '6', '9', '4', '1', '8', '2', '3', '6', '5', '3', '1', '1', '2', '3', '8', '2', '3', '7', '1', '0', '9', '2', '8', '4', '9', '5', '8', '9', '6', '1', '8', '1', '1', '3', '4', '3', '8', '1', '2', '4', '6', '5', '2', '1', '7', '1', '4', '9', '5', '3', '5', '0', '5', '9', '0', '6', '3', '2', '8', '1', '2', '5'])
noncomputable def fragment0395957Acc00700 : List (String × SourceJson) := (fragment0395957Field006Key00, fragment0395957Field006Value00) :: fragment0395957Acc00600
noncomputable def fragment0395957Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '0', '4', '4', '6', '8', '2', '3', '4', '0', '8', '6', '6', '8', '9', '0', '9', '1', '4', '8', '4', '0', '3', '9', '4', '0', '2', '9', '3', '7', '4', '0', '9', '0', '3', '6', '3', '5', '7', '6', '4', '2', '4', '3', '6', '0', '0', '0', '8', '0', '4', '8', '/', '1', '4', '2', '3', '6', '9', '4', '1', '8', '2', '3', '6', '5', '3', '1', '1', '2', '3', '8', '2', '3', '7', '1', '0', '9', '2', '8', '4', '9', '5', '8', '9', '6', '1', '8', '1', '1', '3', '4', '3', '8', '1', '2', '4', '6', '5', '2', '1', '7', '1', '4', '9', '5', '3', '5', '0', '5', '9', '0', '6', '3', '2', '8', '1', '2', '5', '"', ',']

theorem object_fragment0395957_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0395957Field006Chars00 ++ tail)) fragment0395957Acc00600 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0395957Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_006"
  err.flush

noncomputable def fragment0395957Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0395957Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '0', '2', '2', '2', '8', '0', '9', '7', '6', '5', '5', '3', '8', '2', '5', '8', '7', '4', '2', '0', '6', '8', '6', '4', '0', '6', '2', '1', '5', '9', '9', '2', '8', '3', '4', '1', '2', '8', '3', '9', '0', '6', '9', '4', '0', '8', '9', '2', '2', '1', '4', '9', '9', '7', '4', '1', '0', '2', '9', '5', '8', '1', '9', '3', '2', '1', '2', '1', '2', '1', '8', '4', '2', '0', '4', '3', '6', '7', '6', '9', '4', '8', '5', '4', '7', '3', '6', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '/', '2', '2', '9', '3', '1', '7', '7', '8', '3', '6', '5', '6', '4', '4', '2', '4', '4', '8', '5', '7', '4', '9', '0', '1', '4', '8', '1', '6', '4', '6', '3', '8', '5', '8', '0', '9', '9', '7', '4', '3', '9', '3', '0', '6', '5', '4', '3', '1', '7', '8', '1', '3', '7', '8', '2', '9', '4', '3', '8', '1', '0', '0', '4', '1', '8', '8', '5', '0', '0', '8', '3', '7', '4', '0', '8', '8', '0', '9', '1', '5', '0', '9', '1', '8', '1', '4', '1', '7', '8', '0', '6', '4', '9', '9', '5', '6', '5', '5', '4', '7', '3', '1', '6', '4', '6', '0', '9', '5', '3', '0', '5', '1', '1', '1'])
noncomputable def fragment0395957Acc00800 : List (String × SourceJson) := (fragment0395957Field007Key00, fragment0395957Field007Value00) :: fragment0395957Acc00700
noncomputable def fragment0395957Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '3', '0', '2', '2', '2', '8', '0', '9', '7', '6', '5', '5', '3', '8', '2', '5', '8', '7', '4', '2', '0', '6', '8', '6', '4', '0', '6', '2', '1', '5', '9', '9', '2', '8', '3', '4', '1', '2', '8', '3', '9', '0', '6', '9', '4', '0', '8', '9', '2', '2', '1', '4', '9', '9', '7', '4', '1', '0', '2', '9', '5', '8', '1', '9', '3', '2', '1', '2', '1', '2', '1', '8', '4', '2', '0', '4', '3', '6', '7', '6', '9', '4', '8', '5', '4', '7', '3', '6', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '/', '2', '2', '9', '3', '1', '7', '7', '8', '3', '6', '5', '6', '4', '4', '2', '4', '4', '8', '5', '7', '4', '9', '0', '1', '4', '8', '1', '6', '4', '6', '3', '8', '5', '8', '0', '9', '9', '7', '4', '3', '9', '3', '0', '6', '5', '4', '3', '1', '7', '8', '1', '3', '7', '8', '2', '9', '4', '3', '8', '1', '0', '0', '4', '1', '8', '8', '5', '0', '0', '8', '3', '7', '4', '0', '8', '8', '0', '9', '1', '5', '0', '9', '1', '8', '1', '4', '1', '7', '8', '0', '6', '4', '9', '9', '5', '6', '5', '5', '4', '7', '3', '1', '6', '4', '6', '0', '9', '5', '3', '0', '5', '1', '1', '1', '"', ',']

theorem object_fragment0395957_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0395957Field007Chars00 ++ tail)) fragment0395957Acc00700 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0395957Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_007"
  err.flush

noncomputable def fragment0395957Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0395957Field008Value00 : SourceJson := .str (String.ofList ['5', '5', '8', '9', '8', '3', '6', '1', '7', '9', '4', '5', '3', '8', '8', '3'])
noncomputable def fragment0395957Acc00900 : List (String × SourceJson) := (fragment0395957Field008Key00, fragment0395957Field008Value00) :: fragment0395957Acc00800
noncomputable def fragment0395957Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '8', '9', '8', '3', '6', '1', '7', '9', '4', '5', '3', '8', '8', '3', '"', ',']

theorem object_fragment0395957_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0395957Field008Chars00 ++ tail)) fragment0395957Acc00800 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0395957Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_008"
  err.flush

noncomputable def fragment0395957Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0395957Field009Value00 : SourceJson := .str (String.ofList ['3', '9', '0', '4', '8', '6', '4', '0', '2', '8', '4', '9', '5', '3', '6', '8', '8'])
noncomputable def fragment0395957Acc01000 : List (String × SourceJson) := (fragment0395957Field009Key00, fragment0395957Field009Value00) :: fragment0395957Acc00900
noncomputable def fragment0395957Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '0', '4', '8', '6', '4', '0', '2', '8', '4', '9', '5', '3', '6', '8', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0395957_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0395957Field009Chars00 ++ tail)) fragment0395957Acc00900 =
      .ok (.obj (fragment0395957Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0395957_object_field_009"
  err.flush

noncomputable def fragment0395957Chars : List Char := '{' :: (fragment0395957Field000Chars00 ++ fragment0395957Field001Chars00 ++ fragment0395957Field002Chars00 ++ fragment0395957Field003Chars00 ++ fragment0395957Field004Chars00 ++ fragment0395957Field005Chars00 ++ fragment0395957Field006Chars00 ++ fragment0395957Field007Chars00 ++ fragment0395957Field008Chars00 ++ fragment0395957Field009Chars00)
noncomputable def fragment0395957Value : SourceJson := .obj (fragment0395957Acc01000.reverse)

theorem value_fragment0395957 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 228) (fragment0395957Chars ++ tail) =
      .ok (fragment0395957Value, tail) := by
  have hinput : fragment0395957Chars ++ tail = '{' :: (fragment0395957Field000Chars00 ++ (fragment0395957Field001Chars00 ++ (fragment0395957Field002Chars00 ++ (fragment0395957Field003Chars00 ++ (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0395957Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 228) (fragment0395957Chars ++ tail) =
        SourceJson.value (fuel + 228) ('{' :: (fragment0395957Field000Chars00 ++ (fragment0395957Field001Chars00 ++ (fragment0395957Field002Chars00 ++ (fragment0395957Field003Chars00 ++ (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 228)) hinput
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0395957Field000Chars00 ++ (fragment0395957Field001Chars00 ++ (fragment0395957Field002Chars00 ++ (fragment0395957Field003Chars00 ++ (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))))))))))) fragment0395957Acc00000 := by rfl
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0395957Field001Chars00 ++ (fragment0395957Field002Chars00 ++ (fragment0395957Field003Chars00 ++ (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail))))))))))) fragment0395957Acc00100 := object_fragment0395957_field_000 fuel (fragment0395957Field001Chars00 ++ (fragment0395957Field002Chars00 ++ (fragment0395957Field003Chars00 ++ (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0395957Field002Chars00 ++ (fragment0395957Field003Chars00 ++ (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))))))))) fragment0395957Acc00200 := object_fragment0395957_field_001 fuel (fragment0395957Field002Chars00 ++ (fragment0395957Field003Chars00 ++ (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0395957Field003Chars00 ++ (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail))))))))) fragment0395957Acc00300 := object_fragment0395957_field_002 fuel (fragment0395957Field003Chars00 ++ (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))))))) fragment0395957Acc00400 := object_fragment0395957_field_003 fuel (fragment0395957Field004Chars00 ++ (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail))))))) fragment0395957Acc00500 := object_fragment0395957_field_004 fuel (fragment0395957Field005Chars00 ++ (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))))) fragment0395957Acc00600 := object_fragment0395957_field_005 fuel (fragment0395957Field006Chars00 ++ (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail))))) fragment0395957Acc00700 := object_fragment0395957_field_006 fuel (fragment0395957Field007Chars00 ++ (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))) fragment0395957Acc00800 := object_fragment0395957_field_007 fuel (fragment0395957Field008Chars00 ++ (fragment0395957Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0395957Field009Chars00 ++ (tail))) fragment0395957Acc00900 := object_fragment0395957_field_008 fuel (fragment0395957Field009Chars00 ++ (tail))
    _ = .ok (fragment0395957Value, tail) := object_fragment0395957_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0098_before_reader"
  err.flush

noncomputable def chunk0098LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0098SuffixChars00 : List Char := [',']
noncomputable def chunk0098Chars00 : List Char := chunk0098LeadChars00 ++ fragment0394006Chars ++ chunk0098SuffixChars00
noncomputable def chunk0098Push00 (acc : List SourceJson) : List SourceJson := fragment0394006Value :: acc

noncomputable def chunk0098AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0098_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 506)
      (SourceJson.white (chunk0098LeadChars00 ++ (fragment0394006Chars ++ rest))) acc =
      (SourceJson.value (fuel + 505) (fragment0394006Chars ++ rest)).bind
        (chunk0098AfterValue00 (fuel + 505) acc) := by rfl

theorem array_chunk0098 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 506) (SourceJson.white (chunk0098Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 505) (SourceJson.white tail) (chunk0098Push00 acc) := by
  have hinput : chunk0098Chars00 ++ tail = chunk0098LeadChars00 ++ (fragment0394006Chars ++ (chunk0098SuffixChars00 ++ tail)) := by
    simp only [chunk0098Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 506) (SourceJson.white (chunk0098Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 506)
          (SourceJson.white (chunk0098LeadChars00 ++ (fragment0394006Chars ++ (chunk0098SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 506) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 505) (fragment0394006Chars ++ (chunk0098SuffixChars00 ++ tail))).bind
        (chunk0098AfterValue00 (fuel + 505) acc) := array_chunk0098_head fuel (chunk0098SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0394006Value, chunk0098SuffixChars00 ++ tail)).bind
        (chunk0098AfterValue00 (fuel + 505) acc) :=
      congrArg (fun result => result.bind (chunk0098AfterValue00 (fuel + 505) acc))
        (value_fragment0394006 (fuel + 102) (chunk0098SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 505) (SourceJson.white tail) (chunk0098Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0098_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0099_before_reader"
  err.flush

noncomputable def chunk0099LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0099SuffixChars00 : List Char := [',']
noncomputable def chunk0099Chars00 : List Char := chunk0099LeadChars00 ++ fragment0395957Chars ++ chunk0099SuffixChars00
noncomputable def chunk0099Push00 (acc : List SourceJson) : List SourceJson := fragment0395957Value :: acc

noncomputable def chunk0099AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0099_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 505)
      (SourceJson.white (chunk0099LeadChars00 ++ (fragment0395957Chars ++ rest))) acc =
      (SourceJson.value (fuel + 504) (fragment0395957Chars ++ rest)).bind
        (chunk0099AfterValue00 (fuel + 504) acc) := by rfl

theorem array_chunk0099 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 505) (SourceJson.white (chunk0099Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 504) (SourceJson.white tail) (chunk0099Push00 acc) := by
  have hinput : chunk0099Chars00 ++ tail = chunk0099LeadChars00 ++ (fragment0395957Chars ++ (chunk0099SuffixChars00 ++ tail)) := by
    simp only [chunk0099Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 505) (SourceJson.white (chunk0099Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 505)
          (SourceJson.white (chunk0099LeadChars00 ++ (fragment0395957Chars ++ (chunk0099SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 505) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 504) (fragment0395957Chars ++ (chunk0099SuffixChars00 ++ tail))).bind
        (chunk0099AfterValue00 (fuel + 504) acc) := array_chunk0099_head fuel (chunk0099SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0395957Value, chunk0099SuffixChars00 ++ tail)).bind
        (chunk0099AfterValue00 (fuel + 504) acc) :=
      congrArg (fun result => result.bind (chunk0099AfterValue00 (fuel + 504) acc))
        (value_fragment0395957 (fuel + 276) (chunk0099SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 504) (SourceJson.white tail) (chunk0099Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0099_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0098Chars00 ++ chunk0099Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0099Push00 (chunk0098Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 506) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 504) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0098Chars00 ++ (chunk0099Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 506) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 506) (SourceJson.white (chunk0098Chars00 ++ (chunk0099Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 506) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 505) (SourceJson.white (chunk0099Chars00 ++ (tail))) (chunk0098Push00 (acc)) := array_chunk0098 fuel (chunk0099Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 504) (SourceJson.white tail) (blockPush acc) := array_chunk0099 fuel (tail) (chunk0098Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 394000).take 3543 = blockChars := by rfl

theorem block_original_split : sourceRest 394000 = blockChars ++ sourceRest 397543 := by
  calc
    sourceRest 394000 = (sourceRest 394000).take 3543 ++ (sourceRest 394000).drop 3543 :=
      (List.take_append_drop 3543 (sourceRest 394000)).symm
    _ = blockChars ++ (sourceRest 394000).drop 3543 :=
      congrArg (fun part => part ++ (sourceRest 394000).drop 3543) block_original_prefix
    _ = blockChars ++ sourceRest 397543 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 394000 3543)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 506) (SourceJson.white (sourceRest 394000)) acc =
      SourceJson.array (fuel + 504) (SourceJson.white (sourceRest 397543)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 506) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 397543) acc)

#print axioms object_fragment0394006_field_000
#print axioms object_fragment0394006_field_001
#print axioms object_fragment0394006_field_002
#print axioms object_fragment0394006_field_003
#print axioms object_fragment0394006_field_004
#print axioms object_fragment0394006_field_005
#print axioms object_fragment0394006_field_006
#print axioms object_fragment0394006_field_007
#print axioms object_fragment0394006_field_008
#print axioms object_fragment0394006_field_009
#print axioms value_fragment0394006
#print axioms object_fragment0395957_field_000
#print axioms object_fragment0395957_field_001
#print axioms object_fragment0395957_field_002
#print axioms object_fragment0395957_field_003
#print axioms object_fragment0395957_field_004
#print axioms object_fragment0395957_field_005
#print axioms object_fragment0395957_field_006
#print axioms object_fragment0395957_field_007
#print axioms object_fragment0395957_field_008
#print axioms object_fragment0395957_field_009
#print axioms value_fragment0395957
#print axioms array_chunk0098_head
#print axioms array_chunk0098
#print axioms array_chunk0099_head
#print axioms array_chunk0099
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock050

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
