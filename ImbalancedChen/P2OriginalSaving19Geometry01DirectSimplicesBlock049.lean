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

namespace SimplicesBlock049

noncomputable def fragment0390672Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0390672Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0390672Field000Value00 : SourceJson := .number (String.ofList ['9', '6'])
noncomputable def fragment0390672Acc00100 : List (String × SourceJson) := (fragment0390672Field000Key00, fragment0390672Field000Value00) :: fragment0390672Acc00000
noncomputable def fragment0390672Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '6', ',']

theorem object_fragment0390672_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0390672Field000Chars00 ++ tail)) fragment0390672Acc00000 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0390672Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_000"
  err.flush

noncomputable def fragment0390672Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0390672Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['6']), .number (String.ofList ['0'])]
noncomputable def fragment0390672Acc00200 : List (String × SourceJson) := (fragment0390672Field001Key00, fragment0390672Field001Value00) :: fragment0390672Acc00100
noncomputable def fragment0390672Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0390672_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0390672Field001Chars00 ++ tail)) fragment0390672Acc00100 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0390672Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_001"
  err.flush

noncomputable def fragment0390672Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0390672Field002Value00 : SourceJson := .str (String.ofList ['4', '4', '7', '4', '3', '1', '1', '0', '1', '7', '1', '7', '8', '7', '6', '2', '0', '3', '2', '6', '3', '7', '2', '3', '7', '6', '1', '9', '9', '3', '7', '9', '1', '8', '8', '2', '9', '8', '2', '0', '5', '1', '0', '3', '/', '5', '3', '2', '9', '3', '6', '7', '9', '6', '7', '2', '6', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0390672Acc00300 : List (String × SourceJson) := (fragment0390672Field002Key00, fragment0390672Field002Value00) :: fragment0390672Acc00200
noncomputable def fragment0390672Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '4', '7', '4', '3', '1', '1', '0', '1', '7', '1', '7', '8', '7', '6', '2', '0', '3', '2', '6', '3', '7', '2', '3', '7', '6', '1', '9', '9', '3', '7', '9', '1', '8', '8', '2', '9', '8', '2', '0', '5', '1', '0', '3', '/', '5', '3', '2', '9', '3', '6', '7', '9', '6', '7', '2', '6', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0390672_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0390672Field002Chars00 ++ tail)) fragment0390672Acc00200 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0390672Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_002"
  err.flush

noncomputable def fragment0390672Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0390672Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0390672Acc00400 : List (String × SourceJson) := (fragment0390672Field003Key00, fragment0390672Field003Value00) :: fragment0390672Acc00300
noncomputable def fragment0390672Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0390672_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0390672Field003Chars00 ++ tail)) fragment0390672Acc00300 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0390672Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_003"
  err.flush

noncomputable def fragment0390672Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0390672Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0390672Acc00500 : List (String × SourceJson) := (fragment0390672Field004Key00, fragment0390672Field004Value00) :: fragment0390672Acc00400
noncomputable def fragment0390672Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0390672_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0390672Field004Chars00 ++ tail)) fragment0390672Acc00400 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0390672Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_004"
  err.flush

noncomputable def fragment0390672Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0390672Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '2', '9', '4', '7', '1', '5', '1', '7', '4', '6', '9', '/', '4', '1', '7', '0', '6', '6', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '5', '9', '6', '2', '2', '3', '0', '2', '1', '3', '9', '/', '1', '0', '4', '2', '6', '6', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '3', '7', '0', '2', '3', '9', '6', '6', '7', '7', '6', '7', '/', '5', '2', '1', '3', '3', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '8', '2', '3', '8', '1', '0', '2', '7', '9', '8', '1', '7', '/', '7', '8', '2', '0', '0', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '1', '4', '8', '3', '8', '4', '2', '3', '2', '0', '3', '/', '1', '3', '0', '3', '3', '3', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '5', '7', '6', '6', '1', '7', '1', '0', '9', '7', '1', '/', '5', '2', '1', '3', '3', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '3', '5', '2', '5', '6', '5', '5', '9', '/', '1', '0', '2', '8', '9', '4', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '0', '6', '0', '7', '7', '4', '3', '5', '1', '4', '1', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '3', '7', '2', '8', '1', '5', '7', '8', '8', '2', '5', '1', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '1', '5', '1', '2', '5', '7', '4', '0', '6', '4', '8', '7', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0390672Acc00600 : List (String × SourceJson) := (fragment0390672Field005Key00, fragment0390672Field005Value00) :: fragment0390672Acc00500
noncomputable def fragment0390672Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '9', '4', '7', '1', '5', '1', '7', '4', '6', '9', '/', '4', '1', '7', '0', '6', '6', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '5', '9', '6', '2', '2', '3', '0', '2', '1', '3', '9', '/', '1', '0', '4', '2', '6', '6', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '3', '7', '0', '2', '3', '9', '6', '6', '7', '7', '6', '7', '/', '5', '2', '1', '3', '3', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '8', '2', '3', '8', '1', '0', '2', '7', '9', '8', '1', '7', '/', '7', '8', '2', '0', '0', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '1', '4', '8', '3', '8', '4', '2', '3', '2', '0', '3', '/', '1', '3', '0', '3', '3', '3', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '5', '7', '6', '6', '1', '7', '1', '0', '9', '7', '1', '/', '5', '2', '1', '3', '3', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '3', '5', '2', '5', '6', '5', '5', '9', '/', '1', '0', '2', '8', '9', '4', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '0', '6', '0', '7', '7', '4', '3', '5', '1', '4', '1', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '3', '7', '2', '8', '1', '5', '7', '8', '8', '2', '5', '1', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '1', '5', '1', '2', '5', '7', '4', '0', '6', '4', '8', '7', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0390672_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0390672Field005Chars00 ++ tail)) fragment0390672Acc00500 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0390672Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_005"
  err.flush

noncomputable def fragment0390672Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0390672Field006Value00 : SourceJson := .str (String.ofList ['3', '8', '1', '6', '6', '0', '8', '6', '9', '6', '9', '5', '2', '8', '7', '8', '6', '0', '7', '1', '8', '3', '5', '9', '8', '7', '0', '2', '9', '3', '0', '5', '3', '7', '3', '0', '8', '1', '6', '4', '3', '5', '8', '1', '2', '4', '7', '5', '1', '4', '2', '4', '/', '4', '4', '9', '7', '3', '4', '0', '8', '5', '0', '8', '9', '2', '7', '8', '3', '0', '7', '8', '6', '1', '4', '0', '4', '2', '4', '6', '1', '0', '2', '6', '1', '4', '0', '1', '4', '2', '9', '9', '4', '2', '6', '6', '7', '6', '9', '7', '3', '8', '5', '1', '7', '9', '0', '0', '1', '3', '5', '1', '7', '7', '7', '0', '6', '2', '5'])
noncomputable def fragment0390672Acc00700 : List (String × SourceJson) := (fragment0390672Field006Key00, fragment0390672Field006Value00) :: fragment0390672Acc00600
noncomputable def fragment0390672Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '8', '1', '6', '6', '0', '8', '6', '9', '6', '9', '5', '2', '8', '7', '8', '6', '0', '7', '1', '8', '3', '5', '9', '8', '7', '0', '2', '9', '3', '0', '5', '3', '7', '3', '0', '8', '1', '6', '4', '3', '5', '8', '1', '2', '4', '7', '5', '1', '4', '2', '4', '/', '4', '4', '9', '7', '3', '4', '0', '8', '5', '0', '8', '9', '2', '7', '8', '3', '0', '7', '8', '6', '1', '4', '0', '4', '2', '4', '6', '1', '0', '2', '6', '1', '4', '0', '1', '4', '2', '9', '9', '4', '2', '6', '6', '7', '6', '9', '7', '3', '8', '5', '1', '7', '9', '0', '0', '1', '3', '5', '1', '7', '7', '7', '0', '6', '2', '5', '"', ',']

theorem object_fragment0390672_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0390672Field006Chars00 ++ tail)) fragment0390672Acc00600 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0390672Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_006"
  err.flush

noncomputable def fragment0390672Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0390672Field007Value00 : SourceJson := .str (String.ofList ['5', '2', '3', '6', '3', '3', '9', '5', '7', '3', '5', '6', '8', '6', '8', '6', '8', '7', '6', '0', '5', '1', '5', '3', '6', '2', '4', '9', '8', '7', '4', '6', '3', '8', '6', '4', '6', '9', '6', '7', '4', '0', '8', '7', '5', '8', '1', '2', '0', '0', '3', '5', '8', '2', '3', '8', '5', '2', '9', '9', '6', '1', '5', '8', '7', '2', '3', '6', '7', '3', '3', '2', '2', '0', '6', '1', '8', '7', '9', '7', '2', '9', '7', '6', '5', '7', '7', '6', '0', '3', '3', '5', '0', '4', '5', '8', '1', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '9', '2', '8', '1', '5', '6', '6', '8', '1', '9', '0', '4', '0', '7', '5', '7', '0', '1', '3', '0', '8', '4', '5', '0', '9', '5', '5', '7', '7', '0', '4', '8', '7', '7', '9', '6', '7', '7', '1', '2', '1', '4', '4', '3', '0', '2', '5', '4', '8', '9', '8', '9', '3', '3', '5', '2', '6', '4', '5', '4', '7', '6', '4', '1', '4', '5', '9', '8', '5', '6', '4', '2', '2', '1', '3', '7', '9', '8', '9', '7', '3', '6', '5', '7', '2', '7', '6', '6', '4', '1', '5', '4', '7', '7', '9', '4', '8', '4', '7', '9', '9', '5', '3', '5', '0', '8', '0', '2', '8', '2', '5', '5', '5', '7', '1', '8', '9', '2', '2', '5', '5', '7', '5', '6', '0', '3'])
noncomputable def fragment0390672Acc00800 : List (String × SourceJson) := (fragment0390672Field007Key00, fragment0390672Field007Value00) :: fragment0390672Acc00700
noncomputable def fragment0390672Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '2', '3', '6', '3', '3', '9', '5', '7', '3', '5', '6', '8', '6', '8', '6', '8', '7', '6', '0', '5', '1', '5', '3', '6', '2', '4', '9', '8', '7', '4', '6', '3', '8', '6', '4', '6', '9', '6', '7', '4', '0', '8', '7', '5', '8', '1', '2', '0', '0', '3', '5', '8', '2', '3', '8', '5', '2', '9', '9', '6', '1', '5', '8', '7', '2', '3', '6', '7', '3', '3', '2', '2', '0', '6', '1', '8', '7', '9', '7', '2', '9', '7', '6', '5', '7', '7', '6', '0', '3', '3', '5', '0', '4', '5', '8', '1', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '9', '2', '8', '1', '5', '6', '6', '8', '1', '9', '0', '4', '0', '7', '5', '7', '0', '1', '3', '0', '8', '4', '5', '0', '9', '5', '5', '7', '7', '0', '4', '8', '7', '7', '9', '6', '7', '7', '1', '2', '1', '4', '4', '3', '0', '2', '5', '4', '8', '9', '8', '9', '3', '3', '5', '2', '6', '4', '5', '4', '7', '6', '4', '1', '4', '5', '9', '8', '5', '6', '4', '2', '2', '1', '3', '7', '9', '8', '9', '7', '3', '6', '5', '7', '2', '7', '6', '6', '4', '1', '5', '4', '7', '7', '9', '4', '8', '4', '7', '9', '9', '5', '3', '5', '0', '8', '0', '2', '8', '2', '5', '5', '5', '7', '1', '8', '9', '2', '2', '5', '5', '7', '5', '6', '0', '3', '"', ',']

theorem object_fragment0390672_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0390672Field007Chars00 ++ tail)) fragment0390672Acc00700 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0390672Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_007"
  err.flush

noncomputable def fragment0390672Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0390672Field008Value00 : SourceJson := .str (String.ofList ['6', '7', '2', '3', '5', '9', '2', '9', '8', '7', '9', '6', '5', '5', '4'])
noncomputable def fragment0390672Acc00900 : List (String × SourceJson) := (fragment0390672Field008Key00, fragment0390672Field008Value00) :: fragment0390672Acc00800
noncomputable def fragment0390672Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '7', '2', '3', '5', '9', '2', '9', '8', '7', '9', '6', '5', '5', '4', '"', ',']

theorem object_fragment0390672_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0390672Field008Chars00 ++ tail)) fragment0390672Acc00800 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0390672Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_008"
  err.flush

noncomputable def fragment0390672Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0390672Field009Value00 : SourceJson := .str (String.ofList ['4', '6', '4', '6', '7', '1', '0', '1', '4', '9', '6', '4', '8', '6', '8', '0'])
noncomputable def fragment0390672Acc01000 : List (String × SourceJson) := (fragment0390672Field009Key00, fragment0390672Field009Value00) :: fragment0390672Acc00900
noncomputable def fragment0390672Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '4', '6', '7', '1', '0', '1', '4', '9', '6', '4', '8', '6', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0390672_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0390672Field009Chars00 ++ tail)) fragment0390672Acc00900 =
      .ok (.obj (fragment0390672Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0390672_object_field_009"
  err.flush

noncomputable def fragment0390672Chars : List Char := '{' :: (fragment0390672Field000Chars00 ++ fragment0390672Field001Chars00 ++ fragment0390672Field002Chars00 ++ fragment0390672Field003Chars00 ++ fragment0390672Field004Chars00 ++ fragment0390672Field005Chars00 ++ fragment0390672Field006Chars00 ++ fragment0390672Field007Chars00 ++ fragment0390672Field008Chars00 ++ fragment0390672Field009Chars00)
noncomputable def fragment0390672Value : SourceJson := .obj (fragment0390672Acc01000.reverse)

theorem value_fragment0390672 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 253) (fragment0390672Chars ++ tail) =
      .ok (fragment0390672Value, tail) := by
  have hinput : fragment0390672Chars ++ tail = '{' :: (fragment0390672Field000Chars00 ++ (fragment0390672Field001Chars00 ++ (fragment0390672Field002Chars00 ++ (fragment0390672Field003Chars00 ++ (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0390672Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 253) (fragment0390672Chars ++ tail) =
        SourceJson.value (fuel + 253) ('{' :: (fragment0390672Field000Chars00 ++ (fragment0390672Field001Chars00 ++ (fragment0390672Field002Chars00 ++ (fragment0390672Field003Chars00 ++ (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 253)) hinput
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0390672Field000Chars00 ++ (fragment0390672Field001Chars00 ++ (fragment0390672Field002Chars00 ++ (fragment0390672Field003Chars00 ++ (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))))))))))) fragment0390672Acc00000 := by rfl
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0390672Field001Chars00 ++ (fragment0390672Field002Chars00 ++ (fragment0390672Field003Chars00 ++ (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail))))))))))) fragment0390672Acc00100 := object_fragment0390672_field_000 fuel (fragment0390672Field001Chars00 ++ (fragment0390672Field002Chars00 ++ (fragment0390672Field003Chars00 ++ (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0390672Field002Chars00 ++ (fragment0390672Field003Chars00 ++ (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))))))))) fragment0390672Acc00200 := object_fragment0390672_field_001 fuel (fragment0390672Field002Chars00 ++ (fragment0390672Field003Chars00 ++ (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0390672Field003Chars00 ++ (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail))))))))) fragment0390672Acc00300 := object_fragment0390672_field_002 fuel (fragment0390672Field003Chars00 ++ (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))))))) fragment0390672Acc00400 := object_fragment0390672_field_003 fuel (fragment0390672Field004Chars00 ++ (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail))))))) fragment0390672Acc00500 := object_fragment0390672_field_004 fuel (fragment0390672Field005Chars00 ++ (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))))) fragment0390672Acc00600 := object_fragment0390672_field_005 fuel (fragment0390672Field006Chars00 ++ (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail))))) fragment0390672Acc00700 := object_fragment0390672_field_006 fuel (fragment0390672Field007Chars00 ++ (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))) fragment0390672Acc00800 := object_fragment0390672_field_007 fuel (fragment0390672Field008Chars00 ++ (fragment0390672Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0390672Field009Chars00 ++ (tail))) fragment0390672Acc00900 := object_fragment0390672_field_008 fuel (fragment0390672Field009Chars00 ++ (tail))
    _ = .ok (fragment0390672Value, tail) := object_fragment0390672_field_009 fuel (tail)

noncomputable def fragment0392318Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0392318Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0392318Field000Value00 : SourceJson := .number (String.ofList ['9', '7'])
noncomputable def fragment0392318Acc00100 : List (String × SourceJson) := (fragment0392318Field000Key00, fragment0392318Field000Value00) :: fragment0392318Acc00000
noncomputable def fragment0392318Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '7', ',']

theorem object_fragment0392318_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 271) (SourceJson.white (fragment0392318Field000Chars00 ++ tail)) fragment0392318Acc00000 =
      SourceJson.object (fuel + 270) (SourceJson.white tail) fragment0392318Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_000"
  err.flush

noncomputable def fragment0392318Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0392318Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['0'])]
noncomputable def fragment0392318Acc00200 : List (String × SourceJson) := (fragment0392318Field001Key00, fragment0392318Field001Value00) :: fragment0392318Acc00100
noncomputable def fragment0392318Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0392318_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment0392318Field001Chars00 ++ tail)) fragment0392318Acc00100 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment0392318Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_001"
  err.flush

noncomputable def fragment0392318Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0392318Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '6', '4', '3', '1', '3', '8', '1', '8', '1', '5', '6', '9', '4', '7', '3', '4', '6', '2', '5', '6', '1', '9', '7', '6', '4', '2', '4', '2', '7', '2', '8', '7', '0', '8', '6', '1', '8', '7', '5', '0', '4', '3', '/', '5', '4', '8', '1', '6', '3', '5', '6', '2', '3', '4', '7', '2', '3', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0392318Acc00300 : List (String × SourceJson) := (fragment0392318Field002Key00, fragment0392318Field002Value00) :: fragment0392318Acc00200
noncomputable def fragment0392318Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '6', '4', '3', '1', '3', '8', '1', '8', '1', '5', '6', '9', '4', '7', '3', '4', '6', '2', '5', '6', '1', '9', '7', '6', '4', '2', '4', '2', '7', '2', '8', '7', '0', '8', '6', '1', '8', '7', '5', '0', '4', '3', '/', '5', '4', '8', '1', '6', '3', '5', '6', '2', '3', '4', '7', '2', '3', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0392318_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0392318Field002Chars00 ++ tail)) fragment0392318Acc00200 =
      SourceJson.object (fuel + 268) (SourceJson.white tail) fragment0392318Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_002"
  err.flush

noncomputable def fragment0392318Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0392318Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0392318Acc00400 : List (String × SourceJson) := (fragment0392318Field003Key00, fragment0392318Field003Value00) :: fragment0392318Acc00300
noncomputable def fragment0392318Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0392318_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment0392318Field003Chars00 ++ tail)) fragment0392318Acc00300 =
      SourceJson.object (fuel + 267) (SourceJson.white tail) fragment0392318Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_003"
  err.flush

noncomputable def fragment0392318Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0392318Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0392318Acc00500 : List (String × SourceJson) := (fragment0392318Field004Key00, fragment0392318Field004Value00) :: fragment0392318Acc00400
noncomputable def fragment0392318Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0392318_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 267) (SourceJson.white (fragment0392318Field004Chars00 ++ tail)) fragment0392318Acc00400 =
      SourceJson.object (fuel + 266) (SourceJson.white tail) fragment0392318Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_004"
  err.flush

noncomputable def fragment0392318Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0392318Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '0', '3', '6', '2', '9', '0', '4', '0', '7', '0', '3', '8', '7', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '7', '0', '5', '4', '1', '9', '5', '5', '1', '5', '9', '7', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '7', '5', '3', '1', '7', '3', '2', '1', '4', '0', '9', '9', '/', '4', '6', '9', '2', '0', '0', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '9', '1', '9', '8', '4', '8', '3', '1', '2', '9', '7', '7', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '8', '8', '0', '6', '5', '9', '4', '3', '3', '3', '3', '7', '/', '2', '3', '4', '6', '0', '0', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '2', '9', '5', '3', '4', '8', '3', '6', '8', '7', '8', '5', '7', '/', '4', '6', '9', '2', '0', '0', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '1', '2', '4', '6', '9', '8', '8', '8', '1', '7', '7', '/', '4', '9', '3', '8', '9', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '6', '3', '5', '8', '5', '2', '6', '6', '8', '1', '2', '9', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '2', '8', '6', '0', '5', '8', '6', '4', '0', '9', '9', '/', '1', '4', '6', '6', '2', '5', '0', '1', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '5', '1', '4', '5', '2', '6', '2', '9', '0', '9', '0', '7', '/', '1', '1', '7', '3', '0', '0', '0', '1', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0392318Acc00600 : List (String × SourceJson) := (fragment0392318Field005Key00, fragment0392318Field005Value00) :: fragment0392318Acc00500
noncomputable def fragment0392318Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '3', '6', '2', '9', '0', '4', '0', '7', '0', '3', '8', '7', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '7', '0', '5', '4', '1', '9', '5', '5', '1', '5', '9', '7', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '7', '5', '3', '1', '7', '3', '2', '1', '4', '0', '9', '9', '/', '4', '6', '9', '2', '0', '0', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '9', '1', '9', '8', '4', '8', '3', '1', '2', '9', '7', '7', '/', '1', '5', '6', '4', '0', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '8', '8', '0', '6', '5', '9', '4', '3', '3', '3', '3', '7', '/', '2', '3', '4', '6', '0', '0', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '2', '9', '5', '3', '4', '8', '3', '6', '8', '7', '8', '5', '7', '/', '4', '6', '9', '2', '0', '0', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '2', '4', '6', '9', '8', '8', '8', '1', '7', '7', '/', '4', '9', '3', '8', '9', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '6', '3', '5', '8', '5', '2', '6', '6', '8', '1', '2', '9', '/', '9', '3', '8', '4', '0', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '2', '8', '6', '0', '5', '8', '6', '4', '0', '9', '9', '/', '1', '4', '6', '6', '2', '5', '0', '1', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '5', '1', '4', '5', '2', '6', '2', '9', '0', '9', '0', '7', '/', '1', '1', '7', '3', '0', '0', '0', '1', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0392318_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0392318Field005Chars00 ++ tail)) fragment0392318Acc00500 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0392318Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_005"
  err.flush

noncomputable def fragment0392318Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0392318Field006Value00 : SourceJson := .str (String.ofList ['5', '1', '0', '7', '4', '0', '5', '3', '6', '9', '2', '2', '3', '2', '4', '2', '3', '7', '0', '5', '4', '4', '2', '3', '2', '4', '7', '8', '2', '1', '1', '9', '7', '3', '6', '1', '9', '9', '8', '8', '2', '6', '8', '4', '4', '3', '4', '2', '0', '0', '9', '6', '/', '1', '7', '9', '1', '1', '0', '3', '9', '4', '2', '5', '4', '0', '5', '5', '2', '4', '9', '4', '2', '2', '0', '4', '6', '8', '3', '9', '7', '6', '6', '9', '0', '2', '8', '8', '7', '5', '5', '4', '7', '0', '9', '5', '2', '7', '1', '4', '6', '8', '8', '2', '0', '3', '1', '4', '4', '3', '3', '8', '2', '3', '9', '7', '0', '6', '2', '5'])
noncomputable def fragment0392318Acc00700 : List (String × SourceJson) := (fragment0392318Field006Key00, fragment0392318Field006Value00) :: fragment0392318Acc00600
noncomputable def fragment0392318Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '1', '0', '7', '4', '0', '5', '3', '6', '9', '2', '2', '3', '2', '4', '2', '3', '7', '0', '5', '4', '4', '2', '3', '2', '4', '7', '8', '2', '1', '1', '9', '7', '3', '6', '1', '9', '9', '8', '8', '2', '6', '8', '4', '4', '3', '4', '2', '0', '0', '9', '6', '/', '1', '7', '9', '1', '1', '0', '3', '9', '4', '2', '5', '4', '0', '5', '5', '2', '4', '9', '4', '2', '2', '0', '4', '6', '8', '3', '9', '7', '6', '6', '9', '0', '2', '8', '8', '7', '5', '5', '4', '7', '0', '9', '5', '2', '7', '1', '4', '6', '8', '8', '2', '0', '3', '1', '4', '4', '3', '3', '8', '2', '3', '9', '7', '0', '6', '2', '5', '"', ',']

theorem object_fragment0392318_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0392318Field006Chars00 ++ tail)) fragment0392318Acc00600 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0392318Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_006"
  err.flush

noncomputable def fragment0392318Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0392318Field007Value00 : SourceJson := .str (String.ofList ['5', '9', '1', '1', '8', '8', '7', '1', '0', '8', '5', '7', '2', '9', '1', '6', '6', '0', '3', '9', '1', '9', '4', '0', '4', '0', '9', '6', '0', '3', '5', '7', '2', '1', '7', '4', '0', '2', '3', '4', '5', '1', '8', '6', '4', '7', '2', '1', '0', '2', '1', '0', '5', '1', '3', '9', '3', '4', '9', '5', '1', '3', '1', '3', '2', '1', '0', '1', '1', '8', '8', '4', '4', '1', '1', '2', '4', '2', '3', '6', '8', '2', '2', '0', '0', '1', '8', '2', '7', '2', '2', '9', '1', '4', '9', '7', '1', '9', '1', '5', '2', '2', '6', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '0', '1', '5', '0', '3', '9', '8', '4', '5', '2', '4', '6', '8', '7', '9', '7', '2', '6', '0', '4', '5', '8', '9', '5', '9', '9', '9', '2', '9', '8', '0', '0', '8', '9', '4', '3', '6', '8', '6', '5', '1', '4', '7', '5', '7', '3', '9', '4', '0', '9', '3', '5', '5', '2', '2', '1', '5', '3', '5', '1', '7', '3', '0', '1', '3', '6', '4', '7', '3', '8', '2', '3', '9', '6', '2', '5', '2', '5', '7', '6', '9', '2', '7', '5', '5', '8', '8', '5', '6', '7', '8', '8', '8', '6', '7', '7', '4', '1', '7', '9', '9', '6', '6', '8', '8', '8', '5', '2', '8', '8', '6', '8', '0', '3', '4', '3', '2', '2', '9', '2', '3', '4', '7', '8', '4', '4', '8', '9', '2', '6', '5', '1', '4', '6', '0', '1'])
noncomputable def fragment0392318Acc00800 : List (String × SourceJson) := (fragment0392318Field007Key00, fragment0392318Field007Value00) :: fragment0392318Acc00700
noncomputable def fragment0392318Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '9', '1', '1', '8', '8', '7', '1', '0', '8', '5', '7', '2', '9', '1', '6', '6', '0', '3', '9', '1', '9', '4', '0', '4', '0', '9', '6', '0', '3', '5', '7', '2', '1', '7', '4', '0', '2', '3', '4', '5', '1', '8', '6', '4', '7', '2', '1', '0', '2', '1', '0', '5', '1', '3', '9', '3', '4', '9', '5', '1', '3', '1', '3', '2', '1', '0', '1', '1', '8', '8', '4', '4', '1', '1', '2', '4', '2', '3', '6', '8', '2', '2', '0', '0', '1', '8', '2', '7', '2', '2', '9', '1', '4', '9', '7', '1', '9', '1', '5', '2', '2', '6', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '0', '1', '5', '0', '3', '9', '8', '4', '5', '2', '4', '6', '8', '7', '9', '7', '2', '6', '0', '4', '5', '8', '9', '5', '9', '9', '9', '2', '9', '8', '0', '0', '8', '9', '4', '3', '6', '8', '6', '5', '1', '4', '7', '5', '7', '3', '9', '4', '0', '9', '3', '5', '5', '2', '2', '1', '5', '3', '5', '1', '7', '3', '0', '1', '3', '6', '4', '7', '3', '8', '2', '3', '9', '6', '2', '5', '2', '5', '7', '6', '9', '2', '7', '5', '5', '8', '8', '5', '6', '7', '8', '8', '8', '6', '7', '7', '4', '1', '7', '9', '9', '6', '6', '8', '8', '8', '5', '2', '8', '8', '6', '8', '0', '3', '4', '3', '2', '2', '9', '2', '3', '4', '7', '8', '4', '4', '8', '9', '2', '6', '5', '1', '4', '6', '0', '1', '"', ',']

theorem object_fragment0392318_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0392318Field007Chars00 ++ tail)) fragment0392318Acc00700 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0392318Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_007"
  err.flush

noncomputable def fragment0392318Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0392318Field008Value00 : SourceJson := .str (String.ofList ['2', '2', '5', '9', '2', '2', '3', '1', '1', '3', '7', '9', '1', '3', '6'])
noncomputable def fragment0392318Acc00900 : List (String × SourceJson) := (fragment0392318Field008Key00, fragment0392318Field008Value00) :: fragment0392318Acc00800
noncomputable def fragment0392318Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '5', '9', '2', '2', '3', '1', '1', '3', '7', '9', '1', '3', '6', '"', ',']

theorem object_fragment0392318_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0392318Field008Chars00 ++ tail)) fragment0392318Acc00800 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0392318Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_008"
  err.flush

noncomputable def fragment0392318Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0392318Field009Value00 : SourceJson := .str (String.ofList ['1', '5', '5', '3', '5', '0', '5', '0', '1', '6', '9', '9', '8', '0', '3', '0'])
noncomputable def fragment0392318Acc01000 : List (String × SourceJson) := (fragment0392318Field009Key00, fragment0392318Field009Value00) :: fragment0392318Acc00900
noncomputable def fragment0392318Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '5', '3', '5', '0', '5', '0', '1', '6', '9', '9', '8', '0', '3', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0392318_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0392318Field009Chars00 ++ tail)) fragment0392318Acc00900 =
      .ok (.obj (fragment0392318Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0392318_object_field_009"
  err.flush

noncomputable def fragment0392318Chars : List Char := '{' :: (fragment0392318Field000Chars00 ++ fragment0392318Field001Chars00 ++ fragment0392318Field002Chars00 ++ fragment0392318Field003Chars00 ++ fragment0392318Field004Chars00 ++ fragment0392318Field005Chars00 ++ fragment0392318Field006Chars00 ++ fragment0392318Field007Chars00 ++ fragment0392318Field008Chars00 ++ fragment0392318Field009Chars00)
noncomputable def fragment0392318Value : SourceJson := .obj (fragment0392318Acc01000.reverse)

theorem value_fragment0392318 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 272) (fragment0392318Chars ++ tail) =
      .ok (fragment0392318Value, tail) := by
  have hinput : fragment0392318Chars ++ tail = '{' :: (fragment0392318Field000Chars00 ++ (fragment0392318Field001Chars00 ++ (fragment0392318Field002Chars00 ++ (fragment0392318Field003Chars00 ++ (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0392318Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 272) (fragment0392318Chars ++ tail) =
        SourceJson.value (fuel + 272) ('{' :: (fragment0392318Field000Chars00 ++ (fragment0392318Field001Chars00 ++ (fragment0392318Field002Chars00 ++ (fragment0392318Field003Chars00 ++ (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 272)) hinput
    _ = SourceJson.object (fuel + 271) (SourceJson.white (fragment0392318Field000Chars00 ++ (fragment0392318Field001Chars00 ++ (fragment0392318Field002Chars00 ++ (fragment0392318Field003Chars00 ++ (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))))))))))) fragment0392318Acc00000 := by rfl
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment0392318Field001Chars00 ++ (fragment0392318Field002Chars00 ++ (fragment0392318Field003Chars00 ++ (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail))))))))))) fragment0392318Acc00100 := object_fragment0392318_field_000 fuel (fragment0392318Field001Chars00 ++ (fragment0392318Field002Chars00 ++ (fragment0392318Field003Chars00 ++ (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0392318Field002Chars00 ++ (fragment0392318Field003Chars00 ++ (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))))))))) fragment0392318Acc00200 := object_fragment0392318_field_001 fuel (fragment0392318Field002Chars00 ++ (fragment0392318Field003Chars00 ++ (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment0392318Field003Chars00 ++ (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail))))))))) fragment0392318Acc00300 := object_fragment0392318_field_002 fuel (fragment0392318Field003Chars00 ++ (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 267) (SourceJson.white (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))))))) fragment0392318Acc00400 := object_fragment0392318_field_003 fuel (fragment0392318Field004Chars00 ++ (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail))))))) fragment0392318Acc00500 := object_fragment0392318_field_004 fuel (fragment0392318Field005Chars00 ++ (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))))) fragment0392318Acc00600 := object_fragment0392318_field_005 fuel (fragment0392318Field006Chars00 ++ (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail))))) fragment0392318Acc00700 := object_fragment0392318_field_006 fuel (fragment0392318Field007Chars00 ++ (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))) fragment0392318Acc00800 := object_fragment0392318_field_007 fuel (fragment0392318Field008Chars00 ++ (fragment0392318Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0392318Field009Chars00 ++ (tail))) fragment0392318Acc00900 := object_fragment0392318_field_008 fuel (fragment0392318Field009Chars00 ++ (tail))
    _ = .ok (fragment0392318Value, tail) := object_fragment0392318_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0096_before_reader"
  err.flush

noncomputable def chunk0096LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0096SuffixChars00 : List Char := [',']
noncomputable def chunk0096Chars00 : List Char := chunk0096LeadChars00 ++ fragment0390672Chars ++ chunk0096SuffixChars00
noncomputable def chunk0096Push00 (acc : List SourceJson) : List SourceJson := fragment0390672Value :: acc

noncomputable def chunk0096AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0096_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 508)
      (SourceJson.white (chunk0096LeadChars00 ++ (fragment0390672Chars ++ rest))) acc =
      (SourceJson.value (fuel + 507) (fragment0390672Chars ++ rest)).bind
        (chunk0096AfterValue00 (fuel + 507) acc) := by rfl

theorem array_chunk0096 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 508) (SourceJson.white (chunk0096Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 507) (SourceJson.white tail) (chunk0096Push00 acc) := by
  have hinput : chunk0096Chars00 ++ tail = chunk0096LeadChars00 ++ (fragment0390672Chars ++ (chunk0096SuffixChars00 ++ tail)) := by
    simp only [chunk0096Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 508) (SourceJson.white (chunk0096Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 508)
          (SourceJson.white (chunk0096LeadChars00 ++ (fragment0390672Chars ++ (chunk0096SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 508) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 507) (fragment0390672Chars ++ (chunk0096SuffixChars00 ++ tail))).bind
        (chunk0096AfterValue00 (fuel + 507) acc) := array_chunk0096_head fuel (chunk0096SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0390672Value, chunk0096SuffixChars00 ++ tail)).bind
        (chunk0096AfterValue00 (fuel + 507) acc) :=
      congrArg (fun result => result.bind (chunk0096AfterValue00 (fuel + 507) acc))
        (value_fragment0390672 (fuel + 254) (chunk0096SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 507) (SourceJson.white tail) (chunk0096Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0096_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0097_before_reader"
  err.flush

noncomputable def chunk0097LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0097SuffixChars00 : List Char := [',']
noncomputable def chunk0097Chars00 : List Char := chunk0097LeadChars00 ++ fragment0392318Chars ++ chunk0097SuffixChars00
noncomputable def chunk0097Push00 (acc : List SourceJson) : List SourceJson := fragment0392318Value :: acc

noncomputable def chunk0097AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0097_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 507)
      (SourceJson.white (chunk0097LeadChars00 ++ (fragment0392318Chars ++ rest))) acc =
      (SourceJson.value (fuel + 506) (fragment0392318Chars ++ rest)).bind
        (chunk0097AfterValue00 (fuel + 506) acc) := by rfl

theorem array_chunk0097 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 507) (SourceJson.white (chunk0097Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 506) (SourceJson.white tail) (chunk0097Push00 acc) := by
  have hinput : chunk0097Chars00 ++ tail = chunk0097LeadChars00 ++ (fragment0392318Chars ++ (chunk0097SuffixChars00 ++ tail)) := by
    simp only [chunk0097Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 507) (SourceJson.white (chunk0097Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 507)
          (SourceJson.white (chunk0097LeadChars00 ++ (fragment0392318Chars ++ (chunk0097SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 507) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 506) (fragment0392318Chars ++ (chunk0097SuffixChars00 ++ tail))).bind
        (chunk0097AfterValue00 (fuel + 506) acc) := array_chunk0097_head fuel (chunk0097SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0392318Value, chunk0097SuffixChars00 ++ tail)).bind
        (chunk0097AfterValue00 (fuel + 506) acc) :=
      congrArg (fun result => result.bind (chunk0097AfterValue00 (fuel + 506) acc))
        (value_fragment0392318 (fuel + 234) (chunk0097SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 506) (SourceJson.white tail) (chunk0097Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0097_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0096Chars00 ++ chunk0097Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0097Push00 (chunk0096Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 508) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 506) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0096Chars00 ++ (chunk0097Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 508) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 508) (SourceJson.white (chunk0096Chars00 ++ (chunk0097Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 508) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 507) (SourceJson.white (chunk0097Chars00 ++ (tail))) (chunk0096Push00 (acc)) := array_chunk0096 fuel (chunk0097Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 506) (SourceJson.white tail) (blockPush acc) := array_chunk0097 fuel (tail) (chunk0096Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 390666).take 3334 = blockChars := by rfl

theorem block_original_split : sourceRest 390666 = blockChars ++ sourceRest 394000 := by
  calc
    sourceRest 390666 = (sourceRest 390666).take 3334 ++ (sourceRest 390666).drop 3334 :=
      (List.take_append_drop 3334 (sourceRest 390666)).symm
    _ = blockChars ++ (sourceRest 390666).drop 3334 :=
      congrArg (fun part => part ++ (sourceRest 390666).drop 3334) block_original_prefix
    _ = blockChars ++ sourceRest 394000 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 390666 3334)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 508) (SourceJson.white (sourceRest 390666)) acc =
      SourceJson.array (fuel + 506) (SourceJson.white (sourceRest 394000)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 508) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 394000) acc)

#print axioms object_fragment0390672_field_000
#print axioms object_fragment0390672_field_001
#print axioms object_fragment0390672_field_002
#print axioms object_fragment0390672_field_003
#print axioms object_fragment0390672_field_004
#print axioms object_fragment0390672_field_005
#print axioms object_fragment0390672_field_006
#print axioms object_fragment0390672_field_007
#print axioms object_fragment0390672_field_008
#print axioms object_fragment0390672_field_009
#print axioms value_fragment0390672
#print axioms object_fragment0392318_field_000
#print axioms object_fragment0392318_field_001
#print axioms object_fragment0392318_field_002
#print axioms object_fragment0392318_field_003
#print axioms object_fragment0392318_field_004
#print axioms object_fragment0392318_field_005
#print axioms object_fragment0392318_field_006
#print axioms object_fragment0392318_field_007
#print axioms object_fragment0392318_field_008
#print axioms object_fragment0392318_field_009
#print axioms value_fragment0392318
#print axioms array_chunk0096_head
#print axioms array_chunk0096
#print axioms array_chunk0097_head
#print axioms array_chunk0097
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock049

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
