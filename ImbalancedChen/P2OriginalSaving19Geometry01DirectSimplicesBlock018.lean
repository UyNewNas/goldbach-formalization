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

namespace SimplicesBlock018

noncomputable def fragment0286041Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0286041Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0286041Field000Value00 : SourceJson := .number (String.ofList ['3', '6'])
noncomputable def fragment0286041Acc00100 : List (String × SourceJson) := (fragment0286041Field000Key00, fragment0286041Field000Value00) :: fragment0286041Acc00000
noncomputable def fragment0286041Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '6', ',']

theorem object_fragment0286041_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 385) (SourceJson.white (fragment0286041Field000Chars00 ++ tail)) fragment0286041Acc00000 =
      SourceJson.object (fuel + 384) (SourceJson.white tail) fragment0286041Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_000"
  err.flush

noncomputable def fragment0286041Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0286041Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0286041Acc00200 : List (String × SourceJson) := (fragment0286041Field001Key00, fragment0286041Field001Value00) :: fragment0286041Acc00100
noncomputable def fragment0286041Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0286041_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 384) (SourceJson.white (fragment0286041Field001Chars00 ++ tail)) fragment0286041Acc00100 =
      SourceJson.object (fuel + 383) (SourceJson.white tail) fragment0286041Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_001"
  err.flush

noncomputable def fragment0286041Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0286041Field002Value00 : SourceJson := .str (String.ofList ['6', '4', '3', '9', '4', '0', '9', '9', '7', '2', '8', '7', '2', '7', '0', '3', '3', '3', '8', '2', '6', '6', '4', '5', '6', '8', '6', '2', '0', '9', '4', '2', '2', '0', '6', '8', '6', '4', '7', '7', '/', '1', '6', '2', '8', '8', '8', '7', '4', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0286041Acc00300 : List (String × SourceJson) := (fragment0286041Field002Key00, fragment0286041Field002Value00) :: fragment0286041Acc00200
noncomputable def fragment0286041Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '4', '3', '9', '4', '0', '9', '9', '7', '2', '8', '7', '2', '7', '0', '3', '3', '3', '8', '2', '6', '6', '4', '5', '6', '8', '6', '2', '0', '9', '4', '2', '2', '0', '6', '8', '6', '4', '7', '7', '/', '1', '6', '2', '8', '8', '8', '7', '4', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0286041_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 383) (SourceJson.white (fragment0286041Field002Chars00 ++ tail)) fragment0286041Acc00200 =
      SourceJson.object (fuel + 382) (SourceJson.white tail) fragment0286041Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_002"
  err.flush

noncomputable def fragment0286041Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0286041Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0'])
noncomputable def fragment0286041Acc00400 : List (String × SourceJson) := (fragment0286041Field003Key00, fragment0286041Field003Value00) :: fragment0286041Acc00300
noncomputable def fragment0286041Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0', '"', ',']

theorem object_fragment0286041_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 382) (SourceJson.white (fragment0286041Field003Chars00 ++ tail)) fragment0286041Acc00300 =
      SourceJson.object (fuel + 381) (SourceJson.white tail) fragment0286041Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_003"
  err.flush

noncomputable def fragment0286041Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0286041Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0286041Acc00500 : List (String × SourceJson) := (fragment0286041Field004Key00, fragment0286041Field004Value00) :: fragment0286041Acc00400
noncomputable def fragment0286041Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0286041_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 381) (SourceJson.white (fragment0286041Field004Chars00 ++ tail)) fragment0286041Acc00400 =
      SourceJson.object (fuel + 380) (SourceJson.white tail) fragment0286041Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_004"
  err.flush

noncomputable def fragment0286041Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0286041Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '0', '6', '7', '8', '7', '0', '6', '6', '7', '9', '6', '4', '8', '5', '6', '1', '3', '/', '7', '2', '1', '5', '7', '1', '6', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '2', '7', '9', '6', '8', '7', '1', '2', '8', '8', '7', '8', '3', '5', '6', '6', '2', '7', '/', '3', '5', '3', '5', '7', '0', '0', '9', '0', '0', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '0', '3', '9', '3', '0', '7', '2', '9', '7', '6', '8', '2', '6', '2', '7', '7', '9', '/', '2', '4', '4', '7', '7', '9', '2', '9', '3', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '7', '9', '3', '5', '3', '7', '2', '0', '0', '9', '0', '7', '5', '8', '6', '1', '9', '9', '/', '5', '3', '0', '3', '5', '5', '1', '3', '5', '0', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '1', '0', '7', '6', '0', '6', '9', '9', '6', '1', '3', '9', '6', '1', '2', '9', '3', '/', '1', '8', '7', '1', '8', '4', '1', '6', '5', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '5', '0', '1', '1', '0', '4', '3', '3', '5', '6', '6', '4', '5', '2', '6', '6', '9', '3', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '6', '2', '5', '3', '3', '7', '5', '6', '0', '2', '3', '4', '7', '3', '9', '6', '7', '/', '1', '6', '7', '4', '8', '0', '5', '6', '8', '9', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '9', '8', '8', '9', '8', '6', '7', '9', '1', '4', '1', '3', '3', '3', '9', '5', '3', '3', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '8', '3', '0', '5', '0', '7', '5', '9', '3', '8', '0', '8', '9', '9', '9', '2', '2', '3', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '1', '4', '4', '4', '1', '5', '9', '4', '8', '4', '7', '2', '6', '6', '9', '9', '5', '3', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0286041Acc00600 : List (String × SourceJson) := (fragment0286041Field005Key00, fragment0286041Field005Value00) :: fragment0286041Acc00500
noncomputable def fragment0286041Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '6', '7', '8', '7', '0', '6', '6', '7', '9', '6', '4', '8', '5', '6', '1', '3', '/', '7', '2', '1', '5', '7', '1', '6', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '2', '7', '9', '6', '8', '7', '1', '2', '8', '8', '7', '8', '3', '5', '6', '6', '2', '7', '/', '3', '5', '3', '5', '7', '0', '0', '9', '0', '0', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '0', '3', '9', '3', '0', '7', '2', '9', '7', '6', '8', '2', '6', '2', '7', '7', '9', '/', '2', '4', '4', '7', '7', '9', '2', '9', '3', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '7', '9', '3', '5', '3', '7', '2', '0', '0', '9', '0', '7', '5', '8', '6', '1', '9', '9', '/', '5', '3', '0', '3', '5', '5', '1', '3', '5', '0', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '1', '0', '7', '6', '0', '6', '9', '9', '6', '1', '3', '9', '6', '1', '2', '9', '3', '/', '1', '8', '7', '1', '8', '4', '1', '6', '5', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '5', '0', '1', '1', '0', '4', '3', '3', '5', '6', '6', '4', '5', '2', '6', '6', '9', '3', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '6', '2', '5', '3', '3', '7', '5', '6', '0', '2', '3', '4', '7', '3', '9', '6', '7', '/', '1', '6', '7', '4', '8', '0', '5', '6', '8', '9', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '9', '8', '8', '9', '8', '6', '7', '9', '1', '4', '1', '3', '3', '3', '9', '5', '3', '3', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '8', '3', '0', '5', '0', '7', '5', '9', '3', '8', '0', '8', '9', '9', '9', '2', '2', '3', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '1', '4', '4', '4', '1', '5', '9', '4', '8', '4', '7', '2', '6', '6', '9', '9', '5', '3', '/', '3', '1', '8', '2', '1', '3', '0', '8', '1', '0', '3', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0286041_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 380) (SourceJson.white (fragment0286041Field005Chars00 ++ tail)) fragment0286041Acc00500 =
      SourceJson.object (fuel + 379) (SourceJson.white tail) fragment0286041Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_005"
  err.flush

noncomputable def fragment0286041Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0286041Field006Value00 : SourceJson := .str (String.ofList ['3', '9', '6', '2', '1', '1', '4', '5', '8', '6', '8', '2', '9', '9', '7', '1', '6', '6', '7', '5', '1', '3', '9', '6', '2', '1', '8', '6', '3', '1', '6', '9', '4', '2', '9', '5', '0', '8', '8', '9', '2', '6', '1', '2', '2', '6', '8', '2', '1', '4', '4', '0', '0', '0', '0', '/', '1', '2', '4', '7', '9', '5', '5', '2', '4', '3', '5', '1', '9', '0', '9', '6', '8', '7', '3', '8', '9', '5', '1', '2', '2', '1', '7', '4', '6', '8', '0', '9', '7', '8', '1', '0', '9', '2', '2', '0', '3', '3', '4', '6', '3', '8', '2', '2', '4', '9', '0', '1', '2', '6', '0', '9', '7', '0', '3', '2', '1', '8', '0', '2', '0', '2', '3'])
noncomputable def fragment0286041Acc00700 : List (String × SourceJson) := (fragment0286041Field006Key00, fragment0286041Field006Value00) :: fragment0286041Acc00600
noncomputable def fragment0286041Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '9', '6', '2', '1', '1', '4', '5', '8', '6', '8', '2', '9', '9', '7', '1', '6', '6', '7', '5', '1', '3', '9', '6', '2', '1', '8', '6', '3', '1', '6', '9', '4', '2', '9', '5', '0', '8', '8', '9', '2', '6', '1', '2', '2', '6', '8', '2', '1', '4', '4', '0', '0', '0', '0', '/', '1', '2', '4', '7', '9', '5', '5', '2', '4', '3', '5', '1', '9', '0', '9', '6', '8', '7', '3', '8', '9', '5', '1', '2', '2', '1', '7', '4', '6', '8', '0', '9', '7', '8', '1', '0', '9', '2', '2', '0', '3', '3', '4', '6', '3', '8', '2', '2', '4', '9', '0', '1', '2', '6', '0', '9', '7', '0', '3', '2', '1', '8', '0', '2', '0', '2', '3', '"', ',']

theorem object_fragment0286041_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 379) (SourceJson.white (fragment0286041Field006Chars00 ++ tail)) fragment0286041Acc00600 =
      SourceJson.object (fuel + 378) (SourceJson.white tail) fragment0286041Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_006"
  err.flush

noncomputable def fragment0286041Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0286041Field007Value00 : SourceJson := .str (String.ofList ['2', '0', '1', '6', '1', '4', '2', '2', '5', '5', '3', '8', '4', '8', '8', '9', '9', '3', '9', '0', '4', '2', '1', '6', '6', '0', '4', '8', '9', '2', '8', '3', '3', '0', '4', '0', '7', '6', '3', '1', '3', '1', '8', '3', '8', '8', '8', '7', '7', '4', '4', '0', '2', '2', '3', '1', '8', '7', '6', '4', '8', '3', '5', '8', '1', '4', '2', '8', '6', '4', '2', '3', '2', '5', '8', '2', '6', '0', '8', '8', '4', '8', '7', '7', '0', '9', '4', '6', '4', '6', '1', '5', '6', '1', '0', '6', '7', '3', '1', '3', '0', '6', '3', '6', '6', '0', '5', '3', '0', '0', '4', '9', '0', '7', '8', '3', '1', '9', '1', '9', '0', '9', '3', '7', '6', '7', '5', '1', '8', '4', '0', '1', '2', '6', '7', '6', '9', '2', '2', '3', '2', '0', '3', '1', '7', '2', '0', '6', '4', '6', '0', '8', '3', '8', '7', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '1', '1', '4', '0', '9', '5', '1', '3', '3', '8', '9', '8', '2', '1', '6', '8', '7', '6', '0', '1', '3', '3', '4', '0', '3', '2', '7', '7', '9', '3', '3', '0', '0', '4', '8', '0', '0', '1', '0', '6', '0', '8', '4', '9', '1', '9', '0', '1', '0', '4', '4', '7', '4', '8', '6', '6', '1', '3', '3', '8', '3', '7', '7', '2', '3', '3', '2', '0', '1', '3', '6', '0', '3', '9', '0', '7', '2', '4', '1', '5', '0', '4', '2', '3', '3', '4', '9', '7', '5', '4', '8', '5', '1', '3', '9', '5', '8', '8', '5', '8', '7', '9', '6', '2', '7', '0', '9', '8', '6', '3', '8', '1', '4', '2', '1', '9', '6', '4', '8', '1', '6', '0', '4', '9', '6', '9', '0', '7', '5', '0', '0', '3', '0', '9', '8', '7', '8', '8', '1', '5', '5', '0', '1', '2', '4', '3', '6', '3', '5', '0', '0', '6', '8', '7', '4', '5', '1', '9', '2', '9', '3', '9', '6', '1', '3', '7', '9', '4', '5', '9', '5', '0', '0', '0', '4', '9', '5', '6', '9', '9', '6', '3', '4', '0', '6', '4', '1', '7', '9', '2', '3'])
noncomputable def fragment0286041Acc00800 : List (String × SourceJson) := (fragment0286041Field007Key00, fragment0286041Field007Value00) :: fragment0286041Acc00700
noncomputable def fragment0286041Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '0', '1', '6', '1', '4', '2', '2', '5', '5', '3', '8', '4', '8', '8', '9', '9', '3', '9', '0', '4', '2', '1', '6', '6', '0', '4', '8', '9', '2', '8', '3', '3', '0', '4', '0', '7', '6', '3', '1', '3', '1', '8', '3', '8', '8', '8', '7', '7', '4', '4', '0', '2', '2', '3', '1', '8', '7', '6', '4', '8', '3', '5', '8', '1', '4', '2', '8', '6', '4', '2', '3', '2', '5', '8', '2', '6', '0', '8', '8', '4', '8', '7', '7', '0', '9', '4', '6', '4', '6', '1', '5', '6', '1', '0', '6', '7', '3', '1', '3', '0', '6', '3', '6', '6', '0', '5', '3', '0', '0', '4', '9', '0', '7', '8', '3', '1', '9', '1', '9', '0', '9', '3', '7', '6', '7', '5', '1', '8', '4', '0', '1', '2', '6', '7', '6', '9', '2', '2', '3', '2', '0', '3', '1', '7', '2', '0', '6', '4', '6', '0', '8', '3', '8', '7', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '1', '1', '4', '0', '9', '5', '1', '3', '3', '8', '9', '8', '2', '1', '6', '8', '7', '6', '0', '1', '3', '3', '4', '0', '3', '2', '7', '7', '9', '3', '3', '0', '0', '4', '8', '0', '0', '1', '0', '6', '0', '8', '4', '9', '1', '9', '0', '1', '0', '4', '4', '7', '4', '8', '6', '6', '1', '3', '3', '8', '3', '7', '7', '2', '3', '3', '2', '0', '1', '3', '6', '0', '3', '9', '0', '7', '2', '4', '1', '5', '0', '4', '2', '3', '3', '4', '9', '7', '5', '4', '8', '5', '1', '3', '9', '5', '8', '8', '5', '8', '7', '9', '6', '2', '7', '0', '9', '8', '6', '3', '8', '1', '4', '2', '1', '9', '6', '4', '8', '1', '6', '0', '4', '9', '6', '9', '0', '7', '5', '0', '0', '3', '0', '9', '8', '7', '8', '8', '1', '5', '5', '0', '1', '2', '4', '3', '6', '3', '5', '0', '0', '6', '8', '7', '4', '5', '1', '9', '2', '9', '3', '9', '6', '1', '3', '7', '9', '4', '5', '9', '5', '0', '0', '0', '4', '9', '5', '6', '9', '9', '6', '3', '4', '0', '6', '4', '1', '7', '9', '2', '3', '"', ',']

theorem object_fragment0286041_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 378) (SourceJson.white (fragment0286041Field007Chars00 ++ tail)) fragment0286041Acc00700 =
      SourceJson.object (fuel + 377) (SourceJson.white tail) fragment0286041Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_007"
  err.flush

noncomputable def fragment0286041Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0286041Field008Value00 : SourceJson := .str (String.ofList ['2', '5', '1', '5', '4', '0', '3', '1', '7', '6', '6', '4', '2', '0', '3', '6', '8', '5'])
noncomputable def fragment0286041Acc00900 : List (String × SourceJson) := (fragment0286041Field008Key00, fragment0286041Field008Value00) :: fragment0286041Acc00800
noncomputable def fragment0286041Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '1', '5', '4', '0', '3', '1', '7', '6', '6', '4', '2', '0', '3', '6', '8', '5', '"', ',']

theorem object_fragment0286041_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 377) (SourceJson.white (fragment0286041Field008Chars00 ++ tail)) fragment0286041Acc00800 =
      SourceJson.object (fuel + 376) (SourceJson.white tail) fragment0286041Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_008"
  err.flush

noncomputable def fragment0286041Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0286041Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '4', '5', '3', '3', '4', '6', '9', '4', '7', '8', '6', '1', '4', '4', '6', '1', '4'])
noncomputable def fragment0286041Acc01000 : List (String × SourceJson) := (fragment0286041Field009Key00, fragment0286041Field009Value00) :: fragment0286041Acc00900
noncomputable def fragment0286041Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '4', '5', '3', '3', '4', '6', '9', '4', '7', '8', '6', '1', '4', '4', '6', '1', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0286041_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 376) (SourceJson.white (fragment0286041Field009Chars00 ++ tail)) fragment0286041Acc00900 =
      .ok (.obj (fragment0286041Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286041_object_field_009"
  err.flush

noncomputable def fragment0286041Chars : List Char := '{' :: (fragment0286041Field000Chars00 ++ fragment0286041Field001Chars00 ++ fragment0286041Field002Chars00 ++ fragment0286041Field003Chars00 ++ fragment0286041Field004Chars00 ++ fragment0286041Field005Chars00 ++ fragment0286041Field006Chars00 ++ fragment0286041Field007Chars00 ++ fragment0286041Field008Chars00 ++ fragment0286041Field009Chars00)
noncomputable def fragment0286041Value : SourceJson := .obj (fragment0286041Acc01000.reverse)

theorem value_fragment0286041 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 386) (fragment0286041Chars ++ tail) =
      .ok (fragment0286041Value, tail) := by
  have hinput : fragment0286041Chars ++ tail = '{' :: (fragment0286041Field000Chars00 ++ (fragment0286041Field001Chars00 ++ (fragment0286041Field002Chars00 ++ (fragment0286041Field003Chars00 ++ (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0286041Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 386) (fragment0286041Chars ++ tail) =
        SourceJson.value (fuel + 386) ('{' :: (fragment0286041Field000Chars00 ++ (fragment0286041Field001Chars00 ++ (fragment0286041Field002Chars00 ++ (fragment0286041Field003Chars00 ++ (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 386)) hinput
    _ = SourceJson.object (fuel + 385) (SourceJson.white (fragment0286041Field000Chars00 ++ (fragment0286041Field001Chars00 ++ (fragment0286041Field002Chars00 ++ (fragment0286041Field003Chars00 ++ (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))))))))))) fragment0286041Acc00000 := by rfl
    _ = SourceJson.object (fuel + 384) (SourceJson.white (fragment0286041Field001Chars00 ++ (fragment0286041Field002Chars00 ++ (fragment0286041Field003Chars00 ++ (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail))))))))))) fragment0286041Acc00100 := object_fragment0286041_field_000 fuel (fragment0286041Field001Chars00 ++ (fragment0286041Field002Chars00 ++ (fragment0286041Field003Chars00 ++ (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 383) (SourceJson.white (fragment0286041Field002Chars00 ++ (fragment0286041Field003Chars00 ++ (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))))))))) fragment0286041Acc00200 := object_fragment0286041_field_001 fuel (fragment0286041Field002Chars00 ++ (fragment0286041Field003Chars00 ++ (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 382) (SourceJson.white (fragment0286041Field003Chars00 ++ (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail))))))))) fragment0286041Acc00300 := object_fragment0286041_field_002 fuel (fragment0286041Field003Chars00 ++ (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 381) (SourceJson.white (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))))))) fragment0286041Acc00400 := object_fragment0286041_field_003 fuel (fragment0286041Field004Chars00 ++ (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 380) (SourceJson.white (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail))))))) fragment0286041Acc00500 := object_fragment0286041_field_004 fuel (fragment0286041Field005Chars00 ++ (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 379) (SourceJson.white (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))))) fragment0286041Acc00600 := object_fragment0286041_field_005 fuel (fragment0286041Field006Chars00 ++ (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 378) (SourceJson.white (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail))))) fragment0286041Acc00700 := object_fragment0286041_field_006 fuel (fragment0286041Field007Chars00 ++ (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 377) (SourceJson.white (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))) fragment0286041Acc00800 := object_fragment0286041_field_007 fuel (fragment0286041Field008Chars00 ++ (fragment0286041Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 376) (SourceJson.white (fragment0286041Field009Chars00 ++ (tail))) fragment0286041Acc00900 := object_fragment0286041_field_008 fuel (fragment0286041Field009Chars00 ++ (tail))
    _ = .ok (fragment0286041Value, tail) := object_fragment0286041_field_009 fuel (tail)

noncomputable def fragment0287964Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0287964Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0287964Field000Value00 : SourceJson := .number (String.ofList ['3', '7'])
noncomputable def fragment0287964Acc00100 : List (String × SourceJson) := (fragment0287964Field000Key00, fragment0287964Field000Value00) :: fragment0287964Acc00000
noncomputable def fragment0287964Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '7', ',']

theorem object_fragment0287964_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0287964Field000Chars00 ++ tail)) fragment0287964Acc00000 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0287964Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_000"
  err.flush

noncomputable def fragment0287964Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0287964Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0287964Acc00200 : List (String × SourceJson) := (fragment0287964Field001Key00, fragment0287964Field001Value00) :: fragment0287964Acc00100
noncomputable def fragment0287964Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0287964_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0287964Field001Chars00 ++ tail)) fragment0287964Acc00100 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0287964Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_001"
  err.flush

noncomputable def fragment0287964Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0287964Field002Value00 : SourceJson := .str (String.ofList ['2', '5', '3', '5', '2', '2', '7', '5', '5', '6', '9', '9', '3', '2', '4', '7', '7', '3', '8', '9', '3', '0', '1', '0', '9', '8', '8', '4', '7', '8', '1', '3', '7', '8', '4', '1', '5', '0', '9', '9', '1', '/', '2', '2', '0', '0', '7', '9', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0287964Acc00300 : List (String × SourceJson) := (fragment0287964Field002Key00, fragment0287964Field002Value00) :: fragment0287964Acc00200
noncomputable def fragment0287964Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '5', '3', '5', '2', '2', '7', '5', '5', '6', '9', '9', '3', '2', '4', '7', '7', '3', '8', '9', '3', '0', '1', '0', '9', '8', '8', '4', '7', '8', '1', '3', '7', '8', '4', '1', '5', '0', '9', '9', '1', '/', '2', '2', '0', '0', '7', '9', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0287964_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0287964Field002Chars00 ++ tail)) fragment0287964Acc00200 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0287964Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_002"
  err.flush

noncomputable def fragment0287964Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0287964Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0287964Acc00400 : List (String × SourceJson) := (fragment0287964Field003Key00, fragment0287964Field003Value00) :: fragment0287964Acc00300
noncomputable def fragment0287964Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0287964_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0287964Field003Chars00 ++ tail)) fragment0287964Acc00300 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0287964Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_003"
  err.flush

noncomputable def fragment0287964Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0287964Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0287964Acc00500 : List (String × SourceJson) := (fragment0287964Field004Key00, fragment0287964Field004Value00) :: fragment0287964Acc00400
noncomputable def fragment0287964Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0287964_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0287964Field004Chars00 ++ tail)) fragment0287964Acc00400 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0287964Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_004"
  err.flush

noncomputable def fragment0287964Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0287964Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '4', '4', '5', '1', '9', '3', '2', '1', '6', '7', '/', '1', '7', '2', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '4', '3', '6', '8', '9', '1', '6', '7', '9', '/', '1', '2', '1', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '0', '2', '0', '8', '3', '0', '8', '1', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '1', '4', '0', '7', '7', '9', '0', '7', '9', '/', '4', '5', '3', '8', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '4', '2', '7', '8', '7', '7', '3', '6', '6', '9', '/', '1', '0', '8', '9', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '7', '2', '7', '9', '0', '2', '6', '2', '3', '9', '/', '2', '1', '7', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '4', '6', '2', '2', '8', '5', '6', '7', '/', '5', '7', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '1', '1', '5', '4', '9', '8', '6', '2', '7', '/', '2', '7', '2', '3', '1', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '7', '1', '6', '3', '0', '4', '2', '1', '2', '1', '/', '2', '1', '7', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '0', '4', '8', '1', '3', '7', '2', '4', '7', '3', '/', '2', '1', '7', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0287964Acc00600 : List (String × SourceJson) := (fragment0287964Field005Key00, fragment0287964Field005Value00) :: fragment0287964Acc00500
noncomputable def fragment0287964Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '5', '1', '9', '3', '2', '1', '6', '7', '/', '1', '7', '2', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '4', '3', '6', '8', '9', '1', '6', '7', '9', '/', '1', '2', '1', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '0', '2', '0', '8', '3', '0', '8', '1', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '1', '4', '0', '7', '7', '9', '0', '7', '9', '/', '4', '5', '3', '8', '6', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '4', '2', '7', '8', '7', '7', '3', '6', '6', '9', '/', '1', '0', '8', '9', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '7', '2', '7', '9', '0', '2', '6', '2', '3', '9', '/', '2', '1', '7', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '4', '6', '2', '2', '8', '5', '6', '7', '/', '5', '7', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '1', '1', '5', '4', '9', '8', '6', '2', '7', '/', '2', '7', '2', '3', '1', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '7', '1', '6', '3', '0', '4', '2', '1', '2', '1', '/', '2', '1', '7', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '0', '4', '8', '1', '3', '7', '2', '4', '7', '3', '/', '2', '1', '7', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0287964_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0287964Field005Chars00 ++ tail)) fragment0287964Acc00500 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0287964Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_005"
  err.flush

noncomputable def fragment0287964Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0287964Field006Value00 : SourceJson := .str (String.ofList ['4', '8', '9', '1', '8', '7', '7', '8', '8', '8', '2', '3', '8', '6', '1', '6', '9', '6', '1', '0', '2', '2', '8', '4', '2', '0', '1', '1', '5', '7', '8', '0', '6', '3', '7', '4', '4', '0', '0', '7', '5', '2', '9', '5', '7', '5', '6', '6', '6', '2', '1', '4', '4', '0', '0', '0', '/', '1', '0', '3', '6', '7', '9', '6', '0', '3', '4', '4', '9', '4', '5', '8', '5', '3', '2', '6', '7', '2', '0', '4', '8', '0', '3', '9', '4', '9', '5', '1', '2', '2', '0', '9', '1', '3', '5', '7', '7', '1', '7', '0', '7', '4', '9', '6', '1', '1', '7', '6', '0', '5', '2', '8', '5', '7', '7', '7', '6', '5', '6', '2', '1', '6', '8', '0', '7'])
noncomputable def fragment0287964Acc00700 : List (String × SourceJson) := (fragment0287964Field006Key00, fragment0287964Field006Value00) :: fragment0287964Acc00600
noncomputable def fragment0287964Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '8', '9', '1', '8', '7', '7', '8', '8', '8', '2', '3', '8', '6', '1', '6', '9', '6', '1', '0', '2', '2', '8', '4', '2', '0', '1', '1', '5', '7', '8', '0', '6', '3', '7', '4', '4', '0', '0', '7', '5', '2', '9', '5', '7', '5', '6', '6', '6', '2', '1', '4', '4', '0', '0', '0', '/', '1', '0', '3', '6', '7', '9', '6', '0', '3', '4', '4', '9', '4', '5', '8', '5', '3', '2', '6', '7', '2', '0', '4', '8', '0', '3', '9', '4', '9', '5', '1', '2', '2', '0', '9', '1', '3', '5', '7', '7', '1', '7', '0', '7', '4', '9', '6', '1', '1', '7', '6', '0', '5', '2', '8', '5', '7', '7', '7', '6', '5', '6', '2', '1', '6', '8', '0', '7', '"', ',']

theorem object_fragment0287964_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0287964Field006Chars00 ++ tail)) fragment0287964Acc00600 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0287964Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_006"
  err.flush

noncomputable def fragment0287964Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0287964Field007Value00 : SourceJson := .str (String.ofList ['6', '5', '5', '4', '0', '7', '8', '3', '8', '6', '4', '6', '8', '1', '8', '2', '8', '3', '5', '3', '7', '0', '4', '4', '1', '7', '0', '9', '3', '0', '6', '0', '9', '1', '9', '6', '4', '8', '8', '9', '8', '0', '3', '6', '1', '1', '9', '5', '7', '0', '8', '7', '1', '2', '7', '8', '0', '7', '3', '5', '7', '0', '3', '3', '5', '4', '7', '6', '8', '7', '2', '7', '8', '7', '1', '1', '7', '7', '1', '1', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '1', '8', '4', '5', '6', '3', '2', '7', '7', '9', '7', '6', '3', '4', '9', '5', '0', '9', '8', '2', '8', '7', '7', '1', '9', '2', '8', '8', '7', '5', '3', '7', '2', '1', '7', '1', '3', '1', '9', '0', '4', '2', '5', '0', '4', '8', '7', '6', '0', '3', '7', '2', '7', '8', '7', '4', '7', '9', '1', '5', '6', '9', '5', '4', '8', '9', '7', '3', '7', '9', '8', '6', '9', '0', '2', '0', '2', '9', '2', '3', '3', '8', '6', '8', '8', '2', '2', '9', '3', '1', '9', '0', '5', '7', '2', '4', '1', '1', '7', '2', '2', '7', '2', '1', '3', '9', '5', '1'])
noncomputable def fragment0287964Acc00800 : List (String × SourceJson) := (fragment0287964Field007Key00, fragment0287964Field007Value00) :: fragment0287964Acc00700
noncomputable def fragment0287964Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '5', '5', '4', '0', '7', '8', '3', '8', '6', '4', '6', '8', '1', '8', '2', '8', '3', '5', '3', '7', '0', '4', '4', '1', '7', '0', '9', '3', '0', '6', '0', '9', '1', '9', '6', '4', '8', '8', '9', '8', '0', '3', '6', '1', '1', '9', '5', '7', '0', '8', '7', '1', '2', '7', '8', '0', '7', '3', '5', '7', '0', '3', '3', '5', '4', '7', '6', '8', '7', '2', '7', '8', '7', '1', '1', '7', '7', '1', '1', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '1', '8', '4', '5', '6', '3', '2', '7', '7', '9', '7', '6', '3', '4', '9', '5', '0', '9', '8', '2', '8', '7', '7', '1', '9', '2', '8', '8', '7', '5', '3', '7', '2', '1', '7', '1', '3', '1', '9', '0', '4', '2', '5', '0', '4', '8', '7', '6', '0', '3', '7', '2', '7', '8', '7', '4', '7', '9', '1', '5', '6', '9', '5', '4', '8', '9', '7', '3', '7', '9', '8', '6', '9', '0', '2', '0', '2', '9', '2', '3', '3', '8', '6', '8', '8', '2', '2', '9', '3', '1', '9', '0', '5', '7', '2', '4', '1', '1', '7', '2', '2', '7', '2', '1', '3', '9', '5', '1', '"', ',']

theorem object_fragment0287964_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0287964Field007Chars00 ++ tail)) fragment0287964Acc00700 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0287964Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_007"
  err.flush

noncomputable def fragment0287964Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0287964Field008Value00 : SourceJson := .str (String.ofList ['3', '7', '3', '8', '1', '9', '4', '2', '3', '9', '1', '2', '2', '8', '3', '0', '0', '0'])
noncomputable def fragment0287964Acc00900 : List (String × SourceJson) := (fragment0287964Field008Key00, fragment0287964Field008Value00) :: fragment0287964Acc00800
noncomputable def fragment0287964Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '3', '8', '1', '9', '4', '2', '3', '9', '1', '2', '2', '8', '3', '0', '0', '0', '"', ',']

theorem object_fragment0287964_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0287964Field008Chars00 ++ tail)) fragment0287964Acc00800 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0287964Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_008"
  err.flush

noncomputable def fragment0287964Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0287964Field009Value00 : SourceJson := .str (String.ofList ['3', '3', '2', '4', '7', '0', '4', '9', '3', '0', '0', '9', '0', '5', '5', '7', '2', '7', '1'])
noncomputable def fragment0287964Acc01000 : List (String × SourceJson) := (fragment0287964Field009Key00, fragment0287964Field009Value00) :: fragment0287964Acc00900
noncomputable def fragment0287964Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '2', '4', '7', '0', '4', '9', '3', '0', '0', '9', '0', '5', '5', '7', '2', '7', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0287964_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0287964Field009Chars00 ++ tail)) fragment0287964Acc00900 =
      .ok (.obj (fragment0287964Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287964_object_field_009"
  err.flush

noncomputable def fragment0287964Chars : List Char := '{' :: (fragment0287964Field000Chars00 ++ fragment0287964Field001Chars00 ++ fragment0287964Field002Chars00 ++ fragment0287964Field003Chars00 ++ fragment0287964Field004Chars00 ++ fragment0287964Field005Chars00 ++ fragment0287964Field006Chars00 ++ fragment0287964Field007Chars00 ++ fragment0287964Field008Chars00 ++ fragment0287964Field009Chars00)
noncomputable def fragment0287964Value : SourceJson := .obj (fragment0287964Acc01000.reverse)

theorem value_fragment0287964 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 223) (fragment0287964Chars ++ tail) =
      .ok (fragment0287964Value, tail) := by
  have hinput : fragment0287964Chars ++ tail = '{' :: (fragment0287964Field000Chars00 ++ (fragment0287964Field001Chars00 ++ (fragment0287964Field002Chars00 ++ (fragment0287964Field003Chars00 ++ (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0287964Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 223) (fragment0287964Chars ++ tail) =
        SourceJson.value (fuel + 223) ('{' :: (fragment0287964Field000Chars00 ++ (fragment0287964Field001Chars00 ++ (fragment0287964Field002Chars00 ++ (fragment0287964Field003Chars00 ++ (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 223)) hinput
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0287964Field000Chars00 ++ (fragment0287964Field001Chars00 ++ (fragment0287964Field002Chars00 ++ (fragment0287964Field003Chars00 ++ (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))))))))))) fragment0287964Acc00000 := by rfl
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0287964Field001Chars00 ++ (fragment0287964Field002Chars00 ++ (fragment0287964Field003Chars00 ++ (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail))))))))))) fragment0287964Acc00100 := object_fragment0287964_field_000 fuel (fragment0287964Field001Chars00 ++ (fragment0287964Field002Chars00 ++ (fragment0287964Field003Chars00 ++ (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0287964Field002Chars00 ++ (fragment0287964Field003Chars00 ++ (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))))))))) fragment0287964Acc00200 := object_fragment0287964_field_001 fuel (fragment0287964Field002Chars00 ++ (fragment0287964Field003Chars00 ++ (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0287964Field003Chars00 ++ (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail))))))))) fragment0287964Acc00300 := object_fragment0287964_field_002 fuel (fragment0287964Field003Chars00 ++ (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))))))) fragment0287964Acc00400 := object_fragment0287964_field_003 fuel (fragment0287964Field004Chars00 ++ (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail))))))) fragment0287964Acc00500 := object_fragment0287964_field_004 fuel (fragment0287964Field005Chars00 ++ (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))))) fragment0287964Acc00600 := object_fragment0287964_field_005 fuel (fragment0287964Field006Chars00 ++ (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail))))) fragment0287964Acc00700 := object_fragment0287964_field_006 fuel (fragment0287964Field007Chars00 ++ (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))) fragment0287964Acc00800 := object_fragment0287964_field_007 fuel (fragment0287964Field008Chars00 ++ (fragment0287964Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0287964Field009Chars00 ++ (tail))) fragment0287964Acc00900 := object_fragment0287964_field_008 fuel (fragment0287964Field009Chars00 ++ (tail))
    _ = .ok (fragment0287964Value, tail) := object_fragment0287964_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_before_reader"
  err.flush

noncomputable def chunk0036LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0036SuffixChars00 : List Char := [',']
noncomputable def chunk0036Chars00 : List Char := chunk0036LeadChars00 ++ fragment0286041Chars ++ chunk0036SuffixChars00
noncomputable def chunk0036Push00 (acc : List SourceJson) : List SourceJson := fragment0286041Value :: acc

noncomputable def chunk0036AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0036_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 568)
      (SourceJson.white (chunk0036LeadChars00 ++ (fragment0286041Chars ++ rest))) acc =
      (SourceJson.value (fuel + 567) (fragment0286041Chars ++ rest)).bind
        (chunk0036AfterValue00 (fuel + 567) acc) := by rfl

theorem array_chunk0036 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 568) (SourceJson.white (chunk0036Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 567) (SourceJson.white tail) (chunk0036Push00 acc) := by
  have hinput : chunk0036Chars00 ++ tail = chunk0036LeadChars00 ++ (fragment0286041Chars ++ (chunk0036SuffixChars00 ++ tail)) := by
    simp only [chunk0036Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 568) (SourceJson.white (chunk0036Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 568)
          (SourceJson.white (chunk0036LeadChars00 ++ (fragment0286041Chars ++ (chunk0036SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 568) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 567) (fragment0286041Chars ++ (chunk0036SuffixChars00 ++ tail))).bind
        (chunk0036AfterValue00 (fuel + 567) acc) := array_chunk0036_head fuel (chunk0036SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0286041Value, chunk0036SuffixChars00 ++ tail)).bind
        (chunk0036AfterValue00 (fuel + 567) acc) :=
      congrArg (fun result => result.bind (chunk0036AfterValue00 (fuel + 567) acc))
        (value_fragment0286041 (fuel + 181) (chunk0036SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 567) (SourceJson.white tail) (chunk0036Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_before_reader"
  err.flush

noncomputable def chunk0037LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0037SuffixChars00 : List Char := [',']
noncomputable def chunk0037Chars00 : List Char := chunk0037LeadChars00 ++ fragment0287964Chars ++ chunk0037SuffixChars00
noncomputable def chunk0037Push00 (acc : List SourceJson) : List SourceJson := fragment0287964Value :: acc

noncomputable def chunk0037AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0037_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 567)
      (SourceJson.white (chunk0037LeadChars00 ++ (fragment0287964Chars ++ rest))) acc =
      (SourceJson.value (fuel + 566) (fragment0287964Chars ++ rest)).bind
        (chunk0037AfterValue00 (fuel + 566) acc) := by rfl

theorem array_chunk0037 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 567) (SourceJson.white (chunk0037Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 566) (SourceJson.white tail) (chunk0037Push00 acc) := by
  have hinput : chunk0037Chars00 ++ tail = chunk0037LeadChars00 ++ (fragment0287964Chars ++ (chunk0037SuffixChars00 ++ tail)) := by
    simp only [chunk0037Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 567) (SourceJson.white (chunk0037Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 567)
          (SourceJson.white (chunk0037LeadChars00 ++ (fragment0287964Chars ++ (chunk0037SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 567) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 566) (fragment0287964Chars ++ (chunk0037SuffixChars00 ++ tail))).bind
        (chunk0037AfterValue00 (fuel + 566) acc) := array_chunk0037_head fuel (chunk0037SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0287964Value, chunk0037SuffixChars00 ++ tail)).bind
        (chunk0037AfterValue00 (fuel + 566) acc) :=
      congrArg (fun result => result.bind (chunk0037AfterValue00 (fuel + 566) acc))
        (value_fragment0287964 (fuel + 343) (chunk0037SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 566) (SourceJson.white tail) (chunk0037Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0036Chars00 ++ chunk0037Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0037Push00 (chunk0036Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 568) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 566) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 568) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 568) (SourceJson.white (chunk0036Chars00 ++ (chunk0037Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 568) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 567) (SourceJson.white (chunk0037Chars00 ++ (tail))) (chunk0036Push00 (acc)) := array_chunk0036 fuel (chunk0037Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 566) (SourceJson.white tail) (blockPush acc) := array_chunk0037 fuel (tail) (chunk0036Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 286035).take 3519 = blockChars := by rfl

theorem block_original_split : sourceRest 286035 = blockChars ++ sourceRest 289554 := by
  calc
    sourceRest 286035 = (sourceRest 286035).take 3519 ++ (sourceRest 286035).drop 3519 :=
      (List.take_append_drop 3519 (sourceRest 286035)).symm
    _ = blockChars ++ (sourceRest 286035).drop 3519 :=
      congrArg (fun part => part ++ (sourceRest 286035).drop 3519) block_original_prefix
    _ = blockChars ++ sourceRest 289554 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 286035 3519)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 568) (SourceJson.white (sourceRest 286035)) acc =
      SourceJson.array (fuel + 566) (SourceJson.white (sourceRest 289554)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 568) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 289554) acc)

#print axioms object_fragment0286041_field_000
#print axioms object_fragment0286041_field_001
#print axioms object_fragment0286041_field_002
#print axioms object_fragment0286041_field_003
#print axioms object_fragment0286041_field_004
#print axioms object_fragment0286041_field_005
#print axioms object_fragment0286041_field_006
#print axioms object_fragment0286041_field_007
#print axioms object_fragment0286041_field_008
#print axioms object_fragment0286041_field_009
#print axioms value_fragment0286041
#print axioms object_fragment0287964_field_000
#print axioms object_fragment0287964_field_001
#print axioms object_fragment0287964_field_002
#print axioms object_fragment0287964_field_003
#print axioms object_fragment0287964_field_004
#print axioms object_fragment0287964_field_005
#print axioms object_fragment0287964_field_006
#print axioms object_fragment0287964_field_007
#print axioms object_fragment0287964_field_008
#print axioms object_fragment0287964_field_009
#print axioms value_fragment0287964
#print axioms array_chunk0036_head
#print axioms array_chunk0036
#print axioms array_chunk0037_head
#print axioms array_chunk0037
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock018

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
