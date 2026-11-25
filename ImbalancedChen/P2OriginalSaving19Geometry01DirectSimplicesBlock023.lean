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

namespace SimplicesBlock023

noncomputable def fragment0302247Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0302247Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0302247Field000Value00 : SourceJson := .number (String.ofList ['4', '5'])
noncomputable def fragment0302247Acc00100 : List (String × SourceJson) := (fragment0302247Field000Key00, fragment0302247Field000Value00) :: fragment0302247Acc00000
noncomputable def fragment0302247Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '5', ',']

theorem object_fragment0302247_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 278) (SourceJson.white (fragment0302247Field000Chars00 ++ tail)) fragment0302247Acc00000 =
      SourceJson.object (fuel + 277) (SourceJson.white tail) fragment0302247Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_000"
  err.flush

noncomputable def fragment0302247Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0302247Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['0'])]
noncomputable def fragment0302247Acc00200 : List (String × SourceJson) := (fragment0302247Field001Key00, fragment0302247Field001Value00) :: fragment0302247Acc00100
noncomputable def fragment0302247Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0302247_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 277) (SourceJson.white (fragment0302247Field001Chars00 ++ tail)) fragment0302247Acc00100 =
      SourceJson.object (fuel + 276) (SourceJson.white tail) fragment0302247Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_001"
  err.flush

noncomputable def fragment0302247Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0302247Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '6', '9', '0', '7', '4', '8', '5', '2', '0', '5', '8', '6', '0', '1', '2', '5', '4', '3', '8', '6', '5', '1', '3', '0', '4', '7', '5', '2', '8', '5', '4', '8', '0', '3', '5', '0', '3', '1', '1', '1', '/', '2', '9', '1', '3', '4', '5', '7', '6', '9', '9', '7', '7', '9', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0302247Acc00300 : List (String × SourceJson) := (fragment0302247Field002Key00, fragment0302247Field002Value00) :: fragment0302247Acc00200
noncomputable def fragment0302247Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '6', '9', '0', '7', '4', '8', '5', '2', '0', '5', '8', '6', '0', '1', '2', '5', '4', '3', '8', '6', '5', '1', '3', '0', '4', '7', '5', '2', '8', '5', '4', '8', '0', '3', '5', '0', '3', '1', '1', '1', '/', '2', '9', '1', '3', '4', '5', '7', '6', '9', '9', '7', '7', '9', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0302247_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 276) (SourceJson.white (fragment0302247Field002Chars00 ++ tail)) fragment0302247Acc00200 =
      SourceJson.object (fuel + 275) (SourceJson.white tail) fragment0302247Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_002"
  err.flush

noncomputable def fragment0302247Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0302247Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0302247Acc00400 : List (String × SourceJson) := (fragment0302247Field003Key00, fragment0302247Field003Value00) :: fragment0302247Acc00300
noncomputable def fragment0302247Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0302247_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 275) (SourceJson.white (fragment0302247Field003Chars00 ++ tail)) fragment0302247Acc00300 =
      SourceJson.object (fuel + 274) (SourceJson.white tail) fragment0302247Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_003"
  err.flush

noncomputable def fragment0302247Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0302247Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0302247Acc00500 : List (String × SourceJson) := (fragment0302247Field004Key00, fragment0302247Field004Value00) :: fragment0302247Acc00400
noncomputable def fragment0302247Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0302247_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 274) (SourceJson.white (fragment0302247Field004Chars00 ++ tail)) fragment0302247Acc00400 =
      SourceJson.object (fuel + 273) (SourceJson.white tail) fragment0302247Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_004"
  err.flush

noncomputable def fragment0302247Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0302247Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '2', '5', '3', '4', '3', '1', '5', '8', '0', '2', '3', '0', '9', '/', '7', '3', '3', '6', '1', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '6', '7', '1', '3', '0', '0', '3', '9', '1', '3', '3', '7', '/', '7', '3', '3', '6', '1', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '2', '5', '9', '1', '9', '4', '1', '9', '5', '8', '4', '7', '7', '/', '2', '2', '0', '0', '8', '5', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '0', '3', '8', '8', '4', '1', '9', '6', '1', '5', '1', '9', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '3', '6', '8', '1', '7', '5', '6', '5', '8', '2', '2', '7', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '0', '7', '5', '3', '1', '3', '0', '7', '5', '1', '9', '3', '9', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '0', '7', '8', '0', '7', '6', '6', '5', '4', '6', '9', '9', '/', '5', '7', '9', '1', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '0', '6', '0', '7', '5', '3', '8', '5', '4', '1', '5', '0', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '4', '3', '9', '5', '0', '3', '5', '1', '4', '6', '1', '2', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '4', '3', '9', '2', '1', '0', '0', '6', '7', '6', '6', '8', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0302247Acc00600 : List (String × SourceJson) := (fragment0302247Field005Key00, fragment0302247Field005Value00) :: fragment0302247Acc00500
noncomputable def fragment0302247Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '5', '3', '4', '3', '1', '5', '8', '0', '2', '3', '0', '9', '/', '7', '3', '3', '6', '1', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '6', '7', '1', '3', '0', '0', '3', '9', '1', '3', '3', '7', '/', '7', '3', '3', '6', '1', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '2', '5', '9', '1', '9', '4', '1', '9', '5', '8', '4', '7', '7', '/', '2', '2', '0', '0', '8', '5', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '0', '3', '8', '8', '4', '1', '9', '6', '1', '5', '1', '9', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '3', '6', '8', '1', '7', '5', '6', '5', '8', '2', '2', '7', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '0', '7', '5', '3', '1', '3', '0', '7', '5', '1', '9', '3', '9', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '0', '7', '8', '0', '7', '6', '6', '5', '4', '6', '9', '9', '/', '5', '7', '9', '1', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '0', '6', '0', '7', '5', '3', '8', '5', '4', '1', '5', '0', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '3', '9', '5', '0', '3', '5', '1', '4', '6', '1', '2', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '3', '9', '2', '1', '0', '0', '6', '7', '6', '6', '8', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0302247_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 273) (SourceJson.white (fragment0302247Field005Chars00 ++ tail)) fragment0302247Acc00500 =
      SourceJson.object (fuel + 272) (SourceJson.white tail) fragment0302247Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_005"
  err.flush

noncomputable def fragment0302247Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0302247Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '5', '3', '3', '0', '5', '4', '8', '1', '7', '0', '8', '8', '2', '6', '6', '6', '1', '8', '0', '9', '0', '9', '9', '5', '6', '0', '8', '3', '5', '3', '8', '3', '9', '8', '9', '1', '7', '1', '3', '9', '0', '1', '0', '0', '0', '/', '2', '5', '1', '4', '3', '6', '7', '4', '6', '8', '6', '2', '7', '1', '3', '8', '8', '7', '4', '5', '8', '6', '9', '9', '6', '7', '9', '0', '4', '6', '8', '7', '0', '1', '1', '4', '1', '4', '3', '3', '5', '1', '6', '1', '8', '7', '5', '5', '5', '8', '6', '9', '4', '6', '4', '6', '4', '3', '6', '1', '5', '8', '2', '8', '7'])
noncomputable def fragment0302247Acc00700 : List (String × SourceJson) := (fragment0302247Field006Key00, fragment0302247Field006Value00) :: fragment0302247Acc00600
noncomputable def fragment0302247Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '5', '3', '3', '0', '5', '4', '8', '1', '7', '0', '8', '8', '2', '6', '6', '6', '1', '8', '0', '9', '0', '9', '9', '5', '6', '0', '8', '3', '5', '3', '8', '3', '9', '8', '9', '1', '7', '1', '3', '9', '0', '1', '0', '0', '0', '/', '2', '5', '1', '4', '3', '6', '7', '4', '6', '8', '6', '2', '7', '1', '3', '8', '8', '7', '4', '5', '8', '6', '9', '9', '6', '7', '9', '0', '4', '6', '8', '7', '0', '1', '1', '4', '1', '4', '3', '3', '5', '1', '6', '1', '8', '7', '5', '5', '5', '8', '6', '9', '4', '6', '4', '6', '4', '3', '6', '1', '5', '8', '2', '8', '7', '"', ',']

theorem object_fragment0302247_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 272) (SourceJson.white (fragment0302247Field006Chars00 ++ tail)) fragment0302247Acc00600 =
      SourceJson.object (fuel + 271) (SourceJson.white tail) fragment0302247Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_006"
  err.flush

noncomputable def fragment0302247Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0302247Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '5', '0', '1', '1', '6', '5', '8', '8', '2', '6', '4', '8', '1', '8', '7', '8', '2', '4', '9', '0', '4', '9', '2', '8', '2', '8', '4', '1', '3', '0', '8', '9', '1', '1', '6', '2', '1', '8', '5', '6', '2', '4', '3', '8', '2', '3', '8', '6', '0', '2', '1', '3', '0', '2', '5', '2', '6', '2', '8', '6', '9', '3', '3', '8', '0', '9', '3', '5', '1', '5', '6', '9', '2', '7', '3', '8', '3', '6', '7', '2', '3', '8', '3', '4', '2', '6', '6', '2', '5', '7', '6', '0', '1', '4', '5', '6', '7', '6', '3', '6', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '0', '8', '0', '6', '9', '4', '4', '3', '8', '2', '6', '0', '9', '5', '8', '9', '0', '2', '9', '6', '9', '6', '7', '9', '3', '0', '6', '5', '9', '3', '1', '8', '9', '1', '3', '7', '3', '9', '4', '9', '0', '5', '0', '9', '7', '8', '7', '8', '4', '8', '7', '9', '2', '8', '0', '1', '1', '5', '4', '3', '6', '3', '2', '6', '6', '1', '4', '1', '9', '2', '0', '6', '7', '9', '3', '8', '4', '0', '0', '4', '2', '6', '6', '3', '0', '7', '3', '4', '5', '1', '2', '7', '1', '5', '0', '2', '6', '3', '5', '4', '7', '0', '6', '8', '8', '1', '3', '7', '5', '0', '9', '2', '9', '1', '3', '5', '2', '5', '1', '9', '7', '5', '2', '6', '7', '5', '0', '1', '3', '1', '6', '7', '8', '2', '2', '2', '5', '7', '5', '3'])
noncomputable def fragment0302247Acc00800 : List (String × SourceJson) := (fragment0302247Field007Key00, fragment0302247Field007Value00) :: fragment0302247Acc00700
noncomputable def fragment0302247Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '5', '0', '1', '1', '6', '5', '8', '8', '2', '6', '4', '8', '1', '8', '7', '8', '2', '4', '9', '0', '4', '9', '2', '8', '2', '8', '4', '1', '3', '0', '8', '9', '1', '1', '6', '2', '1', '8', '5', '6', '2', '4', '3', '8', '2', '3', '8', '6', '0', '2', '1', '3', '0', '2', '5', '2', '6', '2', '8', '6', '9', '3', '3', '8', '0', '9', '3', '5', '1', '5', '6', '9', '2', '7', '3', '8', '3', '6', '7', '2', '3', '8', '3', '4', '2', '6', '6', '2', '5', '7', '6', '0', '1', '4', '5', '6', '7', '6', '3', '6', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '0', '8', '0', '6', '9', '4', '4', '3', '8', '2', '6', '0', '9', '5', '8', '9', '0', '2', '9', '6', '9', '6', '7', '9', '3', '0', '6', '5', '9', '3', '1', '8', '9', '1', '3', '7', '3', '9', '4', '9', '0', '5', '0', '9', '7', '8', '7', '8', '4', '8', '7', '9', '2', '8', '0', '1', '1', '5', '4', '3', '6', '3', '2', '6', '6', '1', '4', '1', '9', '2', '0', '6', '7', '9', '3', '8', '4', '0', '0', '4', '2', '6', '6', '3', '0', '7', '3', '4', '5', '1', '2', '7', '1', '5', '0', '2', '6', '3', '5', '4', '7', '0', '6', '8', '8', '1', '3', '7', '5', '0', '9', '2', '9', '1', '3', '5', '2', '5', '1', '9', '7', '5', '2', '6', '7', '5', '0', '1', '3', '1', '6', '7', '8', '2', '2', '2', '5', '7', '5', '3', '"', ',']

theorem object_fragment0302247_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 271) (SourceJson.white (fragment0302247Field007Chars00 ++ tail)) fragment0302247Acc00700 =
      SourceJson.object (fuel + 270) (SourceJson.white tail) fragment0302247Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_007"
  err.flush

noncomputable def fragment0302247Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0302247Field008Value00 : SourceJson := .str (String.ofList ['3', '3', '1', '8', '9', '8', '4', '1', '5', '4', '9'])
noncomputable def fragment0302247Acc00900 : List (String × SourceJson) := (fragment0302247Field008Key00, fragment0302247Field008Value00) :: fragment0302247Acc00800
noncomputable def fragment0302247Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '1', '8', '9', '8', '4', '1', '5', '4', '9', '"', ',']

theorem object_fragment0302247_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment0302247Field008Chars00 ++ tail)) fragment0302247Acc00800 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment0302247Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_008"
  err.flush

noncomputable def fragment0302247Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0302247Field009Value00 : SourceJson := .str (String.ofList ['2', '8', '5', '0', '7', '6', '3', '9', '1', '1', '1', '3'])
noncomputable def fragment0302247Acc01000 : List (String × SourceJson) := (fragment0302247Field009Key00, fragment0302247Field009Value00) :: fragment0302247Acc00900
noncomputable def fragment0302247Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '8', '5', '0', '7', '6', '3', '9', '1', '1', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0302247_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0302247Field009Chars00 ++ tail)) fragment0302247Acc00900 =
      .ok (.obj (fragment0302247Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0302247_object_field_009"
  err.flush

noncomputable def fragment0302247Chars : List Char := '{' :: (fragment0302247Field000Chars00 ++ fragment0302247Field001Chars00 ++ fragment0302247Field002Chars00 ++ fragment0302247Field003Chars00 ++ fragment0302247Field004Chars00 ++ fragment0302247Field005Chars00 ++ fragment0302247Field006Chars00 ++ fragment0302247Field007Chars00 ++ fragment0302247Field008Chars00 ++ fragment0302247Field009Chars00)
noncomputable def fragment0302247Value : SourceJson := .obj (fragment0302247Acc01000.reverse)

theorem value_fragment0302247 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 279) (fragment0302247Chars ++ tail) =
      .ok (fragment0302247Value, tail) := by
  have hinput : fragment0302247Chars ++ tail = '{' :: (fragment0302247Field000Chars00 ++ (fragment0302247Field001Chars00 ++ (fragment0302247Field002Chars00 ++ (fragment0302247Field003Chars00 ++ (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0302247Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 279) (fragment0302247Chars ++ tail) =
        SourceJson.value (fuel + 279) ('{' :: (fragment0302247Field000Chars00 ++ (fragment0302247Field001Chars00 ++ (fragment0302247Field002Chars00 ++ (fragment0302247Field003Chars00 ++ (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 279)) hinput
    _ = SourceJson.object (fuel + 278) (SourceJson.white (fragment0302247Field000Chars00 ++ (fragment0302247Field001Chars00 ++ (fragment0302247Field002Chars00 ++ (fragment0302247Field003Chars00 ++ (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))))))))))) fragment0302247Acc00000 := by rfl
    _ = SourceJson.object (fuel + 277) (SourceJson.white (fragment0302247Field001Chars00 ++ (fragment0302247Field002Chars00 ++ (fragment0302247Field003Chars00 ++ (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail))))))))))) fragment0302247Acc00100 := object_fragment0302247_field_000 fuel (fragment0302247Field001Chars00 ++ (fragment0302247Field002Chars00 ++ (fragment0302247Field003Chars00 ++ (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 276) (SourceJson.white (fragment0302247Field002Chars00 ++ (fragment0302247Field003Chars00 ++ (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))))))))) fragment0302247Acc00200 := object_fragment0302247_field_001 fuel (fragment0302247Field002Chars00 ++ (fragment0302247Field003Chars00 ++ (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 275) (SourceJson.white (fragment0302247Field003Chars00 ++ (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail))))))))) fragment0302247Acc00300 := object_fragment0302247_field_002 fuel (fragment0302247Field003Chars00 ++ (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 274) (SourceJson.white (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))))))) fragment0302247Acc00400 := object_fragment0302247_field_003 fuel (fragment0302247Field004Chars00 ++ (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 273) (SourceJson.white (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail))))))) fragment0302247Acc00500 := object_fragment0302247_field_004 fuel (fragment0302247Field005Chars00 ++ (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 272) (SourceJson.white (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))))) fragment0302247Acc00600 := object_fragment0302247_field_005 fuel (fragment0302247Field006Chars00 ++ (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 271) (SourceJson.white (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail))))) fragment0302247Acc00700 := object_fragment0302247_field_006 fuel (fragment0302247Field007Chars00 ++ (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))) fragment0302247Acc00800 := object_fragment0302247_field_007 fuel (fragment0302247Field008Chars00 ++ (fragment0302247Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0302247Field009Chars00 ++ (tail))) fragment0302247Acc00900 := object_fragment0302247_field_008 fuel (fragment0302247Field009Chars00 ++ (tail))
    _ = .ok (fragment0302247Value, tail) := object_fragment0302247_field_009 fuel (tail)

noncomputable def fragment0303943Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0303943Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0303943Field000Value00 : SourceJson := .number (String.ofList ['4', '6'])
noncomputable def fragment0303943Acc00100 : List (String × SourceJson) := (fragment0303943Field000Key00, fragment0303943Field000Value00) :: fragment0303943Acc00000
noncomputable def fragment0303943Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '6', ',']

theorem object_fragment0303943_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 510) (SourceJson.white (fragment0303943Field000Chars00 ++ tail)) fragment0303943Acc00000 =
      SourceJson.object (fuel + 509) (SourceJson.white tail) fragment0303943Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_000"
  err.flush

noncomputable def fragment0303943Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0303943Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0303943Acc00200 : List (String × SourceJson) := (fragment0303943Field001Key00, fragment0303943Field001Value00) :: fragment0303943Acc00100
noncomputable def fragment0303943Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0303943_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 509) (SourceJson.white (fragment0303943Field001Chars00 ++ tail)) fragment0303943Acc00100 =
      SourceJson.object (fuel + 508) (SourceJson.white tail) fragment0303943Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_001"
  err.flush

noncomputable def fragment0303943Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0303943Field002Value00 : SourceJson := .str (String.ofList ['2', '9', '6', '5', '7', '1', '6', '7', '4', '4', '3', '5', '5', '9', '8', '6', '8', '6', '0', '9', '6', '0', '6', '9', '1', '7', '1', '3', '2', '9', '1', '4', '3', '6', '6', '6', '2', '3', '6', '5', '5', '7', '6', '7', '/', '9', '4', '0', '7', '3', '1', '7', '5', '1', '9', '7', '3', '8', '0', '0', '3', '7', '8', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0303943Acc00300 : List (String × SourceJson) := (fragment0303943Field002Key00, fragment0303943Field002Value00) :: fragment0303943Acc00200
noncomputable def fragment0303943Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '9', '6', '5', '7', '1', '6', '7', '4', '4', '3', '5', '5', '9', '8', '6', '8', '6', '0', '9', '6', '0', '6', '9', '1', '7', '1', '3', '2', '9', '1', '4', '3', '6', '6', '6', '2', '3', '6', '5', '5', '7', '6', '7', '/', '9', '4', '0', '7', '3', '1', '7', '5', '1', '9', '7', '3', '8', '0', '0', '3', '7', '8', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0303943_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 508) (SourceJson.white (fragment0303943Field002Chars00 ++ tail)) fragment0303943Acc00200 =
      SourceJson.object (fuel + 507) (SourceJson.white tail) fragment0303943Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_002"
  err.flush

noncomputable def fragment0303943Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0303943Field003Value00 : SourceJson := .str (String.ofList ['8', '9', '9', '1', '5', '3', '1', '1', '3', '/', '1', '1', '1', '0', '1', '9', '3', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0303943Acc00400 : List (String × SourceJson) := (fragment0303943Field003Key00, fragment0303943Field003Value00) :: fragment0303943Acc00300
noncomputable def fragment0303943Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '8', '9', '9', '1', '5', '3', '1', '1', '3', '/', '1', '1', '1', '0', '1', '9', '3', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0303943_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 507) (SourceJson.white (fragment0303943Field003Chars00 ++ tail)) fragment0303943Acc00300 =
      SourceJson.object (fuel + 506) (SourceJson.white tail) fragment0303943Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_003"
  err.flush

noncomputable def fragment0303943Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0303943Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4'])]
noncomputable def fragment0303943Acc00500 : List (String × SourceJson) := (fragment0303943Field004Key00, fragment0303943Field004Value00) :: fragment0303943Acc00400
noncomputable def fragment0303943Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0303943_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 506) (SourceJson.white (fragment0303943Field004Chars00 ++ tail)) fragment0303943Acc00400 =
      SourceJson.object (fuel + 505) (SourceJson.white tail) fragment0303943Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_004"
  err.flush

noncomputable def fragment0303943Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0303943Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '5', '8', '4', '8', '2', '4', '8', '1', '7', '5', '4', '3', '5', '3', '1', '7', '8', '2', '6', '5', '4', '2', '1', '/', '8', '7', '3', '2', '3', '0', '2', '1', '2', '2', '5', '0', '3', '1', '4', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '5', '0', '4', '2', '6', '6', '1', '6', '3', '2', '6', '7', '4', '9', '7', '9', '3', '1', '2', '8', '1', '3', '9', '/', '8', '5', '5', '7', '6', '5', '6', '0', '8', '0', '0', '5', '3', '0', '7', '9', '3', '9', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '6', '2', '3', '2', '6', '5', '5', '2', '6', '6', '4', '1', '1', '2', '2', '2', '7', '1', '5', '3', '9', '5', '9', '0', '1', '/', '1', '2', '8', '3', '6', '4', '8', '4', '1', '2', '0', '0', '7', '9', '6', '1', '9', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '1', '0', '1', '5', '5', '2', '5', '3', '9', '0', '8', '2', '8', '0', '3', '5', '3', '2', '0', '3', '2', '1', '9', '7', '/', '1', '0', '6', '9', '7', '0', '7', '0', '1', '0', '0', '0', '6', '6', '3', '4', '9', '2', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '8', '6', '4', '2', '5', '4', '4', '5', '2', '3', '7', '1', '1', '7', '3', '8', '6', '7', '8', '7', '0', '1', '0', '1', '/', '2', '1', '3', '9', '4', '1', '4', '0', '2', '0', '0', '1', '3', '2', '6', '9', '8', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '6', '9', '6', '0', '7', '8', '3', '2', '3', '0', '8', '7', '1', '2', '1', '3', '4', '0', '8', '3', '5', '6', '9', '3', '9', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '1', '4', '7', '2', '5', '4', '8', '6', '2', '4', '9', '1', '6', '5', '9', '6', '8', '0', '6', '1', '6', '2', '9', '/', '3', '3', '7', '8', '0', '2', '2', '1', '3', '6', '8', '6', '3', '0', '5', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '2', '8', '5', '2', '6', '5', '1', '2', '9', '0', '0', '3', '8', '0', '0', '1', '6', '5', '0', '6', '1', '5', '4', '7', '1', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '9', '5', '7', '8', '3', '2', '0', '1', '7', '6', '8', '1', '6', '3', '5', '6', '9', '1', '9', '7', '2', '6', '3', '3', '3', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '1', '6', '1', '5', '4', '1', '8', '5', '1', '7', '9', '2', '6', '6', '8', '9', '2', '2', '9', '3', '1', '1', '0', '3', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0303943Acc00600 : List (String × SourceJson) := (fragment0303943Field005Key00, fragment0303943Field005Value00) :: fragment0303943Acc00500
noncomputable def fragment0303943Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '8', '4', '8', '2', '4', '8', '1', '7', '5', '4', '3', '5', '3', '1', '7', '8', '2', '6', '5', '4', '2', '1', '/', '8', '7', '3', '2', '3', '0', '2', '1', '2', '2', '5', '0', '3', '1', '4', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '5', '0', '4', '2', '6', '6', '1', '6', '3', '2', '6', '7', '4', '9', '7', '9', '3', '1', '2', '8', '1', '3', '9', '/', '8', '5', '5', '7', '6', '5', '6', '0', '8', '0', '0', '5', '3', '0', '7', '9', '3', '9', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '2', '3', '2', '6', '5', '5', '2', '6', '6', '4', '1', '1', '2', '2', '2', '7', '1', '5', '3', '9', '5', '9', '0', '1', '/', '1', '2', '8', '3', '6', '4', '8', '4', '1', '2', '0', '0', '7', '9', '6', '1', '9', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '1', '0', '1', '5', '5', '2', '5', '3', '9', '0', '8', '2', '8', '0', '3', '5', '3', '2', '0', '3', '2', '1', '9', '7', '/', '1', '0', '6', '9', '7', '0', '7', '0', '1', '0', '0', '0', '6', '6', '3', '4', '9', '2', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '8', '6', '4', '2', '5', '4', '4', '5', '2', '3', '7', '1', '1', '7', '3', '8', '6', '7', '8', '7', '0', '1', '0', '1', '/', '2', '1', '3', '9', '4', '1', '4', '0', '2', '0', '0', '1', '3', '2', '6', '9', '8', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '6', '9', '6', '0', '7', '8', '3', '2', '3', '0', '8', '7', '1', '2', '1', '3', '4', '0', '8', '3', '5', '6', '9', '3', '9', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '1', '4', '7', '2', '5', '4', '8', '6', '2', '4', '9', '1', '6', '5', '9', '6', '8', '0', '6', '1', '6', '2', '9', '/', '3', '3', '7', '8', '0', '2', '2', '1', '3', '6', '8', '6', '3', '0', '5', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '2', '8', '5', '2', '6', '5', '1', '2', '9', '0', '0', '3', '8', '0', '0', '1', '6', '5', '0', '6', '1', '5', '4', '7', '1', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '5', '7', '8', '3', '2', '0', '1', '7', '6', '8', '1', '6', '3', '5', '6', '9', '1', '9', '7', '2', '6', '3', '3', '3', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '1', '6', '1', '5', '4', '1', '8', '5', '1', '7', '9', '2', '6', '6', '8', '9', '2', '2', '9', '3', '1', '1', '0', '3', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0303943_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 505) (SourceJson.white (fragment0303943Field005Chars00 ++ tail)) fragment0303943Acc00500 =
      SourceJson.object (fuel + 504) (SourceJson.white tail) fragment0303943Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_005"
  err.flush

noncomputable def fragment0303943Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0303943Field006Value00 : SourceJson := .str (String.ofList ['9', '0', '2', '8', '1', '0', '0', '6', '8', '4', '6', '4', '2', '7', '0', '7', '2', '9', '6', '2', '9', '3', '0', '9', '2', '3', '3', '4', '2', '0', '2', '0', '1', '4', '5', '8', '0', '8', '9', '3', '4', '3', '3', '5', '1', '8', '9', '7', '4', '5', '7', '2', '/', '5', '3', '1', '0', '0', '2', '0', '8', '6', '0', '0', '3', '3', '7', '2', '0', '6', '4', '3', '4', '4', '5', '5', '9', '6', '8', '5', '8', '4', '2', '5', '9', '6', '6', '2', '8', '6', '1', '0', '3', '5', '8', '9', '7', '4', '8', '9', '6', '2', '2', '3', '5', '3', '5', '7', '1', '4', '2', '7', '2', '7', '2', '0', '6', '2', '5'])
noncomputable def fragment0303943Acc00700 : List (String × SourceJson) := (fragment0303943Field006Key00, fragment0303943Field006Value00) :: fragment0303943Acc00600
noncomputable def fragment0303943Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '0', '2', '8', '1', '0', '0', '6', '8', '4', '6', '4', '2', '7', '0', '7', '2', '9', '6', '2', '9', '3', '0', '9', '2', '3', '3', '4', '2', '0', '2', '0', '1', '4', '5', '8', '0', '8', '9', '3', '4', '3', '3', '5', '1', '8', '9', '7', '4', '5', '7', '2', '/', '5', '3', '1', '0', '0', '2', '0', '8', '6', '0', '0', '3', '3', '7', '2', '0', '6', '4', '3', '4', '4', '5', '5', '9', '6', '8', '5', '8', '4', '2', '5', '9', '6', '6', '2', '8', '6', '1', '0', '3', '5', '8', '9', '7', '4', '8', '9', '6', '2', '2', '3', '5', '3', '5', '7', '1', '4', '2', '7', '2', '7', '2', '0', '6', '2', '5', '"', ',']

theorem object_fragment0303943_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 504) (SourceJson.white (fragment0303943Field006Chars00 ++ tail)) fragment0303943Acc00600 =
      SourceJson.object (fuel + 503) (SourceJson.white tail) fragment0303943Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_006"
  err.flush

noncomputable def fragment0303943Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0303943Field007Value00 : SourceJson := .str (String.ofList ['8', '9', '8', '7', '5', '0', '6', '0', '7', '8', '7', '0', '1', '1', '8', '8', '2', '0', '0', '5', '5', '9', '8', '4', '6', '0', '2', '2', '9', '9', '1', '4', '2', '0', '5', '9', '8', '6', '6', '5', '4', '6', '3', '6', '7', '7', '9', '6', '5', '5', '3', '3', '2', '4', '7', '9', '6', '1', '0', '5', '6', '7', '3', '8', '2', '9', '2', '2', '5', '8', '3', '7', '8', '3', '4', '9', '8', '5', '4', '2', '6', '5', '9', '1', '1', '6', '8', '1', '6', '2', '6', '3', '5', '7', '5', '9', '2', '4', '2', '6', '8', '1', '5', '3', '0', '2', '8', '0', '0', '7', '0', '5', '5', '7', '8', '2', '9', '2', '8', '9', '6', '4', '3', '7', '6', '0', '2', '9', '5', '5', '5', '8', '1', '2', '9', '6', '6', '3', '0', '8', '8', '0', '0', '9', '9', '8', '3', '5', '1', '2', '4', '7', '0', '5', '0', '2', '7', '5', '6', '8', '0', '2', '5', '9', '3', '0', '3', '9', '2', '1', '5', '6', '4', '8', '9', '7', '9', '2', '0', '4', '8', '5', '2', '7', '6', '7', '1', '6', '1', '6', '2', '4', '2', '3', '1', '1', '2', '9', '1', '7', '6', '5', '6', '6', '3', '6', '5', '0', '0', '0', '7', '1', '0', '7', '9', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '9', '9', '8', '2', '4', '5', '9', '6', '7', '7', '1', '2', '4', '8', '9', '1', '9', '0', '0', '9', '2', '1', '8', '5', '0', '1', '0', '1', '6', '0', '8', '5', '9', '1', '7', '1', '9', '9', '5', '7', '1', '6', '0', '7', '3', '3', '3', '9', '3', '5', '8', '7', '6', '2', '1', '7', '9', '1', '8', '6', '9', '4', '4', '3', '5', '5', '3', '8', '1', '5', '8', '4', '9', '3', '1', '2', '6', '5', '8', '5', '7', '8', '2', '7', '6', '1', '7', '3', '9', '0', '2', '7', '6', '9', '6', '4', '8', '2', '0', '6', '7', '8', '5', '1', '7', '9', '3', '0', '9', '7', '3', '4', '1', '3', '5', '9', '8', '8', '8', '1', '9', '5', '5', '9', '8', '1', '0', '1', '6', '6', '6', '4', '6', '3', '0', '8', '1', '3', '8', '0', '8', '2', '7', '1', '3', '6', '0', '3', '5', '4', '5', '7', '9', '5', '4', '9', '3', '4', '0', '2', '2', '3', '8', '3', '2', '6', '3', '9', '7', '1', '9', '8', '4', '5', '8', '3', '0', '2', '5', '6', '4', '7', '8', '9', '5', '2', '3', '4', '0', '6', '4', '2', '2', '0', '2', '7', '0', '0', '6', '6', '3', '0', '9', '0', '6', '1', '5', '6', '5', '6', '5', '6', '4', '9', '6', '3', '5', '9', '4', '5', '0', '9', '3', '7', '2', '2', '6', '5', '3', '7', '6', '9', '8', '9', '9', '6', '4', '6', '8', '4', '7', '4', '5', '4', '7', '9', '3', '3', '2', '7', '7', '4', '3', '9', '9'])
noncomputable def fragment0303943Acc00800 : List (String × SourceJson) := (fragment0303943Field007Key00, fragment0303943Field007Value00) :: fragment0303943Acc00700
noncomputable def fragment0303943Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '9', '8', '7', '5', '0', '6', '0', '7', '8', '7', '0', '1', '1', '8', '8', '2', '0', '0', '5', '5', '9', '8', '4', '6', '0', '2', '2', '9', '9', '1', '4', '2', '0', '5', '9', '8', '6', '6', '5', '4', '6', '3', '6', '7', '7', '9', '6', '5', '5', '3', '3', '2', '4', '7', '9', '6', '1', '0', '5', '6', '7', '3', '8', '2', '9', '2', '2', '5', '8', '3', '7', '8', '3', '4', '9', '8', '5', '4', '2', '6', '5', '9', '1', '1', '6', '8', '1', '6', '2', '6', '3', '5', '7', '5', '9', '2', '4', '2', '6', '8', '1', '5', '3', '0', '2', '8', '0', '0', '7', '0', '5', '5', '7', '8', '2', '9', '2', '8', '9', '6', '4', '3', '7', '6', '0', '2', '9', '5', '5', '5', '8', '1', '2', '9', '6', '6', '3', '0', '8', '8', '0', '0', '9', '9', '8', '3', '5', '1', '2', '4', '7', '0', '5', '0', '2', '7', '5', '6', '8', '0', '2', '5', '9', '3', '0', '3', '9', '2', '1', '5', '6', '4', '8', '9', '7', '9', '2', '0', '4', '8', '5', '2', '7', '6', '7', '1', '6', '1', '6', '2', '4', '2', '3', '1', '1', '2', '9', '1', '7', '6', '5', '6', '6', '3', '6', '5', '0', '0', '0', '7', '1', '0', '7', '9', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '9', '9', '8', '2', '4', '5', '9', '6', '7', '7', '1', '2', '4', '8', '9', '1', '9', '0', '0', '9', '2', '1', '8', '5', '0', '1', '0', '1', '6', '0', '8', '5', '9', '1', '7', '1', '9', '9', '5', '7', '1', '6', '0', '7', '3', '3', '3', '9', '3', '5', '8', '7', '6', '2', '1', '7', '9', '1', '8', '6', '9', '4', '4', '3', '5', '5', '3', '8', '1', '5', '8', '4', '9', '3', '1', '2', '6', '5', '8', '5', '7', '8', '2', '7', '6', '1', '7', '3', '9', '0', '2', '7', '6', '9', '6', '4', '8', '2', '0', '6', '7', '8', '5', '1', '7', '9', '3', '0', '9', '7', '3', '4', '1', '3', '5', '9', '8', '8', '8', '1', '9', '5', '5', '9', '8', '1', '0', '1', '6', '6', '6', '4', '6', '3', '0', '8', '1', '3', '8', '0', '8', '2', '7', '1', '3', '6', '0', '3', '5', '4', '5', '7', '9', '5', '4', '9', '3', '4', '0', '2', '2', '3', '8', '3', '2', '6', '3', '9', '7', '1', '9', '8', '4', '5', '8', '3', '0', '2', '5', '6', '4', '7', '8', '9', '5', '2', '3', '4', '0', '6', '4', '2', '2', '0', '2', '7', '0', '0', '6', '6', '3', '0', '9', '0', '6', '1', '5', '6', '5', '6', '5', '6', '4', '9', '6', '3', '5', '9', '4', '5', '0', '9', '3', '7', '2', '2', '6', '5', '3', '7', '6', '9', '8', '9', '9', '6', '4', '6', '8', '4', '7', '4', '5', '4', '7', '9', '3', '3', '2', '7', '7', '4', '3', '9', '9', '"', ',']

theorem object_fragment0303943_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 503) (SourceJson.white (fragment0303943Field007Chars00 ++ tail)) fragment0303943Acc00700 =
      SourceJson.object (fuel + 502) (SourceJson.white tail) fragment0303943Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_007"
  err.flush

noncomputable def fragment0303943Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0303943Field008Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '7', '0', '3', '7', '6', '9', '9', '2', '7', '0', '8', '6', '7'])
noncomputable def fragment0303943Acc00900 : List (String × SourceJson) := (fragment0303943Field008Key00, fragment0303943Field008Value00) :: fragment0303943Acc00800
noncomputable def fragment0303943Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '4', '7', '0', '3', '7', '6', '9', '9', '2', '7', '0', '8', '6', '7', '"', ',']

theorem object_fragment0303943_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 502) (SourceJson.white (fragment0303943Field008Chars00 ++ tail)) fragment0303943Acc00800 =
      SourceJson.object (fuel + 501) (SourceJson.white tail) fragment0303943Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_008"
  err.flush

noncomputable def fragment0303943Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0303943Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '7', '1', '1', '9', '6', '9', '4', '7', '1', '4', '4', '0', '5', '4'])
noncomputable def fragment0303943Acc01000 : List (String × SourceJson) := (fragment0303943Field009Key00, fragment0303943Field009Value00) :: fragment0303943Acc00900
noncomputable def fragment0303943Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '8', '7', '1', '1', '9', '6', '9', '4', '7', '1', '4', '4', '0', '5', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0303943_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 501) (SourceJson.white (fragment0303943Field009Chars00 ++ tail)) fragment0303943Acc00900 =
      .ok (.obj (fragment0303943Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0303943_object_field_009"
  err.flush

noncomputable def fragment0303943Chars : List Char := '{' :: (fragment0303943Field000Chars00 ++ fragment0303943Field001Chars00 ++ fragment0303943Field002Chars00 ++ fragment0303943Field003Chars00 ++ fragment0303943Field004Chars00 ++ fragment0303943Field005Chars00 ++ fragment0303943Field006Chars00 ++ fragment0303943Field007Chars00 ++ fragment0303943Field008Chars00 ++ fragment0303943Field009Chars00)
noncomputable def fragment0303943Value : SourceJson := .obj (fragment0303943Acc01000.reverse)

theorem value_fragment0303943 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 511) (fragment0303943Chars ++ tail) =
      .ok (fragment0303943Value, tail) := by
  have hinput : fragment0303943Chars ++ tail = '{' :: (fragment0303943Field000Chars00 ++ (fragment0303943Field001Chars00 ++ (fragment0303943Field002Chars00 ++ (fragment0303943Field003Chars00 ++ (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0303943Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 511) (fragment0303943Chars ++ tail) =
        SourceJson.value (fuel + 511) ('{' :: (fragment0303943Field000Chars00 ++ (fragment0303943Field001Chars00 ++ (fragment0303943Field002Chars00 ++ (fragment0303943Field003Chars00 ++ (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 511)) hinput
    _ = SourceJson.object (fuel + 510) (SourceJson.white (fragment0303943Field000Chars00 ++ (fragment0303943Field001Chars00 ++ (fragment0303943Field002Chars00 ++ (fragment0303943Field003Chars00 ++ (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))))))))))) fragment0303943Acc00000 := by rfl
    _ = SourceJson.object (fuel + 509) (SourceJson.white (fragment0303943Field001Chars00 ++ (fragment0303943Field002Chars00 ++ (fragment0303943Field003Chars00 ++ (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail))))))))))) fragment0303943Acc00100 := object_fragment0303943_field_000 fuel (fragment0303943Field001Chars00 ++ (fragment0303943Field002Chars00 ++ (fragment0303943Field003Chars00 ++ (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 508) (SourceJson.white (fragment0303943Field002Chars00 ++ (fragment0303943Field003Chars00 ++ (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))))))))) fragment0303943Acc00200 := object_fragment0303943_field_001 fuel (fragment0303943Field002Chars00 ++ (fragment0303943Field003Chars00 ++ (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 507) (SourceJson.white (fragment0303943Field003Chars00 ++ (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail))))))))) fragment0303943Acc00300 := object_fragment0303943_field_002 fuel (fragment0303943Field003Chars00 ++ (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 506) (SourceJson.white (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))))))) fragment0303943Acc00400 := object_fragment0303943_field_003 fuel (fragment0303943Field004Chars00 ++ (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 505) (SourceJson.white (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail))))))) fragment0303943Acc00500 := object_fragment0303943_field_004 fuel (fragment0303943Field005Chars00 ++ (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 504) (SourceJson.white (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))))) fragment0303943Acc00600 := object_fragment0303943_field_005 fuel (fragment0303943Field006Chars00 ++ (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 503) (SourceJson.white (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail))))) fragment0303943Acc00700 := object_fragment0303943_field_006 fuel (fragment0303943Field007Chars00 ++ (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 502) (SourceJson.white (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))) fragment0303943Acc00800 := object_fragment0303943_field_007 fuel (fragment0303943Field008Chars00 ++ (fragment0303943Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 501) (SourceJson.white (fragment0303943Field009Chars00 ++ (tail))) fragment0303943Acc00900 := object_fragment0303943_field_008 fuel (fragment0303943Field009Chars00 ++ (tail))
    _ = .ok (fragment0303943Value, tail) := object_fragment0303943_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_before_reader"
  err.flush

noncomputable def chunk0045LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0045SuffixChars00 : List Char := [',']
noncomputable def chunk0045Chars00 : List Char := chunk0045LeadChars00 ++ fragment0302247Chars ++ chunk0045SuffixChars00
noncomputable def chunk0045Push00 (acc : List SourceJson) : List SourceJson := fragment0302247Value :: acc

noncomputable def chunk0045AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0045_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 559)
      (SourceJson.white (chunk0045LeadChars00 ++ (fragment0302247Chars ++ rest))) acc =
      (SourceJson.value (fuel + 558) (fragment0302247Chars ++ rest)).bind
        (chunk0045AfterValue00 (fuel + 558) acc) := by rfl

theorem array_chunk0045 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 559) (SourceJson.white (chunk0045Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 558) (SourceJson.white tail) (chunk0045Push00 acc) := by
  have hinput : chunk0045Chars00 ++ tail = chunk0045LeadChars00 ++ (fragment0302247Chars ++ (chunk0045SuffixChars00 ++ tail)) := by
    simp only [chunk0045Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 559) (SourceJson.white (chunk0045Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 559)
          (SourceJson.white (chunk0045LeadChars00 ++ (fragment0302247Chars ++ (chunk0045SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 559) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 558) (fragment0302247Chars ++ (chunk0045SuffixChars00 ++ tail))).bind
        (chunk0045AfterValue00 (fuel + 558) acc) := array_chunk0045_head fuel (chunk0045SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0302247Value, chunk0045SuffixChars00 ++ tail)).bind
        (chunk0045AfterValue00 (fuel + 558) acc) :=
      congrArg (fun result => result.bind (chunk0045AfterValue00 (fuel + 558) acc))
        (value_fragment0302247 (fuel + 279) (chunk0045SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 558) (SourceJson.white tail) (chunk0045Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_before_reader"
  err.flush

noncomputable def chunk0046LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0046SuffixChars00 : List Char := [',']
noncomputable def chunk0046Chars00 : List Char := chunk0046LeadChars00 ++ fragment0303943Chars ++ chunk0046SuffixChars00
noncomputable def chunk0046Push00 (acc : List SourceJson) : List SourceJson := fragment0303943Value :: acc

noncomputable def chunk0046AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0046_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 558)
      (SourceJson.white (chunk0046LeadChars00 ++ (fragment0303943Chars ++ rest))) acc =
      (SourceJson.value (fuel + 557) (fragment0303943Chars ++ rest)).bind
        (chunk0046AfterValue00 (fuel + 557) acc) := by rfl

theorem array_chunk0046 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 558) (SourceJson.white (chunk0046Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 557) (SourceJson.white tail) (chunk0046Push00 acc) := by
  have hinput : chunk0046Chars00 ++ tail = chunk0046LeadChars00 ++ (fragment0303943Chars ++ (chunk0046SuffixChars00 ++ tail)) := by
    simp only [chunk0046Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 558) (SourceJson.white (chunk0046Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 558)
          (SourceJson.white (chunk0046LeadChars00 ++ (fragment0303943Chars ++ (chunk0046SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 558) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 557) (fragment0303943Chars ++ (chunk0046SuffixChars00 ++ tail))).bind
        (chunk0046AfterValue00 (fuel + 557) acc) := array_chunk0046_head fuel (chunk0046SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0303943Value, chunk0046SuffixChars00 ++ tail)).bind
        (chunk0046AfterValue00 (fuel + 557) acc) :=
      congrArg (fun result => result.bind (chunk0046AfterValue00 (fuel + 557) acc))
        (value_fragment0303943 (fuel + 46) (chunk0046SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 557) (SourceJson.white tail) (chunk0046Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0045Chars00 ++ chunk0046Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0046Push00 (chunk0045Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 559) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 557) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0045Chars00 ++ (chunk0046Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 559) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 559) (SourceJson.white (chunk0045Chars00 ++ (chunk0046Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 559) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 558) (SourceJson.white (chunk0046Chars00 ++ (tail))) (chunk0045Push00 (acc)) := array_chunk0045 fuel (chunk0046Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 557) (SourceJson.white tail) (blockPush acc) := array_chunk0046 fuel (tail) (chunk0045Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 302241).take 3861 = blockChars := by rfl

theorem block_original_split : sourceRest 302241 = blockChars ++ sourceRest 306102 := by
  calc
    sourceRest 302241 = (sourceRest 302241).take 3861 ++ (sourceRest 302241).drop 3861 :=
      (List.take_append_drop 3861 (sourceRest 302241)).symm
    _ = blockChars ++ (sourceRest 302241).drop 3861 :=
      congrArg (fun part => part ++ (sourceRest 302241).drop 3861) block_original_prefix
    _ = blockChars ++ sourceRest 306102 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 302241 3861)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 559) (SourceJson.white (sourceRest 302241)) acc =
      SourceJson.array (fuel + 557) (SourceJson.white (sourceRest 306102)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 559) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 306102) acc)

#print axioms object_fragment0302247_field_000
#print axioms object_fragment0302247_field_001
#print axioms object_fragment0302247_field_002
#print axioms object_fragment0302247_field_003
#print axioms object_fragment0302247_field_004
#print axioms object_fragment0302247_field_005
#print axioms object_fragment0302247_field_006
#print axioms object_fragment0302247_field_007
#print axioms object_fragment0302247_field_008
#print axioms object_fragment0302247_field_009
#print axioms value_fragment0302247
#print axioms object_fragment0303943_field_000
#print axioms object_fragment0303943_field_001
#print axioms object_fragment0303943_field_002
#print axioms object_fragment0303943_field_003
#print axioms object_fragment0303943_field_004
#print axioms object_fragment0303943_field_005
#print axioms object_fragment0303943_field_006
#print axioms object_fragment0303943_field_007
#print axioms object_fragment0303943_field_008
#print axioms object_fragment0303943_field_009
#print axioms value_fragment0303943
#print axioms array_chunk0045_head
#print axioms array_chunk0045
#print axioms array_chunk0046_head
#print axioms array_chunk0046
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock023

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
