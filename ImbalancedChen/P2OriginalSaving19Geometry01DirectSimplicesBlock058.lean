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

namespace SimplicesBlock058

noncomputable def fragment0420538Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0420538Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0420538Field000Value00 : SourceJson := .number (String.ofList ['1', '1', '4'])
noncomputable def fragment0420538Acc00100 : List (String × SourceJson) := (fragment0420538Field000Key00, fragment0420538Field000Value00) :: fragment0420538Acc00000
noncomputable def fragment0420538Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '4', ',']

theorem object_fragment0420538_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 274) (SourceJson.white (fragment0420538Field000Chars00 ++ tail)) fragment0420538Acc00000 =
      SourceJson.object (fuel + 273) (SourceJson.white tail) fragment0420538Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_000"
  err.flush

noncomputable def fragment0420538Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0420538Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5'])]
noncomputable def fragment0420538Acc00200 : List (String × SourceJson) := (fragment0420538Field001Key00, fragment0420538Field001Value00) :: fragment0420538Acc00100
noncomputable def fragment0420538Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0420538_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 273) (SourceJson.white (fragment0420538Field001Chars00 ++ tail)) fragment0420538Acc00100 =
      SourceJson.object (fuel + 272) (SourceJson.white tail) fragment0420538Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_001"
  err.flush

noncomputable def fragment0420538Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0420538Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '1', '7', '2', '8', '9', '2', '3', '6', '5', '2', '4', '6', '6', '0', '6', '3', '9', '5', '9', '9', '8', '9', '8', '1', '7', '9', '3', '5', '1', '3', '6', '2', '8', '8', '2', '2', '9', '5', '9', '/', '9', '4', '3', '9', '6', '0', '2', '9', '4', '7', '2', '8', '5', '1', '8', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0420538Acc00300 : List (String × SourceJson) := (fragment0420538Field002Key00, fragment0420538Field002Value00) :: fragment0420538Acc00200
noncomputable def fragment0420538Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '3', '1', '7', '2', '8', '9', '2', '3', '6', '5', '2', '4', '6', '6', '0', '6', '3', '9', '5', '9', '9', '8', '9', '8', '1', '7', '9', '3', '5', '1', '3', '6', '2', '8', '8', '2', '2', '9', '5', '9', '/', '9', '4', '3', '9', '6', '0', '2', '9', '4', '7', '2', '8', '5', '1', '8', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0420538_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 272) (SourceJson.white (fragment0420538Field002Chars00 ++ tail)) fragment0420538Acc00200 =
      SourceJson.object (fuel + 271) (SourceJson.white tail) fragment0420538Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_002"
  err.flush

noncomputable def fragment0420538Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0420538Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0420538Acc00400 : List (String × SourceJson) := (fragment0420538Field003Key00, fragment0420538Field003Value00) :: fragment0420538Acc00300
noncomputable def fragment0420538Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0420538_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 271) (SourceJson.white (fragment0420538Field003Chars00 ++ tail)) fragment0420538Acc00300 =
      SourceJson.object (fuel + 270) (SourceJson.white tail) fragment0420538Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_003"
  err.flush

noncomputable def fragment0420538Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0420538Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0420538Acc00500 : List (String × SourceJson) := (fragment0420538Field004Key00, fragment0420538Field004Value00) :: fragment0420538Acc00400
noncomputable def fragment0420538Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0420538_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 270) (SourceJson.white (fragment0420538Field004Chars00 ++ tail)) fragment0420538Acc00400 =
      SourceJson.object (fuel + 269) (SourceJson.white tail) fragment0420538Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_004"
  err.flush

noncomputable def fragment0420538Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0420538Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '9', '7', '8', '4', '9', '2', '9', '4', '4', '2', '9', '9', '1', '/', '1', '2', '2', '2', '6', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '0', '1', '3', '2', '3', '7', '0', '9', '1', '3', '7', '1', '/', '1', '2', '2', '2', '6', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '6', '8', '3', '3', '7', '5', '0', '2', '5', '2', '7', '8', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '4', '4', '6', '5', '1', '1', '9', '8', '4', '5', '1', '9', '7', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '6', '8', '2', '9', '2', '1', '9', '9', '3', '7', '5', '6', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '6', '8', '7', '9', '0', '9', '0', '2', '9', '1', '5', '4', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '9', '4', '7', '5', '6', '6', '6', '6', '9', '/', '1', '5', '4', '4', '4', '5', '7', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '8', '8', '3', '3', '6', '6', '3', '0', '7', '9', '2', '3', '/', '7', '3', '3', '6', '1', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '3', '4', '5', '9', '9', '7', '0', '7', '4', '4', '8', '9', '/', '3', '6', '6', '8', '0', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '3', '4', '5', '0', '1', '8', '9', '1', '8', '0', '0', '9', '/', '3', '6', '6', '8', '0', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0420538Acc00600 : List (String × SourceJson) := (fragment0420538Field005Key00, fragment0420538Field005Value00) :: fragment0420538Acc00500
noncomputable def fragment0420538Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '7', '8', '4', '9', '2', '9', '4', '4', '2', '9', '9', '1', '/', '1', '2', '2', '2', '6', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '0', '1', '3', '2', '3', '7', '0', '9', '1', '3', '7', '1', '/', '1', '2', '2', '2', '6', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '6', '8', '3', '3', '7', '5', '0', '2', '5', '2', '7', '8', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '4', '4', '6', '5', '1', '1', '9', '8', '4', '5', '1', '9', '7', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '6', '8', '2', '9', '2', '1', '9', '9', '3', '7', '5', '6', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '6', '8', '7', '9', '0', '9', '0', '2', '9', '1', '5', '4', '3', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '9', '4', '7', '5', '6', '6', '6', '6', '9', '/', '1', '5', '4', '4', '4', '5', '7', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '8', '8', '3', '3', '6', '6', '3', '0', '7', '9', '2', '3', '/', '7', '3', '3', '6', '1', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '3', '4', '5', '9', '9', '7', '0', '7', '4', '4', '8', '9', '/', '3', '6', '6', '8', '0', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '3', '4', '5', '0', '1', '8', '9', '1', '8', '0', '0', '9', '/', '3', '6', '6', '8', '0', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0420538_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 269) (SourceJson.white (fragment0420538Field005Chars00 ++ tail)) fragment0420538Acc00500 =
      SourceJson.object (fuel + 268) (SourceJson.white tail) fragment0420538Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_005"
  err.flush

noncomputable def fragment0420538Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0420538Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '9', '2', '6', '0', '4', '7', '8', '8', '2', '5', '2', '0', '1', '4', '1', '3', '6', '7', '5', '8', '9', '5', '5', '1', '9', '8', '1', '5', '6', '3', '4', '3', '6', '1', '3', '7', '2', '1', '5', '2', '9', '0', '0', '0', '/', '1', '3', '0', '7', '9', '4', '1', '3', '8', '6', '8', '1', '3', '6', '3', '7', '9', '9', '2', '1', '8', '9', '6', '0', '5', '4', '8', '4', '3', '1', '9', '6', '6', '7', '9', '7', '8', '1', '2', '8', '9', '9', '2', '6', '5', '7', '4', '8', '7', '7', '3', '0', '9', '9', '0', '2', '9', '6', '4', '8', '6', '6', '6', '7', '3'])
noncomputable def fragment0420538Acc00700 : List (String × SourceJson) := (fragment0420538Field006Key00, fragment0420538Field006Value00) :: fragment0420538Acc00600
noncomputable def fragment0420538Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '9', '2', '6', '0', '4', '7', '8', '8', '2', '5', '2', '0', '1', '4', '1', '3', '6', '7', '5', '8', '9', '5', '5', '1', '9', '8', '1', '5', '6', '3', '4', '3', '6', '1', '3', '7', '2', '1', '5', '2', '9', '0', '0', '0', '/', '1', '3', '0', '7', '9', '4', '1', '3', '8', '6', '8', '1', '3', '6', '3', '7', '9', '9', '2', '1', '8', '9', '6', '0', '5', '4', '8', '4', '3', '1', '9', '6', '6', '7', '9', '7', '8', '1', '2', '8', '9', '9', '2', '6', '5', '7', '4', '8', '7', '7', '3', '0', '9', '9', '0', '2', '9', '6', '4', '8', '6', '6', '6', '7', '3', '"', ',']

theorem object_fragment0420538_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 268) (SourceJson.white (fragment0420538Field006Chars00 ++ tail)) fragment0420538Acc00600 =
      SourceJson.object (fuel + 267) (SourceJson.white tail) fragment0420538Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_006"
  err.flush

noncomputable def fragment0420538Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0420538Field007Value00 : SourceJson := .str (String.ofList ['7', '5', '7', '8', '3', '8', '0', '5', '9', '7', '9', '3', '6', '8', '3', '4', '7', '0', '3', '2', '3', '7', '3', '4', '9', '6', '6', '3', '3', '1', '9', '6', '9', '2', '1', '0', '5', '0', '9', '5', '1', '3', '4', '5', '0', '4', '4', '7', '7', '6', '2', '9', '3', '7', '2', '5', '3', '4', '1', '2', '8', '0', '4', '1', '7', '3', '2', '3', '8', '0', '0', '5', '5', '5', '7', '9', '3', '4', '0', '6', '2', '3', '6', '6', '4', '9', '1', '2', '6', '5', '3', '6', '8', '9', '0', '6', '9', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '4', '9', '4', '1', '2', '3', '5', '1', '3', '1', '4', '6', '0', '0', '2', '1', '4', '7', '5', '9', '3', '5', '9', '1', '6', '4', '7', '5', '6', '0', '3', '2', '2', '7', '1', '5', '9', '5', '6', '5', '5', '2', '9', '3', '4', '3', '2', '3', '1', '1', '5', '2', '6', '1', '8', '7', '4', '5', '1', '0', '1', '1', '5', '7', '0', '1', '6', '6', '8', '0', '0', '1', '6', '2', '3', '0', '5', '2', '6', '4', '8', '2', '7', '0', '3', '4', '6', '0', '3', '7', '5', '5', '3', '5', '4', '9', '3', '5', '4', '7', '0', '3', '3', '1', '3', '4', '4', '0', '8', '9', '1', '6', '8', '5', '8', '7', '5', '3', '2', '7', '2', '8', '7', '6', '0', '0', '9', '1', '1', '4', '2', '0', '8', '4', '4', '7', '0', '7', '7'])
noncomputable def fragment0420538Acc00800 : List (String × SourceJson) := (fragment0420538Field007Key00, fragment0420538Field007Value00) :: fragment0420538Acc00700
noncomputable def fragment0420538Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '5', '7', '8', '3', '8', '0', '5', '9', '7', '9', '3', '6', '8', '3', '4', '7', '0', '3', '2', '3', '7', '3', '4', '9', '6', '6', '3', '3', '1', '9', '6', '9', '2', '1', '0', '5', '0', '9', '5', '1', '3', '4', '5', '0', '4', '4', '7', '7', '6', '2', '9', '3', '7', '2', '5', '3', '4', '1', '2', '8', '0', '4', '1', '7', '3', '2', '3', '8', '0', '0', '5', '5', '5', '7', '9', '3', '4', '0', '6', '2', '3', '6', '6', '4', '9', '1', '2', '6', '5', '3', '6', '8', '9', '0', '6', '9', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '4', '9', '4', '1', '2', '3', '5', '1', '3', '1', '4', '6', '0', '0', '2', '1', '4', '7', '5', '9', '3', '5', '9', '1', '6', '4', '7', '5', '6', '0', '3', '2', '2', '7', '1', '5', '9', '5', '6', '5', '5', '2', '9', '3', '4', '3', '2', '3', '1', '1', '5', '2', '6', '1', '8', '7', '4', '5', '1', '0', '1', '1', '5', '7', '0', '1', '6', '6', '8', '0', '0', '1', '6', '2', '3', '0', '5', '2', '6', '4', '8', '2', '7', '0', '3', '4', '6', '0', '3', '7', '5', '5', '3', '5', '4', '9', '3', '5', '4', '7', '0', '3', '3', '1', '3', '4', '4', '0', '8', '9', '1', '6', '8', '5', '8', '7', '5', '3', '2', '7', '2', '8', '7', '6', '0', '0', '9', '1', '1', '4', '2', '0', '8', '4', '4', '7', '0', '7', '7', '"', ',']

theorem object_fragment0420538_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 267) (SourceJson.white (fragment0420538Field007Chars00 ++ tail)) fragment0420538Acc00700 =
      SourceJson.object (fuel + 266) (SourceJson.white tail) fragment0420538Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_007"
  err.flush

noncomputable def fragment0420538Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0420538Field008Value00 : SourceJson := .str (String.ofList ['9', '6', '4', '7', '1', '5', '6', '3', '8', '3'])
noncomputable def fragment0420538Acc00900 : List (String × SourceJson) := (fragment0420538Field008Key00, fragment0420538Field008Value00) :: fragment0420538Acc00800
noncomputable def fragment0420538Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '6', '4', '7', '1', '5', '6', '3', '8', '3', '"', ',']

theorem object_fragment0420538_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0420538Field008Chars00 ++ tail)) fragment0420538Acc00800 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0420538Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_008"
  err.flush

noncomputable def fragment0420538Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0420538Field009Value00 : SourceJson := .str (String.ofList ['5', '2', '2', '3', '7', '2', '2', '9', '6', '5', '2'])
noncomputable def fragment0420538Acc01000 : List (String × SourceJson) := (fragment0420538Field009Key00, fragment0420538Field009Value00) :: fragment0420538Acc00900
noncomputable def fragment0420538Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '2', '2', '3', '7', '2', '2', '9', '6', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0420538_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0420538Field009Chars00 ++ tail)) fragment0420538Acc00900 =
      .ok (.obj (fragment0420538Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0420538_object_field_009"
  err.flush

noncomputable def fragment0420538Chars : List Char := '{' :: (fragment0420538Field000Chars00 ++ fragment0420538Field001Chars00 ++ fragment0420538Field002Chars00 ++ fragment0420538Field003Chars00 ++ fragment0420538Field004Chars00 ++ fragment0420538Field005Chars00 ++ fragment0420538Field006Chars00 ++ fragment0420538Field007Chars00 ++ fragment0420538Field008Chars00 ++ fragment0420538Field009Chars00)
noncomputable def fragment0420538Value : SourceJson := .obj (fragment0420538Acc01000.reverse)

theorem value_fragment0420538 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 275) (fragment0420538Chars ++ tail) =
      .ok (fragment0420538Value, tail) := by
  have hinput : fragment0420538Chars ++ tail = '{' :: (fragment0420538Field000Chars00 ++ (fragment0420538Field001Chars00 ++ (fragment0420538Field002Chars00 ++ (fragment0420538Field003Chars00 ++ (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0420538Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 275) (fragment0420538Chars ++ tail) =
        SourceJson.value (fuel + 275) ('{' :: (fragment0420538Field000Chars00 ++ (fragment0420538Field001Chars00 ++ (fragment0420538Field002Chars00 ++ (fragment0420538Field003Chars00 ++ (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 275)) hinput
    _ = SourceJson.object (fuel + 274) (SourceJson.white (fragment0420538Field000Chars00 ++ (fragment0420538Field001Chars00 ++ (fragment0420538Field002Chars00 ++ (fragment0420538Field003Chars00 ++ (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))))))))))) fragment0420538Acc00000 := by rfl
    _ = SourceJson.object (fuel + 273) (SourceJson.white (fragment0420538Field001Chars00 ++ (fragment0420538Field002Chars00 ++ (fragment0420538Field003Chars00 ++ (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail))))))))))) fragment0420538Acc00100 := object_fragment0420538_field_000 fuel (fragment0420538Field001Chars00 ++ (fragment0420538Field002Chars00 ++ (fragment0420538Field003Chars00 ++ (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 272) (SourceJson.white (fragment0420538Field002Chars00 ++ (fragment0420538Field003Chars00 ++ (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))))))))) fragment0420538Acc00200 := object_fragment0420538_field_001 fuel (fragment0420538Field002Chars00 ++ (fragment0420538Field003Chars00 ++ (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 271) (SourceJson.white (fragment0420538Field003Chars00 ++ (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail))))))))) fragment0420538Acc00300 := object_fragment0420538_field_002 fuel (fragment0420538Field003Chars00 ++ (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 270) (SourceJson.white (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))))))) fragment0420538Acc00400 := object_fragment0420538_field_003 fuel (fragment0420538Field004Chars00 ++ (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 269) (SourceJson.white (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail))))))) fragment0420538Acc00500 := object_fragment0420538_field_004 fuel (fragment0420538Field005Chars00 ++ (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 268) (SourceJson.white (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))))) fragment0420538Acc00600 := object_fragment0420538_field_005 fuel (fragment0420538Field006Chars00 ++ (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 267) (SourceJson.white (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail))))) fragment0420538Acc00700 := object_fragment0420538_field_006 fuel (fragment0420538Field007Chars00 ++ (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))) fragment0420538Acc00800 := object_fragment0420538_field_007 fuel (fragment0420538Field008Chars00 ++ (fragment0420538Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0420538Field009Chars00 ++ (tail))) fragment0420538Acc00900 := object_fragment0420538_field_008 fuel (fragment0420538Field009Chars00 ++ (tail))
    _ = .ok (fragment0420538Value, tail) := object_fragment0420538_field_009 fuel (tail)

noncomputable def fragment0422225Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0422225Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0422225Field000Value00 : SourceJson := .number (String.ofList ['1', '1', '5'])
noncomputable def fragment0422225Acc00100 : List (String × SourceJson) := (fragment0422225Field000Key00, fragment0422225Field000Value00) :: fragment0422225Acc00000
noncomputable def fragment0422225Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '5', ',']

theorem object_fragment0422225_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 449) (SourceJson.white (fragment0422225Field000Chars00 ++ tail)) fragment0422225Acc00000 =
      SourceJson.object (fuel + 448) (SourceJson.white tail) fragment0422225Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_000"
  err.flush

noncomputable def fragment0422225Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0422225Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '5'])]
noncomputable def fragment0422225Acc00200 : List (String × SourceJson) := (fragment0422225Field001Key00, fragment0422225Field001Value00) :: fragment0422225Acc00100
noncomputable def fragment0422225Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0422225_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 448) (SourceJson.white (fragment0422225Field001Chars00 ++ tail)) fragment0422225Acc00100 =
      SourceJson.object (fuel + 447) (SourceJson.white tail) fragment0422225Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_001"
  err.flush

noncomputable def fragment0422225Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0422225Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '1', '4', '5', '9', '1', '2', '5', '1', '5', '2', '0', '3', '4', '5', '9', '9', '5', '9', '9', '9', '3', '9', '7', '9', '7', '3', '3', '8', '1', '7', '7', '2', '3', '6', '3', '1', '7', '2', '5', '1', '/', '1', '1', '1', '9', '6', '6', '2', '7', '7', '0', '9', '2', '0', '6', '5', '3', '8', '3', '8', '0', '9', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0422225Acc00300 : List (String × SourceJson) := (fragment0422225Field002Key00, fragment0422225Field002Value00) :: fragment0422225Acc00200
noncomputable def fragment0422225Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '4', '1', '4', '5', '9', '1', '2', '5', '1', '5', '2', '0', '3', '4', '5', '9', '9', '5', '9', '9', '9', '3', '9', '7', '9', '7', '3', '3', '8', '1', '7', '7', '2', '3', '6', '3', '1', '7', '2', '5', '1', '/', '1', '1', '1', '9', '6', '6', '2', '7', '7', '0', '9', '2', '0', '6', '5', '3', '8', '3', '8', '0', '9', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0422225_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 447) (SourceJson.white (fragment0422225Field002Chars00 ++ tail)) fragment0422225Acc00200 =
      SourceJson.object (fuel + 446) (SourceJson.white tail) fragment0422225Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_002"
  err.flush

noncomputable def fragment0422225Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0422225Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '2', '4', '9', '9', '7', '/', '4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0422225Acc00400 : List (String × SourceJson) := (fragment0422225Field003Key00, fragment0422225Field003Value00) :: fragment0422225Acc00300
noncomputable def fragment0422225Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '2', '4', '9', '9', '7', '/', '4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0422225_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 446) (SourceJson.white (fragment0422225Field003Chars00 ++ tail)) fragment0422225Acc00300 =
      SourceJson.object (fuel + 445) (SourceJson.white tail) fragment0422225Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_003"
  err.flush

noncomputable def fragment0422225Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0422225Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0422225Acc00500 : List (String × SourceJson) := (fragment0422225Field004Key00, fragment0422225Field004Value00) :: fragment0422225Acc00400
noncomputable def fragment0422225Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0422225_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 445) (SourceJson.white (fragment0422225Field004Chars00 ++ tail)) fragment0422225Acc00400 =
      SourceJson.object (fuel + 444) (SourceJson.white tail) fragment0422225Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_004"
  err.flush

noncomputable def fragment0422225Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0422225Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '3', '0', '3', '8', '6', '1', '8', '8', '8', '4', '2', '8', '1', '2', '9', '4', '4', '0', '3', '1', '3', '7', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '3', '4', '2', '7', '0', '5', '8', '1', '6', '1', '6', '4', '1', '9', '6', '7', '2', '6', '3', '2', '7', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '3', '5', '7', '2', '9', '1', '2', '1', '8', '4', '6', '2', '2', '4', '1', '9', '2', '3', '1', '7', '3', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '7', '1', '2', '5', '3', '8', '3', '2', '9', '8', '8', '4', '7', '5', '8', '1', '9', '1', '3', '5', '9', '/', '7', '4', '7', '9', '1', '3', '6', '0', '6', '3', '3', '9', '1', '1', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '0', '7', '2', '2', '8', '8', '4', '7', '5', '5', '9', '9', '1', '9', '0', '3', '3', '5', '9', '3', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '6', '7', '2', '5', '5', '3', '5', '6', '0', '8', '9', '7', '4', '3', '1', '6', '6', '8', '5', '7', '9', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '5', '0', '0', '1', '9', '3', '7', '2', '2', '8', '3', '7', '8', '5', '8', '9', '8', '3', '9', '/', '3', '1', '4', '9', '1', '0', '9', '9', '2', '1', '4', '2', '7', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '9', '9', '5', '5', '4', '7', '5', '3', '4', '2', '2', '2', '3', '0', '5', '8', '8', '7', '2', '5', '7', '/', '5', '9', '8', '3', '3', '0', '8', '8', '5', '0', '7', '1', '2', '9', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '3', '8', '9', '6', '0', '2', '0', '5', '0', '3', '2', '2', '3', '0', '1', '2', '1', '1', '3', '3', '3', '/', '2', '9', '9', '1', '6', '5', '4', '4', '2', '5', '3', '5', '6', '4', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '0', '5', '2', '2', '2', '5', '2', '3', '5', '9', '9', '5', '8', '1', '9', '8', '5', '4', '4', '2', '3', '/', '2', '9', '9', '1', '6', '5', '4', '4', '2', '5', '3', '5', '6', '4', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0422225Acc00600 : List (String × SourceJson) := (fragment0422225Field005Key00, fragment0422225Field005Value00) :: fragment0422225Acc00500
noncomputable def fragment0422225Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '0', '3', '8', '6', '1', '8', '8', '8', '4', '2', '8', '1', '2', '9', '4', '4', '0', '3', '1', '3', '7', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '3', '4', '2', '7', '0', '5', '8', '1', '6', '1', '6', '4', '1', '9', '6', '7', '2', '6', '3', '2', '7', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '3', '5', '7', '2', '9', '1', '2', '1', '8', '4', '6', '2', '2', '4', '1', '9', '2', '3', '1', '7', '3', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '7', '1', '2', '5', '3', '8', '3', '2', '9', '8', '8', '4', '7', '5', '8', '1', '9', '1', '3', '5', '9', '/', '7', '4', '7', '9', '1', '3', '6', '0', '6', '3', '3', '9', '1', '1', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '0', '7', '2', '2', '8', '8', '4', '7', '5', '5', '9', '9', '1', '9', '0', '3', '3', '5', '9', '3', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '6', '7', '2', '5', '5', '3', '5', '6', '0', '8', '9', '7', '4', '3', '1', '6', '6', '8', '5', '7', '9', '/', '9', '9', '7', '2', '1', '8', '1', '4', '1', '7', '8', '5', '4', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '5', '0', '0', '1', '9', '3', '7', '2', '2', '8', '3', '7', '8', '5', '8', '9', '8', '3', '9', '/', '3', '1', '4', '9', '1', '0', '9', '9', '2', '1', '4', '2', '7', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '9', '5', '5', '4', '7', '5', '3', '4', '2', '2', '2', '3', '0', '5', '8', '8', '7', '2', '5', '7', '/', '5', '9', '8', '3', '3', '0', '8', '8', '5', '0', '7', '1', '2', '9', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '3', '8', '9', '6', '0', '2', '0', '5', '0', '3', '2', '2', '3', '0', '1', '2', '1', '1', '3', '3', '3', '/', '2', '9', '9', '1', '6', '5', '4', '4', '2', '5', '3', '5', '6', '4', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '0', '5', '2', '2', '2', '5', '2', '3', '5', '9', '9', '5', '8', '1', '9', '8', '5', '4', '4', '2', '3', '/', '2', '9', '9', '1', '6', '5', '4', '4', '2', '5', '3', '5', '6', '4', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0422225_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 444) (SourceJson.white (fragment0422225Field005Chars00 ++ tail)) fragment0422225Acc00500 =
      SourceJson.object (fuel + 443) (SourceJson.white tail) fragment0422225Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_005"
  err.flush

noncomputable def fragment0422225Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0422225Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '1', '7', '8', '9', '5', '1', '7', '2', '3', '9', '4', '8', '3', '5', '8', '2', '0', '0', '0', '2', '3', '2', '0', '4', '8', '8', '5', '9', '0', '5', '6', '3', '5', '9', '4', '2', '1', '7', '3', '9', '5', '3', '4', '4', '7', '7', '5', '/', '4', '2', '0', '6', '7', '1', '9', '3', '1', '5', '5', '2', '1', '3', '6', '4', '6', '0', '3', '5', '0', '5', '2', '0', '2', '4', '7', '2', '2', '6', '7', '7', '6', '0', '6', '5', '6', '8', '0', '0', '7', '3', '1', '0', '9', '9', '7', '8', '7', '2', '9', '3', '1', '2', '7', '5', '7', '1', '3', '2', '0', '9', '5', '7'])
noncomputable def fragment0422225Acc00700 : List (String × SourceJson) := (fragment0422225Field006Key00, fragment0422225Field006Value00) :: fragment0422225Acc00600
noncomputable def fragment0422225Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '1', '7', '8', '9', '5', '1', '7', '2', '3', '9', '4', '8', '3', '5', '8', '2', '0', '0', '0', '2', '3', '2', '0', '4', '8', '8', '5', '9', '0', '5', '6', '3', '5', '9', '4', '2', '1', '7', '3', '9', '5', '3', '4', '4', '7', '7', '5', '/', '4', '2', '0', '6', '7', '1', '9', '3', '1', '5', '5', '2', '1', '3', '6', '4', '6', '0', '3', '5', '0', '5', '2', '0', '2', '4', '7', '2', '2', '6', '7', '7', '6', '0', '6', '5', '6', '8', '0', '0', '7', '3', '1', '0', '9', '9', '7', '8', '7', '2', '9', '3', '1', '2', '7', '5', '7', '1', '3', '2', '0', '9', '5', '7', '"', ',']

theorem object_fragment0422225_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 443) (SourceJson.white (fragment0422225Field006Chars00 ++ tail)) fragment0422225Acc00600 =
      SourceJson.object (fuel + 442) (SourceJson.white tail) fragment0422225Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_006"
  err.flush

noncomputable def fragment0422225Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0422225Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '3', '5', '2', '2', '5', '0', '9', '8', '7', '0', '5', '7', '3', '5', '0', '8', '8', '8', '3', '8', '1', '6', '2', '7', '0', '8', '3', '6', '4', '1', '3', '3', '7', '1', '7', '7', '0', '1', '7', '9', '4', '5', '3', '8', '2', '3', '6', '0', '1', '1', '0', '6', '6', '4', '8', '3', '5', '4', '4', '0', '7', '8', '7', '8', '4', '3', '8', '5', '4', '8', '8', '8', '0', '2', '7', '2', '2', '1', '3', '2', '8', '5', '2', '7', '0', '6', '7', '9', '6', '1', '3', '2', '3', '4', '6', '9', '9', '8', '7', '9', '8', '4', '8', '4', '2', '0', '9', '7', '6', '8', '9', '9', '9', '3', '4', '2', '5', '6', '4', '0', '5', '9', '0', '5', '4', '7', '4', '6', '8', '0', '1', '3', '8', '4', '4', '4', '4', '5', '8', '6', '5', '8', '6', '4', '3', '1', '0', '5', '8', '8', '7', '5', '7', '9', '1', '5', '1', '6', '6', '8', '8', '8', '5', '3', '9', '3', '2', '6', '2', '0', '0', '3', '0', '2', '8', '0', '8', '1', '5', '7', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '5', '3', '5', '3', '4', '1', '0', '4', '3', '8', '5', '6', '8', '8', '8', '7', '3', '2', '6', '9', '9', '9', '8', '9', '6', '6', '3', '0', '4', '5', '8', '5', '6', '9', '2', '8', '7', '7', '2', '8', '4', '0', '0', '9', '3', '7', '5', '0', '3', '6', '7', '0', '5', '2', '6', '4', '4', '9', '2', '6', '6', '2', '2', '5', '3', '1', '8', '8', '8', '3', '9', '1', '8', '1', '7', '2', '9', '1', '8', '7', '8', '5', '0', '0', '6', '8', '1', '4', '8', '3', '8', '9', '0', '7', '0', '6', '6', '9', '4', '4', '7', '3', '9', '7', '3', '4', '3', '6', '5', '9', '2', '0', '3', '4', '8', '2', '9', '0', '2', '1', '7', '7', '6', '4', '5', '7', '0', '6', '7', '9', '0', '9', '0', '9', '6', '0', '8', '7', '9', '4', '3', '7', '5', '0', '4', '4', '7', '0', '3', '4', '0', '8', '4', '1', '3', '7', '4', '8', '6', '2', '2', '9', '4', '7', '0', '0', '5', '5', '4', '9', '1', '0', '8', '0', '6', '5', '2', '4', '9', '3', '3', '9', '9', '5', '2', '1', '9', '6', '6', '3', '3', '8', '8', '9', '5', '4', '6', '5', '1', '7', '5', '6', '8', '1', '4', '3', '1', '1', '3', '4', '0', '1', '9', '0', '4', '1', '6', '1', '8', '7', '2', '5', '3', '1', '9'])
noncomputable def fragment0422225Acc00800 : List (String × SourceJson) := (fragment0422225Field007Key00, fragment0422225Field007Value00) :: fragment0422225Acc00700
noncomputable def fragment0422225Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '3', '3', '5', '2', '2', '5', '0', '9', '8', '7', '0', '5', '7', '3', '5', '0', '8', '8', '8', '3', '8', '1', '6', '2', '7', '0', '8', '3', '6', '4', '1', '3', '3', '7', '1', '7', '7', '0', '1', '7', '9', '4', '5', '3', '8', '2', '3', '6', '0', '1', '1', '0', '6', '6', '4', '8', '3', '5', '4', '4', '0', '7', '8', '7', '8', '4', '3', '8', '5', '4', '8', '8', '8', '0', '2', '7', '2', '2', '1', '3', '2', '8', '5', '2', '7', '0', '6', '7', '9', '6', '1', '3', '2', '3', '4', '6', '9', '9', '8', '7', '9', '8', '4', '8', '4', '2', '0', '9', '7', '6', '8', '9', '9', '9', '3', '4', '2', '5', '6', '4', '0', '5', '9', '0', '5', '4', '7', '4', '6', '8', '0', '1', '3', '8', '4', '4', '4', '4', '5', '8', '6', '5', '8', '6', '4', '3', '1', '0', '5', '8', '8', '7', '5', '7', '9', '1', '5', '1', '6', '6', '8', '8', '8', '5', '3', '9', '3', '2', '6', '2', '0', '0', '3', '0', '2', '8', '0', '8', '1', '5', '7', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '5', '3', '5', '3', '4', '1', '0', '4', '3', '8', '5', '6', '8', '8', '8', '7', '3', '2', '6', '9', '9', '9', '8', '9', '6', '6', '3', '0', '4', '5', '8', '5', '6', '9', '2', '8', '7', '7', '2', '8', '4', '0', '0', '9', '3', '7', '5', '0', '3', '6', '7', '0', '5', '2', '6', '4', '4', '9', '2', '6', '6', '2', '2', '5', '3', '1', '8', '8', '8', '3', '9', '1', '8', '1', '7', '2', '9', '1', '8', '7', '8', '5', '0', '0', '6', '8', '1', '4', '8', '3', '8', '9', '0', '7', '0', '6', '6', '9', '4', '4', '7', '3', '9', '7', '3', '4', '3', '6', '5', '9', '2', '0', '3', '4', '8', '2', '9', '0', '2', '1', '7', '7', '6', '4', '5', '7', '0', '6', '7', '9', '0', '9', '0', '9', '6', '0', '8', '7', '9', '4', '3', '7', '5', '0', '4', '4', '7', '0', '3', '4', '0', '8', '4', '1', '3', '7', '4', '8', '6', '2', '2', '9', '4', '7', '0', '0', '5', '5', '4', '9', '1', '0', '8', '0', '6', '5', '2', '4', '9', '3', '3', '9', '9', '5', '2', '1', '9', '6', '6', '3', '3', '8', '8', '9', '5', '4', '6', '5', '1', '7', '5', '6', '8', '1', '4', '3', '1', '1', '3', '4', '0', '1', '9', '0', '4', '1', '6', '1', '8', '7', '2', '5', '3', '1', '9', '"', ',']

theorem object_fragment0422225_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 442) (SourceJson.white (fragment0422225Field007Chars00 ++ tail)) fragment0422225Acc00700 =
      SourceJson.object (fuel + 441) (SourceJson.white tail) fragment0422225Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_007"
  err.flush

noncomputable def fragment0422225Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0422225Field008Value00 : SourceJson := .str (String.ofList ['2', '2', '9', '3', '7', '4', '9', '3', '4', '2', '5', '7', '7', '1'])
noncomputable def fragment0422225Acc00900 : List (String × SourceJson) := (fragment0422225Field008Key00, fragment0422225Field008Value00) :: fragment0422225Acc00800
noncomputable def fragment0422225Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '9', '3', '7', '4', '9', '3', '4', '2', '5', '7', '7', '1', '"', ',']

theorem object_fragment0422225_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 441) (SourceJson.white (fragment0422225Field008Chars00 ++ tail)) fragment0422225Acc00800 =
      SourceJson.object (fuel + 440) (SourceJson.white tail) fragment0422225Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_008"
  err.flush

noncomputable def fragment0422225Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0422225Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '5', '2', '9', '4', '2', '8', '6', '5', '9', '4', '4', '9', '3'])
noncomputable def fragment0422225Acc01000 : List (String × SourceJson) := (fragment0422225Field009Key00, fragment0422225Field009Value00) :: fragment0422225Acc00900
noncomputable def fragment0422225Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '2', '9', '4', '2', '8', '6', '5', '9', '4', '4', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0422225_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 440) (SourceJson.white (fragment0422225Field009Chars00 ++ tail)) fragment0422225Acc00900 =
      .ok (.obj (fragment0422225Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0422225_object_field_009"
  err.flush

noncomputable def fragment0422225Chars : List Char := '{' :: (fragment0422225Field000Chars00 ++ fragment0422225Field001Chars00 ++ fragment0422225Field002Chars00 ++ fragment0422225Field003Chars00 ++ fragment0422225Field004Chars00 ++ fragment0422225Field005Chars00 ++ fragment0422225Field006Chars00 ++ fragment0422225Field007Chars00 ++ fragment0422225Field008Chars00 ++ fragment0422225Field009Chars00)
noncomputable def fragment0422225Value : SourceJson := .obj (fragment0422225Acc01000.reverse)

theorem value_fragment0422225 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 450) (fragment0422225Chars ++ tail) =
      .ok (fragment0422225Value, tail) := by
  have hinput : fragment0422225Chars ++ tail = '{' :: (fragment0422225Field000Chars00 ++ (fragment0422225Field001Chars00 ++ (fragment0422225Field002Chars00 ++ (fragment0422225Field003Chars00 ++ (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0422225Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 450) (fragment0422225Chars ++ tail) =
        SourceJson.value (fuel + 450) ('{' :: (fragment0422225Field000Chars00 ++ (fragment0422225Field001Chars00 ++ (fragment0422225Field002Chars00 ++ (fragment0422225Field003Chars00 ++ (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 450)) hinput
    _ = SourceJson.object (fuel + 449) (SourceJson.white (fragment0422225Field000Chars00 ++ (fragment0422225Field001Chars00 ++ (fragment0422225Field002Chars00 ++ (fragment0422225Field003Chars00 ++ (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))))))))))) fragment0422225Acc00000 := by rfl
    _ = SourceJson.object (fuel + 448) (SourceJson.white (fragment0422225Field001Chars00 ++ (fragment0422225Field002Chars00 ++ (fragment0422225Field003Chars00 ++ (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail))))))))))) fragment0422225Acc00100 := object_fragment0422225_field_000 fuel (fragment0422225Field001Chars00 ++ (fragment0422225Field002Chars00 ++ (fragment0422225Field003Chars00 ++ (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 447) (SourceJson.white (fragment0422225Field002Chars00 ++ (fragment0422225Field003Chars00 ++ (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))))))))) fragment0422225Acc00200 := object_fragment0422225_field_001 fuel (fragment0422225Field002Chars00 ++ (fragment0422225Field003Chars00 ++ (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 446) (SourceJson.white (fragment0422225Field003Chars00 ++ (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail))))))))) fragment0422225Acc00300 := object_fragment0422225_field_002 fuel (fragment0422225Field003Chars00 ++ (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 445) (SourceJson.white (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))))))) fragment0422225Acc00400 := object_fragment0422225_field_003 fuel (fragment0422225Field004Chars00 ++ (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 444) (SourceJson.white (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail))))))) fragment0422225Acc00500 := object_fragment0422225_field_004 fuel (fragment0422225Field005Chars00 ++ (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 443) (SourceJson.white (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))))) fragment0422225Acc00600 := object_fragment0422225_field_005 fuel (fragment0422225Field006Chars00 ++ (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 442) (SourceJson.white (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail))))) fragment0422225Acc00700 := object_fragment0422225_field_006 fuel (fragment0422225Field007Chars00 ++ (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 441) (SourceJson.white (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))) fragment0422225Acc00800 := object_fragment0422225_field_007 fuel (fragment0422225Field008Chars00 ++ (fragment0422225Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 440) (SourceJson.white (fragment0422225Field009Chars00 ++ (tail))) fragment0422225Acc00900 := object_fragment0422225_field_008 fuel (fragment0422225Field009Chars00 ++ (tail))
    _ = .ok (fragment0422225Value, tail) := object_fragment0422225_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0114_before_reader"
  err.flush

noncomputable def chunk0114LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0114SuffixChars00 : List Char := [',']
noncomputable def chunk0114Chars00 : List Char := chunk0114LeadChars00 ++ fragment0420538Chars ++ chunk0114SuffixChars00
noncomputable def chunk0114Push00 (acc : List SourceJson) : List SourceJson := fragment0420538Value :: acc

noncomputable def chunk0114AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0114_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 490)
      (SourceJson.white (chunk0114LeadChars00 ++ (fragment0420538Chars ++ rest))) acc =
      (SourceJson.value (fuel + 489) (fragment0420538Chars ++ rest)).bind
        (chunk0114AfterValue00 (fuel + 489) acc) := by rfl

theorem array_chunk0114 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 490) (SourceJson.white (chunk0114Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 489) (SourceJson.white tail) (chunk0114Push00 acc) := by
  have hinput : chunk0114Chars00 ++ tail = chunk0114LeadChars00 ++ (fragment0420538Chars ++ (chunk0114SuffixChars00 ++ tail)) := by
    simp only [chunk0114Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 490) (SourceJson.white (chunk0114Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 490)
          (SourceJson.white (chunk0114LeadChars00 ++ (fragment0420538Chars ++ (chunk0114SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 490) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 489) (fragment0420538Chars ++ (chunk0114SuffixChars00 ++ tail))).bind
        (chunk0114AfterValue00 (fuel + 489) acc) := array_chunk0114_head fuel (chunk0114SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0420538Value, chunk0114SuffixChars00 ++ tail)).bind
        (chunk0114AfterValue00 (fuel + 489) acc) :=
      congrArg (fun result => result.bind (chunk0114AfterValue00 (fuel + 489) acc))
        (value_fragment0420538 (fuel + 214) (chunk0114SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 489) (SourceJson.white tail) (chunk0114Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0114_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0115_before_reader"
  err.flush

noncomputable def chunk0115LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0115SuffixChars00 : List Char := [',']
noncomputable def chunk0115Chars00 : List Char := chunk0115LeadChars00 ++ fragment0422225Chars ++ chunk0115SuffixChars00
noncomputable def chunk0115Push00 (acc : List SourceJson) : List SourceJson := fragment0422225Value :: acc

noncomputable def chunk0115AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0115_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 489)
      (SourceJson.white (chunk0115LeadChars00 ++ (fragment0422225Chars ++ rest))) acc =
      (SourceJson.value (fuel + 488) (fragment0422225Chars ++ rest)).bind
        (chunk0115AfterValue00 (fuel + 488) acc) := by rfl

theorem array_chunk0115 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 489) (SourceJson.white (chunk0115Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 488) (SourceJson.white tail) (chunk0115Push00 acc) := by
  have hinput : chunk0115Chars00 ++ tail = chunk0115LeadChars00 ++ (fragment0422225Chars ++ (chunk0115SuffixChars00 ++ tail)) := by
    simp only [chunk0115Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 489) (SourceJson.white (chunk0115Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 489)
          (SourceJson.white (chunk0115LeadChars00 ++ (fragment0422225Chars ++ (chunk0115SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 489) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 488) (fragment0422225Chars ++ (chunk0115SuffixChars00 ++ tail))).bind
        (chunk0115AfterValue00 (fuel + 488) acc) := array_chunk0115_head fuel (chunk0115SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0422225Value, chunk0115SuffixChars00 ++ tail)).bind
        (chunk0115AfterValue00 (fuel + 488) acc) :=
      congrArg (fun result => result.bind (chunk0115AfterValue00 (fuel + 488) acc))
        (value_fragment0422225 (fuel + 38) (chunk0115SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 488) (SourceJson.white tail) (chunk0115Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0115_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0114Chars00 ++ chunk0115Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0115Push00 (chunk0114Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 490) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 488) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0114Chars00 ++ (chunk0115Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 490) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 490) (SourceJson.white (chunk0114Chars00 ++ (chunk0115Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 490) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 489) (SourceJson.white (chunk0115Chars00 ++ (tail))) (chunk0114Push00 (acc)) := array_chunk0114 fuel (chunk0115Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 488) (SourceJson.white tail) (blockPush acc) := array_chunk0115 fuel (tail) (chunk0114Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 420532).take 3725 = blockChars := by rfl

theorem block_original_split : sourceRest 420532 = blockChars ++ sourceRest 424257 := by
  calc
    sourceRest 420532 = (sourceRest 420532).take 3725 ++ (sourceRest 420532).drop 3725 :=
      (List.take_append_drop 3725 (sourceRest 420532)).symm
    _ = blockChars ++ (sourceRest 420532).drop 3725 :=
      congrArg (fun part => part ++ (sourceRest 420532).drop 3725) block_original_prefix
    _ = blockChars ++ sourceRest 424257 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 420532 3725)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 490) (SourceJson.white (sourceRest 420532)) acc =
      SourceJson.array (fuel + 488) (SourceJson.white (sourceRest 424257)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 490) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 424257) acc)

#print axioms object_fragment0420538_field_000
#print axioms object_fragment0420538_field_001
#print axioms object_fragment0420538_field_002
#print axioms object_fragment0420538_field_003
#print axioms object_fragment0420538_field_004
#print axioms object_fragment0420538_field_005
#print axioms object_fragment0420538_field_006
#print axioms object_fragment0420538_field_007
#print axioms object_fragment0420538_field_008
#print axioms object_fragment0420538_field_009
#print axioms value_fragment0420538
#print axioms object_fragment0422225_field_000
#print axioms object_fragment0422225_field_001
#print axioms object_fragment0422225_field_002
#print axioms object_fragment0422225_field_003
#print axioms object_fragment0422225_field_004
#print axioms object_fragment0422225_field_005
#print axioms object_fragment0422225_field_006
#print axioms object_fragment0422225_field_007
#print axioms object_fragment0422225_field_008
#print axioms object_fragment0422225_field_009
#print axioms value_fragment0422225
#print axioms array_chunk0114_head
#print axioms array_chunk0114
#print axioms array_chunk0115_head
#print axioms array_chunk0115
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock058

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
