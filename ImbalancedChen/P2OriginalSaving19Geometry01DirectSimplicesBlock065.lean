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

namespace SimplicesBlock065

noncomputable def fragment0443905Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0443905Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0443905Field000Value00 : SourceJson := .number (String.ofList ['1', '2', '8'])
noncomputable def fragment0443905Acc00100 : List (String × SourceJson) := (fragment0443905Field000Key00, fragment0443905Field000Value00) :: fragment0443905Acc00000
noncomputable def fragment0443905Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '8', ',']

theorem object_fragment0443905_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0443905Field000Chars00 ++ tail)) fragment0443905Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0443905Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_000"
  err.flush

noncomputable def fragment0443905Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0443905Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1'])]
noncomputable def fragment0443905Acc00200 : List (String × SourceJson) := (fragment0443905Field001Key00, fragment0443905Field001Value00) :: fragment0443905Acc00100
noncomputable def fragment0443905Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0443905_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0443905Field001Chars00 ++ tail)) fragment0443905Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0443905Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_001"
  err.flush

noncomputable def fragment0443905Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0443905Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '9', '2', '1', '9', '7', '5', '2', '2', '0', '7', '9', '1', '6', '3', '9', '5', '4', '7', '9', '1', '5', '0', '2', '5', '1', '1', '9', '7', '8', '8', '3', '8', '8', '5', '0', '1', '2', '3', '5', '5', '1', '/', '2', '6', '2', '2', '1', '1', '1', '9', '2', '9', '8', '0', '1', '4', '4', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0443905Acc00300 : List (String × SourceJson) := (fragment0443905Field002Key00, fragment0443905Field002Value00) :: fragment0443905Acc00200
noncomputable def fragment0443905Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '9', '2', '1', '9', '7', '5', '2', '2', '0', '7', '9', '1', '6', '3', '9', '5', '4', '7', '9', '1', '5', '0', '2', '5', '1', '1', '9', '7', '8', '8', '3', '8', '8', '5', '0', '1', '2', '3', '5', '5', '1', '/', '2', '6', '2', '2', '1', '1', '1', '9', '2', '9', '8', '0', '1', '4', '4', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0443905_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0443905Field002Chars00 ++ tail)) fragment0443905Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0443905Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_002"
  err.flush

noncomputable def fragment0443905Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0443905Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0443905Acc00400 : List (String × SourceJson) := (fragment0443905Field003Key00, fragment0443905Field003Value00) :: fragment0443905Acc00300
noncomputable def fragment0443905Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0443905_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0443905Field003Chars00 ++ tail)) fragment0443905Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0443905Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_003"
  err.flush

noncomputable def fragment0443905Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0443905Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0443905Acc00500 : List (String × SourceJson) := (fragment0443905Field004Key00, fragment0443905Field004Value00) :: fragment0443905Acc00400
noncomputable def fragment0443905Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0443905_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0443905Field004Chars00 ++ tail)) fragment0443905Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0443905Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_004"
  err.flush

noncomputable def fragment0443905Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0443905Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '7', '1', '1', '5', '8', '1', '8', '1', '4', '2', '7', '9', '/', '1', '0', '4', '8', '0', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '3', '1', '1', '5', '1', '0', '4', '1', '2', '8', '3', '/', '1', '0', '4', '8', '0', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '7', '7', '8', '3', '8', '3', '1', '6', '9', '1', '4', '7', '/', '3', '1', '4', '4', '0', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '7', '9', '8', '1', '9', '5', '8', '5', '7', '/', '9', '0', '9', '7', '4', '3', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '8', '4', '8', '4', '6', '6', '3', '9', '9', '3', '4', '9', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '3', '5', '2', '7', '7', '5', '6', '6', '0', '5', '9', '7', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '4', '6', '6', '4', '1', '6', '2', '2', '4', '6', '7', '/', '8', '2', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '6', '4', '6', '7', '7', '3', '9', '8', '4', '3', '3', '3', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '7', '5', '8', '9', '5', '9', '0', '9', '1', '8', '3', '9', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '7', '5', '8', '8', '5', '4', '2', '8', '9', '3', '5', '9', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0443905Acc00600 : List (String × SourceJson) := (fragment0443905Field005Key00, fragment0443905Field005Value00) :: fragment0443905Acc00500
noncomputable def fragment0443905Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '1', '1', '5', '8', '1', '8', '1', '4', '2', '7', '9', '/', '1', '0', '4', '8', '0', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '3', '1', '1', '5', '1', '0', '4', '1', '2', '8', '3', '/', '1', '0', '4', '8', '0', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '7', '7', '8', '3', '8', '3', '1', '6', '9', '1', '4', '7', '/', '3', '1', '4', '4', '0', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '7', '9', '8', '1', '9', '5', '8', '5', '7', '/', '9', '0', '9', '7', '4', '3', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '8', '4', '8', '4', '6', '6', '3', '9', '9', '3', '4', '9', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '3', '5', '2', '7', '7', '5', '6', '6', '0', '5', '9', '7', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '4', '6', '6', '4', '1', '6', '2', '2', '4', '6', '7', '/', '8', '2', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '6', '4', '6', '7', '7', '3', '9', '8', '4', '3', '3', '3', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '7', '5', '8', '9', '5', '9', '0', '9', '1', '8', '3', '9', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '7', '5', '8', '8', '5', '4', '2', '8', '9', '3', '5', '9', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0443905_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0443905Field005Chars00 ++ tail)) fragment0443905Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0443905Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_005"
  err.flush

noncomputable def fragment0443905Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0443905Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '5', '5', '5', '3', '4', '6', '1', '8', '5', '0', '7', '1', '2', '5', '7', '6', '2', '3', '1', '1', '2', '5', '5', '6', '4', '1', '3', '9', '7', '6', '1', '4', '9', '9', '4', '9', '1', '4', '3', '4', '7', '3', '2', '2', '2', '0', '0', '/', '3', '2', '3', '5', '7', '6', '3', '1', '7', '2', '4', '2', '6', '6', '7', '0', '9', '4', '0', '3', '4', '3', '7', '9', '3', '0', '5', '4', '8', '7', '2', '0', '4', '3', '5', '4', '9', '0', '2', '0', '8', '1', '2', '4', '6', '3', '1', '5', '9', '9', '8', '8', '5', '1', '1', '9', '6', '8', '5', '7', '6', '4', '8', '0', '1', '7', '7'])
noncomputable def fragment0443905Acc00700 : List (String × SourceJson) := (fragment0443905Field006Key00, fragment0443905Field006Value00) :: fragment0443905Acc00600
noncomputable def fragment0443905Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '5', '5', '5', '3', '4', '6', '1', '8', '5', '0', '7', '1', '2', '5', '7', '6', '2', '3', '1', '1', '2', '5', '5', '6', '4', '1', '3', '9', '7', '6', '1', '4', '9', '9', '4', '9', '1', '4', '3', '4', '7', '3', '2', '2', '2', '0', '0', '/', '3', '2', '3', '5', '7', '6', '3', '1', '7', '2', '4', '2', '6', '6', '7', '0', '9', '4', '0', '3', '4', '3', '7', '9', '3', '0', '5', '4', '8', '7', '2', '0', '4', '3', '5', '4', '9', '0', '2', '0', '8', '1', '2', '4', '6', '3', '1', '5', '9', '9', '8', '8', '5', '1', '1', '9', '6', '8', '5', '7', '6', '4', '8', '0', '1', '7', '7', '"', ',']

theorem object_fragment0443905_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0443905Field006Chars00 ++ tail)) fragment0443905Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0443905Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_006"
  err.flush

noncomputable def fragment0443905Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0443905Field007Value00 : SourceJson := .str (String.ofList ['2', '8', '0', '1', '0', '2', '5', '3', '2', '8', '5', '7', '8', '6', '3', '0', '9', '8', '3', '9', '4', '3', '1', '9', '5', '4', '8', '0', '7', '8', '8', '7', '1', '2', '6', '0', '6', '4', '3', '9', '0', '6', '2', '3', '4', '8', '1', '6', '6', '9', '3', '6', '2', '1', '3', '4', '7', '5', '0', '5', '6', '7', '9', '0', '8', '5', '8', '1', '0', '3', '7', '0', '2', '9', '7', '4', '3', '1', '2', '2', '7', '9', '9', '8', '8', '1', '3', '8', '1', '0', '7', '6', '2', '7', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '1', '4', '6', '8', '5', '6', '8', '8', '4', '5', '1', '7', '3', '0', '1', '2', '5', '7', '8', '8', '1', '6', '6', '6', '2', '6', '3', '2', '9', '4', '8', '3', '6', '5', '5', '3', '7', '0', '0', '9', '2', '5', '6', '4', '7', '2', '7', '1', '2', '8', '7', '3', '6', '6', '8', '0', '1', '4', '5', '8', '1', '5', '0', '3', '6', '0', '9', '8', '3', '2', '0', '2', '3', '3', '3', '7', '7', '5', '7', '3', '6', '3', '1', '9', '6', '0', '4', '9', '0', '5', '1', '5', '3', '5', '7', '0', '0', '2', '5', '1', '5', '8', '2', '2', '3', '3', '9', '9', '1', '0', '0', '0', '0', '0', '6', '2', '9', '9', '8', '2', '7', '0', '8', '1', '7', '9', '9', '4', '0', '8', '9', '1'])
noncomputable def fragment0443905Acc00800 : List (String × SourceJson) := (fragment0443905Field007Key00, fragment0443905Field007Value00) :: fragment0443905Acc00700
noncomputable def fragment0443905Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '8', '0', '1', '0', '2', '5', '3', '2', '8', '5', '7', '8', '6', '3', '0', '9', '8', '3', '9', '4', '3', '1', '9', '5', '4', '8', '0', '7', '8', '8', '7', '1', '2', '6', '0', '6', '4', '3', '9', '0', '6', '2', '3', '4', '8', '1', '6', '6', '9', '3', '6', '2', '1', '3', '4', '7', '5', '0', '5', '6', '7', '9', '0', '8', '5', '8', '1', '0', '3', '7', '0', '2', '9', '7', '4', '3', '1', '2', '2', '7', '9', '9', '8', '8', '1', '3', '8', '1', '0', '7', '6', '2', '7', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '1', '4', '6', '8', '5', '6', '8', '8', '4', '5', '1', '7', '3', '0', '1', '2', '5', '7', '8', '8', '1', '6', '6', '6', '2', '6', '3', '2', '9', '4', '8', '3', '6', '5', '5', '3', '7', '0', '0', '9', '2', '5', '6', '4', '7', '2', '7', '1', '2', '8', '7', '3', '6', '6', '8', '0', '1', '4', '5', '8', '1', '5', '0', '3', '6', '0', '9', '8', '3', '2', '0', '2', '3', '3', '3', '7', '7', '5', '7', '3', '6', '3', '1', '9', '6', '0', '4', '9', '0', '5', '1', '5', '3', '5', '7', '0', '0', '2', '5', '1', '5', '8', '2', '2', '3', '3', '9', '9', '1', '0', '0', '0', '0', '0', '6', '2', '9', '9', '8', '2', '7', '0', '8', '1', '7', '9', '9', '4', '0', '8', '9', '1', '"', ',']

theorem object_fragment0443905_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0443905Field007Chars00 ++ tail)) fragment0443905Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0443905Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_007"
  err.flush

noncomputable def fragment0443905Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0443905Field008Value00 : SourceJson := .str (String.ofList ['3', '3', '1', '9', '0', '4', '7', '5', '1', '1', '3'])
noncomputable def fragment0443905Acc00900 : List (String × SourceJson) := (fragment0443905Field008Key00, fragment0443905Field008Value00) :: fragment0443905Acc00800
noncomputable def fragment0443905Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '1', '9', '0', '4', '7', '5', '1', '1', '3', '"', ',']

theorem object_fragment0443905_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0443905Field008Chars00 ++ tail)) fragment0443905Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0443905Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_008"
  err.flush

noncomputable def fragment0443905Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0443905Field009Value00 : SourceJson := .str (String.ofList ['3', '1', '0', '5', '1', '4', '2', '4', '9', '1', '6', '5'])
noncomputable def fragment0443905Acc01000 : List (String × SourceJson) := (fragment0443905Field009Key00, fragment0443905Field009Value00) :: fragment0443905Acc00900
noncomputable def fragment0443905Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '0', '5', '1', '4', '2', '4', '9', '1', '6', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0443905_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0443905Field009Chars00 ++ tail)) fragment0443905Acc00900 =
      .ok (.obj (fragment0443905Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0443905_object_field_009"
  err.flush

noncomputable def fragment0443905Chars : List Char := '{' :: (fragment0443905Field000Chars00 ++ fragment0443905Field001Chars00 ++ fragment0443905Field002Chars00 ++ fragment0443905Field003Chars00 ++ fragment0443905Field004Chars00 ++ fragment0443905Field005Chars00 ++ fragment0443905Field006Chars00 ++ fragment0443905Field007Chars00 ++ fragment0443905Field008Chars00 ++ fragment0443905Field009Chars00)
noncomputable def fragment0443905Value : SourceJson := .obj (fragment0443905Acc01000.reverse)

theorem value_fragment0443905 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0443905Chars ++ tail) =
      .ok (fragment0443905Value, tail) := by
  have hinput : fragment0443905Chars ++ tail = '{' :: (fragment0443905Field000Chars00 ++ (fragment0443905Field001Chars00 ++ (fragment0443905Field002Chars00 ++ (fragment0443905Field003Chars00 ++ (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0443905Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0443905Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0443905Field000Chars00 ++ (fragment0443905Field001Chars00 ++ (fragment0443905Field002Chars00 ++ (fragment0443905Field003Chars00 ++ (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0443905Field000Chars00 ++ (fragment0443905Field001Chars00 ++ (fragment0443905Field002Chars00 ++ (fragment0443905Field003Chars00 ++ (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))))))))))) fragment0443905Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0443905Field001Chars00 ++ (fragment0443905Field002Chars00 ++ (fragment0443905Field003Chars00 ++ (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail))))))))))) fragment0443905Acc00100 := object_fragment0443905_field_000 fuel (fragment0443905Field001Chars00 ++ (fragment0443905Field002Chars00 ++ (fragment0443905Field003Chars00 ++ (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0443905Field002Chars00 ++ (fragment0443905Field003Chars00 ++ (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))))))))) fragment0443905Acc00200 := object_fragment0443905_field_001 fuel (fragment0443905Field002Chars00 ++ (fragment0443905Field003Chars00 ++ (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0443905Field003Chars00 ++ (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail))))))))) fragment0443905Acc00300 := object_fragment0443905_field_002 fuel (fragment0443905Field003Chars00 ++ (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))))))) fragment0443905Acc00400 := object_fragment0443905_field_003 fuel (fragment0443905Field004Chars00 ++ (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail))))))) fragment0443905Acc00500 := object_fragment0443905_field_004 fuel (fragment0443905Field005Chars00 ++ (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))))) fragment0443905Acc00600 := object_fragment0443905_field_005 fuel (fragment0443905Field006Chars00 ++ (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail))))) fragment0443905Acc00700 := object_fragment0443905_field_006 fuel (fragment0443905Field007Chars00 ++ (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))) fragment0443905Acc00800 := object_fragment0443905_field_007 fuel (fragment0443905Field008Chars00 ++ (fragment0443905Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0443905Field009Chars00 ++ (tail))) fragment0443905Acc00900 := object_fragment0443905_field_008 fuel (fragment0443905Field009Chars00 ++ (tail))
    _ = .ok (fragment0443905Value, tail) := object_fragment0443905_field_009 fuel (tail)

noncomputable def fragment0445562Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0445562Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0445562Field000Value00 : SourceJson := .number (String.ofList ['1', '2', '9'])
noncomputable def fragment0445562Acc00100 : List (String × SourceJson) := (fragment0445562Field000Key00, fragment0445562Field000Value00) :: fragment0445562Acc00000
noncomputable def fragment0445562Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', '9', ',']

theorem object_fragment0445562_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0445562Field000Chars00 ++ tail)) fragment0445562Acc00000 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0445562Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_000"
  err.flush

noncomputable def fragment0445562Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0445562Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6'])]
noncomputable def fragment0445562Acc00200 : List (String × SourceJson) := (fragment0445562Field001Key00, fragment0445562Field001Value00) :: fragment0445562Acc00100
noncomputable def fragment0445562Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0445562_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0445562Field001Chars00 ++ tail)) fragment0445562Acc00100 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0445562Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_001"
  err.flush

noncomputable def fragment0445562Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0445562Field002Value00 : SourceJson := .str (String.ofList ['4', '6', '8', '5', '9', '2', '3', '9', '9', '9', '0', '2', '9', '8', '6', '3', '5', '3', '3', '7', '8', '1', '7', '3', '8', '1', '8', '6', '0', '4', '7', '9', '1', '2', '2', '4', '9', '7', '7', '8', '9', '/', '6', '5', '5', '5', '2', '7', '9', '8', '2', '4', '5', '0', '3', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0445562Acc00300 : List (String × SourceJson) := (fragment0445562Field002Key00, fragment0445562Field002Value00) :: fragment0445562Acc00200
noncomputable def fragment0445562Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '6', '8', '5', '9', '2', '3', '9', '9', '9', '0', '2', '9', '8', '6', '3', '5', '3', '3', '7', '8', '1', '7', '3', '8', '1', '8', '6', '0', '4', '7', '9', '1', '2', '2', '4', '9', '7', '7', '8', '9', '/', '6', '5', '5', '5', '2', '7', '9', '8', '2', '4', '5', '0', '3', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0445562_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0445562Field002Chars00 ++ tail)) fragment0445562Acc00200 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0445562Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_002"
  err.flush

noncomputable def fragment0445562Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0445562Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0445562Acc00400 : List (String × SourceJson) := (fragment0445562Field003Key00, fragment0445562Field003Value00) :: fragment0445562Acc00300
noncomputable def fragment0445562Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0445562_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0445562Field003Chars00 ++ tail)) fragment0445562Acc00300 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0445562Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_003"
  err.flush

noncomputable def fragment0445562Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0445562Field004Value00 : SourceJson := .arr [.str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0445562Acc00500 : List (String × SourceJson) := (fragment0445562Field004Key00, fragment0445562Field004Value00) :: fragment0445562Acc00400
noncomputable def fragment0445562Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0445562_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0445562Field004Chars00 ++ tail)) fragment0445562Acc00400 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0445562Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_004"
  err.flush

noncomputable def fragment0445562Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0445562Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '8', '0', '2', '0', '4', '4', '8', '5', '8', '3', '2', '9', '7', '/', '2', '6', '2', '0', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '6', '9', '3', '7', '1', '6', '5', '0', '8', '0', '7', '/', '2', '6', '2', '0', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '4', '7', '0', '2', '7', '9', '2', '0', '8', '7', '3', '9', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '7', '3', '2', '3', '1', '9', '1', '3', '4', '2', '9', '/', '8', '7', '3', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '4', '9', '4', '8', '0', '3', '9', '1', '4', '6', '2', '9', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '6', '5', '2', '0', '6', '6', '5', '4', '4', '4', '2', '7', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '2', '3', '1', '5', '4', '8', '1', '0', '4', '1', '/', '8', '2', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '4', '0', '2', '0', '9', '8', '2', '2', '1', '/', '6', '2', '8', '8', '1', '4', '8', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '0', '3', '1', '7', '7', '4', '1', '5', '6', '8', '9', '/', '3', '9', '3', '0', '0', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '0', '3', '1', '5', '1', '2', '1', '5', '0', '6', '9', '/', '3', '9', '3', '0', '0', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0445562Acc00600 : List (String × SourceJson) := (fragment0445562Field005Key00, fragment0445562Field005Value00) :: fragment0445562Acc00500
noncomputable def fragment0445562Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '2', '0', '4', '4', '8', '5', '8', '3', '2', '9', '7', '/', '2', '6', '2', '0', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '6', '9', '3', '7', '1', '6', '5', '0', '8', '0', '7', '/', '2', '6', '2', '0', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '4', '7', '0', '2', '7', '9', '2', '0', '8', '7', '3', '9', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '3', '2', '3', '1', '9', '1', '3', '4', '2', '9', '/', '8', '7', '3', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '4', '9', '4', '8', '0', '3', '9', '1', '4', '6', '2', '9', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '5', '2', '0', '6', '6', '5', '4', '4', '4', '2', '7', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '3', '1', '5', '4', '8', '1', '0', '4', '1', '/', '8', '2', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '4', '0', '2', '0', '9', '8', '2', '2', '1', '/', '6', '2', '8', '8', '1', '4', '8', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '0', '3', '1', '7', '7', '4', '1', '5', '6', '8', '9', '/', '3', '9', '3', '0', '0', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '0', '3', '1', '5', '1', '2', '1', '5', '0', '6', '9', '/', '3', '9', '3', '0', '0', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0445562_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0445562Field005Chars00 ++ tail)) fragment0445562Acc00500 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0445562Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_005"
  err.flush

noncomputable def fragment0445562Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0445562Field006Value00 : SourceJson := .str (String.ofList ['5', '1', '3', '4', '3', '7', '3', '4', '8', '6', '0', '3', '0', '6', '2', '0', '1', '1', '5', '7', '7', '3', '5', '9', '7', '8', '2', '4', '8', '8', '6', '1', '5', '7', '9', '1', '9', '1', '5', '9', '8', '9', '0', '4', '2', '0', '4', '6', '0', '/', '6', '2', '5', '6', '0', '2', '4', '8', '2', '6', '5', '7', '4', '6', '7', '8', '7', '3', '1', '5', '2', '4', '1', '3', '7', '2', '4', '5', '3', '4', '8', '1', '0', '0', '1', '6', '6', '0', '6', '0', '7', '2', '2', '8', '0', '1', '3', '6', '7', '3', '6', '1', '7', '3', '4', '2', '7', '6', '3', '5', '8', '2', '1', '7', '8', '2', '3', '9'])
noncomputable def fragment0445562Acc00700 : List (String × SourceJson) := (fragment0445562Field006Key00, fragment0445562Field006Value00) :: fragment0445562Acc00600
noncomputable def fragment0445562Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '1', '3', '4', '3', '7', '3', '4', '8', '6', '0', '3', '0', '6', '2', '0', '1', '1', '5', '7', '7', '3', '5', '9', '7', '8', '2', '4', '8', '8', '6', '1', '5', '7', '9', '1', '9', '1', '5', '9', '8', '9', '0', '4', '2', '0', '4', '6', '0', '/', '6', '2', '5', '6', '0', '2', '4', '8', '2', '6', '5', '7', '4', '6', '7', '8', '7', '3', '1', '5', '2', '4', '1', '3', '7', '2', '4', '5', '3', '4', '8', '1', '0', '0', '1', '6', '6', '0', '6', '0', '7', '2', '2', '8', '0', '1', '3', '6', '7', '3', '6', '1', '7', '3', '4', '2', '7', '6', '3', '5', '8', '2', '1', '7', '8', '2', '3', '9', '"', ',']

theorem object_fragment0445562_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0445562Field006Chars00 ++ tail)) fragment0445562Acc00600 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0445562Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_006"
  err.flush

noncomputable def fragment0445562Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0445562Field007Value00 : SourceJson := .str (String.ofList ['3', '4', '0', '0', '4', '7', '2', '6', '4', '6', '2', '4', '1', '8', '8', '7', '2', '4', '7', '1', '2', '2', '3', '9', '6', '6', '0', '8', '5', '1', '7', '3', '1', '2', '0', '3', '1', '2', '2', '3', '1', '8', '2', '7', '7', '9', '1', '2', '7', '8', '3', '0', '3', '2', '4', '6', '6', '9', '6', '2', '0', '6', '0', '8', '6', '4', '4', '8', '9', '3', '7', '7', '3', '0', '1', '3', '3', '8', '0', '1', '7', '2', '8', '6', '8', '1', '4', '0', '4', '3', '7', '0', '6', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '9', '0', '7', '9', '8', '8', '2', '8', '9', '2', '0', '9', '9', '6', '1', '1', '8', '0', '4', '0', '9', '5', '8', '3', '2', '9', '1', '7', '7', '1', '3', '7', '5', '7', '5', '9', '5', '3', '0', '3', '1', '7', '4', '6', '2', '1', '8', '8', '4', '0', '3', '5', '8', '5', '4', '1', '7', '7', '7', '7', '8', '6', '8', '8', '9', '7', '4', '1', '5', '2', '2', '1', '4', '2', '0', '2', '8', '3', '5', '9', '5', '7', '2', '1', '2', '1', '0', '3', '0', '7', '1', '0', '7', '7', '6', '1', '8', '5', '5', '6', '2', '2', '1', '3', '4', '9', '8', '0', '4', '9', '8', '0', '9', '4', '3', '9', '3', '4', '8', '5', '5', '0', '2', '4', '8', '3', '2', '0', '7', '8', '3'])
noncomputable def fragment0445562Acc00800 : List (String × SourceJson) := (fragment0445562Field007Key00, fragment0445562Field007Value00) :: fragment0445562Acc00700
noncomputable def fragment0445562Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '0', '0', '4', '7', '2', '6', '4', '6', '2', '4', '1', '8', '8', '7', '2', '4', '7', '1', '2', '2', '3', '9', '6', '6', '0', '8', '5', '1', '7', '3', '1', '2', '0', '3', '1', '2', '2', '3', '1', '8', '2', '7', '7', '9', '1', '2', '7', '8', '3', '0', '3', '2', '4', '6', '6', '9', '6', '2', '0', '6', '0', '8', '6', '4', '4', '8', '9', '3', '7', '7', '3', '0', '1', '3', '3', '8', '0', '1', '7', '2', '8', '6', '8', '1', '4', '0', '4', '3', '7', '0', '6', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '9', '0', '7', '9', '8', '8', '2', '8', '9', '2', '0', '9', '9', '6', '1', '1', '8', '0', '4', '0', '9', '5', '8', '3', '2', '9', '1', '7', '7', '1', '3', '7', '5', '7', '5', '9', '5', '3', '0', '3', '1', '7', '4', '6', '2', '1', '8', '8', '4', '0', '3', '5', '8', '5', '4', '1', '7', '7', '7', '7', '8', '6', '8', '8', '9', '7', '4', '1', '5', '2', '2', '1', '4', '2', '0', '2', '8', '3', '5', '9', '5', '7', '2', '1', '2', '1', '0', '3', '0', '7', '1', '0', '7', '7', '6', '1', '8', '5', '5', '6', '2', '2', '1', '3', '4', '9', '8', '0', '4', '9', '8', '0', '9', '4', '3', '9', '3', '4', '8', '5', '5', '0', '2', '4', '8', '3', '2', '0', '7', '8', '3', '"', ',']

theorem object_fragment0445562_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0445562Field007Chars00 ++ tail)) fragment0445562Acc00700 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0445562Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_007"
  err.flush

noncomputable def fragment0445562Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0445562Field008Value00 : SourceJson := .str (String.ofList ['6', '5', '0', '2', '3', '2', '3', '5', '7', '1'])
noncomputable def fragment0445562Acc00900 : List (String × SourceJson) := (fragment0445562Field008Key00, fragment0445562Field008Value00) :: fragment0445562Acc00800
noncomputable def fragment0445562Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '5', '0', '2', '3', '2', '3', '5', '7', '1', '"', ',']

theorem object_fragment0445562_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0445562Field008Chars00 ++ tail)) fragment0445562Acc00800 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0445562Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_008"
  err.flush

noncomputable def fragment0445562Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0445562Field009Value00 : SourceJson := .str (String.ofList ['3', '9', '0', '0', '0', '2', '3', '9', '7', '4', '6'])
noncomputable def fragment0445562Acc01000 : List (String × SourceJson) := (fragment0445562Field009Key00, fragment0445562Field009Value00) :: fragment0445562Acc00900
noncomputable def fragment0445562Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '0', '0', '0', '2', '3', '9', '7', '4', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0445562_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0445562Field009Chars00 ++ tail)) fragment0445562Acc00900 =
      .ok (.obj (fragment0445562Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0445562_object_field_009"
  err.flush

noncomputable def fragment0445562Chars : List Char := '{' :: (fragment0445562Field000Chars00 ++ fragment0445562Field001Chars00 ++ fragment0445562Field002Chars00 ++ fragment0445562Field003Chars00 ++ fragment0445562Field004Chars00 ++ fragment0445562Field005Chars00 ++ fragment0445562Field006Chars00 ++ fragment0445562Field007Chars00 ++ fragment0445562Field008Chars00 ++ fragment0445562Field009Chars00)
noncomputable def fragment0445562Value : SourceJson := .obj (fragment0445562Acc01000.reverse)

theorem value_fragment0445562 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 258) (fragment0445562Chars ++ tail) =
      .ok (fragment0445562Value, tail) := by
  have hinput : fragment0445562Chars ++ tail = '{' :: (fragment0445562Field000Chars00 ++ (fragment0445562Field001Chars00 ++ (fragment0445562Field002Chars00 ++ (fragment0445562Field003Chars00 ++ (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0445562Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 258) (fragment0445562Chars ++ tail) =
        SourceJson.value (fuel + 258) ('{' :: (fragment0445562Field000Chars00 ++ (fragment0445562Field001Chars00 ++ (fragment0445562Field002Chars00 ++ (fragment0445562Field003Chars00 ++ (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 258)) hinput
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0445562Field000Chars00 ++ (fragment0445562Field001Chars00 ++ (fragment0445562Field002Chars00 ++ (fragment0445562Field003Chars00 ++ (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))))))))))) fragment0445562Acc00000 := by rfl
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0445562Field001Chars00 ++ (fragment0445562Field002Chars00 ++ (fragment0445562Field003Chars00 ++ (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail))))))))))) fragment0445562Acc00100 := object_fragment0445562_field_000 fuel (fragment0445562Field001Chars00 ++ (fragment0445562Field002Chars00 ++ (fragment0445562Field003Chars00 ++ (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0445562Field002Chars00 ++ (fragment0445562Field003Chars00 ++ (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))))))))) fragment0445562Acc00200 := object_fragment0445562_field_001 fuel (fragment0445562Field002Chars00 ++ (fragment0445562Field003Chars00 ++ (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0445562Field003Chars00 ++ (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail))))))))) fragment0445562Acc00300 := object_fragment0445562_field_002 fuel (fragment0445562Field003Chars00 ++ (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))))))) fragment0445562Acc00400 := object_fragment0445562_field_003 fuel (fragment0445562Field004Chars00 ++ (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail))))))) fragment0445562Acc00500 := object_fragment0445562_field_004 fuel (fragment0445562Field005Chars00 ++ (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))))) fragment0445562Acc00600 := object_fragment0445562_field_005 fuel (fragment0445562Field006Chars00 ++ (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail))))) fragment0445562Acc00700 := object_fragment0445562_field_006 fuel (fragment0445562Field007Chars00 ++ (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))) fragment0445562Acc00800 := object_fragment0445562_field_007 fuel (fragment0445562Field008Chars00 ++ (fragment0445562Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0445562Field009Chars00 ++ (tail))) fragment0445562Acc00900 := object_fragment0445562_field_008 fuel (fragment0445562Field009Chars00 ++ (tail))
    _ = .ok (fragment0445562Value, tail) := object_fragment0445562_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0128_before_reader"
  err.flush

noncomputable def chunk0128LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0128SuffixChars00 : List Char := [',']
noncomputable def chunk0128Chars00 : List Char := chunk0128LeadChars00 ++ fragment0443905Chars ++ chunk0128SuffixChars00
noncomputable def chunk0128Push00 (acc : List SourceJson) : List SourceJson := fragment0443905Value :: acc

noncomputable def chunk0128AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0128_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 476)
      (SourceJson.white (chunk0128LeadChars00 ++ (fragment0443905Chars ++ rest))) acc =
      (SourceJson.value (fuel + 475) (fragment0443905Chars ++ rest)).bind
        (chunk0128AfterValue00 (fuel + 475) acc) := by rfl

theorem array_chunk0128 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 476) (SourceJson.white (chunk0128Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 475) (SourceJson.white tail) (chunk0128Push00 acc) := by
  have hinput : chunk0128Chars00 ++ tail = chunk0128LeadChars00 ++ (fragment0443905Chars ++ (chunk0128SuffixChars00 ++ tail)) := by
    simp only [chunk0128Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 476) (SourceJson.white (chunk0128Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 476)
          (SourceJson.white (chunk0128LeadChars00 ++ (fragment0443905Chars ++ (chunk0128SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 476) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 475) (fragment0443905Chars ++ (chunk0128SuffixChars00 ++ tail))).bind
        (chunk0128AfterValue00 (fuel + 475) acc) := array_chunk0128_head fuel (chunk0128SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0443905Value, chunk0128SuffixChars00 ++ tail)).bind
        (chunk0128AfterValue00 (fuel + 475) acc) :=
      congrArg (fun result => result.bind (chunk0128AfterValue00 (fuel + 475) acc))
        (value_fragment0443905 (fuel + 214) (chunk0128SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 475) (SourceJson.white tail) (chunk0128Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0128_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0129_before_reader"
  err.flush

noncomputable def chunk0129LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0129SuffixChars00 : List Char := [',']
noncomputable def chunk0129Chars00 : List Char := chunk0129LeadChars00 ++ fragment0445562Chars ++ chunk0129SuffixChars00
noncomputable def chunk0129Push00 (acc : List SourceJson) : List SourceJson := fragment0445562Value :: acc

noncomputable def chunk0129AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0129_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 475)
      (SourceJson.white (chunk0129LeadChars00 ++ (fragment0445562Chars ++ rest))) acc =
      (SourceJson.value (fuel + 474) (fragment0445562Chars ++ rest)).bind
        (chunk0129AfterValue00 (fuel + 474) acc) := by rfl

theorem array_chunk0129 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 475) (SourceJson.white (chunk0129Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 474) (SourceJson.white tail) (chunk0129Push00 acc) := by
  have hinput : chunk0129Chars00 ++ tail = chunk0129LeadChars00 ++ (fragment0445562Chars ++ (chunk0129SuffixChars00 ++ tail)) := by
    simp only [chunk0129Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 475) (SourceJson.white (chunk0129Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 475)
          (SourceJson.white (chunk0129LeadChars00 ++ (fragment0445562Chars ++ (chunk0129SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 475) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 474) (fragment0445562Chars ++ (chunk0129SuffixChars00 ++ tail))).bind
        (chunk0129AfterValue00 (fuel + 474) acc) := array_chunk0129_head fuel (chunk0129SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0445562Value, chunk0129SuffixChars00 ++ tail)).bind
        (chunk0129AfterValue00 (fuel + 474) acc) :=
      congrArg (fun result => result.bind (chunk0129AfterValue00 (fuel + 474) acc))
        (value_fragment0445562 (fuel + 216) (chunk0129SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 474) (SourceJson.white tail) (chunk0129Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0129_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0128Chars00 ++ chunk0129Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0129Push00 (chunk0128Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 476) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 474) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0128Chars00 ++ (chunk0129Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 476) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 476) (SourceJson.white (chunk0128Chars00 ++ (chunk0129Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 476) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 475) (SourceJson.white (chunk0129Chars00 ++ (tail))) (chunk0128Push00 (acc)) := array_chunk0128 fuel (chunk0129Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 474) (SourceJson.white tail) (blockPush acc) := array_chunk0129 fuel (tail) (chunk0128Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 443899).take 3307 = blockChars := by rfl

theorem block_original_split : sourceRest 443899 = blockChars ++ sourceRest 447206 := by
  calc
    sourceRest 443899 = (sourceRest 443899).take 3307 ++ (sourceRest 443899).drop 3307 :=
      (List.take_append_drop 3307 (sourceRest 443899)).symm
    _ = blockChars ++ (sourceRest 443899).drop 3307 :=
      congrArg (fun part => part ++ (sourceRest 443899).drop 3307) block_original_prefix
    _ = blockChars ++ sourceRest 447206 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 443899 3307)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 476) (SourceJson.white (sourceRest 443899)) acc =
      SourceJson.array (fuel + 474) (SourceJson.white (sourceRest 447206)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 476) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 447206) acc)

#print axioms object_fragment0443905_field_000
#print axioms object_fragment0443905_field_001
#print axioms object_fragment0443905_field_002
#print axioms object_fragment0443905_field_003
#print axioms object_fragment0443905_field_004
#print axioms object_fragment0443905_field_005
#print axioms object_fragment0443905_field_006
#print axioms object_fragment0443905_field_007
#print axioms object_fragment0443905_field_008
#print axioms object_fragment0443905_field_009
#print axioms value_fragment0443905
#print axioms object_fragment0445562_field_000
#print axioms object_fragment0445562_field_001
#print axioms object_fragment0445562_field_002
#print axioms object_fragment0445562_field_003
#print axioms object_fragment0445562_field_004
#print axioms object_fragment0445562_field_005
#print axioms object_fragment0445562_field_006
#print axioms object_fragment0445562_field_007
#print axioms object_fragment0445562_field_008
#print axioms object_fragment0445562_field_009
#print axioms value_fragment0445562
#print axioms array_chunk0128_head
#print axioms array_chunk0128
#print axioms array_chunk0129_head
#print axioms array_chunk0129
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock065

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
