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

namespace SimplicesBlock045

noncomputable def fragment0377003Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0377003Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0377003Field000Value00 : SourceJson := .number (String.ofList ['8', '9'])
noncomputable def fragment0377003Acc00100 : List (String × SourceJson) := (fragment0377003Field000Key00, fragment0377003Field000Value00) :: fragment0377003Acc00000
noncomputable def fragment0377003Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '9', ',']

theorem object_fragment0377003_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 409) (SourceJson.white (fragment0377003Field000Chars00 ++ tail)) fragment0377003Acc00000 =
      SourceJson.object (fuel + 408) (SourceJson.white tail) fragment0377003Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_000"
  err.flush

noncomputable def fragment0377003Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0377003Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0377003Acc00200 : List (String × SourceJson) := (fragment0377003Field001Key00, fragment0377003Field001Value00) :: fragment0377003Acc00100
noncomputable def fragment0377003Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0377003_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 408) (SourceJson.white (fragment0377003Field001Chars00 ++ tail)) fragment0377003Acc00100 =
      SourceJson.object (fuel + 407) (SourceJson.white tail) fragment0377003Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_001"
  err.flush

noncomputable def fragment0377003Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0377003Field002Value00 : SourceJson := .str (String.ofList ['3', '0', '8', '4', '3', '6', '5', '7', '3', '6', '6', '6', '8', '4', '6', '1', '5', '7', '7', '6', '8', '3', '8', '7', '6', '0', '9', '6', '5', '2', '9', '9', '3', '0', '0', '8', '2', '6', '0', '7', '/', '1', '0', '1', '0', '7', '9', '1', '4', '4', '6', '8', '6', '2', '2', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0377003Acc00300 : List (String × SourceJson) := (fragment0377003Field002Key00, fragment0377003Field002Value00) :: fragment0377003Acc00200
noncomputable def fragment0377003Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '0', '8', '4', '3', '6', '5', '7', '3', '6', '6', '6', '8', '4', '6', '1', '5', '7', '7', '6', '8', '3', '8', '7', '6', '0', '9', '6', '5', '2', '9', '9', '3', '0', '0', '8', '2', '6', '0', '7', '/', '1', '0', '1', '0', '7', '9', '1', '4', '4', '6', '8', '6', '2', '2', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0377003_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0377003Field002Chars00 ++ tail)) fragment0377003Acc00200 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0377003Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_002"
  err.flush

noncomputable def fragment0377003Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0377003Field003Value00 : SourceJson := .str (String.ofList ['6', '6', '3', '6', '9', '1', '0', '9', '/', '9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0377003Acc00400 : List (String × SourceJson) := (fragment0377003Field003Key00, fragment0377003Field003Value00) :: fragment0377003Acc00300
noncomputable def fragment0377003Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '6', '3', '6', '9', '1', '0', '9', '/', '9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0377003_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0377003Field003Chars00 ++ tail)) fragment0377003Acc00300 =
      SourceJson.object (fuel + 405) (SourceJson.white tail) fragment0377003Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_003"
  err.flush

noncomputable def fragment0377003Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0377003Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4'])]
noncomputable def fragment0377003Acc00500 : List (String × SourceJson) := (fragment0377003Field004Key00, fragment0377003Field004Value00) :: fragment0377003Acc00400
noncomputable def fragment0377003Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0377003_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0377003Field004Chars00 ++ tail)) fragment0377003Acc00400 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0377003Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_004"
  err.flush

noncomputable def fragment0377003Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0377003Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '1', '2', '3', '7', '5', '0', '7', '3', '0', '7', '4', '5', '7', '3', '6', '2', '3', '9', '7', '/', '9', '5', '5', '3', '5', '7', '8', '2', '4', '3', '4', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '7', '4', '2', '4', '8', '3', '1', '6', '6', '7', '8', '8', '2', '6', '8', '7', '/', '4', '5', '3', '7', '9', '4', '9', '6', '6', '5', '6', '3', '7', '3', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '1', '4', '8', '6', '9', '1', '4', '8', '8', '0', '0', '4', '9', '4', '1', '4', '1', '3', '/', '7', '5', '6', '3', '2', '4', '9', '4', '4', '2', '7', '2', '8', '8', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '9', '3', '2', '2', '9', '0', '4', '6', '0', '9', '1', '9', '3', '1', '4', '2', '6', '7', '5', '9', '/', '5', '4', '4', '5', '5', '3', '9', '5', '9', '8', '7', '6', '4', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '3', '1', '8', '5', '8', '3', '9', '5', '6', '3', '2', '7', '0', '7', '9', '9', '9', '/', '7', '1', '1', '8', '3', '5', '2', '4', '1', '6', '6', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '5', '1', '8', '7', '7', '3', '8', '7', '1', '3', '5', '8', '7', '0', '1', '5', '3', '9', '7', '/', '6', '0', '5', '0', '5', '9', '9', '5', '5', '4', '1', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '7', '8', '6', '3', '3', '2', '7', '9', '2', '7', '0', '7', '5', '9', '3', '2', '3', '6', '9', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '6', '2', '3', '2', '3', '6', '2', '3', '0', '8', '9', '0', '4', '3', '5', '6', '0', '0', '7', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '8', '8', '5', '8', '9', '0', '5', '8', '2', '5', '4', '8', '7', '0', '5', '1', '5', '8', '7', '/', '5', '4', '4', '5', '5', '3', '9', '5', '9', '8', '7', '6', '4', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '8', '8', '4', '8', '0', '1', '4', '7', '4', '6', '2', '8', '9', '5', '2', '2', '0', '0', '7', '/', '5', '4', '4', '5', '5', '3', '9', '5', '9', '8', '7', '6', '4', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0377003Acc00600 : List (String × SourceJson) := (fragment0377003Field005Key00, fragment0377003Field005Value00) :: fragment0377003Acc00500
noncomputable def fragment0377003Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '2', '3', '7', '5', '0', '7', '3', '0', '7', '4', '5', '7', '3', '6', '2', '3', '9', '7', '/', '9', '5', '5', '3', '5', '7', '8', '2', '4', '3', '4', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '5', '9', '7', '4', '2', '4', '8', '3', '1', '6', '6', '7', '8', '8', '2', '6', '8', '7', '/', '4', '5', '3', '7', '9', '4', '9', '6', '6', '5', '6', '3', '7', '3', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '1', '4', '8', '6', '9', '1', '4', '8', '8', '0', '0', '4', '9', '4', '1', '4', '1', '3', '/', '7', '5', '6', '3', '2', '4', '9', '4', '4', '2', '7', '2', '8', '8', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '9', '3', '2', '2', '9', '0', '4', '6', '0', '9', '1', '9', '3', '1', '4', '2', '6', '7', '5', '9', '/', '5', '4', '4', '5', '5', '3', '9', '5', '9', '8', '7', '6', '4', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '3', '1', '8', '5', '8', '3', '9', '5', '6', '3', '2', '7', '0', '7', '9', '9', '9', '/', '7', '1', '1', '8', '3', '5', '2', '4', '1', '6', '6', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '1', '8', '7', '7', '3', '8', '7', '1', '3', '5', '8', '7', '0', '1', '5', '3', '9', '7', '/', '6', '0', '5', '0', '5', '9', '9', '5', '5', '4', '1', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '7', '8', '6', '3', '3', '2', '7', '9', '2', '7', '0', '7', '5', '9', '3', '2', '3', '6', '9', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '6', '2', '3', '2', '3', '6', '2', '3', '0', '8', '9', '0', '4', '3', '5', '6', '0', '0', '7', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '8', '8', '5', '8', '9', '0', '5', '8', '2', '5', '4', '8', '7', '0', '5', '1', '5', '8', '7', '/', '5', '4', '4', '5', '5', '3', '9', '5', '9', '8', '7', '6', '4', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '8', '8', '4', '8', '0', '1', '4', '7', '4', '6', '2', '8', '9', '5', '2', '2', '0', '0', '7', '/', '5', '4', '4', '5', '5', '3', '9', '5', '9', '8', '7', '6', '4', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0377003_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0377003Field005Chars00 ++ tail)) fragment0377003Acc00500 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0377003Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_005"
  err.flush

noncomputable def fragment0377003Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0377003Field006Value00 : SourceJson := .str (String.ofList ['4', '3', '6', '1', '8', '8', '1', '5', '4', '0', '3', '6', '7', '2', '2', '2', '9', '0', '8', '1', '3', '8', '0', '5', '8', '8', '2', '5', '5', '1', '7', '4', '3', '5', '1', '5', '9', '7', '5', '6', '7', '4', '1', '8', '9', '0', '5', '6', '/', '2', '5', '9', '5', '8', '0', '6', '4', '9', '8', '5', '9', '4', '3', '9', '5', '7', '5', '7', '7', '1', '6', '8', '8', '7', '1', '3', '2', '3', '3', '8', '5', '7', '4', '4', '6', '3', '6', '7', '0', '7', '5', '9', '0', '7', '5', '1', '4', '2', '5', '9', '1', '0', '9', '1', '5', '8', '9', '6', '4', '8', '4', '3', '7', '5'])
noncomputable def fragment0377003Acc00700 : List (String × SourceJson) := (fragment0377003Field006Key00, fragment0377003Field006Value00) :: fragment0377003Acc00600
noncomputable def fragment0377003Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '3', '6', '1', '8', '8', '1', '5', '4', '0', '3', '6', '7', '2', '2', '2', '9', '0', '8', '1', '3', '8', '0', '5', '8', '8', '2', '5', '5', '1', '7', '4', '3', '5', '1', '5', '9', '7', '5', '6', '7', '4', '1', '8', '9', '0', '5', '6', '/', '2', '5', '9', '5', '8', '0', '6', '4', '9', '8', '5', '9', '4', '3', '9', '5', '7', '5', '7', '7', '1', '6', '8', '8', '7', '1', '3', '2', '3', '3', '8', '5', '7', '4', '4', '6', '3', '6', '7', '0', '7', '5', '9', '0', '7', '5', '1', '4', '2', '5', '9', '1', '0', '9', '1', '5', '8', '9', '6', '4', '8', '4', '3', '7', '5', '"', ',']

theorem object_fragment0377003_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0377003Field006Chars00 ++ tail)) fragment0377003Acc00600 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0377003Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_006"
  err.flush

noncomputable def fragment0377003Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0377003Field007Value00 : SourceJson := .str (String.ofList ['2', '9', '2', '8', '9', '1', '4', '2', '2', '8', '4', '6', '2', '1', '7', '6', '3', '7', '6', '7', '6', '8', '9', '2', '6', '2', '4', '2', '9', '9', '1', '2', '4', '3', '3', '2', '9', '8', '5', '0', '4', '4', '3', '1', '4', '1', '7', '9', '3', '4', '9', '2', '6', '1', '8', '2', '2', '6', '9', '7', '9', '3', '4', '3', '9', '9', '1', '5', '9', '9', '8', '0', '5', '6', '2', '0', '3', '7', '7', '2', '6', '2', '9', '0', '4', '6', '6', '0', '7', '9', '8', '5', '7', '7', '5', '5', '4', '5', '9', '3', '0', '1', '1', '6', '6', '9', '0', '7', '0', '1', '8', '2', '5', '8', '1', '6', '2', '3', '8', '1', '3', '8', '6', '2', '1', '7', '7', '1', '2', '8', '6', '8', '3', '9', '7', '4', '4', '2', '3', '2', '6', '8', '1', '2', '8', '0', '6', '9', '7', '9', '7', '3', '7', '2', '5', '5', '2', '4', '4', '0', '2', '5', '1', '8', '4', '9', '3', '9', '1', '0', '1', '2', '2', '6', '8', '0', '6', '6', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '1', '0', '9', '0', '7', '6', '6', '7', '1', '3', '6', '4', '9', '6', '0', '5', '0', '2', '9', '5', '1', '1', '6', '7', '5', '2', '4', '8', '1', '4', '4', '6', '4', '2', '4', '7', '3', '1', '8', '3', '5', '8', '0', '5', '4', '1', '3', '2', '9', '7', '9', '5', '2', '9', '2', '2', '6', '4', '5', '6', '5', '7', '5', '6', '3', '4', '4', '2', '0', '8', '7', '4', '1', '4', '4', '1', '3', '5', '9', '5', '7', '0', '0', '2', '2', '9', '8', '4', '7', '1', '4', '3', '6', '1', '8', '8', '1', '6', '9', '4', '6', '0', '3', '1', '0', '1', '3', '9', '8', '3', '3', '3', '3', '5', '7', '1', '2', '6', '1', '3', '6', '9', '3', '4', '4', '9', '0', '7', '8', '6', '5', '4', '8', '7', '5', '9', '4', '7', '0', '4', '8', '1', '9', '3', '0', '2', '9', '0', '8', '9', '9', '9', '9', '8', '9', '5', '0', '8', '0', '5', '2', '1', '8', '0', '7', '5', '7', '5', '0', '4', '6', '0', '7', '3', '9', '6', '6', '4', '2', '7', '5', '0', '2', '7', '2', '9', '1', '4', '9', '7', '4', '5', '0', '2', '1', '9', '3', '6', '2', '0', '2', '3', '0', '1', '1'])
noncomputable def fragment0377003Acc00800 : List (String × SourceJson) := (fragment0377003Field007Key00, fragment0377003Field007Value00) :: fragment0377003Acc00700
noncomputable def fragment0377003Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '9', '2', '8', '9', '1', '4', '2', '2', '8', '4', '6', '2', '1', '7', '6', '3', '7', '6', '7', '6', '8', '9', '2', '6', '2', '4', '2', '9', '9', '1', '2', '4', '3', '3', '2', '9', '8', '5', '0', '4', '4', '3', '1', '4', '1', '7', '9', '3', '4', '9', '2', '6', '1', '8', '2', '2', '6', '9', '7', '9', '3', '4', '3', '9', '9', '1', '5', '9', '9', '8', '0', '5', '6', '2', '0', '3', '7', '7', '2', '6', '2', '9', '0', '4', '6', '6', '0', '7', '9', '8', '5', '7', '7', '5', '5', '4', '5', '9', '3', '0', '1', '1', '6', '6', '9', '0', '7', '0', '1', '8', '2', '5', '8', '1', '6', '2', '3', '8', '1', '3', '8', '6', '2', '1', '7', '7', '1', '2', '8', '6', '8', '3', '9', '7', '4', '4', '2', '3', '2', '6', '8', '1', '2', '8', '0', '6', '9', '7', '9', '7', '3', '7', '2', '5', '5', '2', '4', '4', '0', '2', '5', '1', '8', '4', '9', '3', '9', '1', '0', '1', '2', '2', '6', '8', '0', '6', '6', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '1', '0', '9', '0', '7', '6', '6', '7', '1', '3', '6', '4', '9', '6', '0', '5', '0', '2', '9', '5', '1', '1', '6', '7', '5', '2', '4', '8', '1', '4', '4', '6', '4', '2', '4', '7', '3', '1', '8', '3', '5', '8', '0', '5', '4', '1', '3', '2', '9', '7', '9', '5', '2', '9', '2', '2', '6', '4', '5', '6', '5', '7', '5', '6', '3', '4', '4', '2', '0', '8', '7', '4', '1', '4', '4', '1', '3', '5', '9', '5', '7', '0', '0', '2', '2', '9', '8', '4', '7', '1', '4', '3', '6', '1', '8', '8', '1', '6', '9', '4', '6', '0', '3', '1', '0', '1', '3', '9', '8', '3', '3', '3', '3', '5', '7', '1', '2', '6', '1', '3', '6', '9', '3', '4', '4', '9', '0', '7', '8', '6', '5', '4', '8', '7', '5', '9', '4', '7', '0', '4', '8', '1', '9', '3', '0', '2', '9', '0', '8', '9', '9', '9', '9', '8', '9', '5', '0', '8', '0', '5', '2', '1', '8', '0', '7', '5', '7', '5', '0', '4', '6', '0', '7', '3', '9', '6', '6', '4', '2', '7', '5', '0', '2', '7', '2', '9', '1', '4', '9', '7', '4', '5', '0', '2', '1', '9', '3', '6', '2', '0', '2', '3', '0', '1', '1', '"', ',']

theorem object_fragment0377003_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0377003Field007Chars00 ++ tail)) fragment0377003Acc00700 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0377003Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_007"
  err.flush

noncomputable def fragment0377003Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0377003Field008Value00 : SourceJson := .str (String.ofList ['1', '3', '3', '1', '3', '1', '5', '9', '5', '0', '3', '0', '4'])
noncomputable def fragment0377003Acc00900 : List (String × SourceJson) := (fragment0377003Field008Key00, fragment0377003Field008Value00) :: fragment0377003Acc00800
noncomputable def fragment0377003Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '3', '1', '3', '1', '5', '9', '5', '0', '3', '0', '4', '"', ',']

theorem object_fragment0377003_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0377003Field008Chars00 ++ tail)) fragment0377003Acc00800 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0377003Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_008"
  err.flush

noncomputable def fragment0377003Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0377003Field009Value00 : SourceJson := .str (String.ofList ['9', '2', '4', '1', '7', '7', '7', '2', '0', '7', '5', '0', '6'])
noncomputable def fragment0377003Acc01000 : List (String × SourceJson) := (fragment0377003Field009Key00, fragment0377003Field009Value00) :: fragment0377003Acc00900
noncomputable def fragment0377003Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '2', '4', '1', '7', '7', '7', '2', '0', '7', '5', '0', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0377003_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0377003Field009Chars00 ++ tail)) fragment0377003Acc00900 =
      .ok (.obj (fragment0377003Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0377003_object_field_009"
  err.flush

noncomputable def fragment0377003Chars : List Char := '{' :: (fragment0377003Field000Chars00 ++ fragment0377003Field001Chars00 ++ fragment0377003Field002Chars00 ++ fragment0377003Field003Chars00 ++ fragment0377003Field004Chars00 ++ fragment0377003Field005Chars00 ++ fragment0377003Field006Chars00 ++ fragment0377003Field007Chars00 ++ fragment0377003Field008Chars00 ++ fragment0377003Field009Chars00)
noncomputable def fragment0377003Value : SourceJson := .obj (fragment0377003Acc01000.reverse)

theorem value_fragment0377003 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 410) (fragment0377003Chars ++ tail) =
      .ok (fragment0377003Value, tail) := by
  have hinput : fragment0377003Chars ++ tail = '{' :: (fragment0377003Field000Chars00 ++ (fragment0377003Field001Chars00 ++ (fragment0377003Field002Chars00 ++ (fragment0377003Field003Chars00 ++ (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0377003Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 410) (fragment0377003Chars ++ tail) =
        SourceJson.value (fuel + 410) ('{' :: (fragment0377003Field000Chars00 ++ (fragment0377003Field001Chars00 ++ (fragment0377003Field002Chars00 ++ (fragment0377003Field003Chars00 ++ (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 410)) hinput
    _ = SourceJson.object (fuel + 409) (SourceJson.white (fragment0377003Field000Chars00 ++ (fragment0377003Field001Chars00 ++ (fragment0377003Field002Chars00 ++ (fragment0377003Field003Chars00 ++ (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))))))))))) fragment0377003Acc00000 := by rfl
    _ = SourceJson.object (fuel + 408) (SourceJson.white (fragment0377003Field001Chars00 ++ (fragment0377003Field002Chars00 ++ (fragment0377003Field003Chars00 ++ (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail))))))))))) fragment0377003Acc00100 := object_fragment0377003_field_000 fuel (fragment0377003Field001Chars00 ++ (fragment0377003Field002Chars00 ++ (fragment0377003Field003Chars00 ++ (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0377003Field002Chars00 ++ (fragment0377003Field003Chars00 ++ (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))))))))) fragment0377003Acc00200 := object_fragment0377003_field_001 fuel (fragment0377003Field002Chars00 ++ (fragment0377003Field003Chars00 ++ (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0377003Field003Chars00 ++ (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail))))))))) fragment0377003Acc00300 := object_fragment0377003_field_002 fuel (fragment0377003Field003Chars00 ++ (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))))))) fragment0377003Acc00400 := object_fragment0377003_field_003 fuel (fragment0377003Field004Chars00 ++ (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail))))))) fragment0377003Acc00500 := object_fragment0377003_field_004 fuel (fragment0377003Field005Chars00 ++ (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))))) fragment0377003Acc00600 := object_fragment0377003_field_005 fuel (fragment0377003Field006Chars00 ++ (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail))))) fragment0377003Acc00700 := object_fragment0377003_field_006 fuel (fragment0377003Field007Chars00 ++ (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))) fragment0377003Acc00800 := object_fragment0377003_field_007 fuel (fragment0377003Field008Chars00 ++ (fragment0377003Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0377003Field009Chars00 ++ (tail))) fragment0377003Acc00900 := object_fragment0377003_field_008 fuel (fragment0377003Field009Chars00 ++ (tail))
    _ = .ok (fragment0377003Value, tail) := object_fragment0377003_field_009 fuel (tail)

noncomputable def fragment0378938Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0378938Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0378938Field000Value00 : SourceJson := .number (String.ofList ['9', '0'])
noncomputable def fragment0378938Acc00100 : List (String × SourceJson) := (fragment0378938Field000Key00, fragment0378938Field000Value00) :: fragment0378938Acc00000
noncomputable def fragment0378938Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '0', ',']

theorem object_fragment0378938_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 498) (SourceJson.white (fragment0378938Field000Chars00 ++ tail)) fragment0378938Acc00000 =
      SourceJson.object (fuel + 497) (SourceJson.white tail) fragment0378938Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_000"
  err.flush

noncomputable def fragment0378938Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0378938Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0378938Acc00200 : List (String × SourceJson) := (fragment0378938Field001Key00, fragment0378938Field001Value00) :: fragment0378938Acc00100
noncomputable def fragment0378938Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0378938_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 497) (SourceJson.white (fragment0378938Field001Chars00 ++ tail)) fragment0378938Acc00100 =
      SourceJson.object (fuel + 496) (SourceJson.white tail) fragment0378938Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_001"
  err.flush

noncomputable def fragment0378938Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0378938Field002Value00 : SourceJson := .str (String.ofList ['2', '3', '3', '7', '8', '9', '8', '1', '8', '5', '7', '3', '0', '0', '6', '4', '5', '8', '9', '2', '9', '4', '4', '6', '1', '3', '7', '8', '5', '0', '3', '6', '6', '9', '6', '6', '4', '3', '3', '5', '4', '3', '2', '9', '6', '2', '2', '3', '/', '1', '4', '5', '6', '1', '4', '6', '1', '5', '8', '3', '4', '9', '7', '3', '3', '7', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0378938Acc00300 : List (String × SourceJson) := (fragment0378938Field002Key00, fragment0378938Field002Value00) :: fragment0378938Acc00200
noncomputable def fragment0378938Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '3', '3', '7', '8', '9', '8', '1', '8', '5', '7', '3', '0', '0', '6', '4', '5', '8', '9', '2', '9', '4', '4', '6', '1', '3', '7', '8', '5', '0', '3', '6', '6', '9', '6', '6', '4', '3', '3', '5', '4', '3', '2', '9', '6', '2', '2', '3', '/', '1', '4', '5', '6', '1', '4', '6', '1', '5', '8', '3', '4', '9', '7', '3', '3', '7', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0378938_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 496) (SourceJson.white (fragment0378938Field002Chars00 ++ tail)) fragment0378938Acc00200 =
      SourceJson.object (fuel + 495) (SourceJson.white tail) fragment0378938Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_002"
  err.flush

noncomputable def fragment0378938Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0378938Field003Value00 : SourceJson := .str (String.ofList ['6', '1', '0', '9', '1', '7', '0', '2', '2', '7', '/', '4', '8', '8', '8', '0', '4', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0378938Acc00400 : List (String × SourceJson) := (fragment0378938Field003Key00, fragment0378938Field003Value00) :: fragment0378938Acc00300
noncomputable def fragment0378938Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '1', '0', '9', '1', '7', '0', '2', '2', '7', '/', '4', '8', '8', '8', '0', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0378938_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 495) (SourceJson.white (fragment0378938Field003Chars00 ++ tail)) fragment0378938Acc00300 =
      SourceJson.object (fuel + 494) (SourceJson.white tail) fragment0378938Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_003"
  err.flush

noncomputable def fragment0378938Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0378938Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4'])]
noncomputable def fragment0378938Acc00500 : List (String × SourceJson) := (fragment0378938Field004Key00, fragment0378938Field004Value00) :: fragment0378938Acc00400
noncomputable def fragment0378938Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0378938_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 494) (SourceJson.white (fragment0378938Field004Chars00 ++ tail)) fragment0378938Acc00400 =
      SourceJson.object (fuel + 493) (SourceJson.white tail) fragment0378938Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_004"
  err.flush

noncomputable def fragment0378938Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0378938Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '6', '0', '9', '9', '8', '5', '9', '0', '6', '7', '3', '4', '6', '7', '7', '2', '5', '0', '7', '5', '1', '8', '1', '/', '9', '0', '7', '0', '2', '9', '6', '0', '3', '2', '5', '3', '3', '3', '0', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '0', '0', '2', '5', '7', '8', '2', '4', '1', '8', '1', '5', '1', '6', '8', '7', '1', '0', '5', '3', '4', '2', '1', '9', '/', '4', '4', '4', '4', '4', '4', '5', '0', '5', '5', '9', '4', '1', '3', '2', '1', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '2', '3', '1', '4', '6', '5', '8', '2', '7', '3', '3', '1', '4', '4', '4', '3', '7', '4', '0', '4', '3', '3', '3', '1', '/', '4', '4', '4', '4', '4', '4', '5', '0', '5', '5', '9', '4', '1', '3', '2', '1', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '2', '7', '8', '9', '8', '7', '5', '4', '3', '5', '4', '9', '6', '5', '2', '0', '0', '0', '0', '6', '4', '4', '6', '1', '/', '6', '6', '6', '6', '6', '6', '7', '5', '8', '3', '9', '1', '1', '9', '8', '1', '8', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '8', '5', '8', '2', '8', '4', '6', '6', '4', '9', '9', '5', '5', '9', '9', '0', '7', '0', '5', '2', '7', '7', '/', '6', '5', '3', '5', '9', '4', '8', '6', '1', '1', '6', '7', '8', '4', '1', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '8', '8', '3', '5', '5', '7', '1', '8', '3', '3', '2', '1', '2', '1', '0', '2', '5', '4', '7', '5', '1', '4', '3', '/', '4', '4', '4', '4', '4', '4', '5', '0', '5', '5', '9', '4', '1', '3', '2', '1', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '9', '3', '0', '7', '1', '2', '4', '2', '4', '0', '9', '1', '5', '1', '8', '4', '5', '8', '1', '7', '1', '/', '1', '7', '5', '4', '3', '8', '6', '2', '0', '6', '2', '9', '2', '6', '2', '6', '7', '9', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '4', '3', '5', '3', '8', '4', '6', '1', '9', '2', '0', '7', '5', '0', '9', '5', '8', '7', '8', '5', '4', '7', '7', '/', '1', '3', '3', '3', '3', '3', '3', '5', '1', '6', '7', '8', '2', '3', '9', '6', '3', '6', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '1', '0', '7', '6', '5', '8', '5', '2', '3', '6', '7', '5', '5', '9', '3', '6', '8', '8', '7', '6', '8', '9', '5', '1', '/', '1', '3', '3', '3', '3', '3', '3', '5', '1', '6', '7', '8', '2', '3', '9', '6', '3', '6', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '4', '2', '0', '9', '7', '2', '8', '5', '4', '8', '2', '0', '0', '9', '5', '0', '0', '5', '8', '3', '1', '5', '7', '1', '/', '1', '3', '3', '3', '3', '3', '3', '5', '1', '6', '7', '8', '2', '3', '9', '6', '3', '6', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0378938Acc00600 : List (String × SourceJson) := (fragment0378938Field005Key00, fragment0378938Field005Value00) :: fragment0378938Acc00500
noncomputable def fragment0378938Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '0', '9', '9', '8', '5', '9', '0', '6', '7', '3', '4', '6', '7', '7', '2', '5', '0', '7', '5', '1', '8', '1', '/', '9', '0', '7', '0', '2', '9', '6', '0', '3', '2', '5', '3', '3', '3', '0', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '0', '0', '2', '5', '7', '8', '2', '4', '1', '8', '1', '5', '1', '6', '8', '7', '1', '0', '5', '3', '4', '2', '1', '9', '/', '4', '4', '4', '4', '4', '4', '5', '0', '5', '5', '9', '4', '1', '3', '2', '1', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '2', '3', '1', '4', '6', '5', '8', '2', '7', '3', '3', '1', '4', '4', '4', '3', '7', '4', '0', '4', '3', '3', '3', '1', '/', '4', '4', '4', '4', '4', '4', '5', '0', '5', '5', '9', '4', '1', '3', '2', '1', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '2', '7', '8', '9', '8', '7', '5', '4', '3', '5', '4', '9', '6', '5', '2', '0', '0', '0', '0', '6', '4', '4', '6', '1', '/', '6', '6', '6', '6', '6', '6', '7', '5', '8', '3', '9', '1', '1', '9', '8', '1', '8', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '8', '5', '8', '2', '8', '4', '6', '6', '4', '9', '9', '5', '5', '9', '9', '0', '7', '0', '5', '2', '7', '7', '/', '6', '5', '3', '5', '9', '4', '8', '6', '1', '1', '6', '7', '8', '4', '1', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '8', '8', '3', '5', '5', '7', '1', '8', '3', '3', '2', '1', '2', '1', '0', '2', '5', '4', '7', '5', '1', '4', '3', '/', '4', '4', '4', '4', '4', '4', '5', '0', '5', '5', '9', '4', '1', '3', '2', '1', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '9', '3', '0', '7', '1', '2', '4', '2', '4', '0', '9', '1', '5', '1', '8', '4', '5', '8', '1', '7', '1', '/', '1', '7', '5', '4', '3', '8', '6', '2', '0', '6', '2', '9', '2', '6', '2', '6', '7', '9', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '4', '3', '5', '3', '8', '4', '6', '1', '9', '2', '0', '7', '5', '0', '9', '5', '8', '7', '8', '5', '4', '7', '7', '/', '1', '3', '3', '3', '3', '3', '3', '5', '1', '6', '7', '8', '2', '3', '9', '6', '3', '6', '4', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '1', '0', '7', '6', '5', '8', '5', '2', '3', '6', '7', '5', '5', '9', '3', '6', '8', '8', '7', '6', '8', '9', '5', '1', '/', '1', '3', '3', '3', '3', '3', '3', '5', '1', '6', '7', '8', '2', '3', '9', '6', '3', '6', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '4', '2', '0', '9', '7', '2', '8', '5', '4', '8', '2', '0', '0', '9', '5', '0', '0', '5', '8', '3', '1', '5', '7', '1', '/', '1', '3', '3', '3', '3', '3', '3', '5', '1', '6', '7', '8', '2', '3', '9', '6', '3', '6', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0378938_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 493) (SourceJson.white (fragment0378938Field005Chars00 ++ tail)) fragment0378938Acc00500 =
      SourceJson.object (fuel + 492) (SourceJson.white tail) fragment0378938Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_005"
  err.flush

noncomputable def fragment0378938Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0378938Field006Value00 : SourceJson := .str (String.ofList ['2', '1', '7', '3', '8', '1', '1', '0', '6', '1', '5', '0', '1', '1', '7', '3', '1', '7', '0', '6', '3', '7', '5', '7', '7', '1', '9', '1', '2', '7', '6', '0', '6', '1', '3', '0', '2', '0', '4', '6', '3', '0', '4', '6', '1', '5', '4', '9', '7', '3', '4', '9', '8', '6', '3', '6', '8', '/', '1', '3', '2', '0', '9', '3', '7', '1', '3', '3', '5', '4', '7', '8', '9', '4', '0', '5', '4', '9', '0', '4', '7', '1', '6', '1', '1', '4', '8', '8', '0', '7', '5', '3', '3', '1', '2', '2', '5', '4', '1', '6', '5', '1', '2', '0', '7', '0', '8', '6', '6', '2', '6', '8', '7', '1', '0', '0', '3', '2', '5', '5', '7', '1', '4', '8', '4', '3', '7', '5'])
noncomputable def fragment0378938Acc00700 : List (String × SourceJson) := (fragment0378938Field006Key00, fragment0378938Field006Value00) :: fragment0378938Acc00600
noncomputable def fragment0378938Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '7', '3', '8', '1', '1', '0', '6', '1', '5', '0', '1', '1', '7', '3', '1', '7', '0', '6', '3', '7', '5', '7', '7', '1', '9', '1', '2', '7', '6', '0', '6', '1', '3', '0', '2', '0', '4', '6', '3', '0', '4', '6', '1', '5', '4', '9', '7', '3', '4', '9', '8', '6', '3', '6', '8', '/', '1', '3', '2', '0', '9', '3', '7', '1', '3', '3', '5', '4', '7', '8', '9', '4', '0', '5', '4', '9', '0', '4', '7', '1', '6', '1', '1', '4', '8', '8', '0', '7', '5', '3', '3', '1', '2', '2', '5', '4', '1', '6', '5', '1', '2', '0', '7', '0', '8', '6', '6', '2', '6', '8', '7', '1', '0', '0', '3', '2', '5', '5', '7', '1', '4', '8', '4', '3', '7', '5', '"', ',']

theorem object_fragment0378938_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 492) (SourceJson.white (fragment0378938Field006Chars00 ++ tail)) fragment0378938Acc00600 =
      SourceJson.object (fuel + 491) (SourceJson.white tail) fragment0378938Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_006"
  err.flush

noncomputable def fragment0378938Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0378938Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '5', '8', '1', '3', '9', '4', '2', '4', '5', '3', '3', '7', '7', '8', '6', '7', '7', '4', '7', '8', '5', '0', '1', '7', '1', '9', '8', '5', '6', '2', '3', '5', '9', '3', '1', '6', '0', '7', '9', '1', '6', '9', '8', '4', '5', '3', '0', '5', '9', '8', '5', '6', '2', '2', '1', '0', '7', '3', '8', '9', '1', '3', '3', '5', '8', '2', '0', '0', '9', '1', '2', '6', '2', '9', '1', '1', '6', '9', '1', '0', '7', '3', '5', '2', '9', '2', '2', '1', '6', '2', '2', '9', '5', '2', '6', '9', '4', '8', '4', '5', '2', '7', '6', '0', '7', '8', '6', '0', '5', '4', '6', '9', '9', '6', '9', '9', '4', '8', '3', '0', '4', '9', '2', '5', '4', '5', '2', '2', '1', '6', '7', '1', '9', '2', '9', '0', '0', '3', '8', '8', '8', '2', '6', '7', '7', '8', '5', '4', '6', '0', '4', '2', '3', '6', '6', '6', '2', '6', '2', '9', '0', '8', '3', '5', '6', '2', '0', '5', '4', '9', '7', '4', '3', '1', '0', '5', '4', '4', '2', '1', '2', '1', '4', '1', '7', '6', '0', '5', '1', '4', '9', '7', '4', '6', '4', '7', '6', '0', '0', '1', '5', '1', '8', '5', '9', '7', '6', '9', '6', '6', '1', '6', '1', '7', '7', '7', '8', '3', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '7', '2', '6', '2', '6', '3', '9', '9', '0', '0', '4', '7', '6', '2', '3', '1', '8', '0', '6', '7', '3', '8', '1', '4', '1', '8', '2', '9', '1', '6', '4', '6', '8', '8', '5', '6', '7', '6', '6', '3', '9', '7', '9', '7', '8', '9', '6', '0', '8', '5', '4', '6', '9', '4', '1', '8', '8', '2', '9', '6', '8', '5', '4', '1', '3', '6', '3', '0', '5', '1', '0', '4', '1', '6', '4', '5', '4', '5', '1', '4', '2', '3', '7', '1', '3', '6', '3', '1', '8', '9', '7', '7', '2', '7', '4', '1', '7', '2', '9', '5', '6', '0', '9', '6', '4', '8', '9', '0', '3', '0', '0', '7', '3', '4', '6', '0', '0', '8', '5', '6', '1', '0', '4', '6', '8', '1', '6', '2', '6', '2', '7', '0', '6', '3', '3', '2', '9', '6', '2', '7', '3', '9', '2', '8', '0', '8', '1', '7', '9', '6', '8', '9', '7', '2', '7', '5', '3', '7', '8', '3', '3', '6', '3', '5', '8', '8', '8', '8', '3', '6', '8', '9', '9', '9', '3', '7', '7', '5', '5', '9', '1', '7', '6', '3', '3', '4', '6', '7', '3', '2', '4', '7', '1', '2', '3', '3', '4', '8', '8', '9', '1', '5', '9', '4', '3', '3', '1', '0', '4', '0', '1', '2', '0', '0', '2', '7', '6', '9', '3', '7', '4', '0', '0', '5', '2', '6', '0', '5', '2', '9', '3', '6', '3', '9', '0', '2', '2', '7', '0', '8', '7', '4', '4', '0', '2', '8', '7', '3'])
noncomputable def fragment0378938Acc00800 : List (String × SourceJson) := (fragment0378938Field007Key00, fragment0378938Field007Value00) :: fragment0378938Acc00700
noncomputable def fragment0378938Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '5', '8', '1', '3', '9', '4', '2', '4', '5', '3', '3', '7', '7', '8', '6', '7', '7', '4', '7', '8', '5', '0', '1', '7', '1', '9', '8', '5', '6', '2', '3', '5', '9', '3', '1', '6', '0', '7', '9', '1', '6', '9', '8', '4', '5', '3', '0', '5', '9', '8', '5', '6', '2', '2', '1', '0', '7', '3', '8', '9', '1', '3', '3', '5', '8', '2', '0', '0', '9', '1', '2', '6', '2', '9', '1', '1', '6', '9', '1', '0', '7', '3', '5', '2', '9', '2', '2', '1', '6', '2', '2', '9', '5', '2', '6', '9', '4', '8', '4', '5', '2', '7', '6', '0', '7', '8', '6', '0', '5', '4', '6', '9', '9', '6', '9', '9', '4', '8', '3', '0', '4', '9', '2', '5', '4', '5', '2', '2', '1', '6', '7', '1', '9', '2', '9', '0', '0', '3', '8', '8', '8', '2', '6', '7', '7', '8', '5', '4', '6', '0', '4', '2', '3', '6', '6', '6', '2', '6', '2', '9', '0', '8', '3', '5', '6', '2', '0', '5', '4', '9', '7', '4', '3', '1', '0', '5', '4', '4', '2', '1', '2', '1', '4', '1', '7', '6', '0', '5', '1', '4', '9', '7', '4', '6', '4', '7', '6', '0', '0', '1', '5', '1', '8', '5', '9', '7', '6', '9', '6', '6', '1', '6', '1', '7', '7', '7', '8', '3', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '7', '2', '6', '2', '6', '3', '9', '9', '0', '0', '4', '7', '6', '2', '3', '1', '8', '0', '6', '7', '3', '8', '1', '4', '1', '8', '2', '9', '1', '6', '4', '6', '8', '8', '5', '6', '7', '6', '6', '3', '9', '7', '9', '7', '8', '9', '6', '0', '8', '5', '4', '6', '9', '4', '1', '8', '8', '2', '9', '6', '8', '5', '4', '1', '3', '6', '3', '0', '5', '1', '0', '4', '1', '6', '4', '5', '4', '5', '1', '4', '2', '3', '7', '1', '3', '6', '3', '1', '8', '9', '7', '7', '2', '7', '4', '1', '7', '2', '9', '5', '6', '0', '9', '6', '4', '8', '9', '0', '3', '0', '0', '7', '3', '4', '6', '0', '0', '8', '5', '6', '1', '0', '4', '6', '8', '1', '6', '2', '6', '2', '7', '0', '6', '3', '3', '2', '9', '6', '2', '7', '3', '9', '2', '8', '0', '8', '1', '7', '9', '6', '8', '9', '7', '2', '7', '5', '3', '7', '8', '3', '3', '6', '3', '5', '8', '8', '8', '8', '3', '6', '8', '9', '9', '9', '3', '7', '7', '5', '5', '9', '1', '7', '6', '3', '3', '4', '6', '7', '3', '2', '4', '7', '1', '2', '3', '3', '4', '8', '8', '9', '1', '5', '9', '4', '3', '3', '1', '0', '4', '0', '1', '2', '0', '0', '2', '7', '6', '9', '3', '7', '4', '0', '0', '5', '2', '6', '0', '5', '2', '9', '3', '6', '3', '9', '0', '2', '2', '7', '0', '8', '7', '4', '4', '0', '2', '8', '7', '3', '"', ',']

theorem object_fragment0378938_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 491) (SourceJson.white (fragment0378938Field007Chars00 ++ tail)) fragment0378938Acc00700 =
      SourceJson.object (fuel + 490) (SourceJson.white tail) fragment0378938Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_007"
  err.flush

noncomputable def fragment0378938Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0378938Field008Value00 : SourceJson := .str (String.ofList ['1', '3', '0', '3', '8', '2', '4', '7', '7', '4', '7', '1', '3', '8', '2', '1', '5'])
noncomputable def fragment0378938Acc00900 : List (String × SourceJson) := (fragment0378938Field008Key00, fragment0378938Field008Value00) :: fragment0378938Acc00800
noncomputable def fragment0378938Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '0', '3', '8', '2', '4', '7', '7', '4', '7', '1', '3', '8', '2', '1', '5', '"', ',']

theorem object_fragment0378938_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 490) (SourceJson.white (fragment0378938Field008Chars00 ++ tail)) fragment0378938Acc00800 =
      SourceJson.object (fuel + 489) (SourceJson.white tail) fragment0378938Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_008"
  err.flush

noncomputable def fragment0378938Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0378938Field009Value00 : SourceJson := .str (String.ofList ['9', '4', '3', '3', '9', '6', '7', '5', '1', '6', '7', '1', '8', '5', '6', '6', '8'])
noncomputable def fragment0378938Acc01000 : List (String × SourceJson) := (fragment0378938Field009Key00, fragment0378938Field009Value00) :: fragment0378938Acc00900
noncomputable def fragment0378938Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '4', '3', '3', '9', '6', '7', '5', '1', '6', '7', '1', '8', '5', '6', '6', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0378938_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 489) (SourceJson.white (fragment0378938Field009Chars00 ++ tail)) fragment0378938Acc00900 =
      .ok (.obj (fragment0378938Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0378938_object_field_009"
  err.flush

noncomputable def fragment0378938Chars : List Char := '{' :: (fragment0378938Field000Chars00 ++ fragment0378938Field001Chars00 ++ fragment0378938Field002Chars00 ++ fragment0378938Field003Chars00 ++ fragment0378938Field004Chars00 ++ fragment0378938Field005Chars00 ++ fragment0378938Field006Chars00 ++ fragment0378938Field007Chars00 ++ fragment0378938Field008Chars00 ++ fragment0378938Field009Chars00)
noncomputable def fragment0378938Value : SourceJson := .obj (fragment0378938Acc01000.reverse)

theorem value_fragment0378938 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 499) (fragment0378938Chars ++ tail) =
      .ok (fragment0378938Value, tail) := by
  have hinput : fragment0378938Chars ++ tail = '{' :: (fragment0378938Field000Chars00 ++ (fragment0378938Field001Chars00 ++ (fragment0378938Field002Chars00 ++ (fragment0378938Field003Chars00 ++ (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0378938Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 499) (fragment0378938Chars ++ tail) =
        SourceJson.value (fuel + 499) ('{' :: (fragment0378938Field000Chars00 ++ (fragment0378938Field001Chars00 ++ (fragment0378938Field002Chars00 ++ (fragment0378938Field003Chars00 ++ (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 499)) hinput
    _ = SourceJson.object (fuel + 498) (SourceJson.white (fragment0378938Field000Chars00 ++ (fragment0378938Field001Chars00 ++ (fragment0378938Field002Chars00 ++ (fragment0378938Field003Chars00 ++ (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))))))))))) fragment0378938Acc00000 := by rfl
    _ = SourceJson.object (fuel + 497) (SourceJson.white (fragment0378938Field001Chars00 ++ (fragment0378938Field002Chars00 ++ (fragment0378938Field003Chars00 ++ (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail))))))))))) fragment0378938Acc00100 := object_fragment0378938_field_000 fuel (fragment0378938Field001Chars00 ++ (fragment0378938Field002Chars00 ++ (fragment0378938Field003Chars00 ++ (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 496) (SourceJson.white (fragment0378938Field002Chars00 ++ (fragment0378938Field003Chars00 ++ (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))))))))) fragment0378938Acc00200 := object_fragment0378938_field_001 fuel (fragment0378938Field002Chars00 ++ (fragment0378938Field003Chars00 ++ (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 495) (SourceJson.white (fragment0378938Field003Chars00 ++ (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail))))))))) fragment0378938Acc00300 := object_fragment0378938_field_002 fuel (fragment0378938Field003Chars00 ++ (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 494) (SourceJson.white (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))))))) fragment0378938Acc00400 := object_fragment0378938_field_003 fuel (fragment0378938Field004Chars00 ++ (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 493) (SourceJson.white (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail))))))) fragment0378938Acc00500 := object_fragment0378938_field_004 fuel (fragment0378938Field005Chars00 ++ (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 492) (SourceJson.white (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))))) fragment0378938Acc00600 := object_fragment0378938_field_005 fuel (fragment0378938Field006Chars00 ++ (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 491) (SourceJson.white (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail))))) fragment0378938Acc00700 := object_fragment0378938_field_006 fuel (fragment0378938Field007Chars00 ++ (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 490) (SourceJson.white (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))) fragment0378938Acc00800 := object_fragment0378938_field_007 fuel (fragment0378938Field008Chars00 ++ (fragment0378938Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 489) (SourceJson.white (fragment0378938Field009Chars00 ++ (tail))) fragment0378938Acc00900 := object_fragment0378938_field_008 fuel (fragment0378938Field009Chars00 ++ (tail))
    _ = .ok (fragment0378938Value, tail) := object_fragment0378938_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0089_before_reader"
  err.flush

noncomputable def chunk0089LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0089SuffixChars00 : List Char := [',']
noncomputable def chunk0089Chars00 : List Char := chunk0089LeadChars00 ++ fragment0377003Chars ++ chunk0089SuffixChars00
noncomputable def chunk0089Push00 (acc : List SourceJson) : List SourceJson := fragment0377003Value :: acc

noncomputable def chunk0089AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0089_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 515)
      (SourceJson.white (chunk0089LeadChars00 ++ (fragment0377003Chars ++ rest))) acc =
      (SourceJson.value (fuel + 514) (fragment0377003Chars ++ rest)).bind
        (chunk0089AfterValue00 (fuel + 514) acc) := by rfl

theorem array_chunk0089 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 515) (SourceJson.white (chunk0089Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 514) (SourceJson.white tail) (chunk0089Push00 acc) := by
  have hinput : chunk0089Chars00 ++ tail = chunk0089LeadChars00 ++ (fragment0377003Chars ++ (chunk0089SuffixChars00 ++ tail)) := by
    simp only [chunk0089Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 515) (SourceJson.white (chunk0089Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 515)
          (SourceJson.white (chunk0089LeadChars00 ++ (fragment0377003Chars ++ (chunk0089SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 515) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 514) (fragment0377003Chars ++ (chunk0089SuffixChars00 ++ tail))).bind
        (chunk0089AfterValue00 (fuel + 514) acc) := array_chunk0089_head fuel (chunk0089SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0377003Value, chunk0089SuffixChars00 ++ tail)).bind
        (chunk0089AfterValue00 (fuel + 514) acc) :=
      congrArg (fun result => result.bind (chunk0089AfterValue00 (fuel + 514) acc))
        (value_fragment0377003 (fuel + 104) (chunk0089SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 514) (SourceJson.white tail) (chunk0089Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0089_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0090_before_reader"
  err.flush

noncomputable def chunk0090LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0090SuffixChars00 : List Char := [',']
noncomputable def chunk0090Chars00 : List Char := chunk0090LeadChars00 ++ fragment0378938Chars ++ chunk0090SuffixChars00
noncomputable def chunk0090Push00 (acc : List SourceJson) : List SourceJson := fragment0378938Value :: acc

noncomputable def chunk0090AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0090_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 514)
      (SourceJson.white (chunk0090LeadChars00 ++ (fragment0378938Chars ++ rest))) acc =
      (SourceJson.value (fuel + 513) (fragment0378938Chars ++ rest)).bind
        (chunk0090AfterValue00 (fuel + 513) acc) := by rfl

theorem array_chunk0090 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 514) (SourceJson.white (chunk0090Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 513) (SourceJson.white tail) (chunk0090Push00 acc) := by
  have hinput : chunk0090Chars00 ++ tail = chunk0090LeadChars00 ++ (fragment0378938Chars ++ (chunk0090SuffixChars00 ++ tail)) := by
    simp only [chunk0090Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 514) (SourceJson.white (chunk0090Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 514)
          (SourceJson.white (chunk0090LeadChars00 ++ (fragment0378938Chars ++ (chunk0090SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 514) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 513) (fragment0378938Chars ++ (chunk0090SuffixChars00 ++ tail))).bind
        (chunk0090AfterValue00 (fuel + 513) acc) := array_chunk0090_head fuel (chunk0090SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0378938Value, chunk0090SuffixChars00 ++ tail)).bind
        (chunk0090AfterValue00 (fuel + 513) acc) :=
      congrArg (fun result => result.bind (chunk0090AfterValue00 (fuel + 513) acc))
        (value_fragment0378938 (fuel + 14) (chunk0090SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 513) (SourceJson.white tail) (chunk0090Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0090_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0089Chars00 ++ chunk0090Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0090Push00 (chunk0089Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 515) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 513) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0089Chars00 ++ (chunk0090Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 515) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 515) (SourceJson.white (chunk0089Chars00 ++ (chunk0090Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 515) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 514) (SourceJson.white (chunk0090Chars00 ++ (tail))) (chunk0089Push00 (acc)) := array_chunk0089 fuel (chunk0090Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 513) (SourceJson.white tail) (blockPush acc) := array_chunk0090 fuel (tail) (chunk0089Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 376997).take 4089 = blockChars := by rfl

theorem block_original_split : sourceRest 376997 = blockChars ++ sourceRest 381086 := by
  calc
    sourceRest 376997 = (sourceRest 376997).take 4089 ++ (sourceRest 376997).drop 4089 :=
      (List.take_append_drop 4089 (sourceRest 376997)).symm
    _ = blockChars ++ (sourceRest 376997).drop 4089 :=
      congrArg (fun part => part ++ (sourceRest 376997).drop 4089) block_original_prefix
    _ = blockChars ++ sourceRest 381086 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 376997 4089)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 515) (SourceJson.white (sourceRest 376997)) acc =
      SourceJson.array (fuel + 513) (SourceJson.white (sourceRest 381086)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 515) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 381086) acc)

#print axioms object_fragment0377003_field_000
#print axioms object_fragment0377003_field_001
#print axioms object_fragment0377003_field_002
#print axioms object_fragment0377003_field_003
#print axioms object_fragment0377003_field_004
#print axioms object_fragment0377003_field_005
#print axioms object_fragment0377003_field_006
#print axioms object_fragment0377003_field_007
#print axioms object_fragment0377003_field_008
#print axioms object_fragment0377003_field_009
#print axioms value_fragment0377003
#print axioms object_fragment0378938_field_000
#print axioms object_fragment0378938_field_001
#print axioms object_fragment0378938_field_002
#print axioms object_fragment0378938_field_003
#print axioms object_fragment0378938_field_004
#print axioms object_fragment0378938_field_005
#print axioms object_fragment0378938_field_006
#print axioms object_fragment0378938_field_007
#print axioms object_fragment0378938_field_008
#print axioms object_fragment0378938_field_009
#print axioms value_fragment0378938
#print axioms array_chunk0089_head
#print axioms array_chunk0089
#print axioms array_chunk0090_head
#print axioms array_chunk0090
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock045

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
