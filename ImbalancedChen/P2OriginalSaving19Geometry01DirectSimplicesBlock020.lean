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

namespace SimplicesBlock020

noncomputable def fragment0292757Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0292757Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0292757Field000Value00 : SourceJson := .number (String.ofList ['4', '0'])
noncomputable def fragment0292757Acc00100 : List (String × SourceJson) := (fragment0292757Field000Key00, fragment0292757Field000Value00) :: fragment0292757Acc00000
noncomputable def fragment0292757Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '0', ',']

theorem object_fragment0292757_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 412) (SourceJson.white (fragment0292757Field000Chars00 ++ tail)) fragment0292757Acc00000 =
      SourceJson.object (fuel + 411) (SourceJson.white tail) fragment0292757Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_000"
  err.flush

noncomputable def fragment0292757Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0292757Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0292757Acc00200 : List (String × SourceJson) := (fragment0292757Field001Key00, fragment0292757Field001Value00) :: fragment0292757Acc00100
noncomputable def fragment0292757Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0292757_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 411) (SourceJson.white (fragment0292757Field001Chars00 ++ tail)) fragment0292757Acc00100 =
      SourceJson.object (fuel + 410) (SourceJson.white tail) fragment0292757Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_001"
  err.flush

noncomputable def fragment0292757Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0292757Field002Value00 : SourceJson := .str (String.ofList ['4', '6', '1', '6', '6', '6', '1', '1', '8', '7', '6', '7', '0', '2', '5', '0', '8', '2', '2', '0', '5', '2', '4', '9', '8', '1', '4', '7', '1', '2', '0', '6', '8', '3', '9', '5', '7', '7', '8', '4', '6', '7', '1', '1', '/', '5', '2', '2', '5', '0', '6', '3', '7', '1', '6', '4', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0292757Acc00300 : List (String × SourceJson) := (fragment0292757Field002Key00, fragment0292757Field002Value00) :: fragment0292757Acc00200
noncomputable def fragment0292757Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '6', '1', '6', '6', '6', '1', '1', '8', '7', '6', '7', '0', '2', '5', '0', '8', '2', '2', '0', '5', '2', '4', '9', '8', '1', '4', '7', '1', '2', '0', '6', '8', '3', '9', '5', '7', '7', '8', '4', '6', '7', '1', '1', '/', '5', '2', '2', '5', '0', '6', '3', '7', '1', '6', '4', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0292757_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 410) (SourceJson.white (fragment0292757Field002Chars00 ++ tail)) fragment0292757Acc00200 =
      SourceJson.object (fuel + 409) (SourceJson.white tail) fragment0292757Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_002"
  err.flush

noncomputable def fragment0292757Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0292757Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0'])
noncomputable def fragment0292757Acc00400 : List (String × SourceJson) := (fragment0292757Field003Key00, fragment0292757Field003Value00) :: fragment0292757Acc00300
noncomputable def fragment0292757Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '7', '4', '0', '2', '3', '/', '9', '3', '7', '1', '2', '5', '0', '0', '0', '"', ',']

theorem object_fragment0292757_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 409) (SourceJson.white (fragment0292757Field003Chars00 ++ tail)) fragment0292757Acc00300 =
      SourceJson.object (fuel + 408) (SourceJson.white tail) fragment0292757Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_003"
  err.flush

noncomputable def fragment0292757Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0292757Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0292757Acc00500 : List (String × SourceJson) := (fragment0292757Field004Key00, fragment0292757Field004Value00) :: fragment0292757Acc00400
noncomputable def fragment0292757Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0292757_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 408) (SourceJson.white (fragment0292757Field004Chars00 ++ tail)) fragment0292757Acc00400 =
      SourceJson.object (fuel + 407) (SourceJson.white tail) fragment0292757Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_004"
  err.flush

noncomputable def fragment0292757Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0292757Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '0', '8', '3', '5', '6', '0', '9', '2', '9', '9', '4', '8', '0', '1', '9', '1', '9', '/', '1', '3', '5', '6', '5', '5', '4', '6', '3', '1', '1', '6', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '6', '9', '0', '1', '7', '8', '8', '2', '8', '7', '2', '1', '7', '4', '9', '1', '0', '1', '/', '3', '3', '2', '3', '5', '5', '8', '8', '4', '6', '3', '4', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '0', '1', '2', '6', '2', '4', '4', '9', '0', '4', '5', '4', '2', '6', '0', '5', '7', '4', '9', '/', '2', '3', '0', '0', '9', '2', '5', '3', '5', '5', '1', '6', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '7', '5', '4', '2', '5', '7', '1', '6', '8', '1', '1', '9', '4', '9', '0', '2', '7', '1', '7', '/', '2', '4', '9', '2', '6', '6', '9', '1', '3', '4', '7', '5', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '7', '8', '2', '0', '6', '0', '8', '4', '3', '8', '9', '5', '4', '0', '2', '2', '7', '9', '9', '/', '8', '7', '9', '7', '6', '5', '5', '7', '6', '9', '7', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '7', '1', '3', '7', '7', '2', '9', '8', '7', '3', '6', '7', '9', '9', '5', '4', '8', '2', '7', '9', '/', '1', '4', '9', '5', '6', '0', '1', '4', '8', '0', '8', '5', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '1', '9', '9', '5', '7', '1', '0', '1', '7', '6', '1', '6', '1', '1', '0', '5', '4', '2', '9', '/', '7', '8', '7', '1', '5', '8', '6', '7', '4', '1', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '4', '8', '0', '5', '8', '2', '2', '8', '4', '1', '4', '5', '2', '5', '7', '0', '8', '6', '7', '1', '/', '1', '4', '9', '5', '6', '0', '1', '4', '8', '0', '8', '5', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '5', '3', '6', '0', '1', '6', '0', '3', '8', '4', '6', '5', '3', '6', '7', '1', '0', '1', '3', '/', '1', '4', '9', '5', '6', '0', '1', '4', '8', '0', '8', '5', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '9', '6', '1', '1', '3', '8', '5', '3', '0', '5', '3', '8', '4', '6', '1', '9', '5', '3', '2', '3', '/', '1', '4', '9', '5', '6', '0', '1', '4', '8', '0', '8', '5', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0292757Acc00600 : List (String × SourceJson) := (fragment0292757Field005Key00, fragment0292757Field005Value00) :: fragment0292757Acc00500
noncomputable def fragment0292757Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '8', '3', '5', '6', '0', '9', '2', '9', '9', '4', '8', '0', '1', '9', '1', '9', '/', '1', '3', '5', '6', '5', '5', '4', '6', '3', '1', '1', '6', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '6', '9', '0', '1', '7', '8', '8', '2', '8', '7', '2', '1', '7', '4', '9', '1', '0', '1', '/', '3', '3', '2', '3', '5', '5', '8', '8', '4', '6', '3', '4', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '0', '1', '2', '6', '2', '4', '4', '9', '0', '4', '5', '4', '2', '6', '0', '5', '7', '4', '9', '/', '2', '3', '0', '0', '9', '2', '5', '3', '5', '5', '1', '6', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '7', '5', '4', '2', '5', '7', '1', '6', '8', '1', '1', '9', '4', '9', '0', '2', '7', '1', '7', '/', '2', '4', '9', '2', '6', '6', '9', '1', '3', '4', '7', '5', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '7', '8', '2', '0', '6', '0', '8', '4', '3', '8', '9', '5', '4', '0', '2', '2', '7', '9', '9', '/', '8', '7', '9', '7', '6', '5', '5', '7', '6', '9', '7', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '7', '1', '3', '7', '7', '2', '9', '8', '7', '3', '6', '7', '9', '9', '5', '4', '8', '2', '7', '9', '/', '1', '4', '9', '5', '6', '0', '1', '4', '8', '0', '8', '5', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '1', '9', '9', '5', '7', '1', '0', '1', '7', '6', '1', '6', '1', '1', '0', '5', '4', '2', '9', '/', '7', '8', '7', '1', '5', '8', '6', '7', '4', '1', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '4', '8', '0', '5', '8', '2', '2', '8', '4', '1', '4', '5', '2', '5', '7', '0', '8', '6', '7', '1', '/', '1', '4', '9', '5', '6', '0', '1', '4', '8', '0', '8', '5', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '5', '3', '6', '0', '1', '6', '0', '3', '8', '4', '6', '5', '3', '6', '7', '1', '0', '1', '3', '/', '1', '4', '9', '5', '6', '0', '1', '4', '8', '0', '8', '5', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '9', '6', '1', '1', '3', '8', '5', '3', '0', '5', '3', '8', '4', '6', '1', '9', '5', '3', '2', '3', '/', '1', '4', '9', '5', '6', '0', '1', '4', '8', '0', '8', '5', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0292757_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0292757Field005Chars00 ++ tail)) fragment0292757Acc00500 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0292757Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_005"
  err.flush

noncomputable def fragment0292757Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0292757Field006Value00 : SourceJson := .str (String.ofList ['8', '9', '2', '5', '1', '2', '0', '5', '3', '7', '7', '7', '7', '2', '9', '8', '4', '3', '7', '5', '7', '5', '9', '2', '2', '3', '9', '1', '4', '3', '6', '9', '9', '7', '0', '2', '3', '5', '0', '5', '1', '7', '8', '4', '5', '5', '9', '0', '3', '5', '4', '0', '0', '0', '0', '0', '/', '1', '2', '9', '5', '0', '3', '5', '0', '9', '0', '5', '6', '8', '6', '9', '0', '6', '8', '1', '1', '7', '7', '8', '1', '7', '9', '2', '4', '2', '6', '5', '9', '7', '8', '0', '4', '7', '3', '5', '1', '1', '3', '5', '4', '3', '3', '0', '7', '6', '2', '3', '5', '8', '1', '8', '2', '9', '8', '4', '7', '7', '0', '3', '2', '7', '1', '8', '5', '9'])
noncomputable def fragment0292757Acc00700 : List (String × SourceJson) := (fragment0292757Field006Key00, fragment0292757Field006Value00) :: fragment0292757Acc00600
noncomputable def fragment0292757Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '9', '2', '5', '1', '2', '0', '5', '3', '7', '7', '7', '7', '2', '9', '8', '4', '3', '7', '5', '7', '5', '9', '2', '2', '3', '9', '1', '4', '3', '6', '9', '9', '7', '0', '2', '3', '5', '0', '5', '1', '7', '8', '4', '5', '5', '9', '0', '3', '5', '4', '0', '0', '0', '0', '0', '/', '1', '2', '9', '5', '0', '3', '5', '0', '9', '0', '5', '6', '8', '6', '9', '0', '6', '8', '1', '1', '7', '7', '8', '1', '7', '9', '2', '4', '2', '6', '5', '9', '7', '8', '0', '4', '7', '3', '5', '1', '1', '3', '5', '4', '3', '3', '0', '7', '6', '2', '3', '5', '8', '1', '8', '2', '9', '8', '4', '7', '7', '0', '3', '2', '7', '1', '8', '5', '9', '"', ',']

theorem object_fragment0292757_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0292757Field006Chars00 ++ tail)) fragment0292757Acc00600 =
      SourceJson.object (fuel + 405) (SourceJson.white tail) fragment0292757Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_006"
  err.flush

noncomputable def fragment0292757Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0292757Field007Value00 : SourceJson := .str (String.ofList ['3', '7', '9', '2', '2', '8', '6', '5', '6', '6', '7', '3', '4', '7', '0', '4', '9', '4', '5', '0', '8', '7', '5', '7', '4', '4', '1', '6', '8', '4', '6', '1', '2', '6', '6', '0', '7', '0', '5', '2', '6', '4', '7', '5', '2', '5', '4', '2', '0', '7', '9', '7', '0', '7', '3', '5', '7', '3', '6', '5', '7', '4', '7', '6', '2', '8', '6', '7', '9', '9', '8', '4', '3', '8', '1', '7', '3', '3', '3', '7', '2', '9', '8', '1', '6', '6', '1', '4', '6', '1', '0', '7', '9', '0', '3', '8', '5', '9', '0', '3', '6', '1', '1', '3', '0', '4', '3', '0', '1', '1', '4', '6', '6', '7', '1', '0', '7', '0', '9', '4', '4', '1', '6', '6', '8', '0', '4', '0', '1', '1', '3', '2', '9', '2', '7', '5', '5', '6', '8', '7', '2', '2', '5', '4', '9', '0', '7', '7', '4', '6', '1', '4', '7', '7', '9', '5', '7', '5', '3', '3', '0', '4', '4', '6', '8', '4', '8', '7', '9', '4', '0', '3', '4', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '1', '2', '8', '8', '6', '3', '1', '8', '8', '8', '0', '8', '3', '9', '7', '0', '1', '5', '4', '2', '2', '3', '2', '3', '2', '4', '1', '3', '0', '3', '7', '5', '4', '5', '7', '4', '3', '9', '1', '8', '5', '6', '9', '7', '4', '7', '3', '2', '4', '5', '5', '6', '5', '5', '1', '3', '5', '9', '1', '2', '9', '5', '9', '2', '0', '3', '0', '0', '9', '3', '0', '7', '0', '7', '7', '4', '8', '0', '1', '2', '2', '2', '6', '1', '1', '7', '1', '9', '9', '7', '4', '1', '0', '8', '1', '3', '2', '5', '9', '3', '6', '2', '8', '3', '2', '8', '2', '8', '5', '5', '0', '4', '8', '2', '4', '2', '4', '0', '1', '8', '9', '1', '8', '7', '2', '5', '2', '3', '5', '3', '5', '0', '2', '8', '7', '4', '1', '9', '5', '8', '5', '4', '1', '2', '2', '0', '9', '5', '4', '4', '0', '1', '1', '5', '7', '8', '8', '5', '9', '6', '4', '9', '5', '2', '2', '7', '4', '7', '3', '5', '8', '2', '6', '6', '9', '1', '3', '9', '2', '3', '4', '0', '2', '8', '7', '0', '6', '7', '5', '2', '3', '5', '3', '7', '6', '5', '8', '6', '0', '9', '6', '9', '7', '7', '1'])
noncomputable def fragment0292757Acc00800 : List (String × SourceJson) := (fragment0292757Field007Key00, fragment0292757Field007Value00) :: fragment0292757Acc00700
noncomputable def fragment0292757Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '7', '9', '2', '2', '8', '6', '5', '6', '6', '7', '3', '4', '7', '0', '4', '9', '4', '5', '0', '8', '7', '5', '7', '4', '4', '1', '6', '8', '4', '6', '1', '2', '6', '6', '0', '7', '0', '5', '2', '6', '4', '7', '5', '2', '5', '4', '2', '0', '7', '9', '7', '0', '7', '3', '5', '7', '3', '6', '5', '7', '4', '7', '6', '2', '8', '6', '7', '9', '9', '8', '4', '3', '8', '1', '7', '3', '3', '3', '7', '2', '9', '8', '1', '6', '6', '1', '4', '6', '1', '0', '7', '9', '0', '3', '8', '5', '9', '0', '3', '6', '1', '1', '3', '0', '4', '3', '0', '1', '1', '4', '6', '6', '7', '1', '0', '7', '0', '9', '4', '4', '1', '6', '6', '8', '0', '4', '0', '1', '1', '3', '2', '9', '2', '7', '5', '5', '6', '8', '7', '2', '2', '5', '4', '9', '0', '7', '7', '4', '6', '1', '4', '7', '7', '9', '5', '7', '5', '3', '3', '0', '4', '4', '6', '8', '4', '8', '7', '9', '4', '0', '3', '4', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '1', '2', '8', '8', '6', '3', '1', '8', '8', '8', '0', '8', '3', '9', '7', '0', '1', '5', '4', '2', '2', '3', '2', '3', '2', '4', '1', '3', '0', '3', '7', '5', '4', '5', '7', '4', '3', '9', '1', '8', '5', '6', '9', '7', '4', '7', '3', '2', '4', '5', '5', '6', '5', '5', '1', '3', '5', '9', '1', '2', '9', '5', '9', '2', '0', '3', '0', '0', '9', '3', '0', '7', '0', '7', '7', '4', '8', '0', '1', '2', '2', '2', '6', '1', '1', '7', '1', '9', '9', '7', '4', '1', '0', '8', '1', '3', '2', '5', '9', '3', '6', '2', '8', '3', '2', '8', '2', '8', '5', '5', '0', '4', '8', '2', '4', '2', '4', '0', '1', '8', '9', '1', '8', '7', '2', '5', '2', '3', '5', '3', '5', '0', '2', '8', '7', '4', '1', '9', '5', '8', '5', '4', '1', '2', '2', '0', '9', '5', '4', '4', '0', '1', '1', '5', '7', '8', '8', '5', '9', '6', '4', '9', '5', '2', '2', '7', '4', '7', '3', '5', '8', '2', '6', '6', '9', '1', '3', '9', '2', '3', '4', '0', '2', '8', '7', '0', '6', '7', '5', '2', '3', '5', '3', '7', '6', '5', '8', '6', '0', '9', '6', '9', '7', '7', '1', '"', ',']

theorem object_fragment0292757_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0292757Field007Chars00 ++ tail)) fragment0292757Acc00700 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0292757Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_007"
  err.flush

noncomputable def fragment0292757Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0292757Field008Value00 : SourceJson := .str (String.ofList ['5', '4', '6', '0', '2', '4', '5', '0', '9', '7', '4', '1', '9', '7', '0', '8', '3'])
noncomputable def fragment0292757Acc00900 : List (String × SourceJson) := (fragment0292757Field008Key00, fragment0292757Field008Value00) :: fragment0292757Acc00800
noncomputable def fragment0292757Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '4', '6', '0', '2', '4', '5', '0', '9', '7', '4', '1', '9', '7', '0', '8', '3', '"', ',']

theorem object_fragment0292757_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0292757Field008Chars00 ++ tail)) fragment0292757Acc00800 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0292757Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_008"
  err.flush

noncomputable def fragment0292757Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0292757Field009Value00 : SourceJson := .str (String.ofList ['4', '9', '0', '2', '3', '1', '0', '3', '8', '2', '1', '0', '4', '2', '3', '5', '3', '9'])
noncomputable def fragment0292757Acc01000 : List (String × SourceJson) := (fragment0292757Field009Key00, fragment0292757Field009Value00) :: fragment0292757Acc00900
noncomputable def fragment0292757Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '0', '2', '3', '1', '0', '3', '8', '2', '1', '0', '4', '2', '3', '5', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0292757_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0292757Field009Chars00 ++ tail)) fragment0292757Acc00900 =
      .ok (.obj (fragment0292757Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0292757_object_field_009"
  err.flush

noncomputable def fragment0292757Chars : List Char := '{' :: (fragment0292757Field000Chars00 ++ fragment0292757Field001Chars00 ++ fragment0292757Field002Chars00 ++ fragment0292757Field003Chars00 ++ fragment0292757Field004Chars00 ++ fragment0292757Field005Chars00 ++ fragment0292757Field006Chars00 ++ fragment0292757Field007Chars00 ++ fragment0292757Field008Chars00 ++ fragment0292757Field009Chars00)
noncomputable def fragment0292757Value : SourceJson := .obj (fragment0292757Acc01000.reverse)

theorem value_fragment0292757 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 413) (fragment0292757Chars ++ tail) =
      .ok (fragment0292757Value, tail) := by
  have hinput : fragment0292757Chars ++ tail = '{' :: (fragment0292757Field000Chars00 ++ (fragment0292757Field001Chars00 ++ (fragment0292757Field002Chars00 ++ (fragment0292757Field003Chars00 ++ (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0292757Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 413) (fragment0292757Chars ++ tail) =
        SourceJson.value (fuel + 413) ('{' :: (fragment0292757Field000Chars00 ++ (fragment0292757Field001Chars00 ++ (fragment0292757Field002Chars00 ++ (fragment0292757Field003Chars00 ++ (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 413)) hinput
    _ = SourceJson.object (fuel + 412) (SourceJson.white (fragment0292757Field000Chars00 ++ (fragment0292757Field001Chars00 ++ (fragment0292757Field002Chars00 ++ (fragment0292757Field003Chars00 ++ (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))))))))))) fragment0292757Acc00000 := by rfl
    _ = SourceJson.object (fuel + 411) (SourceJson.white (fragment0292757Field001Chars00 ++ (fragment0292757Field002Chars00 ++ (fragment0292757Field003Chars00 ++ (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail))))))))))) fragment0292757Acc00100 := object_fragment0292757_field_000 fuel (fragment0292757Field001Chars00 ++ (fragment0292757Field002Chars00 ++ (fragment0292757Field003Chars00 ++ (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 410) (SourceJson.white (fragment0292757Field002Chars00 ++ (fragment0292757Field003Chars00 ++ (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))))))))) fragment0292757Acc00200 := object_fragment0292757_field_001 fuel (fragment0292757Field002Chars00 ++ (fragment0292757Field003Chars00 ++ (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 409) (SourceJson.white (fragment0292757Field003Chars00 ++ (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail))))))))) fragment0292757Acc00300 := object_fragment0292757_field_002 fuel (fragment0292757Field003Chars00 ++ (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 408) (SourceJson.white (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))))))) fragment0292757Acc00400 := object_fragment0292757_field_003 fuel (fragment0292757Field004Chars00 ++ (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail))))))) fragment0292757Acc00500 := object_fragment0292757_field_004 fuel (fragment0292757Field005Chars00 ++ (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))))) fragment0292757Acc00600 := object_fragment0292757_field_005 fuel (fragment0292757Field006Chars00 ++ (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail))))) fragment0292757Acc00700 := object_fragment0292757_field_006 fuel (fragment0292757Field007Chars00 ++ (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))) fragment0292757Acc00800 := object_fragment0292757_field_007 fuel (fragment0292757Field008Chars00 ++ (fragment0292757Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0292757Field009Chars00 ++ (tail))) fragment0292757Acc00900 := object_fragment0292757_field_008 fuel (fragment0292757Field009Chars00 ++ (tail))
    _ = .ok (fragment0292757Value, tail) := object_fragment0292757_field_009 fuel (tail)

noncomputable def fragment0294743Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0294743Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0294743Field000Value00 : SourceJson := .number (String.ofList ['4', '1'])
noncomputable def fragment0294743Acc00100 : List (String × SourceJson) := (fragment0294743Field000Key00, fragment0294743Field000Value00) :: fragment0294743Acc00000
noncomputable def fragment0294743Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '1', ',']

theorem object_fragment0294743_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0294743Field000Chars00 ++ tail)) fragment0294743Acc00000 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0294743Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_000"
  err.flush

noncomputable def fragment0294743Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0294743Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0294743Acc00200 : List (String × SourceJson) := (fragment0294743Field001Key00, fragment0294743Field001Value00) :: fragment0294743Acc00100
noncomputable def fragment0294743Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0294743_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0294743Field001Chars00 ++ tail)) fragment0294743Acc00100 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0294743Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_001"
  err.flush

noncomputable def fragment0294743Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0294743Field002Value00 : SourceJson := .str (String.ofList ['8', '9', '0', '6', '2', '5', '1', '4', '8', '8', '3', '4', '8', '8', '1', '2', '1', '9', '9', '4', '2', '2', '5', '1', '2', '6', '1', '5', '4', '6', '9', '0', '3', '9', '8', '7', '8', '4', '7', '8', '4', '8', '7', '4', '3', '7', '/', '3', '4', '5', '9', '2', '0', '3', '4', '8', '8', '0', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0294743Acc00300 : List (String × SourceJson) := (fragment0294743Field002Key00, fragment0294743Field002Value00) :: fragment0294743Acc00200
noncomputable def fragment0294743Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '9', '0', '6', '2', '5', '1', '4', '8', '8', '3', '4', '8', '8', '1', '2', '1', '9', '9', '4', '2', '2', '5', '1', '2', '6', '1', '5', '4', '6', '9', '0', '3', '9', '8', '7', '8', '4', '7', '8', '4', '8', '7', '4', '3', '7', '/', '3', '4', '5', '9', '2', '0', '3', '4', '8', '8', '0', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0294743_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0294743Field002Chars00 ++ tail)) fragment0294743Acc00200 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0294743Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_002"
  err.flush

noncomputable def fragment0294743Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0294743Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0294743Acc00400 : List (String × SourceJson) := (fragment0294743Field003Key00, fragment0294743Field003Value00) :: fragment0294743Acc00300
noncomputable def fragment0294743Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0294743_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0294743Field003Chars00 ++ tail)) fragment0294743Acc00300 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0294743Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_003"
  err.flush

noncomputable def fragment0294743Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0294743Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0294743Acc00500 : List (String × SourceJson) := (fragment0294743Field004Key00, fragment0294743Field004Value00) :: fragment0294743Acc00400
noncomputable def fragment0294743Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0294743_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0294743Field004Chars00 ++ tail)) fragment0294743Acc00400 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0294743Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_004"
  err.flush

noncomputable def fragment0294743Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0294743Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '6', '3', '9', '3', '1', '9', '1', '0', '1', '4', '5', '3', '/', '3', '2', '5', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '7', '1', '4', '6', '2', '6', '6', '1', '4', '0', '5', '1', '/', '2', '2', '7', '5', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '4', '4', '3', '6', '5', '5', '1', '3', '9', '5', '3', '/', '1', '5', '7', '5', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '3', '5', '3', '2', '3', '7', '9', '0', '6', '3', '5', '9', '/', '3', '4', '1', '3', '0', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '1', '2', '3', '3', '4', '2', '5', '5', '3', '8', '8', '1', '/', '2', '0', '4', '7', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '1', '4', '9', '5', '2', '7', '5', '9', '6', '0', '6', '3', '/', '2', '0', '4', '7', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '0', '6', '1', '8', '9', '4', '5', '1', '7', '9', '1', '/', '1', '0', '7', '7', '8', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '7', '2', '4', '1', '2', '6', '1', '1', '0', '2', '0', '9', '/', '2', '0', '4', '7', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '0', '1', '8', '5', '6', '9', '1', '1', '5', '1', '8', '7', '/', '2', '0', '4', '7', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '2', '8', '1', '9', '6', '8', '6', '7', '3', '1', '/', '8', '1', '9', '1', '3', '1', '0', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0294743Acc00600 : List (String × SourceJson) := (fragment0294743Field005Key00, fragment0294743Field005Value00) :: fragment0294743Acc00500
noncomputable def fragment0294743Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '9', '3', '1', '9', '1', '0', '1', '4', '5', '3', '/', '3', '2', '5', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '1', '4', '6', '2', '6', '6', '1', '4', '0', '5', '1', '/', '2', '2', '7', '5', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '4', '4', '3', '6', '5', '5', '1', '3', '9', '5', '3', '/', '1', '5', '7', '5', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '3', '5', '3', '2', '3', '7', '9', '0', '6', '3', '5', '9', '/', '3', '4', '1', '3', '0', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '1', '2', '3', '3', '4', '2', '5', '5', '3', '8', '8', '1', '/', '2', '0', '4', '7', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '1', '4', '9', '5', '2', '7', '5', '9', '6', '0', '6', '3', '/', '2', '0', '4', '7', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '0', '6', '1', '8', '9', '4', '5', '1', '7', '9', '1', '/', '1', '0', '7', '7', '8', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '2', '4', '1', '2', '6', '1', '1', '0', '2', '0', '9', '/', '2', '0', '4', '7', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '0', '1', '8', '5', '6', '9', '1', '1', '5', '1', '8', '7', '/', '2', '0', '4', '7', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '8', '2', '8', '1', '9', '6', '8', '6', '7', '3', '1', '/', '8', '1', '9', '1', '3', '1', '0', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0294743_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0294743Field005Chars00 ++ tail)) fragment0294743Acc00500 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0294743Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_005"
  err.flush

noncomputable def fragment0294743Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0294743Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '0', '1', '9', '5', '1', '9', '7', '1', '6', '5', '0', '3', '0', '2', '7', '6', '7', '9', '0', '5', '1', '7', '2', '6', '8', '7', '0', '8', '5', '7', '4', '4', '1', '2', '8', '5', '6', '1', '1', '9', '6', '0', '1', '5', '3', '2', '6', '1', '4', '1', '0', '4', '0', '0', '0', '0', '/', '1', '0', '7', '5', '9', '0', '9', '7', '7', '5', '9', '3', '6', '1', '3', '3', '6', '7', '6', '6', '4', '6', '3', '4', '6', '3', '1', '0', '0', '9', '0', '8', '6', '9', '6', '5', '1', '1', '0', '3', '8', '3', '2', '5', '8', '6', '4', '4', '1', '5', '3', '7', '0', '9', '3', '3', '3', '3', '7', '8', '6', '6', '2', '8', '2', '2', '0', '5', '3', '1'])
noncomputable def fragment0294743Acc00700 : List (String × SourceJson) := (fragment0294743Field006Key00, fragment0294743Field006Value00) :: fragment0294743Acc00600
noncomputable def fragment0294743Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '0', '1', '9', '5', '1', '9', '7', '1', '6', '5', '0', '3', '0', '2', '7', '6', '7', '9', '0', '5', '1', '7', '2', '6', '8', '7', '0', '8', '5', '7', '4', '4', '1', '2', '8', '5', '6', '1', '1', '9', '6', '0', '1', '5', '3', '2', '6', '1', '4', '1', '0', '4', '0', '0', '0', '0', '/', '1', '0', '7', '5', '9', '0', '9', '7', '7', '5', '9', '3', '6', '1', '3', '3', '6', '7', '6', '6', '4', '6', '3', '4', '6', '3', '1', '0', '0', '9', '0', '8', '6', '9', '6', '5', '1', '1', '0', '3', '8', '3', '2', '5', '8', '6', '4', '4', '1', '5', '3', '7', '0', '9', '3', '3', '3', '3', '7', '8', '6', '6', '2', '8', '2', '2', '0', '5', '3', '1', '"', ',']

theorem object_fragment0294743_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0294743Field006Chars00 ++ tail)) fragment0294743Acc00600 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0294743Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_006"
  err.flush

noncomputable def fragment0294743Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0294743Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '1', '5', '8', '5', '1', '8', '2', '5', '7', '0', '8', '4', '2', '6', '9', '8', '0', '7', '0', '5', '7', '9', '9', '8', '4', '9', '2', '7', '2', '3', '4', '8', '7', '8', '4', '9', '7', '9', '2', '5', '9', '4', '1', '7', '4', '3', '8', '4', '8', '8', '8', '6', '4', '9', '5', '0', '3', '2', '0', '2', '2', '4', '5', '9', '0', '9', '1', '0', '6', '3', '7', '9', '0', '2', '6', '6', '6', '8', '9', '1', '9', '0', '9', '6', '6', '4', '7', '7', '9', '2', '6', '8', '9', '0', '7', '6', '6', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '6', '1', '3', '3', '5', '1', '6', '0', '8', '1', '6', '9', '4', '8', '0', '4', '2', '9', '8', '1', '6', '4', '3', '1', '1', '8', '6', '8', '6', '2', '2', '9', '6', '4', '9', '2', '0', '6', '5', '5', '0', '5', '7', '5', '8', '7', '8', '1', '5', '0', '0', '5', '4', '1', '4', '3', '9', '1', '4', '7', '9', '9', '4', '2', '4', '0', '6', '2', '4', '9', '3', '0', '1', '1', '2', '3', '4', '2', '0', '0', '5', '4', '1', '2', '6', '7', '0', '7', '5', '9', '4', '1', '7', '6', '2', '0', '7', '1', '0', '2', '4', '6', '4', '1', '4', '0', '4', '4', '2', '8', '4', '0', '4', '8', '1', '8', '4', '4', '4', '3', '6', '3', '6', '9', '0', '7', '3', '0', '8', '6', '3'])
noncomputable def fragment0294743Acc00800 : List (String × SourceJson) := (fragment0294743Field007Key00, fragment0294743Field007Value00) :: fragment0294743Acc00700
noncomputable def fragment0294743Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '1', '5', '8', '5', '1', '8', '2', '5', '7', '0', '8', '4', '2', '6', '9', '8', '0', '7', '0', '5', '7', '9', '9', '8', '4', '9', '2', '7', '2', '3', '4', '8', '7', '8', '4', '9', '7', '9', '2', '5', '9', '4', '1', '7', '4', '3', '8', '4', '8', '8', '8', '6', '4', '9', '5', '0', '3', '2', '0', '2', '2', '4', '5', '9', '0', '9', '1', '0', '6', '3', '7', '9', '0', '2', '6', '6', '6', '8', '9', '1', '9', '0', '9', '6', '6', '4', '7', '7', '9', '2', '6', '8', '9', '0', '7', '6', '6', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '6', '1', '3', '3', '5', '1', '6', '0', '8', '1', '6', '9', '4', '8', '0', '4', '2', '9', '8', '1', '6', '4', '3', '1', '1', '8', '6', '8', '6', '2', '2', '9', '6', '4', '9', '2', '0', '6', '5', '5', '0', '5', '7', '5', '8', '7', '8', '1', '5', '0', '0', '5', '4', '1', '4', '3', '9', '1', '4', '7', '9', '9', '4', '2', '4', '0', '6', '2', '4', '9', '3', '0', '1', '1', '2', '3', '4', '2', '0', '0', '5', '4', '1', '2', '6', '7', '0', '7', '5', '9', '4', '1', '7', '6', '2', '0', '7', '1', '0', '2', '4', '6', '4', '1', '4', '0', '4', '4', '2', '8', '4', '0', '4', '8', '1', '8', '4', '4', '4', '3', '6', '3', '6', '9', '0', '7', '3', '0', '8', '6', '3', '"', ',']

theorem object_fragment0294743_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0294743Field007Chars00 ++ tail)) fragment0294743Acc00700 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0294743Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_007"
  err.flush

noncomputable def fragment0294743Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0294743Field008Value00 : SourceJson := .str (String.ofList ['8', '1', '1', '4', '5', '8', '6', '5', '4', '2', '9', '8', '9', '7', '0', '5', '4'])
noncomputable def fragment0294743Acc00900 : List (String × SourceJson) := (fragment0294743Field008Key00, fragment0294743Field008Value00) :: fragment0294743Acc00800
noncomputable def fragment0294743Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '1', '1', '4', '5', '8', '6', '5', '4', '2', '9', '8', '9', '7', '0', '5', '4', '"', ',']

theorem object_fragment0294743_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0294743Field008Chars00 ++ tail)) fragment0294743Acc00800 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0294743Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_008"
  err.flush

noncomputable def fragment0294743Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0294743Field009Value00 : SourceJson := .str (String.ofList ['7', '2', '6', '8', '4', '0', '4', '8', '9', '5', '0', '0', '1', '2', '9', '5', '2', '0'])
noncomputable def fragment0294743Acc01000 : List (String × SourceJson) := (fragment0294743Field009Key00, fragment0294743Field009Value00) :: fragment0294743Acc00900
noncomputable def fragment0294743Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '2', '6', '8', '4', '0', '4', '8', '9', '5', '0', '0', '1', '2', '9', '5', '2', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0294743_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0294743Field009Chars00 ++ tail)) fragment0294743Acc00900 =
      .ok (.obj (fragment0294743Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0294743_object_field_009"
  err.flush

noncomputable def fragment0294743Chars : List Char := '{' :: (fragment0294743Field000Chars00 ++ fragment0294743Field001Chars00 ++ fragment0294743Field002Chars00 ++ fragment0294743Field003Chars00 ++ fragment0294743Field004Chars00 ++ fragment0294743Field005Chars00 ++ fragment0294743Field006Chars00 ++ fragment0294743Field007Chars00 ++ fragment0294743Field008Chars00 ++ fragment0294743Field009Chars00)
noncomputable def fragment0294743Value : SourceJson := .obj (fragment0294743Acc01000.reverse)

theorem value_fragment0294743 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 267) (fragment0294743Chars ++ tail) =
      .ok (fragment0294743Value, tail) := by
  have hinput : fragment0294743Chars ++ tail = '{' :: (fragment0294743Field000Chars00 ++ (fragment0294743Field001Chars00 ++ (fragment0294743Field002Chars00 ++ (fragment0294743Field003Chars00 ++ (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0294743Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 267) (fragment0294743Chars ++ tail) =
        SourceJson.value (fuel + 267) ('{' :: (fragment0294743Field000Chars00 ++ (fragment0294743Field001Chars00 ++ (fragment0294743Field002Chars00 ++ (fragment0294743Field003Chars00 ++ (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 267)) hinput
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0294743Field000Chars00 ++ (fragment0294743Field001Chars00 ++ (fragment0294743Field002Chars00 ++ (fragment0294743Field003Chars00 ++ (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))))))))))) fragment0294743Acc00000 := by rfl
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0294743Field001Chars00 ++ (fragment0294743Field002Chars00 ++ (fragment0294743Field003Chars00 ++ (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail))))))))))) fragment0294743Acc00100 := object_fragment0294743_field_000 fuel (fragment0294743Field001Chars00 ++ (fragment0294743Field002Chars00 ++ (fragment0294743Field003Chars00 ++ (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0294743Field002Chars00 ++ (fragment0294743Field003Chars00 ++ (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))))))))) fragment0294743Acc00200 := object_fragment0294743_field_001 fuel (fragment0294743Field002Chars00 ++ (fragment0294743Field003Chars00 ++ (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0294743Field003Chars00 ++ (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail))))))))) fragment0294743Acc00300 := object_fragment0294743_field_002 fuel (fragment0294743Field003Chars00 ++ (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))))))) fragment0294743Acc00400 := object_fragment0294743_field_003 fuel (fragment0294743Field004Chars00 ++ (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail))))))) fragment0294743Acc00500 := object_fragment0294743_field_004 fuel (fragment0294743Field005Chars00 ++ (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))))) fragment0294743Acc00600 := object_fragment0294743_field_005 fuel (fragment0294743Field006Chars00 ++ (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail))))) fragment0294743Acc00700 := object_fragment0294743_field_006 fuel (fragment0294743Field007Chars00 ++ (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))) fragment0294743Acc00800 := object_fragment0294743_field_007 fuel (fragment0294743Field008Chars00 ++ (fragment0294743Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0294743Field009Chars00 ++ (tail))) fragment0294743Acc00900 := object_fragment0294743_field_008 fuel (fragment0294743Field009Chars00 ++ (tail))
    _ = .ok (fragment0294743Value, tail) := object_fragment0294743_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_before_reader"
  err.flush

noncomputable def chunk0040LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0040SuffixChars00 : List Char := [',']
noncomputable def chunk0040Chars00 : List Char := chunk0040LeadChars00 ++ fragment0292757Chars ++ chunk0040SuffixChars00
noncomputable def chunk0040Push00 (acc : List SourceJson) : List SourceJson := fragment0292757Value :: acc

noncomputable def chunk0040AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0040_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 564)
      (SourceJson.white (chunk0040LeadChars00 ++ (fragment0292757Chars ++ rest))) acc =
      (SourceJson.value (fuel + 563) (fragment0292757Chars ++ rest)).bind
        (chunk0040AfterValue00 (fuel + 563) acc) := by rfl

theorem array_chunk0040 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 564) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 563) (SourceJson.white tail) (chunk0040Push00 acc) := by
  have hinput : chunk0040Chars00 ++ tail = chunk0040LeadChars00 ++ (fragment0292757Chars ++ (chunk0040SuffixChars00 ++ tail)) := by
    simp only [chunk0040Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 564) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 564)
          (SourceJson.white (chunk0040LeadChars00 ++ (fragment0292757Chars ++ (chunk0040SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 564) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 563) (fragment0292757Chars ++ (chunk0040SuffixChars00 ++ tail))).bind
        (chunk0040AfterValue00 (fuel + 563) acc) := array_chunk0040_head fuel (chunk0040SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0292757Value, chunk0040SuffixChars00 ++ tail)).bind
        (chunk0040AfterValue00 (fuel + 563) acc) :=
      congrArg (fun result => result.bind (chunk0040AfterValue00 (fuel + 563) acc))
        (value_fragment0292757 (fuel + 150) (chunk0040SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 563) (SourceJson.white tail) (chunk0040Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_before_reader"
  err.flush

noncomputable def chunk0041LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0041SuffixChars00 : List Char := [',']
noncomputable def chunk0041Chars00 : List Char := chunk0041LeadChars00 ++ fragment0294743Chars ++ chunk0041SuffixChars00
noncomputable def chunk0041Push00 (acc : List SourceJson) : List SourceJson := fragment0294743Value :: acc

noncomputable def chunk0041AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0041_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 563)
      (SourceJson.white (chunk0041LeadChars00 ++ (fragment0294743Chars ++ rest))) acc =
      (SourceJson.value (fuel + 562) (fragment0294743Chars ++ rest)).bind
        (chunk0041AfterValue00 (fuel + 562) acc) := by rfl

theorem array_chunk0041 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 563) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 562) (SourceJson.white tail) (chunk0041Push00 acc) := by
  have hinput : chunk0041Chars00 ++ tail = chunk0041LeadChars00 ++ (fragment0294743Chars ++ (chunk0041SuffixChars00 ++ tail)) := by
    simp only [chunk0041Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 563) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 563)
          (SourceJson.white (chunk0041LeadChars00 ++ (fragment0294743Chars ++ (chunk0041SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 563) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 562) (fragment0294743Chars ++ (chunk0041SuffixChars00 ++ tail))).bind
        (chunk0041AfterValue00 (fuel + 562) acc) := array_chunk0041_head fuel (chunk0041SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0294743Value, chunk0041SuffixChars00 ++ tail)).bind
        (chunk0041AfterValue00 (fuel + 562) acc) :=
      congrArg (fun result => result.bind (chunk0041AfterValue00 (fuel + 562) acc))
        (value_fragment0294743 (fuel + 295) (chunk0041SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 562) (SourceJson.white tail) (chunk0041Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0040Chars00 ++ chunk0041Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0041Push00 (chunk0040Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 564) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 562) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0040Chars00 ++ (chunk0041Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 564) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 564) (SourceJson.white (chunk0040Chars00 ++ (chunk0041Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 564) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 563) (SourceJson.white (chunk0041Chars00 ++ (tail))) (chunk0040Push00 (acc)) := array_chunk0040 fuel (chunk0041Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 562) (SourceJson.white tail) (blockPush acc) := array_chunk0041 fuel (tail) (chunk0040Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 292751).take 3682 = blockChars := by rfl

theorem block_original_split : sourceRest 292751 = blockChars ++ sourceRest 296433 := by
  calc
    sourceRest 292751 = (sourceRest 292751).take 3682 ++ (sourceRest 292751).drop 3682 :=
      (List.take_append_drop 3682 (sourceRest 292751)).symm
    _ = blockChars ++ (sourceRest 292751).drop 3682 :=
      congrArg (fun part => part ++ (sourceRest 292751).drop 3682) block_original_prefix
    _ = blockChars ++ sourceRest 296433 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 292751 3682)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 564) (SourceJson.white (sourceRest 292751)) acc =
      SourceJson.array (fuel + 562) (SourceJson.white (sourceRest 296433)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 564) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 296433) acc)

#print axioms object_fragment0292757_field_000
#print axioms object_fragment0292757_field_001
#print axioms object_fragment0292757_field_002
#print axioms object_fragment0292757_field_003
#print axioms object_fragment0292757_field_004
#print axioms object_fragment0292757_field_005
#print axioms object_fragment0292757_field_006
#print axioms object_fragment0292757_field_007
#print axioms object_fragment0292757_field_008
#print axioms object_fragment0292757_field_009
#print axioms value_fragment0292757
#print axioms object_fragment0294743_field_000
#print axioms object_fragment0294743_field_001
#print axioms object_fragment0294743_field_002
#print axioms object_fragment0294743_field_003
#print axioms object_fragment0294743_field_004
#print axioms object_fragment0294743_field_005
#print axioms object_fragment0294743_field_006
#print axioms object_fragment0294743_field_007
#print axioms object_fragment0294743_field_008
#print axioms object_fragment0294743_field_009
#print axioms value_fragment0294743
#print axioms array_chunk0040_head
#print axioms array_chunk0040
#print axioms array_chunk0041_head
#print axioms array_chunk0041
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock020

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
