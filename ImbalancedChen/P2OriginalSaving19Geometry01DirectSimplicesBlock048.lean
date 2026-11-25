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

namespace SimplicesBlock048

noncomputable def fragment0386640Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0386640Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0386640Field000Value00 : SourceJson := .number (String.ofList ['9', '4'])
noncomputable def fragment0386640Acc00100 : List (String × SourceJson) := (fragment0386640Field000Key00, fragment0386640Field000Value00) :: fragment0386640Acc00000
noncomputable def fragment0386640Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '4', ',']

theorem object_fragment0386640_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0386640Field000Chars00 ++ tail)) fragment0386640Acc00000 =
      SourceJson.object (fuel + 436) (SourceJson.white tail) fragment0386640Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_000"
  err.flush

noncomputable def fragment0386640Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0386640Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '5']), .number (String.ofList ['0'])]
noncomputable def fragment0386640Acc00200 : List (String × SourceJson) := (fragment0386640Field001Key00, fragment0386640Field001Value00) :: fragment0386640Acc00100
noncomputable def fragment0386640Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0386640_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0386640Field001Chars00 ++ tail)) fragment0386640Acc00100 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0386640Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_001"
  err.flush

noncomputable def fragment0386640Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0386640Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '5', '9', '1', '4', '6', '9', '2', '4', '8', '9', '8', '9', '2', '4', '8', '5', '6', '7', '3', '9', '9', '4', '6', '7', '4', '1', '8', '2', '5', '4', '4', '4', '4', '2', '8', '8', '0', '9', '5', '7', '/', '1', '8', '6', '6', '1', '0', '4', '6', '1', '8', '2', '0', '1', '0', '8', '9', '7', '3', '0', '1', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0386640Acc00300 : List (String × SourceJson) := (fragment0386640Field002Key00, fragment0386640Field002Value00) :: fragment0386640Acc00200
noncomputable def fragment0386640Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '3', '5', '9', '1', '4', '6', '9', '2', '4', '8', '9', '8', '9', '2', '4', '8', '5', '6', '7', '3', '9', '9', '4', '6', '7', '4', '1', '8', '2', '5', '4', '4', '4', '4', '2', '8', '8', '0', '9', '5', '7', '/', '1', '8', '6', '6', '1', '0', '4', '6', '1', '8', '2', '0', '1', '0', '8', '9', '7', '3', '0', '1', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0386640_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0386640Field002Chars00 ++ tail)) fragment0386640Acc00200 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0386640Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_002"
  err.flush

noncomputable def fragment0386640Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0386640Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '2', '4', '9', '9', '7', '/', '4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0386640Acc00400 : List (String × SourceJson) := (fragment0386640Field003Key00, fragment0386640Field003Value00) :: fragment0386640Acc00300
noncomputable def fragment0386640Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '2', '4', '9', '9', '7', '/', '4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0386640_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0386640Field003Chars00 ++ tail)) fragment0386640Acc00300 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0386640Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_003"
  err.flush

noncomputable def fragment0386640Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0386640Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0386640Acc00500 : List (String × SourceJson) := (fragment0386640Field004Key00, fragment0386640Field004Value00) :: fragment0386640Acc00400
noncomputable def fragment0386640Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0386640_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0386640Field004Chars00 ++ tail)) fragment0386640Acc00400 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0386640Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_004"
  err.flush

noncomputable def fragment0386640Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0386640Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '7', '7', '9', '9', '7', '1', '6', '4', '9', '8', '7', '4', '4', '2', '8', '2', '9', '0', '4', '4', '7', '/', '6', '2', '3', '2', '6', '1', '3', '3', '8', '6', '1', '5', '9', '2', '8', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '3', '9', '1', '8', '1', '6', '6', '6', '4', '9', '3', '6', '8', '7', '7', '4', '8', '5', '1', '7', '1', '/', '4', '9', '8', '6', '0', '9', '0', '7', '0', '8', '9', '2', '7', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '9', '9', '7', '2', '2', '4', '3', '4', '1', '5', '4', '7', '2', '3', '3', '7', '4', '9', '3', '3', '3', '7', '/', '1', '4', '9', '5', '8', '2', '7', '2', '1', '2', '6', '7', '8', '2', '2', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '8', '6', '0', '6', '1', '5', '6', '6', '8', '1', '3', '4', '4', '2', '3', '3', '7', '1', '1', '0', '1', '/', '4', '9', '8', '6', '0', '9', '0', '7', '0', '8', '9', '2', '7', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '4', '3', '6', '3', '4', '1', '7', '0', '8', '9', '0', '2', '2', '5', '9', '8', '5', '4', '5', '3', '/', '3', '7', '3', '9', '5', '6', '8', '0', '3', '1', '6', '9', '5', '5', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '0', '7', '2', '5', '2', '3', '7', '5', '3', '5', '6', '7', '1', '7', '2', '8', '9', '4', '2', '9', '1', '/', '1', '4', '9', '5', '8', '2', '7', '2', '1', '2', '6', '7', '8', '2', '2', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '4', '3', '9', '0', '8', '2', '3', '8', '0', '5', '1', '9', '1', '6', '1', '9', '9', '5', '1', '/', '1', '5', '7', '4', '5', '5', '4', '9', '6', '0', '7', '1', '3', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '5', '3', '6', '8', '1', '0', '1', '5', '7', '4', '0', '1', '9', '7', '1', '1', '9', '2', '2', '7', '/', '2', '9', '9', '1', '6', '5', '4', '4', '2', '5', '3', '5', '6', '4', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '4', '7', '4', '3', '3', '7', '2', '6', '8', '3', '0', '6', '3', '7', '1', '4', '8', '3', '6', '5', '9', '/', '1', '4', '9', '5', '8', '2', '7', '2', '1', '2', '6', '7', '8', '2', '2', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '5', '7', '6', '4', '1', '2', '2', '1', '5', '2', '8', '5', '7', '8', '2', '7', '0', '1', '3', '0', '1', '/', '3', '7', '3', '9', '5', '6', '8', '0', '3', '1', '6', '9', '5', '5', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0386640Acc00600 : List (String × SourceJson) := (fragment0386640Field005Key00, fragment0386640Field005Value00) :: fragment0386640Acc00500
noncomputable def fragment0386640Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '7', '9', '9', '7', '1', '6', '4', '9', '8', '7', '4', '4', '2', '8', '2', '9', '0', '4', '4', '7', '/', '6', '2', '3', '2', '6', '1', '3', '3', '8', '6', '1', '5', '9', '2', '8', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '3', '9', '1', '8', '1', '6', '6', '6', '4', '9', '3', '6', '8', '7', '7', '4', '8', '5', '1', '7', '1', '/', '4', '9', '8', '6', '0', '9', '0', '7', '0', '8', '9', '2', '7', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '9', '9', '7', '2', '2', '4', '3', '4', '1', '5', '4', '7', '2', '3', '3', '7', '4', '9', '3', '3', '3', '7', '/', '1', '4', '9', '5', '8', '2', '7', '2', '1', '2', '6', '7', '8', '2', '2', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '8', '6', '0', '6', '1', '5', '6', '6', '8', '1', '3', '4', '4', '2', '3', '3', '7', '1', '1', '0', '1', '/', '4', '9', '8', '6', '0', '9', '0', '7', '0', '8', '9', '2', '7', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '4', '3', '6', '3', '4', '1', '7', '0', '8', '9', '0', '2', '2', '5', '9', '8', '5', '4', '5', '3', '/', '3', '7', '3', '9', '5', '6', '8', '0', '3', '1', '6', '9', '5', '5', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '0', '7', '2', '5', '2', '3', '7', '5', '3', '5', '6', '7', '1', '7', '2', '8', '9', '4', '2', '9', '1', '/', '1', '4', '9', '5', '8', '2', '7', '2', '1', '2', '6', '7', '8', '2', '2', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '4', '3', '9', '0', '8', '2', '3', '8', '0', '5', '1', '9', '1', '6', '1', '9', '9', '5', '1', '/', '1', '5', '7', '4', '5', '5', '4', '9', '6', '0', '7', '1', '3', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '5', '3', '6', '8', '1', '0', '1', '5', '7', '4', '0', '1', '9', '7', '1', '1', '9', '2', '2', '7', '/', '2', '9', '9', '1', '6', '5', '4', '4', '2', '5', '3', '5', '6', '4', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '4', '7', '4', '3', '3', '7', '2', '6', '8', '3', '0', '6', '3', '7', '1', '4', '8', '3', '6', '5', '9', '/', '1', '4', '9', '5', '8', '2', '7', '2', '1', '2', '6', '7', '8', '2', '2', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '5', '7', '6', '4', '1', '2', '2', '1', '5', '2', '8', '5', '7', '8', '2', '7', '0', '1', '3', '0', '1', '/', '3', '7', '3', '9', '5', '6', '8', '0', '3', '1', '6', '9', '5', '5', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0386640_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0386640Field005Chars00 ++ tail)) fragment0386640Acc00500 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0386640Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_005"
  err.flush

noncomputable def fragment0386640Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0386640Field006Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '3', '1', '5', '8', '1', '5', '4', '0', '1', '8', '1', '3', '2', '5', '8', '4', '8', '1', '9', '1', '7', '8', '5', '8', '2', '7', '3', '6', '2', '9', '1', '3', '0', '1', '3', '2', '3', '4', '3', '1', '5', '6', '9', '9', '6', '0', '0', '/', '8', '1', '5', '8', '3', '3', '1', '7', '8', '1', '3', '0', '7', '6', '8', '8', '9', '5', '2', '2', '7', '5', '6', '5', '5', '8', '7', '6', '4', '1', '0', '3', '2', '2', '9', '1', '1', '0', '2', '7', '1', '0', '3', '5', '0', '2', '1', '8', '4', '8', '6', '1', '0', '6', '9', '3', '8', '5', '4', '8', '0', '0', '8', '0', '3'])
noncomputable def fragment0386640Acc00700 : List (String × SourceJson) := (fragment0386640Field006Key00, fragment0386640Field006Value00) :: fragment0386640Acc00600
noncomputable def fragment0386640Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '1', '9', '3', '1', '5', '8', '1', '5', '4', '0', '1', '8', '1', '3', '2', '5', '8', '4', '8', '1', '9', '1', '7', '8', '5', '8', '2', '7', '3', '6', '2', '9', '1', '3', '0', '1', '3', '2', '3', '4', '3', '1', '5', '6', '9', '9', '6', '0', '0', '/', '8', '1', '5', '8', '3', '3', '1', '7', '8', '1', '3', '0', '7', '6', '8', '8', '9', '5', '2', '2', '7', '5', '6', '5', '5', '8', '7', '6', '4', '1', '0', '3', '2', '2', '9', '1', '1', '0', '2', '7', '1', '0', '3', '5', '0', '2', '1', '8', '4', '8', '6', '1', '0', '6', '9', '3', '8', '5', '4', '8', '0', '0', '8', '0', '3', '"', ',']

theorem object_fragment0386640_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0386640Field006Chars00 ++ tail)) fragment0386640Acc00600 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0386640Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_006"
  err.flush

noncomputable def fragment0386640Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0386640Field007Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '4', '1', '0', '2', '2', '7', '3', '5', '0', '6', '6', '2', '1', '2', '8', '5', '0', '3', '8', '7', '0', '9', '0', '2', '7', '6', '3', '7', '0', '5', '2', '7', '9', '7', '8', '8', '2', '7', '4', '3', '0', '7', '4', '1', '3', '6', '7', '1', '7', '6', '7', '3', '7', '8', '4', '0', '8', '1', '9', '6', '7', '8', '0', '3', '8', '9', '2', '8', '2', '6', '5', '5', '2', '2', '3', '7', '5', '9', '7', '7', '2', '6', '2', '3', '2', '5', '7', '5', '5', '6', '0', '0', '9', '7', '7', '6', '0', '4', '3', '5', '1', '4', '3', '6', '3', '4', '1', '6', '8', '9', '5', '3', '5', '9', '1', '8', '6', '3', '2', '7', '4', '4', '4', '4', '9', '1', '2', '3', '0', '6', '9', '2', '4', '6', '8', '7', '2', '8', '4', '7', '4', '6', '7', '4', '4', '5', '0', '6', '9', '3', '9', '5', '1', '7', '4', '5', '8', '8', '3', '8', '7', '5', '3', '6', '7', '1', '4', '5', '1', '9', '7', '6', '9', '2', '1', '9', '6', '6', '9', '7', '2', '3', '5', '1', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '3', '7', '4', '3', '0', '5', '9', '3', '1', '1', '1', '0', '9', '9', '7', '4', '5', '2', '6', '6', '7', '2', '7', '2', '1', '2', '6', '5', '8', '3', '9', '1', '2', '6', '1', '2', '0', '5', '1', '8', '9', '3', '4', '9', '3', '6', '9', '2', '7', '3', '1', '7', '4', '1', '3', '5', '8', '4', '1', '7', '1', '1', '4', '8', '0', '1', '4', '8', '5', '4', '0', '8', '2', '9', '1', '6', '5', '0', '1', '0', '2', '1', '6', '7', '3', '6', '3', '6', '8', '1', '8', '6', '6', '3', '5', '4', '4', '1', '2', '0', '7', '4', '7', '8', '5', '6', '8', '5', '6', '1', '1', '9', '2', '7', '4', '4', '8', '5', '8', '8', '3', '2', '6', '4', '2', '3', '4', '3', '1', '5', '6', '6', '0', '5', '6', '7', '4', '3', '1', '2', '6', '3', '1', '4', '5', '7', '4', '2', '3', '0', '2', '0', '9', '2', '6', '8', '3', '9', '0', '1', '1', '8', '8', '6', '0', '9', '9', '3', '1', '1', '4', '4', '6', '4', '4', '7', '4', '3', '2', '1', '2', '1', '1', '8', '2', '0', '2', '4', '5', '4', '8', '1', '8', '0', '6', '3', '1', '7', '2', '7', '0', '1', '0', '5', '4', '9', '4', '7', '5', '4', '2', '6', '7', '0', '1', '2', '0', '9'])
noncomputable def fragment0386640Acc00800 : List (String × SourceJson) := (fragment0386640Field007Key00, fragment0386640Field007Value00) :: fragment0386640Acc00700
noncomputable def fragment0386640Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '4', '4', '1', '0', '2', '2', '7', '3', '5', '0', '6', '6', '2', '1', '2', '8', '5', '0', '3', '8', '7', '0', '9', '0', '2', '7', '6', '3', '7', '0', '5', '2', '7', '9', '7', '8', '8', '2', '7', '4', '3', '0', '7', '4', '1', '3', '6', '7', '1', '7', '6', '7', '3', '7', '8', '4', '0', '8', '1', '9', '6', '7', '8', '0', '3', '8', '9', '2', '8', '2', '6', '5', '5', '2', '2', '3', '7', '5', '9', '7', '7', '2', '6', '2', '3', '2', '5', '7', '5', '5', '6', '0', '0', '9', '7', '7', '6', '0', '4', '3', '5', '1', '4', '3', '6', '3', '4', '1', '6', '8', '9', '5', '3', '5', '9', '1', '8', '6', '3', '2', '7', '4', '4', '4', '4', '9', '1', '2', '3', '0', '6', '9', '2', '4', '6', '8', '7', '2', '8', '4', '7', '4', '6', '7', '4', '4', '5', '0', '6', '9', '3', '9', '5', '1', '7', '4', '5', '8', '8', '3', '8', '7', '5', '3', '6', '7', '1', '4', '5', '1', '9', '7', '6', '9', '2', '1', '9', '6', '6', '9', '7', '2', '3', '5', '1', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '3', '7', '4', '3', '0', '5', '9', '3', '1', '1', '1', '0', '9', '9', '7', '4', '5', '2', '6', '6', '7', '2', '7', '2', '1', '2', '6', '5', '8', '3', '9', '1', '2', '6', '1', '2', '0', '5', '1', '8', '9', '3', '4', '9', '3', '6', '9', '2', '7', '3', '1', '7', '4', '1', '3', '5', '8', '4', '1', '7', '1', '1', '4', '8', '0', '1', '4', '8', '5', '4', '0', '8', '2', '9', '1', '6', '5', '0', '1', '0', '2', '1', '6', '7', '3', '6', '3', '6', '8', '1', '8', '6', '6', '3', '5', '4', '4', '1', '2', '0', '7', '4', '7', '8', '5', '6', '8', '5', '6', '1', '1', '9', '2', '7', '4', '4', '8', '5', '8', '8', '3', '2', '6', '4', '2', '3', '4', '3', '1', '5', '6', '6', '0', '5', '6', '7', '4', '3', '1', '2', '6', '3', '1', '4', '5', '7', '4', '2', '3', '0', '2', '0', '9', '2', '6', '8', '3', '9', '0', '1', '1', '8', '8', '6', '0', '9', '9', '3', '1', '1', '4', '4', '6', '4', '4', '7', '4', '3', '2', '1', '2', '1', '1', '8', '2', '0', '2', '4', '5', '4', '8', '1', '8', '0', '6', '3', '1', '7', '2', '7', '0', '1', '0', '5', '4', '9', '4', '7', '5', '4', '2', '6', '7', '0', '1', '2', '0', '9', '"', ',']

theorem object_fragment0386640_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0386640Field007Chars00 ++ tail)) fragment0386640Acc00700 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0386640Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_007"
  err.flush

noncomputable def fragment0386640Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0386640Field008Value00 : SourceJson := .str (String.ofList ['8', '9', '2', '7', '7', '6', '9', '1', '5', '3', '9', '1', '8', '0'])
noncomputable def fragment0386640Acc00900 : List (String × SourceJson) := (fragment0386640Field008Key00, fragment0386640Field008Value00) :: fragment0386640Acc00800
noncomputable def fragment0386640Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '9', '2', '7', '7', '6', '9', '1', '5', '3', '9', '1', '8', '0', '"', ',']

theorem object_fragment0386640_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0386640Field008Chars00 ++ tail)) fragment0386640Acc00800 =
      SourceJson.object (fuel + 428) (SourceJson.white tail) fragment0386640Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_008"
  err.flush

noncomputable def fragment0386640Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0386640Field009Value00 : SourceJson := .str (String.ofList ['6', '1', '2', '9', '2', '0', '9', '0', '6', '2', '1', '2', '9', '4', '3'])
noncomputable def fragment0386640Acc01000 : List (String × SourceJson) := (fragment0386640Field009Key00, fragment0386640Field009Value00) :: fragment0386640Acc00900
noncomputable def fragment0386640Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '1', '2', '9', '2', '0', '9', '0', '6', '2', '1', '2', '9', '4', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0386640_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 428) (SourceJson.white (fragment0386640Field009Chars00 ++ tail)) fragment0386640Acc00900 =
      .ok (.obj (fragment0386640Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0386640_object_field_009"
  err.flush

noncomputable def fragment0386640Chars : List Char := '{' :: (fragment0386640Field000Chars00 ++ fragment0386640Field001Chars00 ++ fragment0386640Field002Chars00 ++ fragment0386640Field003Chars00 ++ fragment0386640Field004Chars00 ++ fragment0386640Field005Chars00 ++ fragment0386640Field006Chars00 ++ fragment0386640Field007Chars00 ++ fragment0386640Field008Chars00 ++ fragment0386640Field009Chars00)
noncomputable def fragment0386640Value : SourceJson := .obj (fragment0386640Acc01000.reverse)

theorem value_fragment0386640 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 438) (fragment0386640Chars ++ tail) =
      .ok (fragment0386640Value, tail) := by
  have hinput : fragment0386640Chars ++ tail = '{' :: (fragment0386640Field000Chars00 ++ (fragment0386640Field001Chars00 ++ (fragment0386640Field002Chars00 ++ (fragment0386640Field003Chars00 ++ (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0386640Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 438) (fragment0386640Chars ++ tail) =
        SourceJson.value (fuel + 438) ('{' :: (fragment0386640Field000Chars00 ++ (fragment0386640Field001Chars00 ++ (fragment0386640Field002Chars00 ++ (fragment0386640Field003Chars00 ++ (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 438)) hinput
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0386640Field000Chars00 ++ (fragment0386640Field001Chars00 ++ (fragment0386640Field002Chars00 ++ (fragment0386640Field003Chars00 ++ (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))))))))))) fragment0386640Acc00000 := by rfl
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0386640Field001Chars00 ++ (fragment0386640Field002Chars00 ++ (fragment0386640Field003Chars00 ++ (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail))))))))))) fragment0386640Acc00100 := object_fragment0386640_field_000 fuel (fragment0386640Field001Chars00 ++ (fragment0386640Field002Chars00 ++ (fragment0386640Field003Chars00 ++ (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0386640Field002Chars00 ++ (fragment0386640Field003Chars00 ++ (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))))))))) fragment0386640Acc00200 := object_fragment0386640_field_001 fuel (fragment0386640Field002Chars00 ++ (fragment0386640Field003Chars00 ++ (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0386640Field003Chars00 ++ (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail))))))))) fragment0386640Acc00300 := object_fragment0386640_field_002 fuel (fragment0386640Field003Chars00 ++ (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))))))) fragment0386640Acc00400 := object_fragment0386640_field_003 fuel (fragment0386640Field004Chars00 ++ (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail))))))) fragment0386640Acc00500 := object_fragment0386640_field_004 fuel (fragment0386640Field005Chars00 ++ (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))))) fragment0386640Acc00600 := object_fragment0386640_field_005 fuel (fragment0386640Field006Chars00 ++ (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail))))) fragment0386640Acc00700 := object_fragment0386640_field_006 fuel (fragment0386640Field007Chars00 ++ (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))) fragment0386640Acc00800 := object_fragment0386640_field_007 fuel (fragment0386640Field008Chars00 ++ (fragment0386640Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 428) (SourceJson.white (fragment0386640Field009Chars00 ++ (tail))) fragment0386640Acc00900 := object_fragment0386640_field_008 fuel (fragment0386640Field009Chars00 ++ (tail))
    _ = .ok (fragment0386640Value, tail) := object_fragment0386640_field_009 fuel (tail)

noncomputable def fragment0388660Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0388660Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0388660Field000Value00 : SourceJson := .number (String.ofList ['9', '5'])
noncomputable def fragment0388660Acc00100 : List (String × SourceJson) := (fragment0388660Field000Key00, fragment0388660Field000Value00) :: fragment0388660Acc00000
noncomputable def fragment0388660Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '5', ',']

theorem object_fragment0388660_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0388660Field000Chars00 ++ tail)) fragment0388660Acc00000 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0388660Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_000"
  err.flush

noncomputable def fragment0388660Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0388660Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0388660Acc00200 : List (String × SourceJson) := (fragment0388660Field001Key00, fragment0388660Field001Value00) :: fragment0388660Acc00100
noncomputable def fragment0388660Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0388660_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0388660Field001Chars00 ++ tail)) fragment0388660Acc00100 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0388660Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_001"
  err.flush

noncomputable def fragment0388660Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0388660Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '0', '7', '9', '0', '5', '2', '6', '1', '7', '4', '4', '9', '4', '3', '3', '0', '3', '9', '2', '7', '4', '2', '1', '7', '6', '9', '0', '8', '9', '6', '7', '5', '8', '9', '5', '7', '4', '6', '1', '3', '4', '7', '3', '/', '3', '7', '5', '7', '3', '9', '6', '1', '2', '0', '8', '0', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0388660Acc00300 : List (String × SourceJson) := (fragment0388660Field002Key00, fragment0388660Field002Value00) :: fragment0388660Acc00200
noncomputable def fragment0388660Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '0', '7', '9', '0', '5', '2', '6', '1', '7', '4', '4', '9', '4', '3', '3', '0', '3', '9', '2', '7', '4', '2', '1', '7', '6', '9', '0', '8', '9', '6', '7', '5', '8', '9', '5', '7', '4', '6', '1', '3', '4', '7', '3', '/', '3', '7', '5', '7', '3', '9', '6', '1', '2', '0', '8', '0', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0388660_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0388660Field002Chars00 ++ tail)) fragment0388660Acc00200 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0388660Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_002"
  err.flush

noncomputable def fragment0388660Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0388660Field003Value00 : SourceJson := .str (String.ofList ['3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0'])
noncomputable def fragment0388660Acc00400 : List (String × SourceJson) := (fragment0388660Field003Key00, fragment0388660Field003Value00) :: fragment0388660Acc00300
noncomputable def fragment0388660Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '4', '6', '3', '0', '0', '6', '1', '/', '4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0388660_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0388660Field003Chars00 ++ tail)) fragment0388660Acc00300 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0388660Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_003"
  err.flush

noncomputable def fragment0388660Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0388660Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0388660Acc00500 : List (String × SourceJson) := (fragment0388660Field004Key00, fragment0388660Field004Value00) :: fragment0388660Acc00400
noncomputable def fragment0388660Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0388660_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0388660Field004Chars00 ++ tail)) fragment0388660Acc00400 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0388660Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_004"
  err.flush

noncomputable def fragment0388660Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0388660Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '0', '0', '9', '7', '1', '3', '0', '3', '0', '3', '7', '7', '6', '8', '7', '2', '7', '0', '6', '3', '/', '7', '2', '2', '1', '5', '2', '2', '9', '7', '7', '3', '3', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '3', '0', '9', '4', '5', '6', '1', '8', '9', '8', '9', '4', '7', '3', '1', '0', '2', '6', '6', '0', '1', '/', '2', '5', '2', '7', '5', '3', '3', '0', '4', '2', '0', '6', '7', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '2', '1', '7', '9', '0', '0', '8', '4', '0', '5', '7', '5', '6', '8', '4', '0', '8', '0', '8', '9', '/', '5', '0', '5', '5', '0', '6', '6', '0', '8', '4', '1', '3', '4', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '0', '1', '0', '9', '4', '3', '9', '0', '6', '4', '5', '7', '1', '0', '4', '8', '3', '1', '9', '7', '/', '7', '5', '8', '2', '5', '9', '9', '1', '2', '6', '2', '0', '1', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '2', '2', '2', '5', '0', '0', '7', '7', '6', '1', '3', '0', '6', '2', '6', '8', '5', '0', '1', '/', '5', '0', '5', '5', '0', '6', '6', '0', '8', '4', '1', '3', '4', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '7', '3', '2', '4', '0', '9', '6', '9', '8', '8', '4', '9', '8', '9', '1', '1', '2', '7', '1', '/', '5', '0', '5', '5', '0', '6', '6', '0', '8', '4', '1', '3', '4', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '1', '0', '9', '9', '7', '0', '4', '4', '1', '8', '0', '1', '4', '9', '9', '5', '2', '2', '9', '/', '7', '9', '8', '1', '6', '8', '3', '2', '9', '0', '7', '3', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '1', '9', '9', '1', '7', '1', '4', '7', '3', '1', '2', '4', '7', '9', '9', '5', '6', '7', '3', '9', '/', '1', '5', '1', '6', '5', '1', '9', '8', '2', '5', '2', '4', '0', '3', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '6', '6', '0', '4', '9', '0', '7', '8', '4', '5', '5', '0', '4', '0', '4', '6', '5', '9', '0', '9', '/', '7', '5', '8', '2', '5', '9', '9', '1', '2', '6', '2', '0', '1', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '4', '7', '0', '1', '8', '7', '3', '7', '5', '6', '6', '8', '6', '1', '5', '1', '0', '7', '3', '4', '1', '/', '7', '5', '8', '2', '5', '9', '9', '1', '2', '6', '2', '0', '1', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0388660Acc00600 : List (String × SourceJson) := (fragment0388660Field005Key00, fragment0388660Field005Value00) :: fragment0388660Acc00500
noncomputable def fragment0388660Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '0', '9', '7', '1', '3', '0', '3', '0', '3', '7', '7', '6', '8', '7', '2', '7', '0', '6', '3', '/', '7', '2', '2', '1', '5', '2', '2', '9', '7', '7', '3', '3', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '3', '0', '9', '4', '5', '6', '1', '8', '9', '8', '9', '4', '7', '3', '1', '0', '2', '6', '6', '0', '1', '/', '2', '5', '2', '7', '5', '3', '3', '0', '4', '2', '0', '6', '7', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '2', '1', '7', '9', '0', '0', '8', '4', '0', '5', '7', '5', '6', '8', '4', '0', '8', '0', '8', '9', '/', '5', '0', '5', '5', '0', '6', '6', '0', '8', '4', '1', '3', '4', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '0', '1', '0', '9', '4', '3', '9', '0', '6', '4', '5', '7', '1', '0', '4', '8', '3', '1', '9', '7', '/', '7', '5', '8', '2', '5', '9', '9', '1', '2', '6', '2', '0', '1', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '2', '2', '2', '5', '0', '0', '7', '7', '6', '1', '3', '0', '6', '2', '6', '8', '5', '0', '1', '/', '5', '0', '5', '5', '0', '6', '6', '0', '8', '4', '1', '3', '4', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '7', '3', '2', '4', '0', '9', '6', '9', '8', '8', '4', '9', '8', '9', '1', '1', '2', '7', '1', '/', '5', '0', '5', '5', '0', '6', '6', '0', '8', '4', '1', '3', '4', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '1', '0', '9', '9', '7', '0', '4', '4', '1', '8', '0', '1', '4', '9', '9', '5', '2', '2', '9', '/', '7', '9', '8', '1', '6', '8', '3', '2', '9', '0', '7', '3', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '1', '9', '9', '1', '7', '1', '4', '7', '3', '1', '2', '4', '7', '9', '9', '5', '6', '7', '3', '9', '/', '1', '5', '1', '6', '5', '1', '9', '8', '2', '5', '2', '4', '0', '3', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '6', '6', '0', '4', '9', '0', '7', '8', '4', '5', '5', '0', '4', '0', '4', '6', '5', '9', '0', '9', '/', '7', '5', '8', '2', '5', '9', '9', '1', '2', '6', '2', '0', '1', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '4', '7', '0', '1', '8', '7', '3', '7', '5', '6', '6', '8', '6', '1', '5', '1', '0', '7', '3', '4', '1', '/', '7', '5', '8', '2', '5', '9', '9', '1', '2', '6', '2', '0', '1', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0388660_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0388660Field005Chars00 ++ tail)) fragment0388660Acc00500 =
      SourceJson.object (fuel + 428) (SourceJson.white tail) fragment0388660Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_005"
  err.flush

noncomputable def fragment0388660Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0388660Field006Value00 : SourceJson := .str (String.ofList ['4', '1', '8', '5', '1', '8', '9', '3', '5', '0', '9', '0', '3', '4', '7', '0', '6', '8', '3', '1', '1', '6', '9', '2', '1', '0', '7', '2', '6', '4', '2', '5', '9', '8', '6', '5', '6', '7', '8', '0', '4', '5', '8', '5', '8', '2', '2', '2', '7', '5', '5', '2', '/', '1', '5', '8', '3', '9', '0', '5', '0', '3', '9', '1', '6', '7', '7', '3', '8', '0', '0', '5', '4', '1', '1', '9', '4', '2', '8', '2', '0', '2', '0', '8', '7', '0', '1', '3', '8', '0', '7', '2', '5', '2', '4', '0', '4', '7', '7', '5', '7', '4', '9', '5', '2', '9', '4', '1', '6', '2', '5', '7', '3', '2', '6', '0', '2', '5'])
noncomputable def fragment0388660Acc00700 : List (String × SourceJson) := (fragment0388660Field006Key00, fragment0388660Field006Value00) :: fragment0388660Acc00600
noncomputable def fragment0388660Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '1', '8', '5', '1', '8', '9', '3', '5', '0', '9', '0', '3', '4', '7', '0', '6', '8', '3', '1', '1', '6', '9', '2', '1', '0', '7', '2', '6', '4', '2', '5', '9', '8', '6', '5', '6', '7', '8', '0', '4', '5', '8', '5', '8', '2', '2', '2', '7', '5', '5', '2', '/', '1', '5', '8', '3', '9', '0', '5', '0', '3', '9', '1', '6', '7', '7', '3', '8', '0', '0', '5', '4', '1', '1', '9', '4', '2', '8', '2', '0', '2', '0', '8', '7', '0', '1', '3', '8', '0', '7', '2', '5', '2', '4', '0', '4', '7', '7', '5', '7', '4', '9', '5', '2', '9', '4', '1', '6', '2', '5', '7', '3', '2', '6', '0', '2', '5', '"', ',']

theorem object_fragment0388660_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 428) (SourceJson.white (fragment0388660Field006Chars00 ++ tail)) fragment0388660Acc00600 =
      SourceJson.object (fuel + 427) (SourceJson.white tail) fragment0388660Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_006"
  err.flush

noncomputable def fragment0388660Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0388660Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '9', '7', '5', '3', '2', '4', '5', '2', '7', '6', '0', '8', '9', '8', '4', '9', '1', '2', '3', '1', '1', '6', '1', '6', '2', '8', '6', '1', '1', '2', '0', '3', '5', '2', '6', '7', '2', '9', '8', '7', '1', '9', '9', '8', '8', '8', '7', '8', '2', '5', '2', '0', '6', '8', '3', '0', '6', '3', '3', '0', '4', '9', '3', '2', '1', '5', '3', '2', '8', '8', '0', '8', '5', '1', '5', '7', '6', '3', '0', '5', '1', '9', '1', '5', '1', '6', '8', '0', '2', '1', '2', '3', '9', '5', '2', '4', '7', '7', '3', '0', '4', '3', '8', '8', '1', '1', '2', '2', '0', '9', '6', '7', '4', '3', '8', '1', '9', '3', '5', '8', '0', '4', '8', '2', '4', '4', '8', '0', '3', '2', '2', '0', '8', '7', '0', '2', '7', '6', '1', '0', '7', '5', '9', '7', '4', '1', '7', '0', '9', '9', '7', '1', '9', '3', '0', '8', '7', '2', '2', '1', '5', '8', '5', '9', '9', '8', '9', '2', '4', '9', '4', '7', '5', '1', '1', '7', '0', '9', '4', '1', '8', '6', '5', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '4', '1', '2', '6', '2', '1', '5', '7', '0', '7', '0', '6', '8', '9', '9', '4', '3', '1', '9', '0', '4', '0', '3', '5', '1', '6', '6', '8', '2', '5', '2', '4', '5', '5', '8', '0', '7', '7', '7', '9', '4', '5', '7', '2', '1', '1', '7', '3', '8', '7', '9', '0', '7', '3', '5', '5', '9', '7', '1', '0', '0', '2', '3', '3', '3', '5', '1', '8', '5', '7', '7', '6', '9', '1', '8', '0', '2', '9', '1', '6', '8', '4', '2', '9', '9', '7', '0', '7', '5', '9', '5', '2', '6', '2', '0', '7', '7', '6', '5', '0', '6', '1', '0', '6', '1', '6', '2', '7', '3', '0', '8', '4', '0', '8', '6', '0', '6', '8', '1', '8', '0', '2', '4', '6', '6', '6', '4', '1', '6', '1', '5', '7', '0', '2', '7', '6', '4', '8', '2', '8', '3', '9', '7', '1', '9', '1', '8', '8', '0', '5', '5', '9', '8', '5', '7', '1', '7', '7', '6', '1', '0', '7', '1', '5', '3', '4', '7', '9', '2', '4', '8', '4', '6', '1', '7', '3', '7', '2', '6', '7', '0', '4', '1', '0', '6', '6', '6', '7', '8', '8', '6', '0', '3', '2', '5', '2', '5', '6', '3', '1', '0', '9', '3', '4', '3', '9', '1', '2', '1', '6', '2', '5', '1', '7', '5', '1'])
noncomputable def fragment0388660Acc00800 : List (String × SourceJson) := (fragment0388660Field007Key00, fragment0388660Field007Value00) :: fragment0388660Acc00700
noncomputable def fragment0388660Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '9', '7', '5', '3', '2', '4', '5', '2', '7', '6', '0', '8', '9', '8', '4', '9', '1', '2', '3', '1', '1', '6', '1', '6', '2', '8', '6', '1', '1', '2', '0', '3', '5', '2', '6', '7', '2', '9', '8', '7', '1', '9', '9', '8', '8', '8', '7', '8', '2', '5', '2', '0', '6', '8', '3', '0', '6', '3', '3', '0', '4', '9', '3', '2', '1', '5', '3', '2', '8', '8', '0', '8', '5', '1', '5', '7', '6', '3', '0', '5', '1', '9', '1', '5', '1', '6', '8', '0', '2', '1', '2', '3', '9', '5', '2', '4', '7', '7', '3', '0', '4', '3', '8', '8', '1', '1', '2', '2', '0', '9', '6', '7', '4', '3', '8', '1', '9', '3', '5', '8', '0', '4', '8', '2', '4', '4', '8', '0', '3', '2', '2', '0', '8', '7', '0', '2', '7', '6', '1', '0', '7', '5', '9', '7', '4', '1', '7', '0', '9', '9', '7', '1', '9', '3', '0', '8', '7', '2', '2', '1', '5', '8', '5', '9', '9', '8', '9', '2', '4', '9', '4', '7', '5', '1', '1', '7', '0', '9', '4', '1', '8', '6', '5', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '4', '1', '2', '6', '2', '1', '5', '7', '0', '7', '0', '6', '8', '9', '9', '4', '3', '1', '9', '0', '4', '0', '3', '5', '1', '6', '6', '8', '2', '5', '2', '4', '5', '5', '8', '0', '7', '7', '7', '9', '4', '5', '7', '2', '1', '1', '7', '3', '8', '7', '9', '0', '7', '3', '5', '5', '9', '7', '1', '0', '0', '2', '3', '3', '3', '5', '1', '8', '5', '7', '7', '6', '9', '1', '8', '0', '2', '9', '1', '6', '8', '4', '2', '9', '9', '7', '0', '7', '5', '9', '5', '2', '6', '2', '0', '7', '7', '6', '5', '0', '6', '1', '0', '6', '1', '6', '2', '7', '3', '0', '8', '4', '0', '8', '6', '0', '6', '8', '1', '8', '0', '2', '4', '6', '6', '6', '4', '1', '6', '1', '5', '7', '0', '2', '7', '6', '4', '8', '2', '8', '3', '9', '7', '1', '9', '1', '8', '8', '0', '5', '5', '9', '8', '5', '7', '1', '7', '7', '6', '1', '0', '7', '1', '5', '3', '4', '7', '9', '2', '4', '8', '4', '6', '1', '7', '3', '7', '2', '6', '7', '0', '4', '1', '0', '6', '6', '6', '7', '8', '8', '6', '0', '3', '2', '5', '2', '5', '6', '3', '1', '0', '9', '3', '4', '3', '9', '1', '2', '1', '6', '2', '5', '1', '7', '5', '1', '"', ',']

theorem object_fragment0388660_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 427) (SourceJson.white (fragment0388660Field007Chars00 ++ tail)) fragment0388660Acc00700 =
      SourceJson.object (fuel + 426) (SourceJson.white tail) fragment0388660Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_007"
  err.flush

noncomputable def fragment0388660Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0388660Field008Value00 : SourceJson := .str (String.ofList ['2', '0', '9', '3', '4', '6', '4', '2', '7', '8', '7', '7', '1', '2', '8', '1', '1'])
noncomputable def fragment0388660Acc00900 : List (String × SourceJson) := (fragment0388660Field008Key00, fragment0388660Field008Value00) :: fragment0388660Acc00800
noncomputable def fragment0388660Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '9', '3', '4', '6', '4', '2', '7', '8', '7', '7', '1', '2', '8', '1', '1', '"', ',']

theorem object_fragment0388660_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 426) (SourceJson.white (fragment0388660Field008Chars00 ++ tail)) fragment0388660Acc00800 =
      SourceJson.object (fuel + 425) (SourceJson.white tail) fragment0388660Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_008"
  err.flush

noncomputable def fragment0388660Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0388660Field009Value00 : SourceJson := .str (String.ofList ['1', '5', '0', '4', '5', '1', '9', '8', '4', '2', '3', '0', '3', '0', '4', '9', '6', '4'])
noncomputable def fragment0388660Acc01000 : List (String × SourceJson) := (fragment0388660Field009Key00, fragment0388660Field009Value00) :: fragment0388660Acc00900
noncomputable def fragment0388660Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '0', '4', '5', '1', '9', '8', '4', '2', '3', '0', '3', '0', '4', '9', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0388660_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 425) (SourceJson.white (fragment0388660Field009Chars00 ++ tail)) fragment0388660Acc00900 =
      .ok (.obj (fragment0388660Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0388660_object_field_009"
  err.flush

noncomputable def fragment0388660Chars : List Char := '{' :: (fragment0388660Field000Chars00 ++ fragment0388660Field001Chars00 ++ fragment0388660Field002Chars00 ++ fragment0388660Field003Chars00 ++ fragment0388660Field004Chars00 ++ fragment0388660Field005Chars00 ++ fragment0388660Field006Chars00 ++ fragment0388660Field007Chars00 ++ fragment0388660Field008Chars00 ++ fragment0388660Field009Chars00)
noncomputable def fragment0388660Value : SourceJson := .obj (fragment0388660Acc01000.reverse)

theorem value_fragment0388660 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 435) (fragment0388660Chars ++ tail) =
      .ok (fragment0388660Value, tail) := by
  have hinput : fragment0388660Chars ++ tail = '{' :: (fragment0388660Field000Chars00 ++ (fragment0388660Field001Chars00 ++ (fragment0388660Field002Chars00 ++ (fragment0388660Field003Chars00 ++ (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0388660Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 435) (fragment0388660Chars ++ tail) =
        SourceJson.value (fuel + 435) ('{' :: (fragment0388660Field000Chars00 ++ (fragment0388660Field001Chars00 ++ (fragment0388660Field002Chars00 ++ (fragment0388660Field003Chars00 ++ (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 435)) hinput
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0388660Field000Chars00 ++ (fragment0388660Field001Chars00 ++ (fragment0388660Field002Chars00 ++ (fragment0388660Field003Chars00 ++ (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))))))))))) fragment0388660Acc00000 := by rfl
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0388660Field001Chars00 ++ (fragment0388660Field002Chars00 ++ (fragment0388660Field003Chars00 ++ (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail))))))))))) fragment0388660Acc00100 := object_fragment0388660_field_000 fuel (fragment0388660Field001Chars00 ++ (fragment0388660Field002Chars00 ++ (fragment0388660Field003Chars00 ++ (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0388660Field002Chars00 ++ (fragment0388660Field003Chars00 ++ (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))))))))) fragment0388660Acc00200 := object_fragment0388660_field_001 fuel (fragment0388660Field002Chars00 ++ (fragment0388660Field003Chars00 ++ (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0388660Field003Chars00 ++ (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail))))))))) fragment0388660Acc00300 := object_fragment0388660_field_002 fuel (fragment0388660Field003Chars00 ++ (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))))))) fragment0388660Acc00400 := object_fragment0388660_field_003 fuel (fragment0388660Field004Chars00 ++ (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail))))))) fragment0388660Acc00500 := object_fragment0388660_field_004 fuel (fragment0388660Field005Chars00 ++ (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 428) (SourceJson.white (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))))) fragment0388660Acc00600 := object_fragment0388660_field_005 fuel (fragment0388660Field006Chars00 ++ (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 427) (SourceJson.white (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail))))) fragment0388660Acc00700 := object_fragment0388660_field_006 fuel (fragment0388660Field007Chars00 ++ (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 426) (SourceJson.white (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))) fragment0388660Acc00800 := object_fragment0388660_field_007 fuel (fragment0388660Field008Chars00 ++ (fragment0388660Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 425) (SourceJson.white (fragment0388660Field009Chars00 ++ (tail))) fragment0388660Acc00900 := object_fragment0388660_field_008 fuel (fragment0388660Field009Chars00 ++ (tail))
    _ = .ok (fragment0388660Value, tail) := object_fragment0388660_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0094_before_reader"
  err.flush

noncomputable def chunk0094LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0094SuffixChars00 : List Char := [',']
noncomputable def chunk0094Chars00 : List Char := chunk0094LeadChars00 ++ fragment0386640Chars ++ chunk0094SuffixChars00
noncomputable def chunk0094Push00 (acc : List SourceJson) : List SourceJson := fragment0386640Value :: acc

noncomputable def chunk0094AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0094_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 510)
      (SourceJson.white (chunk0094LeadChars00 ++ (fragment0386640Chars ++ rest))) acc =
      (SourceJson.value (fuel + 509) (fragment0386640Chars ++ rest)).bind
        (chunk0094AfterValue00 (fuel + 509) acc) := by rfl

theorem array_chunk0094 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 510) (SourceJson.white (chunk0094Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 509) (SourceJson.white tail) (chunk0094Push00 acc) := by
  have hinput : chunk0094Chars00 ++ tail = chunk0094LeadChars00 ++ (fragment0386640Chars ++ (chunk0094SuffixChars00 ++ tail)) := by
    simp only [chunk0094Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 510) (SourceJson.white (chunk0094Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 510)
          (SourceJson.white (chunk0094LeadChars00 ++ (fragment0386640Chars ++ (chunk0094SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 510) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 509) (fragment0386640Chars ++ (chunk0094SuffixChars00 ++ tail))).bind
        (chunk0094AfterValue00 (fuel + 509) acc) := array_chunk0094_head fuel (chunk0094SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0386640Value, chunk0094SuffixChars00 ++ tail)).bind
        (chunk0094AfterValue00 (fuel + 509) acc) :=
      congrArg (fun result => result.bind (chunk0094AfterValue00 (fuel + 509) acc))
        (value_fragment0386640 (fuel + 71) (chunk0094SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 509) (SourceJson.white tail) (chunk0094Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0094_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0095_before_reader"
  err.flush

noncomputable def chunk0095LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0095SuffixChars00 : List Char := [',']
noncomputable def chunk0095Chars00 : List Char := chunk0095LeadChars00 ++ fragment0388660Chars ++ chunk0095SuffixChars00
noncomputable def chunk0095Push00 (acc : List SourceJson) : List SourceJson := fragment0388660Value :: acc

noncomputable def chunk0095AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0095_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 509)
      (SourceJson.white (chunk0095LeadChars00 ++ (fragment0388660Chars ++ rest))) acc =
      (SourceJson.value (fuel + 508) (fragment0388660Chars ++ rest)).bind
        (chunk0095AfterValue00 (fuel + 508) acc) := by rfl

theorem array_chunk0095 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 509) (SourceJson.white (chunk0095Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 508) (SourceJson.white tail) (chunk0095Push00 acc) := by
  have hinput : chunk0095Chars00 ++ tail = chunk0095LeadChars00 ++ (fragment0388660Chars ++ (chunk0095SuffixChars00 ++ tail)) := by
    simp only [chunk0095Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 509) (SourceJson.white (chunk0095Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 509)
          (SourceJson.white (chunk0095LeadChars00 ++ (fragment0388660Chars ++ (chunk0095SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 509) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 508) (fragment0388660Chars ++ (chunk0095SuffixChars00 ++ tail))).bind
        (chunk0095AfterValue00 (fuel + 508) acc) := array_chunk0095_head fuel (chunk0095SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0388660Value, chunk0095SuffixChars00 ++ tail)).bind
        (chunk0095AfterValue00 (fuel + 508) acc) :=
      congrArg (fun result => result.bind (chunk0095AfterValue00 (fuel + 508) acc))
        (value_fragment0388660 (fuel + 73) (chunk0095SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 508) (SourceJson.white tail) (chunk0095Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0095_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0094Chars00 ++ chunk0095Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0095Push00 (chunk0094Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 510) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 508) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 510) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 510) (SourceJson.white (chunk0094Chars00 ++ (chunk0095Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 510) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 509) (SourceJson.white (chunk0095Chars00 ++ (tail))) (chunk0094Push00 (acc)) := array_chunk0094 fuel (chunk0095Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 508) (SourceJson.white tail) (blockPush acc) := array_chunk0095 fuel (tail) (chunk0094Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 386634).take 4032 = blockChars := by rfl

theorem block_original_split : sourceRest 386634 = blockChars ++ sourceRest 390666 := by
  calc
    sourceRest 386634 = (sourceRest 386634).take 4032 ++ (sourceRest 386634).drop 4032 :=
      (List.take_append_drop 4032 (sourceRest 386634)).symm
    _ = blockChars ++ (sourceRest 386634).drop 4032 :=
      congrArg (fun part => part ++ (sourceRest 386634).drop 4032) block_original_prefix
    _ = blockChars ++ sourceRest 390666 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 386634 4032)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 510) (SourceJson.white (sourceRest 386634)) acc =
      SourceJson.array (fuel + 508) (SourceJson.white (sourceRest 390666)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 510) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 390666) acc)

#print axioms object_fragment0386640_field_000
#print axioms object_fragment0386640_field_001
#print axioms object_fragment0386640_field_002
#print axioms object_fragment0386640_field_003
#print axioms object_fragment0386640_field_004
#print axioms object_fragment0386640_field_005
#print axioms object_fragment0386640_field_006
#print axioms object_fragment0386640_field_007
#print axioms object_fragment0386640_field_008
#print axioms object_fragment0386640_field_009
#print axioms value_fragment0386640
#print axioms object_fragment0388660_field_000
#print axioms object_fragment0388660_field_001
#print axioms object_fragment0388660_field_002
#print axioms object_fragment0388660_field_003
#print axioms object_fragment0388660_field_004
#print axioms object_fragment0388660_field_005
#print axioms object_fragment0388660_field_006
#print axioms object_fragment0388660_field_007
#print axioms object_fragment0388660_field_008
#print axioms object_fragment0388660_field_009
#print axioms value_fragment0388660
#print axioms array_chunk0094_head
#print axioms array_chunk0094
#print axioms array_chunk0095_head
#print axioms array_chunk0095
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock048

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
