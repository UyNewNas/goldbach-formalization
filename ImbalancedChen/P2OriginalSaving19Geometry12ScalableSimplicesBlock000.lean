import ImbalancedChen.P2OriginalSaving19Geometry12ScalableInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry12ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock000

noncomputable def fragment1454530Acc00000 : List (String × SourceJson) := []

noncomputable def fragment1454530Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment1454530Field000Value00 : SourceJson := .number (String.ofList ['0'])
noncomputable def fragment1454530Acc00100 : List (String × SourceJson) := (fragment1454530Field000Key00, fragment1454530Field000Value00) :: fragment1454530Acc00000
noncomputable def fragment1454530Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '0', ',']

theorem object_fragment1454530_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 479) (SourceJson.white (fragment1454530Field000Chars00 ++ tail)) fragment1454530Acc00000 =
      SourceJson.object (fuel + 478) (SourceJson.white tail) fragment1454530Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_000"
  err.flush

noncomputable def fragment1454530Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment1454530Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['8', '5']), .number (String.ofList ['5', '0']), .number (String.ofList ['4', '7']), .number (String.ofList ['9']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment1454530Acc00200 : List (String × SourceJson) := (fragment1454530Field001Key00, fragment1454530Field001Value00) :: fragment1454530Acc00100
noncomputable def fragment1454530Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1454530_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 478) (SourceJson.white (fragment1454530Field001Chars00 ++ tail)) fragment1454530Acc00100 =
      SourceJson.object (fuel + 477) (SourceJson.white tail) fragment1454530Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_001"
  err.flush

noncomputable def fragment1454530Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment1454530Field002Value00 : SourceJson := .str (String.ofList ['7', '1', '6', '4', '6', '2', '4', '0', '9', '6', '7', '0', '5', '0', '4', '7', '0', '0', '4', '9', '5', '2', '2', '0', '2', '4', '6', '0', '6', '8', '7', '5', '9', '4', '5', '0', '8', '1', '3', '9', '0', '7', '6', '7', '9', '/', '2', '5', '4', '2', '2', '9', '1', '4', '5', '5', '8', '6', '1', '9', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1454530Acc00300 : List (String × SourceJson) := (fragment1454530Field002Key00, fragment1454530Field002Value00) :: fragment1454530Acc00200
noncomputable def fragment1454530Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '1', '6', '4', '6', '2', '4', '0', '9', '6', '7', '0', '5', '0', '4', '7', '0', '0', '4', '9', '5', '2', '2', '0', '2', '4', '6', '0', '6', '8', '7', '5', '9', '4', '5', '0', '8', '1', '3', '9', '0', '7', '6', '7', '9', '/', '2', '5', '4', '2', '2', '9', '1', '4', '5', '5', '8', '6', '1', '9', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1454530_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 477) (SourceJson.white (fragment1454530Field002Chars00 ++ tail)) fragment1454530Acc00200 =
      SourceJson.object (fuel + 476) (SourceJson.white tail) fragment1454530Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_002"
  err.flush

noncomputable def fragment1454530Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment1454530Field003Value00 : SourceJson := .str (String.ofList ['3', '7', '1', '3', '8', '9', '6', '7', '3', '/', '2', '3', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1454530Acc00400 : List (String × SourceJson) := (fragment1454530Field003Key00, fragment1454530Field003Value00) :: fragment1454530Acc00300
noncomputable def fragment1454530Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '7', '1', '3', '8', '9', '6', '7', '3', '/', '2', '3', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1454530_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment1454530Field003Chars00 ++ tail)) fragment1454530Acc00300 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment1454530Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_003"
  err.flush

noncomputable def fragment1454530Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment1454530Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '0', '4', '6', '9', '4', '1', '/', '4', '2', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0'])]
noncomputable def fragment1454530Acc00500 : List (String × SourceJson) := (fragment1454530Field004Key00, fragment1454530Field004Value00) :: fragment1454530Acc00400
noncomputable def fragment1454530Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '0', '4', '6', '9', '4', '1', '/', '4', '2', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1454530_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment1454530Field004Chars00 ++ tail)) fragment1454530Acc00400 =
      SourceJson.object (fuel + 474) (SourceJson.white tail) fragment1454530Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_004"
  err.flush

noncomputable def fragment1454530Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment1454530Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '3', '2', '4', '5', '1', '3', '4', '7', '5', '1', '9', '6', '9', '4', '9', '1', '1', '5', '9', '2', '5', '2', '9', '1', '/', '4', '8', '9', '8', '9', '3', '8', '8', '8', '3', '3', '5', '3', '1', '4', '7', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '2', '3', '9', '8', '6', '8', '2', '7', '9', '9', '9', '2', '6', '9', '4', '9', '6', '5', '1', '6', '6', '1', '1', '/', '9', '7', '9', '7', '8', '7', '7', '7', '6', '6', '7', '0', '6', '2', '9', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '6', '4', '0', '9', '0', '5', '2', '9', '3', '8', '6', '5', '2', '9', '6', '6', '0', '9', '9', '1', '1', '/', '1', '5', '4', '7', '0', '3', '3', '3', '3', '1', '5', '8', '5', '2', '0', '4', '5', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '2', '6', '3', '6', '5', '0', '2', '6', '3', '9', '9', '9', '6', '7', '7', '6', '1', '0', '0', '2', '8', '6', '3', '/', '2', '9', '3', '9', '3', '6', '3', '3', '3', '0', '0', '1', '1', '8', '8', '8', '6', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '6', '9', '4', '4', '1', '1', '8', '8', '9', '5', '5', '8', '5', '9', '6', '5', '1', '4', '6', '9', '7', '7', '/', '1', '5', '4', '7', '0', '3', '3', '3', '3', '1', '5', '8', '5', '2', '0', '4', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '2', '4', '9', '9', '6', '8', '0', '6', '0', '3', '4', '5', '3', '4', '4', '6', '6', '2', '9', '3', '/', '1', '7', '5', '7', '9', '9', '2', '4', '2', '2', '2', '5', '5', '9', '1', '4', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '7', '0', '3', '4', '4', '4', '5', '3', '2', '0', '0', '6', '6', '3', '2', '7', '9', '6', '3', '8', '1', '9', '/', '2', '1', '0', '9', '5', '9', '0', '9', '0', '6', '7', '0', '7', '0', '9', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '8', '3', '7', '7', '8', '0', '7', '7', '3', '3', '9', '2', '2', '3', '8', '6', '9', '2', '5', '6', '2', '4', '1', '/', '9', '2', '8', '2', '1', '9', '9', '9', '8', '9', '5', '1', '1', '2', '2', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '6', '9', '8', '9', '6', '5', '7', '4', '6', '6', '3', '5', '5', '1', '3', '4', '2', '0', '3', '7', '0', '4', '7', '/', '5', '8', '7', '8', '7', '2', '6', '6', '6', '0', '0', '2', '3', '7', '7', '7', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '3', '5', '7', '5', '4', '1', '1', '7', '7', '3', '2', '6', '6', '8', '5', '6', '0', '6', '0', '1', '6', '0', '1', '/', '2', '9', '3', '9', '3', '6', '3', '3', '3', '0', '0', '1', '1', '8', '8', '8', '6', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment1454530Acc00600 : List (String × SourceJson) := (fragment1454530Field005Key00, fragment1454530Field005Value00) :: fragment1454530Acc00500
noncomputable def fragment1454530Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '4', '5', '1', '3', '4', '7', '5', '1', '9', '6', '9', '4', '9', '1', '1', '5', '9', '2', '5', '2', '9', '1', '/', '4', '8', '9', '8', '9', '3', '8', '8', '8', '3', '3', '5', '3', '1', '4', '7', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '2', '3', '9', '8', '6', '8', '2', '7', '9', '9', '9', '2', '6', '9', '4', '9', '6', '5', '1', '6', '6', '1', '1', '/', '9', '7', '9', '7', '8', '7', '7', '7', '6', '6', '7', '0', '6', '2', '9', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '6', '4', '0', '9', '0', '5', '2', '9', '3', '8', '6', '5', '2', '9', '6', '6', '0', '9', '9', '1', '1', '/', '1', '5', '4', '7', '0', '3', '3', '3', '3', '1', '5', '8', '5', '2', '0', '4', '5', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '2', '6', '3', '6', '5', '0', '2', '6', '3', '9', '9', '9', '6', '7', '7', '6', '1', '0', '0', '2', '8', '6', '3', '/', '2', '9', '3', '9', '3', '6', '3', '3', '3', '0', '0', '1', '1', '8', '8', '8', '6', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '6', '9', '4', '4', '1', '1', '8', '8', '9', '5', '5', '8', '5', '9', '6', '5', '1', '4', '6', '9', '7', '7', '/', '1', '5', '4', '7', '0', '3', '3', '3', '3', '1', '5', '8', '5', '2', '0', '4', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '2', '4', '9', '9', '6', '8', '0', '6', '0', '3', '4', '5', '3', '4', '4', '6', '6', '2', '9', '3', '/', '1', '7', '5', '7', '9', '9', '2', '4', '2', '2', '2', '5', '5', '9', '1', '4', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '0', '3', '4', '4', '4', '5', '3', '2', '0', '0', '6', '6', '3', '2', '7', '9', '6', '3', '8', '1', '9', '/', '2', '1', '0', '9', '5', '9', '0', '9', '0', '6', '7', '0', '7', '0', '9', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '8', '3', '7', '7', '8', '0', '7', '7', '3', '3', '9', '2', '2', '3', '8', '6', '9', '2', '5', '6', '2', '4', '1', '/', '9', '2', '8', '2', '1', '9', '9', '9', '8', '9', '5', '1', '1', '2', '2', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '6', '9', '8', '9', '6', '5', '7', '4', '6', '6', '3', '5', '5', '1', '3', '4', '2', '0', '3', '7', '0', '4', '7', '/', '5', '8', '7', '8', '7', '2', '6', '6', '6', '0', '0', '2', '3', '7', '7', '7', '2', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '3', '5', '7', '5', '4', '1', '1', '7', '7', '3', '2', '6', '6', '8', '5', '6', '0', '6', '0', '1', '6', '0', '1', '/', '2', '9', '3', '9', '3', '6', '3', '3', '3', '0', '0', '1', '1', '8', '8', '8', '6', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1454530_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 474) (SourceJson.white (fragment1454530Field005Chars00 ++ tail)) fragment1454530Acc00500 =
      SourceJson.object (fuel + 473) (SourceJson.white tail) fragment1454530Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_005"
  err.flush

noncomputable def fragment1454530Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1454530Field006Value00 : SourceJson := .str (String.ofList ['3', '3', '9', '4', '6', '0', '1', '5', '8', '6', '1', '1', '5', '4', '2', '2', '3', '3', '1', '2', '2', '7', '4', '6', '9', '6', '3', '2', '8', '3', '2', '6', '9', '3', '7', '9', '7', '2', '1', '5', '9', '6', '9', '4', '2', '4', '3', '1', '4', '6', '5', '6', '8', '2', '1', '5', '0', '2', '5', '/', '7', '4', '9', '9', '0', '6', '3', '0', '7', '8', '3', '2', '8', '6', '6', '1', '9', '6', '0', '2', '7', '0', '4', '7', '5', '0', '9', '1', '6', '4', '3', '6', '0', '9', '5', '3', '0', '5', '2', '4', '9', '0', '7', '2', '1', '9', '5', '6', '3', '8', '6', '5', '0', '6', '6', '4', '6', '4', '8', '7', '0', '8', '4', '9', '6', '6', '4', '6', '4'])
noncomputable def fragment1454530Acc00700 : List (String × SourceJson) := (fragment1454530Field006Key00, fragment1454530Field006Value00) :: fragment1454530Acc00600
noncomputable def fragment1454530Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '9', '4', '6', '0', '1', '5', '8', '6', '1', '1', '5', '4', '2', '2', '3', '3', '1', '2', '2', '7', '4', '6', '9', '6', '3', '2', '8', '3', '2', '6', '9', '3', '7', '9', '7', '2', '1', '5', '9', '6', '9', '4', '2', '4', '3', '1', '4', '6', '5', '6', '8', '2', '1', '5', '0', '2', '5', '/', '7', '4', '9', '9', '0', '6', '3', '0', '7', '8', '3', '2', '8', '6', '6', '1', '9', '6', '0', '2', '7', '0', '4', '7', '5', '0', '9', '1', '6', '4', '3', '6', '0', '9', '5', '3', '0', '5', '2', '4', '9', '0', '7', '2', '1', '9', '5', '6', '3', '8', '6', '5', '0', '6', '6', '4', '6', '4', '8', '7', '0', '8', '4', '9', '6', '6', '4', '6', '4', '"', ',']

theorem object_fragment1454530_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 473) (SourceJson.white (fragment1454530Field006Chars00 ++ tail)) fragment1454530Acc00600 =
      SourceJson.object (fuel + 472) (SourceJson.white tail) fragment1454530Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_006"
  err.flush

noncomputable def fragment1454530Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1454530Field007Value00 : SourceJson := .str (String.ofList ['5', '5', '6', '2', '7', '5', '0', '3', '5', '6', '3', '1', '2', '5', '0', '8', '3', '1', '7', '8', '6', '5', '2', '4', '7', '6', '8', '8', '7', '6', '6', '2', '9', '6', '0', '2', '4', '5', '6', '4', '0', '9', '7', '6', '7', '6', '6', '2', '4', '3', '9', '0', '1', '0', '8', '2', '3', '7', '4', '2', '5', '1', '8', '0', '5', '2', '5', '4', '9', '5', '6', '4', '5', '1', '2', '9', '3', '7', '1', '2', '6', '0', '5', '3', '0', '5', '6', '6', '8', '0', '0', '0', '3', '3', '3', '7', '3', '9', '0', '7', '0', '7', '3', '7', '6', '0', '3', '8', '1', '4', '6', '2', '3', '4', '8', '6', '0', '1', '6', '4', '0', '8', '7', '7', '2', '8', '1', '2', '6', '5', '5', '0', '6', '7', '7', '5', '0', '2', '8', '2', '6', '8', '9', '4', '5', '1', '8', '3', '8', '2', '7', '0', '6', '0', '4', '0', '6', '7', '2', '2', '5', '5', '8', '8', '6', '8', '1', '1', '7', '7', '9', '0', '1', '9', '1', '9', '2', '4', '4', '9', '2', '8', '1', '7', '6', '0', '5', '6', '3', '9', '4', '0', '9', '7', '4', '3', '1', '0', '0', '9', '0', '6', '1', '3', '5', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '9', '7', '2', '6', '2', '3', '1', '4', '6', '3', '2', '8', '1', '3', '1', '6', '3', '8', '3', '1', '4', '2', '7', '7', '8', '1', '8', '6', '1', '7', '4', '6', '0', '9', '1', '7', '0', '7', '5', '6', '3', '1', '3', '9', '4', '1', '2', '7', '5', '5', '5', '1', '5', '1', '8', '8', '4', '3', '5', '5', '0', '7', '2', '5', '0', '5', '9', '8', '9', '2', '8', '2', '8', '2', '2', '6', '8', '1', '8', '9', '0', '0', '8', '8', '8', '3', '3', '3', '8', '6', '7', '3', '0', '3', '9', '4', '6', '4', '0', '4', '0', '1', '0', '5', '0', '0', '3', '2', '4', '3', '7', '0', '9', '5', '3', '1', '5', '1', '2', '8', '9', '3', '9', '8', '4', '9', '4', '9', '4', '7', '6', '3', '2', '1', '6', '7', '1', '8', '6', '1', '2', '9', '2', '0', '9', '1', '3', '9', '6', '9', '5', '5', '5', '4', '8', '8', '4', '6', '8', '9', '0', '6', '7', '2', '1', '7', '8', '2', '3', '7', '0', '7', '5', '4', '9', '4', '5', '0', '9', '9', '7', '6', '2', '8', '4', '1', '6', '5', '7', '4', '5', '3', '0', '5', '0', '8', '3', '2', '7', '7', '1', '0', '8', '7', '5', '7', '8', '2', '8', '2', '7', '2', '6', '8', '7', '2', '4', '6', '2', '0', '6', '4', '3', '6', '6', '1', '9', '2', '1', '0', '3', '0', '9', '2', '9', '7', '3'])
noncomputable def fragment1454530Acc00800 : List (String × SourceJson) := (fragment1454530Field007Key00, fragment1454530Field007Value00) :: fragment1454530Acc00700
noncomputable def fragment1454530Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '5', '6', '2', '7', '5', '0', '3', '5', '6', '3', '1', '2', '5', '0', '8', '3', '1', '7', '8', '6', '5', '2', '4', '7', '6', '8', '8', '7', '6', '6', '2', '9', '6', '0', '2', '4', '5', '6', '4', '0', '9', '7', '6', '7', '6', '6', '2', '4', '3', '9', '0', '1', '0', '8', '2', '3', '7', '4', '2', '5', '1', '8', '0', '5', '2', '5', '4', '9', '5', '6', '4', '5', '1', '2', '9', '3', '7', '1', '2', '6', '0', '5', '3', '0', '5', '6', '6', '8', '0', '0', '0', '3', '3', '3', '7', '3', '9', '0', '7', '0', '7', '3', '7', '6', '0', '3', '8', '1', '4', '6', '2', '3', '4', '8', '6', '0', '1', '6', '4', '0', '8', '7', '7', '2', '8', '1', '2', '6', '5', '5', '0', '6', '7', '7', '5', '0', '2', '8', '2', '6', '8', '9', '4', '5', '1', '8', '3', '8', '2', '7', '0', '6', '0', '4', '0', '6', '7', '2', '2', '5', '5', '8', '8', '6', '8', '1', '1', '7', '7', '9', '0', '1', '9', '1', '9', '2', '4', '4', '9', '2', '8', '1', '7', '6', '0', '5', '6', '3', '9', '4', '0', '9', '7', '4', '3', '1', '0', '0', '9', '0', '6', '1', '3', '5', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '9', '7', '2', '6', '2', '3', '1', '4', '6', '3', '2', '8', '1', '3', '1', '6', '3', '8', '3', '1', '4', '2', '7', '7', '8', '1', '8', '6', '1', '7', '4', '6', '0', '9', '1', '7', '0', '7', '5', '6', '3', '1', '3', '9', '4', '1', '2', '7', '5', '5', '5', '1', '5', '1', '8', '8', '4', '3', '5', '5', '0', '7', '2', '5', '0', '5', '9', '8', '9', '2', '8', '2', '8', '2', '2', '6', '8', '1', '8', '9', '0', '0', '8', '8', '8', '3', '3', '3', '8', '6', '7', '3', '0', '3', '9', '4', '6', '4', '0', '4', '0', '1', '0', '5', '0', '0', '3', '2', '4', '3', '7', '0', '9', '5', '3', '1', '5', '1', '2', '8', '9', '3', '9', '8', '4', '9', '4', '9', '4', '7', '6', '3', '2', '1', '6', '7', '1', '8', '6', '1', '2', '9', '2', '0', '9', '1', '3', '9', '6', '9', '5', '5', '5', '4', '8', '8', '4', '6', '8', '9', '0', '6', '7', '2', '1', '7', '8', '2', '3', '7', '0', '7', '5', '4', '9', '4', '5', '0', '9', '9', '7', '6', '2', '8', '4', '1', '6', '5', '7', '4', '5', '3', '0', '5', '0', '8', '3', '2', '7', '7', '1', '0', '8', '7', '5', '7', '8', '2', '8', '2', '7', '2', '6', '8', '7', '2', '4', '6', '2', '0', '6', '4', '3', '6', '6', '1', '9', '2', '1', '0', '3', '0', '9', '2', '9', '7', '3', '"', ',']

theorem object_fragment1454530_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment1454530Field007Chars00 ++ tail)) fragment1454530Acc00700 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment1454530Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_007"
  err.flush

noncomputable def fragment1454530Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1454530Field008Value00 : SourceJson := .str (String.ofList ['3', '5', '8', '6', '4', '2', '1', '9', '7', '4', '6', '7', '5', '1', '8', '0', '3', '8', '2'])
noncomputable def fragment1454530Acc00900 : List (String × SourceJson) := (fragment1454530Field008Key00, fragment1454530Field008Value00) :: fragment1454530Acc00800
noncomputable def fragment1454530Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '5', '8', '6', '4', '2', '1', '9', '7', '4', '6', '7', '5', '1', '8', '0', '3', '8', '2', '"', ',']

theorem object_fragment1454530_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment1454530Field008Chars00 ++ tail)) fragment1454530Acc00800 =
      SourceJson.object (fuel + 470) (SourceJson.white tail) fragment1454530Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_008"
  err.flush

noncomputable def fragment1454530Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1454530Field009Value00 : SourceJson := .str (String.ofList ['4', '0', '1', '6', '6', '0', '0', '9', '8', '3', '9', '1', '0', '5', '2', '0', '6', '0', '8', '4'])
noncomputable def fragment1454530Acc01000 : List (String × SourceJson) := (fragment1454530Field009Key00, fragment1454530Field009Value00) :: fragment1454530Acc00900
noncomputable def fragment1454530Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '1', '6', '6', '0', '0', '9', '8', '3', '9', '1', '0', '5', '2', '0', '6', '0', '8', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment1454530_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment1454530Field009Chars00 ++ tail)) fragment1454530Acc00900 =
      .ok (.obj (fragment1454530Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1454530_object_field_009"
  err.flush

noncomputable def fragment1454530Chars : List Char := '{' :: (fragment1454530Field000Chars00 ++ fragment1454530Field001Chars00 ++ fragment1454530Field002Chars00 ++ fragment1454530Field003Chars00 ++ fragment1454530Field004Chars00 ++ fragment1454530Field005Chars00 ++ fragment1454530Field006Chars00 ++ fragment1454530Field007Chars00 ++ fragment1454530Field008Chars00 ++ fragment1454530Field009Chars00)
noncomputable def fragment1454530Value : SourceJson := .obj (fragment1454530Acc01000.reverse)

theorem value_fragment1454530 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 480) (fragment1454530Chars ++ tail) =
      .ok (fragment1454530Value, tail) := by
  have hinput : fragment1454530Chars ++ tail = '{' :: (fragment1454530Field000Chars00 ++ (fragment1454530Field001Chars00 ++ (fragment1454530Field002Chars00 ++ (fragment1454530Field003Chars00 ++ (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment1454530Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 480) (fragment1454530Chars ++ tail) =
        SourceJson.value (fuel + 480) ('{' :: (fragment1454530Field000Chars00 ++ (fragment1454530Field001Chars00 ++ (fragment1454530Field002Chars00 ++ (fragment1454530Field003Chars00 ++ (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 480)) hinput
    _ = SourceJson.object (fuel + 479) (SourceJson.white (fragment1454530Field000Chars00 ++ (fragment1454530Field001Chars00 ++ (fragment1454530Field002Chars00 ++ (fragment1454530Field003Chars00 ++ (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))))))))))) fragment1454530Acc00000 := by rfl
    _ = SourceJson.object (fuel + 478) (SourceJson.white (fragment1454530Field001Chars00 ++ (fragment1454530Field002Chars00 ++ (fragment1454530Field003Chars00 ++ (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail))))))))))) fragment1454530Acc00100 := object_fragment1454530_field_000 fuel (fragment1454530Field001Chars00 ++ (fragment1454530Field002Chars00 ++ (fragment1454530Field003Chars00 ++ (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 477) (SourceJson.white (fragment1454530Field002Chars00 ++ (fragment1454530Field003Chars00 ++ (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))))))))) fragment1454530Acc00200 := object_fragment1454530_field_001 fuel (fragment1454530Field002Chars00 ++ (fragment1454530Field003Chars00 ++ (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment1454530Field003Chars00 ++ (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail))))))))) fragment1454530Acc00300 := object_fragment1454530_field_002 fuel (fragment1454530Field003Chars00 ++ (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))))))) fragment1454530Acc00400 := object_fragment1454530_field_003 fuel (fragment1454530Field004Chars00 ++ (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 474) (SourceJson.white (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail))))))) fragment1454530Acc00500 := object_fragment1454530_field_004 fuel (fragment1454530Field005Chars00 ++ (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 473) (SourceJson.white (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))))) fragment1454530Acc00600 := object_fragment1454530_field_005 fuel (fragment1454530Field006Chars00 ++ (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail))))) fragment1454530Acc00700 := object_fragment1454530_field_006 fuel (fragment1454530Field007Chars00 ++ (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))) fragment1454530Acc00800 := object_fragment1454530_field_007 fuel (fragment1454530Field008Chars00 ++ (fragment1454530Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment1454530Field009Chars00 ++ (tail))) fragment1454530Acc00900 := object_fragment1454530_field_008 fuel (fragment1454530Field009Chars00 ++ (tail))
    _ = .ok (fragment1454530Value, tail) := object_fragment1454530_field_009 fuel (tail)

noncomputable def fragment1456658Acc00000 : List (String × SourceJson) := []

noncomputable def fragment1456658Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment1456658Field000Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment1456658Acc00100 : List (String × SourceJson) := (fragment1456658Field000Key00, fragment1456658Field000Value00) :: fragment1456658Acc00000
noncomputable def fragment1456658Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', ',']

theorem object_fragment1456658_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment1456658Field000Chars00 ++ tail)) fragment1456658Acc00000 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment1456658Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_000"
  err.flush

noncomputable def fragment1456658Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment1456658Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['8', '5']), .number (String.ofList ['5', '0']), .number (String.ofList ['4', '7']), .number (String.ofList ['9']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment1456658Acc00200 : List (String × SourceJson) := (fragment1456658Field001Key00, fragment1456658Field001Value00) :: fragment1456658Acc00100
noncomputable def fragment1456658Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1456658_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment1456658Field001Chars00 ++ tail)) fragment1456658Acc00100 =
      SourceJson.object (fuel + 474) (SourceJson.white tail) fragment1456658Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_001"
  err.flush

noncomputable def fragment1456658Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment1456658Field002Value00 : SourceJson := .str (String.ofList ['4', '5', '4', '6', '7', '3', '2', '6', '0', '3', '9', '0', '2', '2', '7', '6', '9', '9', '2', '8', '8', '6', '3', '8', '1', '5', '1', '9', '5', '4', '3', '3', '5', '0', '5', '8', '1', '3', '6', '7', '9', '5', '4', '9', '6', '2', '7', '/', '1', '3', '6', '4', '5', '6', '7', '2', '8', '1', '4', '2', '9', '5', '2', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1456658Acc00300 : List (String × SourceJson) := (fragment1456658Field002Key00, fragment1456658Field002Value00) :: fragment1456658Acc00200
noncomputable def fragment1456658Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '5', '4', '6', '7', '3', '2', '6', '0', '3', '9', '0', '2', '2', '7', '6', '9', '9', '2', '8', '8', '6', '3', '8', '1', '5', '1', '9', '5', '4', '3', '3', '5', '0', '5', '8', '1', '3', '6', '7', '9', '5', '4', '9', '6', '2', '7', '/', '1', '3', '6', '4', '5', '6', '7', '2', '8', '1', '4', '2', '9', '5', '2', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1456658_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 474) (SourceJson.white (fragment1456658Field002Chars00 ++ tail)) fragment1456658Acc00200 =
      SourceJson.object (fuel + 473) (SourceJson.white tail) fragment1456658Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_002"
  err.flush

noncomputable def fragment1456658Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment1456658Field003Value00 : SourceJson := .str (String.ofList ['4', '8', '9', '3', '0', '7', '9', '7', '0', '3', '/', '2', '9', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1456658Acc00400 : List (String × SourceJson) := (fragment1456658Field003Key00, fragment1456658Field003Value00) :: fragment1456658Acc00300
noncomputable def fragment1456658Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '8', '9', '3', '0', '7', '9', '7', '0', '3', '/', '2', '9', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1456658_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 473) (SourceJson.white (fragment1456658Field003Chars00 ++ tail)) fragment1456658Acc00300 =
      SourceJson.object (fuel + 472) (SourceJson.white tail) fragment1456658Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_003"
  err.flush

noncomputable def fragment1456658Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment1456658Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '0', '4', '6', '9', '4', '1', '/', '4', '2', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '0', '9', '9', '1', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0'])]
noncomputable def fragment1456658Acc00500 : List (String × SourceJson) := (fragment1456658Field004Key00, fragment1456658Field004Value00) :: fragment1456658Acc00400
noncomputable def fragment1456658Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '0', '4', '6', '9', '4', '1', '/', '4', '2', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '0', '9', '9', '1', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1456658_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment1456658Field004Chars00 ++ tail)) fragment1456658Acc00400 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment1456658Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_004"
  err.flush

noncomputable def fragment1456658Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment1456658Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '7', '5', '5', '6', '9', '5', '9', '4', '3', '9', '6', '5', '7', '3', '5', '4', '1', '9', '7', '5', '8', '4', '7', '/', '7', '7', '7', '6', '3', '6', '0', '6', '8', '0', '2', '4', '2', '7', '0', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '6', '5', '5', '8', '1', '3', '6', '0', '1', '3', '8', '2', '4', '1', '3', '8', '6', '0', '6', '8', '5', '9', '/', '2', '2', '4', '6', '5', '0', '4', '1', '9', '6', '5', '1', '4', '5', '5', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '4', '5', '3', '8', '4', '7', '5', '8', '0', '5', '2', '0', '0', '8', '7', '7', '4', '5', '3', '0', '3', '1', '/', '3', '1', '9', '2', '4', '0', '0', '7', '0', '0', '3', '1', '0', '1', '6', '1', '3', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '1', '7', '5', '5', '8', '1', '0', '9', '6', '8', '6', '0', '5', '2', '8', '6', '5', '6', '7', '5', '5', '8', '2', '3', '/', '6', '0', '6', '5', '5', '6', '1', '3', '3', '0', '5', '8', '9', '3', '0', '6', '5', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '8', '0', '6', '0', '2', '2', '0', '4', '0', '0', '1', '4', '8', '5', '9', '0', '4', '3', '6', '6', '8', '1', '7', '/', '3', '1', '9', '2', '4', '0', '0', '7', '0', '0', '3', '1', '0', '1', '6', '1', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '2', '3', '5', '7', '3', '0', '4', '3', '9', '0', '2', '4', '4', '0', '9', '2', '3', '2', '3', '5', '3', '/', '3', '6', '2', '7', '7', '2', '8', '0', '6', '8', '5', '3', '4', '2', '7', '4', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '5', '1', '4', '3', '2', '3', '1', '8', '1', '0', '7', '8', '5', '0', '5', '1', '9', '8', '8', '7', '/', '1', '3', '6', '0', '3', '9', '8', '0', '2', '5', '7', '0', '0', '3', '5', '2', '8', '4', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '6', '7', '7', '6', '2', '3', '2', '2', '8', '1', '8', '1', '9', '3', '3', '9', '6', '1', '2', '1', '0', '9', '1', '/', '1', '9', '1', '5', '4', '4', '0', '4', '2', '0', '1', '8', '6', '0', '9', '6', '8', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '3', '6', '4', '9', '1', '8', '9', '3', '7', '6', '9', '9', '2', '9', '8', '1', '2', '5', '8', '2', '5', '1', '/', '4', '4', '9', '3', '0', '0', '8', '3', '9', '3', '0', '2', '9', '1', '1', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '1', '4', '6', '9', '4', '4', '8', '5', '8', '6', '0', '8', '7', '4', '2', '8', '5', '7', '4', '1', '6', '9', '/', '6', '7', '3', '9', '5', '1', '2', '5', '8', '9', '5', '4', '3', '6', '7', '3', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment1456658Acc00600 : List (String × SourceJson) := (fragment1456658Field005Key00, fragment1456658Field005Value00) :: fragment1456658Acc00500
noncomputable def fragment1456658Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '5', '6', '9', '5', '9', '4', '3', '9', '6', '5', '7', '3', '5', '4', '1', '9', '7', '5', '8', '4', '7', '/', '7', '7', '7', '6', '3', '6', '0', '6', '8', '0', '2', '4', '2', '7', '0', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '6', '5', '5', '8', '1', '3', '6', '0', '1', '3', '8', '2', '4', '1', '3', '8', '6', '0', '6', '8', '5', '9', '/', '2', '2', '4', '6', '5', '0', '4', '1', '9', '6', '5', '1', '4', '5', '5', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '4', '5', '3', '8', '4', '7', '5', '8', '0', '5', '2', '0', '0', '8', '7', '7', '4', '5', '3', '0', '3', '1', '/', '3', '1', '9', '2', '4', '0', '0', '7', '0', '0', '3', '1', '0', '1', '6', '1', '3', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '1', '7', '5', '5', '8', '1', '0', '9', '6', '8', '6', '0', '5', '2', '8', '6', '5', '6', '7', '5', '5', '8', '2', '3', '/', '6', '0', '6', '5', '5', '6', '1', '3', '3', '0', '5', '8', '9', '3', '0', '6', '5', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '8', '0', '6', '0', '2', '2', '0', '4', '0', '0', '1', '4', '8', '5', '9', '0', '4', '3', '6', '6', '8', '1', '7', '/', '3', '1', '9', '2', '4', '0', '0', '7', '0', '0', '3', '1', '0', '1', '6', '1', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '2', '3', '5', '7', '3', '0', '4', '3', '9', '0', '2', '4', '4', '0', '9', '2', '3', '2', '3', '5', '3', '/', '3', '6', '2', '7', '7', '2', '8', '0', '6', '8', '5', '3', '4', '2', '7', '4', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '5', '1', '4', '3', '2', '3', '1', '8', '1', '0', '7', '8', '5', '0', '5', '1', '9', '8', '8', '7', '/', '1', '3', '6', '0', '3', '9', '8', '0', '2', '5', '7', '0', '0', '3', '5', '2', '8', '4', '3', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '6', '7', '7', '6', '2', '3', '2', '2', '8', '1', '8', '1', '9', '3', '3', '9', '6', '1', '2', '1', '0', '9', '1', '/', '1', '9', '1', '5', '4', '4', '0', '4', '2', '0', '1', '8', '6', '0', '9', '6', '8', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '3', '6', '4', '9', '1', '8', '9', '3', '7', '6', '9', '9', '2', '9', '8', '1', '2', '5', '8', '2', '5', '1', '/', '4', '4', '9', '3', '0', '0', '8', '3', '9', '3', '0', '2', '9', '1', '1', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '1', '4', '6', '9', '4', '4', '8', '5', '8', '6', '0', '8', '7', '4', '2', '8', '5', '7', '4', '1', '6', '9', '/', '6', '7', '3', '9', '5', '1', '2', '5', '8', '9', '5', '4', '3', '6', '7', '3', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1456658_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment1456658Field005Chars00 ++ tail)) fragment1456658Acc00500 =
      SourceJson.object (fuel + 470) (SourceJson.white tail) fragment1456658Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_005"
  err.flush

noncomputable def fragment1456658Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1456658Field006Value00 : SourceJson := .str (String.ofList ['5', '5', '6', '1', '8', '8', '1', '2', '5', '4', '7', '8', '0', '6', '4', '2', '5', '3', '7', '3', '4', '4', '0', '5', '7', '1', '9', '9', '5', '9', '7', '9', '6', '6', '6', '3', '9', '5', '7', '6', '1', '9', '7', '6', '0', '0', '6', '5', '1', '3', '7', '3', '0', '1', '9', '5', '2', '5', '/', '9', '9', '8', '5', '4', '5', '6', '8', '1', '3', '5', '2', '1', '7', '5', '9', '5', '7', '4', '6', '8', '2', '4', '6', '3', '9', '1', '8', '8', '2', '1', '3', '0', '8', '1', '6', '9', '0', '0', '2', '6', '5', '5', '3', '3', '2', '6', '7', '1', '3', '3', '0', '8', '4', '3', '1', '3', '5', '4', '7', '9', '0', '9', '4', '2', '9', '7', '6'])
noncomputable def fragment1456658Acc00700 : List (String × SourceJson) := (fragment1456658Field006Key00, fragment1456658Field006Value00) :: fragment1456658Acc00600
noncomputable def fragment1456658Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '5', '6', '1', '8', '8', '1', '2', '5', '4', '7', '8', '0', '6', '4', '2', '5', '3', '7', '3', '4', '4', '0', '5', '7', '1', '9', '9', '5', '9', '7', '9', '6', '6', '6', '3', '9', '5', '7', '6', '1', '9', '7', '6', '0', '0', '6', '5', '1', '3', '7', '3', '0', '1', '9', '5', '2', '5', '/', '9', '9', '8', '5', '4', '5', '6', '8', '1', '3', '5', '2', '1', '7', '5', '9', '5', '7', '4', '6', '8', '2', '4', '6', '3', '9', '1', '8', '8', '2', '1', '3', '0', '8', '1', '6', '9', '0', '0', '2', '6', '5', '5', '3', '3', '2', '6', '7', '1', '3', '3', '0', '8', '4', '3', '1', '3', '5', '4', '7', '9', '0', '9', '4', '2', '9', '7', '6', '"', ',']

theorem object_fragment1456658_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment1456658Field006Chars00 ++ tail)) fragment1456658Acc00600 =
      SourceJson.object (fuel + 469) (SourceJson.white tail) fragment1456658Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_006"
  err.flush

noncomputable def fragment1456658Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1456658Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '0', '8', '0', '5', '4', '4', '2', '3', '1', '7', '5', '8', '8', '4', '3', '9', '2', '9', '1', '0', '0', '1', '5', '6', '5', '9', '8', '9', '0', '7', '7', '4', '6', '9', '6', '9', '6', '6', '9', '5', '3', '0', '7', '3', '1', '5', '5', '2', '1', '3', '4', '5', '6', '1', '2', '8', '4', '9', '5', '0', '7', '9', '9', '0', '0', '2', '6', '6', '0', '1', '2', '6', '3', '5', '8', '7', '8', '8', '3', '2', '1', '5', '8', '2', '4', '4', '5', '9', '6', '0', '8', '1', '9', '4', '2', '1', '5', '3', '3', '1', '5', '7', '5', '4', '1', '1', '9', '3', '3', '2', '1', '4', '9', '5', '7', '4', '8', '4', '1', '2', '5', '0', '4', '5', '9', '8', '2', '2', '2', '5', '4', '5', '5', '9', '2', '5', '9', '1', '7', '9', '2', '7', '1', '8', '1', '8', '4', '3', '9', '6', '0', '3', '6', '6', '3', '2', '1', '4', '8', '4', '5', '8', '1', '9', '4', '5', '0', '8', '1', '5', '5', '3', '2', '4', '6', '9', '8', '9', '4', '3', '3', '7', '1', '6', '0', '4', '8', '0', '2', '3', '9', '3', '9', '1', '0', '9', '2', '5', '4', '9', '5', '6', '4', '0', '0', '5', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '4', '2', '1', '5', '5', '7', '5', '3', '3', '3', '4', '4', '0', '6', '0', '5', '7', '2', '6', '3', '3', '3', '5', '2', '1', '6', '5', '8', '3', '2', '2', '2', '5', '2', '1', '0', '0', '6', '6', '5', '4', '8', '8', '8', '5', '3', '7', '1', '4', '9', '3', '8', '4', '2', '6', '0', '9', '8', '4', '0', '4', '3', '9', '1', '6', '3', '1', '1', '6', '1', '7', '2', '5', '8', '8', '1', '3', '2', '3', '5', '1', '6', '9', '9', '6', '8', '0', '3', '9', '5', '3', '4', '0', '1', '8', '6', '5', '7', '0', '9', '5', '3', '1', '6', '2', '6', '0', '3', '0', '7', '3', '5', '8', '5', '9', '9', '0', '8', '9', '7', '0', '6', '8', '1', '8', '0', '8', '5', '2', '3', '2', '7', '6', '4', '3', '3', '6', '4', '8', '8', '6', '8', '9', '9', '2', '3', '9', '8', '8', '6', '1', '7', '9', '7', '7', '7', '5', '6', '0', '2', '3', '0', '4', '2', '7', '6', '5', '5', '2', '4', '8', '9', '6', '3', '7', '6', '8', '1', '0', '5', '8', '9', '3', '4', '9', '4', '3', '5', '6', '7', '1', '9', '5', '0', '3', '2', '9', '6', '6', '1', '2', '9', '8', '5', '2', '2', '3', '3', '8', '7', '2', '2', '9', '3', '9', '8', '8', '1', '3', '8', '4', '8', '2', '7', '4', '3', '1', '3', '6', '3', '4', '7', '1', '7', '4', '1'])
noncomputable def fragment1456658Acc00800 : List (String × SourceJson) := (fragment1456658Field007Key00, fragment1456658Field007Value00) :: fragment1456658Acc00700
noncomputable def fragment1456658Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '0', '8', '0', '5', '4', '4', '2', '3', '1', '7', '5', '8', '8', '4', '3', '9', '2', '9', '1', '0', '0', '1', '5', '6', '5', '9', '8', '9', '0', '7', '7', '4', '6', '9', '6', '9', '6', '6', '9', '5', '3', '0', '7', '3', '1', '5', '5', '2', '1', '3', '4', '5', '6', '1', '2', '8', '4', '9', '5', '0', '7', '9', '9', '0', '0', '2', '6', '6', '0', '1', '2', '6', '3', '5', '8', '7', '8', '8', '3', '2', '1', '5', '8', '2', '4', '4', '5', '9', '6', '0', '8', '1', '9', '4', '2', '1', '5', '3', '3', '1', '5', '7', '5', '4', '1', '1', '9', '3', '3', '2', '1', '4', '9', '5', '7', '4', '8', '4', '1', '2', '5', '0', '4', '5', '9', '8', '2', '2', '2', '5', '4', '5', '5', '9', '2', '5', '9', '1', '7', '9', '2', '7', '1', '8', '1', '8', '4', '3', '9', '6', '0', '3', '6', '6', '3', '2', '1', '4', '8', '4', '5', '8', '1', '9', '4', '5', '0', '8', '1', '5', '5', '3', '2', '4', '6', '9', '8', '9', '4', '3', '3', '7', '1', '6', '0', '4', '8', '0', '2', '3', '9', '3', '9', '1', '0', '9', '2', '5', '4', '9', '5', '6', '4', '0', '0', '5', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '4', '2', '1', '5', '5', '7', '5', '3', '3', '3', '4', '4', '0', '6', '0', '5', '7', '2', '6', '3', '3', '3', '5', '2', '1', '6', '5', '8', '3', '2', '2', '2', '5', '2', '1', '0', '0', '6', '6', '5', '4', '8', '8', '8', '5', '3', '7', '1', '4', '9', '3', '8', '4', '2', '6', '0', '9', '8', '4', '0', '4', '3', '9', '1', '6', '3', '1', '1', '6', '1', '7', '2', '5', '8', '8', '1', '3', '2', '3', '5', '1', '6', '9', '9', '6', '8', '0', '3', '9', '5', '3', '4', '0', '1', '8', '6', '5', '7', '0', '9', '5', '3', '1', '6', '2', '6', '0', '3', '0', '7', '3', '5', '8', '5', '9', '9', '0', '8', '9', '7', '0', '6', '8', '1', '8', '0', '8', '5', '2', '3', '2', '7', '6', '4', '3', '3', '6', '4', '8', '8', '6', '8', '9', '9', '2', '3', '9', '8', '8', '6', '1', '7', '9', '7', '7', '7', '5', '6', '0', '2', '3', '0', '4', '2', '7', '6', '5', '5', '2', '4', '8', '9', '6', '3', '7', '6', '8', '1', '0', '5', '8', '9', '3', '4', '9', '4', '3', '5', '6', '7', '1', '9', '5', '0', '3', '2', '9', '6', '6', '1', '2', '9', '8', '5', '2', '2', '3', '3', '8', '7', '2', '2', '9', '3', '9', '8', '8', '1', '3', '8', '4', '8', '2', '7', '4', '3', '1', '3', '6', '3', '4', '7', '1', '7', '4', '1', '"', ',']

theorem object_fragment1456658_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 469) (SourceJson.white (fragment1456658Field007Chars00 ++ tail)) fragment1456658Acc00700 =
      SourceJson.object (fuel + 468) (SourceJson.white tail) fragment1456658Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_007"
  err.flush

noncomputable def fragment1456658Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1456658Field008Value00 : SourceJson := .str (String.ofList ['4', '4', '1', '2', '9', '9', '4', '2', '1', '9', '1', '7', '3', '6', '9', '6', '0', '1', '2'])
noncomputable def fragment1456658Acc00900 : List (String × SourceJson) := (fragment1456658Field008Key00, fragment1456658Field008Value00) :: fragment1456658Acc00800
noncomputable def fragment1456658Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '1', '2', '9', '9', '4', '2', '1', '9', '1', '7', '3', '6', '9', '6', '0', '1', '2', '"', ',']

theorem object_fragment1456658_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 468) (SourceJson.white (fragment1456658Field008Chars00 ++ tail)) fragment1456658Acc00800 =
      SourceJson.object (fuel + 467) (SourceJson.white tail) fragment1456658Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_008"
  err.flush

noncomputable def fragment1456658Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1456658Field009Value00 : SourceJson := .str (String.ofList ['4', '9', '3', '4', '0', '3', '0', '2', '3', '7', '7', '5', '1', '0', '3', '8', '3', '7', '1', '6'])
noncomputable def fragment1456658Acc01000 : List (String × SourceJson) := (fragment1456658Field009Key00, fragment1456658Field009Value00) :: fragment1456658Acc00900
noncomputable def fragment1456658Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '3', '4', '0', '3', '0', '2', '3', '7', '7', '5', '1', '0', '3', '8', '3', '7', '1', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment1456658_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 467) (SourceJson.white (fragment1456658Field009Chars00 ++ tail)) fragment1456658Acc00900 =
      .ok (.obj (fragment1456658Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1456658_object_field_009"
  err.flush

noncomputable def fragment1456658Chars : List Char := '{' :: (fragment1456658Field000Chars00 ++ fragment1456658Field001Chars00 ++ fragment1456658Field002Chars00 ++ fragment1456658Field003Chars00 ++ fragment1456658Field004Chars00 ++ fragment1456658Field005Chars00 ++ fragment1456658Field006Chars00 ++ fragment1456658Field007Chars00 ++ fragment1456658Field008Chars00 ++ fragment1456658Field009Chars00)
noncomputable def fragment1456658Value : SourceJson := .obj (fragment1456658Acc01000.reverse)

theorem value_fragment1456658 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 477) (fragment1456658Chars ++ tail) =
      .ok (fragment1456658Value, tail) := by
  have hinput : fragment1456658Chars ++ tail = '{' :: (fragment1456658Field000Chars00 ++ (fragment1456658Field001Chars00 ++ (fragment1456658Field002Chars00 ++ (fragment1456658Field003Chars00 ++ (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment1456658Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 477) (fragment1456658Chars ++ tail) =
        SourceJson.value (fuel + 477) ('{' :: (fragment1456658Field000Chars00 ++ (fragment1456658Field001Chars00 ++ (fragment1456658Field002Chars00 ++ (fragment1456658Field003Chars00 ++ (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 477)) hinput
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment1456658Field000Chars00 ++ (fragment1456658Field001Chars00 ++ (fragment1456658Field002Chars00 ++ (fragment1456658Field003Chars00 ++ (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))))))))))) fragment1456658Acc00000 := by rfl
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment1456658Field001Chars00 ++ (fragment1456658Field002Chars00 ++ (fragment1456658Field003Chars00 ++ (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail))))))))))) fragment1456658Acc00100 := object_fragment1456658_field_000 fuel (fragment1456658Field001Chars00 ++ (fragment1456658Field002Chars00 ++ (fragment1456658Field003Chars00 ++ (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 474) (SourceJson.white (fragment1456658Field002Chars00 ++ (fragment1456658Field003Chars00 ++ (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))))))))) fragment1456658Acc00200 := object_fragment1456658_field_001 fuel (fragment1456658Field002Chars00 ++ (fragment1456658Field003Chars00 ++ (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 473) (SourceJson.white (fragment1456658Field003Chars00 ++ (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail))))))))) fragment1456658Acc00300 := object_fragment1456658_field_002 fuel (fragment1456658Field003Chars00 ++ (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))))))) fragment1456658Acc00400 := object_fragment1456658_field_003 fuel (fragment1456658Field004Chars00 ++ (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail))))))) fragment1456658Acc00500 := object_fragment1456658_field_004 fuel (fragment1456658Field005Chars00 ++ (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))))) fragment1456658Acc00600 := object_fragment1456658_field_005 fuel (fragment1456658Field006Chars00 ++ (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 469) (SourceJson.white (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail))))) fragment1456658Acc00700 := object_fragment1456658_field_006 fuel (fragment1456658Field007Chars00 ++ (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 468) (SourceJson.white (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))) fragment1456658Acc00800 := object_fragment1456658_field_007 fuel (fragment1456658Field008Chars00 ++ (fragment1456658Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 467) (SourceJson.white (fragment1456658Field009Chars00 ++ (tail))) fragment1456658Acc00900 := object_fragment1456658_field_008 fuel (fragment1456658Field009Chars00 ++ (tail))
    _ = .ok (fragment1456658Value, tail) := object_fragment1456658_field_009 fuel (tail)

noncomputable def fragment1458777Acc00000 : List (String × SourceJson) := []

noncomputable def fragment1458777Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment1458777Field000Value00 : SourceJson := .number (String.ofList ['2'])
noncomputable def fragment1458777Acc00100 : List (String × SourceJson) := (fragment1458777Field000Key00, fragment1458777Field000Value00) :: fragment1458777Acc00000
noncomputable def fragment1458777Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', ',']

theorem object_fragment1458777_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 544) (SourceJson.white (fragment1458777Field000Chars00 ++ tail)) fragment1458777Acc00000 =
      SourceJson.object (fuel + 543) (SourceJson.white tail) fragment1458777Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_000"
  err.flush

noncomputable def fragment1458777Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment1458777Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['8', '5']), .number (String.ofList ['5', '0']), .number (String.ofList ['4', '7']), .number (String.ofList ['9']), .number (String.ofList ['5']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment1458777Acc00200 : List (String × SourceJson) := (fragment1458777Field001Key00, fragment1458777Field001Value00) :: fragment1458777Acc00100
noncomputable def fragment1458777Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1458777_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 543) (SourceJson.white (fragment1458777Field001Chars00 ++ tail)) fragment1458777Acc00100 =
      SourceJson.object (fuel + 542) (SourceJson.white tail) fragment1458777Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_001"
  err.flush

noncomputable def fragment1458777Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment1458777Field002Value00 : SourceJson := .str (String.ofList ['4', '9', '6', '7', '0', '1', '5', '0', '5', '2', '5', '2', '7', '0', '6', '7', '0', '7', '4', '9', '4', '8', '4', '1', '6', '5', '5', '4', '5', '0', '3', '6', '4', '7', '8', '3', '1', '3', '7', '2', '2', '5', '8', '9', '9', '2', '6', '7', '1', '/', '1', '2', '2', '5', '9', '2', '4', '7', '1', '8', '6', '5', '9', '8', '3', '7', '7', '0', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1458777Acc00300 : List (String × SourceJson) := (fragment1458777Field002Key00, fragment1458777Field002Value00) :: fragment1458777Acc00200
noncomputable def fragment1458777Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '9', '6', '7', '0', '1', '5', '0', '5', '2', '5', '2', '7', '0', '6', '7', '0', '7', '4', '9', '4', '8', '4', '1', '6', '5', '5', '4', '5', '0', '3', '6', '4', '7', '8', '3', '1', '3', '7', '2', '2', '5', '8', '9', '9', '2', '6', '7', '1', '/', '1', '2', '2', '5', '9', '2', '4', '7', '1', '8', '6', '5', '9', '8', '3', '7', '7', '0', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1458777_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 542) (SourceJson.white (fragment1458777Field002Chars00 ++ tail)) fragment1458777Acc00200 =
      SourceJson.object (fuel + 541) (SourceJson.white tail) fragment1458777Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_002"
  err.flush

noncomputable def fragment1458777Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment1458777Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '9', '6', '8', '9', '2', '9', '5', '6', '1', '/', '1', '1', '8', '0', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1458777Acc00400 : List (String × SourceJson) := (fragment1458777Field003Key00, fragment1458777Field003Value00) :: fragment1458777Acc00300
noncomputable def fragment1458777Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '9', '6', '8', '9', '2', '9', '5', '6', '1', '/', '1', '1', '8', '0', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1458777_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 541) (SourceJson.white (fragment1458777Field003Chars00 ++ tail)) fragment1458777Acc00300 =
      SourceJson.object (fuel + 540) (SourceJson.white tail) fragment1458777Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_003"
  err.flush

noncomputable def fragment1458777Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment1458777Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '0', '4', '6', '9', '4', '1', '/', '4', '2', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '9', '6', '8', '7', '9', '/', '1', '6', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0'])]
noncomputable def fragment1458777Acc00500 : List (String × SourceJson) := (fragment1458777Field004Key00, fragment1458777Field004Value00) :: fragment1458777Acc00400
noncomputable def fragment1458777Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '0', '4', '6', '9', '4', '1', '/', '4', '2', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '9', '6', '8', '7', '9', '/', '1', '6', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1458777_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 540) (SourceJson.white (fragment1458777Field004Chars00 ++ tail)) fragment1458777Acc00400 =
      SourceJson.object (fuel + 539) (SourceJson.white tail) fragment1458777Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_004"
  err.flush

noncomputable def fragment1458777Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment1458777Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '8', '1', '1', '3', '3', '0', '1', '9', '4', '2', '8', '9', '2', '0', '6', '8', '8', '9', '9', '3', '7', '4', '3', '7', '/', '2', '6', '7', '4', '3', '0', '8', '2', '6', '7', '9', '1', '4', '2', '0', '7', '1', '9', '9', '3', '2', '7', '3', '6', '0', '0', '0']), .str (String.ofList ['8', '3', '1', '1', '4', '1', '0', '9', '1', '0', '0', '5', '4', '9', '2', '3', '3', '1', '5', '5', '1', '3', '2', '0', '6', '4', '6', '7', '/', '1', '6', '7', '1', '4', '4', '2', '6', '6', '7', '4', '4', '6', '3', '7', '9', '4', '9', '9', '5', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '2', '9', '6', '0', '4', '4', '4', '9', '8', '8', '6', '7', '6', '6', '8', '2', '7', '7', '8', '1', '7', '3', '6', '9', '7', '9', '/', '2', '6', '3', '9', '1', '2', '0', '0', '0', '1', '2', '3', '1', '1', '2', '5', '5', '2', '5', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '5', '5', '0', '9', '1', '5', '0', '9', '9', '2', '0', '3', '0', '3', '9', '1', '6', '5', '0', '0', '6', '2', '9', '0', '9', '9', '/', '3', '1', '3', '3', '9', '5', '5', '0', '0', '1', '4', '6', '1', '9', '6', '1', '5', '6', '1', '7', '1', '1', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '5', '5', '3', '8', '4', '6', '1', '7', '9', '0', '1', '1', '7', '9', '6', '4', '0', '1', '4', '5', '5', '8', '2', '6', '9', '/', '6', '5', '9', '7', '8', '0', '0', '0', '0', '3', '0', '7', '7', '8', '1', '3', '8', '1', '4', '1', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '0', '0', '3', '6', '4', '7', '7', '6', '6', '9', '9', '1', '2', '9', '2', '8', '9', '5', '9', '0', '7', '1', '9', '/', '4', '7', '9', '8', '4', '0', '0', '0', '0', '2', '2', '3', '8', '4', '1', '0', '0', '4', '6', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '5', '9', '6', '4', '0', '9', '8', '0', '6', '9', '8', '8', '1', '4', '6', '9', '3', '8', '3', '3', '6', '9', '6', '3', '7', '/', '7', '1', '9', '7', '6', '0', '0', '0', '0', '3', '3', '5', '7', '6', '1', '5', '0', '6', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '1', '2', '3', '2', '5', '2', '9', '2', '9', '7', '7', '2', '3', '9', '9', '1', '8', '5', '0', '3', '8', '9', '8', '8', '2', '7', '/', '7', '9', '1', '7', '3', '6', '0', '0', '0', '3', '6', '9', '3', '3', '7', '6', '5', '7', '6', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '4', '4', '5', '6', '9', '0', '9', '2', '6', '5', '3', '6', '1', '7', '5', '0', '9', '9', '6', '5', '9', '6', '1', '8', '7', '7', '/', '1', '2', '5', '3', '5', '8', '2', '0', '0', '0', '5', '8', '4', '7', '8', '4', '6', '2', '4', '6', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '0', '8', '0', '0', '0', '4', '8', '6', '4', '6', '9', '1', '8', '8', '9', '4', '7', '3', '5', '6', '5', '3', '4', '8', '2', '9', '/', '5', '0', '1', '4', '3', '2', '8', '0', '0', '2', '3', '3', '9', '1', '3', '8', '4', '9', '8', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment1458777Acc00600 : List (String × SourceJson) := (fragment1458777Field005Key00, fragment1458777Field005Value00) :: fragment1458777Acc00500
noncomputable def fragment1458777Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '1', '1', '3', '3', '0', '1', '9', '4', '2', '8', '9', '2', '0', '6', '8', '8', '9', '9', '3', '7', '4', '3', '7', '/', '2', '6', '7', '4', '3', '0', '8', '2', '6', '7', '9', '1', '4', '2', '0', '7', '1', '9', '9', '3', '2', '7', '3', '6', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '1', '1', '4', '1', '0', '9', '1', '0', '0', '5', '4', '9', '2', '3', '3', '1', '5', '5', '1', '3', '2', '0', '6', '4', '6', '7', '/', '1', '6', '7', '1', '4', '4', '2', '6', '6', '7', '4', '4', '6', '3', '7', '9', '4', '9', '9', '5', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '2', '9', '6', '0', '4', '4', '4', '9', '8', '8', '6', '7', '6', '6', '8', '2', '7', '7', '8', '1', '7', '3', '6', '9', '7', '9', '/', '2', '6', '3', '9', '1', '2', '0', '0', '0', '1', '2', '3', '1', '1', '2', '5', '5', '2', '5', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '5', '0', '9', '1', '5', '0', '9', '9', '2', '0', '3', '0', '3', '9', '1', '6', '5', '0', '0', '6', '2', '9', '0', '9', '9', '/', '3', '1', '3', '3', '9', '5', '5', '0', '0', '1', '4', '6', '1', '9', '6', '1', '5', '6', '1', '7', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '5', '5', '3', '8', '4', '6', '1', '7', '9', '0', '1', '1', '7', '9', '6', '4', '0', '1', '4', '5', '5', '8', '2', '6', '9', '/', '6', '5', '9', '7', '8', '0', '0', '0', '0', '3', '0', '7', '7', '8', '1', '3', '8', '1', '4', '1', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '0', '0', '3', '6', '4', '7', '7', '6', '6', '9', '9', '1', '2', '9', '2', '8', '9', '5', '9', '0', '7', '1', '9', '/', '4', '7', '9', '8', '4', '0', '0', '0', '0', '2', '2', '3', '8', '4', '1', '0', '0', '4', '6', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '5', '9', '6', '4', '0', '9', '8', '0', '6', '9', '8', '8', '1', '4', '6', '9', '3', '8', '3', '3', '6', '9', '6', '3', '7', '/', '7', '1', '9', '7', '6', '0', '0', '0', '0', '3', '3', '5', '7', '6', '1', '5', '0', '6', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '1', '2', '3', '2', '5', '2', '9', '2', '9', '7', '7', '2', '3', '9', '9', '1', '8', '5', '0', '3', '8', '9', '8', '8', '2', '7', '/', '7', '9', '1', '7', '3', '6', '0', '0', '0', '3', '6', '9', '3', '3', '7', '6', '5', '7', '6', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '4', '5', '6', '9', '0', '9', '2', '6', '5', '3', '6', '1', '7', '5', '0', '9', '9', '6', '5', '9', '6', '1', '8', '7', '7', '/', '1', '2', '5', '3', '5', '8', '2', '0', '0', '0', '5', '8', '4', '7', '8', '4', '6', '2', '4', '6', '8', '4', '7', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '0', '8', '0', '0', '0', '4', '8', '6', '4', '6', '9', '1', '8', '8', '9', '4', '7', '3', '5', '6', '5', '3', '4', '8', '2', '9', '/', '5', '0', '1', '4', '3', '2', '8', '0', '0', '2', '3', '3', '9', '1', '3', '8', '4', '9', '8', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1458777_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 539) (SourceJson.white (fragment1458777Field005Chars00 ++ tail)) fragment1458777Acc00500 =
      SourceJson.object (fuel + 538) (SourceJson.white tail) fragment1458777Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_005"
  err.flush

noncomputable def fragment1458777Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1458777Field006Value00 : SourceJson := .str (String.ofList ['3', '5', '3', '3', '2', '1', '0', '9', '4', '9', '7', '4', '2', '9', '7', '4', '3', '8', '9', '6', '4', '8', '2', '0', '5', '7', '9', '9', '9', '0', '7', '4', '7', '5', '4', '8', '8', '6', '5', '6', '9', '0', '4', '5', '0', '5', '0', '5', '3', '4', '3', '8', '0', '3', '4', '2', '7', '8', '6', '6', '2', '5', '/', '5', '4', '8', '0', '3', '8', '0', '5', '8', '4', '1', '0', '4', '5', '1', '6', '2', '7', '2', '9', '6', '3', '2', '8', '1', '3', '6', '1', '0', '7', '5', '4', '1', '2', '1', '7', '4', '2', '5', '3', '9', '0', '9', '1', '2', '4', '9', '3', '3', '2', '2', '1', '9', '8', '5', '2', '2', '1', '9', '9', '1', '3', '0', '3', '3', '6', '6', '6', '3', '1', '2', '1'])
noncomputable def fragment1458777Acc00700 : List (String × SourceJson) := (fragment1458777Field006Key00, fragment1458777Field006Value00) :: fragment1458777Acc00600
noncomputable def fragment1458777Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '5', '3', '3', '2', '1', '0', '9', '4', '9', '7', '4', '2', '9', '7', '4', '3', '8', '9', '6', '4', '8', '2', '0', '5', '7', '9', '9', '9', '0', '7', '4', '7', '5', '4', '8', '8', '6', '5', '6', '9', '0', '4', '5', '0', '5', '0', '5', '3', '4', '3', '8', '0', '3', '4', '2', '7', '8', '6', '6', '2', '5', '/', '5', '4', '8', '0', '3', '8', '0', '5', '8', '4', '1', '0', '4', '5', '1', '6', '2', '7', '2', '9', '6', '3', '2', '8', '1', '3', '6', '1', '0', '7', '5', '4', '1', '2', '1', '7', '4', '2', '5', '3', '9', '0', '9', '1', '2', '4', '9', '3', '3', '2', '2', '1', '9', '8', '5', '2', '2', '1', '9', '9', '1', '3', '0', '3', '3', '6', '6', '6', '3', '1', '2', '1', '"', ',']

theorem object_fragment1458777_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 538) (SourceJson.white (fragment1458777Field006Chars00 ++ tail)) fragment1458777Acc00600 =
      SourceJson.object (fuel + 537) (SourceJson.white tail) fragment1458777Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_006"
  err.flush

noncomputable def fragment1458777Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1458777Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '9', '1', '4', '0', '1', '0', '3', '0', '8', '3', '5', '3', '1', '2', '0', '2', '6', '3', '5', '3', '1', '3', '4', '5', '8', '8', '0', '7', '2', '3', '7', '7', '0', '1', '3', '9', '8', '0', '0', '4', '8', '4', '8', '8', '9', '2', '1', '2', '5', '8', '0', '8', '5', '3', '5', '8', '8', '2', '6', '2', '0', '3', '8', '0', '7', '6', '1', '7', '2', '6', '7', '7', '4', '8', '9', '9', '9', '1', '8', '4', '3', '4', '5', '4', '4', '7', '3', '6', '3', '4', '3', '1', '3', '0', '2', '5', '2', '7', '7', '1', '8', '4', '3', '9', '5', '2', '6', '4', '1', '2', '1', '2', '2', '8', '2', '8', '3', '1', '3', '7', '2', '2', '3', '4', '3', '2', '3', '0', '0', '4', '5', '0', '7', '7', '1', '8', '4', '9', '5', '2', '9', '8', '6', '6', '0', '7', '3', '9', '0', '3', '8', '7', '7', '8', '4', '4', '9', '6', '5', '3', '6', '2', '0', '2', '0', '7', '5', '1', '7', '4', '1', '8', '5', '9', '2', '8', '7', '5', '4', '1', '2', '4', '4', '6', '8', '0', '4', '0', '7', '7', '2', '4', '6', '7', '5', '7', '6', '8', '8', '1', '3', '0', '0', '6', '2', '9', '8', '5', '9', '7', '0', '3', '6', '9', '6', '0', '3', '1', '9', '4', '2', '2', '3', '2', '1', '0', '1', '3', '7', '4', '4', '6', '4', '4', '9', '9', '2', '4', '8', '2', '4', '3', '3', '2', '8', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '4', '9', '5', '7', '7', '9', '9', '1', '9', '3', '0', '6', '3', '3', '0', '8', '9', '7', '9', '7', '7', '6', '2', '2', '2', '5', '9', '3', '4', '0', '0', '3', '7', '2', '2', '4', '5', '9', '7', '5', '8', '0', '4', '7', '2', '7', '0', '6', '7', '7', '2', '0', '4', '3', '8', '9', '0', '0', '6', '2', '6', '3', '3', '7', '9', '3', '9', '4', '0', '8', '3', '3', '7', '7', '7', '5', '0', '7', '4', '1', '7', '5', '0', '5', '3', '6', '5', '6', '6', '3', '2', '9', '6', '3', '4', '6', '1', '0', '8', '5', '8', '2', '7', '6', '7', '3', '7', '1', '5', '4', '1', '7', '9', '9', '8', '4', '9', '5', '5', '3', '9', '2', '0', '6', '5', '0', '3', '5', '2', '5', '8', '0', '2', '6', '5', '0', '4', '3', '1', '2', '7', '0', '4', '5', '9', '3', '5', '6', '8', '9', '2', '6', '8', '4', '6', '9', '9', '0', '8', '6', '9', '0', '9', '7', '2', '0', '2', '9', '8', '1', '4', '4', '6', '9', '4', '8', '3', '0', '1', '8', '8', '3', '5', '2', '0', '3', '9', '6', '2', '4', '4', '7', '8', '4', '9', '0', '9', '9', '9', '3', '6', '9', '9', '5', '8', '9', '0', '0', '7', '9', '3', '9', '8', '6', '9', '9', '1', '8', '3', '2', '7', '7', '9', '5', '8', '9', '8', '4', '2', '3', '7', '2', '0', '3', '9', '4', '3', '9', '5', '4', '7', '6', '2', '7', '3', '7', '8', '9', '5', '4', '4', '1', '4', '6', '8', '1', '1', '2', '6', '0', '1', '1', '7', '1', '5', '2', '8', '3'])
noncomputable def fragment1458777Acc00800 : List (String × SourceJson) := (fragment1458777Field007Key00, fragment1458777Field007Value00) :: fragment1458777Acc00700
noncomputable def fragment1458777Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '9', '1', '4', '0', '1', '0', '3', '0', '8', '3', '5', '3', '1', '2', '0', '2', '6', '3', '5', '3', '1', '3', '4', '5', '8', '8', '0', '7', '2', '3', '7', '7', '0', '1', '3', '9', '8', '0', '0', '4', '8', '4', '8', '8', '9', '2', '1', '2', '5', '8', '0', '8', '5', '3', '5', '8', '8', '2', '6', '2', '0', '3', '8', '0', '7', '6', '1', '7', '2', '6', '7', '7', '4', '8', '9', '9', '9', '1', '8', '4', '3', '4', '5', '4', '4', '7', '3', '6', '3', '4', '3', '1', '3', '0', '2', '5', '2', '7', '7', '1', '8', '4', '3', '9', '5', '2', '6', '4', '1', '2', '1', '2', '2', '8', '2', '8', '3', '1', '3', '7', '2', '2', '3', '4', '3', '2', '3', '0', '0', '4', '5', '0', '7', '7', '1', '8', '4', '9', '5', '2', '9', '8', '6', '6', '0', '7', '3', '9', '0', '3', '8', '7', '7', '8', '4', '4', '9', '6', '5', '3', '6', '2', '0', '2', '0', '7', '5', '1', '7', '4', '1', '8', '5', '9', '2', '8', '7', '5', '4', '1', '2', '4', '4', '6', '8', '0', '4', '0', '7', '7', '2', '4', '6', '7', '5', '7', '6', '8', '8', '1', '3', '0', '0', '6', '2', '9', '8', '5', '9', '7', '0', '3', '6', '9', '6', '0', '3', '1', '9', '4', '2', '2', '3', '2', '1', '0', '1', '3', '7', '4', '4', '6', '4', '4', '9', '9', '2', '4', '8', '2', '4', '3', '3', '2', '8', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '4', '9', '5', '7', '7', '9', '9', '1', '9', '3', '0', '6', '3', '3', '0', '8', '9', '7', '9', '7', '7', '6', '2', '2', '2', '5', '9', '3', '4', '0', '0', '3', '7', '2', '2', '4', '5', '9', '7', '5', '8', '0', '4', '7', '2', '7', '0', '6', '7', '7', '2', '0', '4', '3', '8', '9', '0', '0', '6', '2', '6', '3', '3', '7', '9', '3', '9', '4', '0', '8', '3', '3', '7', '7', '7', '5', '0', '7', '4', '1', '7', '5', '0', '5', '3', '6', '5', '6', '6', '3', '2', '9', '6', '3', '4', '6', '1', '0', '8', '5', '8', '2', '7', '6', '7', '3', '7', '1', '5', '4', '1', '7', '9', '9', '8', '4', '9', '5', '5', '3', '9', '2', '0', '6', '5', '0', '3', '5', '2', '5', '8', '0', '2', '6', '5', '0', '4', '3', '1', '2', '7', '0', '4', '5', '9', '3', '5', '6', '8', '9', '2', '6', '8', '4', '6', '9', '9', '0', '8', '6', '9', '0', '9', '7', '2', '0', '2', '9', '8', '1', '4', '4', '6', '9', '4', '8', '3', '0', '1', '8', '8', '3', '5', '2', '0', '3', '9', '6', '2', '4', '4', '7', '8', '4', '9', '0', '9', '9', '9', '3', '6', '9', '9', '5', '8', '9', '0', '0', '7', '9', '3', '9', '8', '6', '9', '9', '1', '8', '3', '2', '7', '7', '9', '5', '8', '9', '8', '4', '2', '3', '7', '2', '0', '3', '9', '4', '3', '9', '5', '4', '7', '6', '2', '7', '3', '7', '8', '9', '5', '4', '4', '1', '4', '6', '8', '1', '1', '2', '6', '0', '1', '1', '7', '1', '5', '2', '8', '3', '"', ',']

theorem object_fragment1458777_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 537) (SourceJson.white (fragment1458777Field007Chars00 ++ tail)) fragment1458777Acc00700 =
      SourceJson.object (fuel + 536) (SourceJson.white tail) fragment1458777Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_007"
  err.flush

noncomputable def fragment1458777Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1458777Field008Value00 : SourceJson := .str (String.ofList ['5', '1', '0', '7', '8', '5', '3', '4', '9', '7', '1', '7', '0', '1', '1', '7', '0', '4', '2'])
noncomputable def fragment1458777Acc00900 : List (String × SourceJson) := (fragment1458777Field008Key00, fragment1458777Field008Value00) :: fragment1458777Acc00800
noncomputable def fragment1458777Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '1', '0', '7', '8', '5', '3', '4', '9', '7', '1', '7', '0', '1', '1', '7', '0', '4', '2', '"', ',']

theorem object_fragment1458777_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 536) (SourceJson.white (fragment1458777Field008Chars00 ++ tail)) fragment1458777Acc00800 =
      SourceJson.object (fuel + 535) (SourceJson.white tail) fragment1458777Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_008"
  err.flush

noncomputable def fragment1458777Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1458777Field009Value00 : SourceJson := .str (String.ofList ['5', '5', '2', '5', '3', '6', '9', '3', '2', '8', '4', '1', '5', '2', '4', '2', '7', '0', '7', '5'])
noncomputable def fragment1458777Acc01000 : List (String × SourceJson) := (fragment1458777Field009Key00, fragment1458777Field009Value00) :: fragment1458777Acc00900
noncomputable def fragment1458777Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '2', '5', '3', '6', '9', '3', '2', '8', '4', '1', '5', '2', '4', '2', '7', '0', '7', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment1458777_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 535) (SourceJson.white (fragment1458777Field009Chars00 ++ tail)) fragment1458777Acc00900 =
      .ok (.obj (fragment1458777Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1458777_object_field_009"
  err.flush

noncomputable def fragment1458777Chars : List Char := '{' :: (fragment1458777Field000Chars00 ++ fragment1458777Field001Chars00 ++ fragment1458777Field002Chars00 ++ fragment1458777Field003Chars00 ++ fragment1458777Field004Chars00 ++ fragment1458777Field005Chars00 ++ fragment1458777Field006Chars00 ++ fragment1458777Field007Chars00 ++ fragment1458777Field008Chars00 ++ fragment1458777Field009Chars00)
noncomputable def fragment1458777Value : SourceJson := .obj (fragment1458777Acc01000.reverse)

theorem value_fragment1458777 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 545) (fragment1458777Chars ++ tail) =
      .ok (fragment1458777Value, tail) := by
  have hinput : fragment1458777Chars ++ tail = '{' :: (fragment1458777Field000Chars00 ++ (fragment1458777Field001Chars00 ++ (fragment1458777Field002Chars00 ++ (fragment1458777Field003Chars00 ++ (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment1458777Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 545) (fragment1458777Chars ++ tail) =
        SourceJson.value (fuel + 545) ('{' :: (fragment1458777Field000Chars00 ++ (fragment1458777Field001Chars00 ++ (fragment1458777Field002Chars00 ++ (fragment1458777Field003Chars00 ++ (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 545)) hinput
    _ = SourceJson.object (fuel + 544) (SourceJson.white (fragment1458777Field000Chars00 ++ (fragment1458777Field001Chars00 ++ (fragment1458777Field002Chars00 ++ (fragment1458777Field003Chars00 ++ (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))))))))))) fragment1458777Acc00000 := by rfl
    _ = SourceJson.object (fuel + 543) (SourceJson.white (fragment1458777Field001Chars00 ++ (fragment1458777Field002Chars00 ++ (fragment1458777Field003Chars00 ++ (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail))))))))))) fragment1458777Acc00100 := object_fragment1458777_field_000 fuel (fragment1458777Field001Chars00 ++ (fragment1458777Field002Chars00 ++ (fragment1458777Field003Chars00 ++ (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 542) (SourceJson.white (fragment1458777Field002Chars00 ++ (fragment1458777Field003Chars00 ++ (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))))))))) fragment1458777Acc00200 := object_fragment1458777_field_001 fuel (fragment1458777Field002Chars00 ++ (fragment1458777Field003Chars00 ++ (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 541) (SourceJson.white (fragment1458777Field003Chars00 ++ (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail))))))))) fragment1458777Acc00300 := object_fragment1458777_field_002 fuel (fragment1458777Field003Chars00 ++ (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 540) (SourceJson.white (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))))))) fragment1458777Acc00400 := object_fragment1458777_field_003 fuel (fragment1458777Field004Chars00 ++ (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 539) (SourceJson.white (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail))))))) fragment1458777Acc00500 := object_fragment1458777_field_004 fuel (fragment1458777Field005Chars00 ++ (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 538) (SourceJson.white (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))))) fragment1458777Acc00600 := object_fragment1458777_field_005 fuel (fragment1458777Field006Chars00 ++ (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 537) (SourceJson.white (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail))))) fragment1458777Acc00700 := object_fragment1458777_field_006 fuel (fragment1458777Field007Chars00 ++ (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 536) (SourceJson.white (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))) fragment1458777Acc00800 := object_fragment1458777_field_007 fuel (fragment1458777Field008Chars00 ++ (fragment1458777Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 535) (SourceJson.white (fragment1458777Field009Chars00 ++ (tail))) fragment1458777Acc00900 := object_fragment1458777_field_008 fuel (fragment1458777Field009Chars00 ++ (tail))
    _ = .ok (fragment1458777Value, tail) := object_fragment1458777_field_009 fuel (tail)

noncomputable def fragment1461045Acc00000 : List (String × SourceJson) := []

noncomputable def fragment1461045Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment1461045Field000Value00 : SourceJson := .number (String.ofList ['3'])
noncomputable def fragment1461045Acc00100 : List (String × SourceJson) := (fragment1461045Field000Key00, fragment1461045Field000Value00) :: fragment1461045Acc00000
noncomputable def fragment1461045Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', ',']

theorem object_fragment1461045_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 554) (SourceJson.white (fragment1461045Field000Chars00 ++ tail)) fragment1461045Acc00000 =
      SourceJson.object (fuel + 553) (SourceJson.white tail) fragment1461045Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_000"
  err.flush

noncomputable def fragment1461045Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment1461045Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['8', '5']), .number (String.ofList ['5', '0']), .number (String.ofList ['4', '7']), .number (String.ofList ['9']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['1'])]
noncomputable def fragment1461045Acc00200 : List (String × SourceJson) := (fragment1461045Field001Key00, fragment1461045Field001Value00) :: fragment1461045Acc00100
noncomputable def fragment1461045Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1461045_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 553) (SourceJson.white (fragment1461045Field001Chars00 ++ tail)) fragment1461045Acc00100 =
      SourceJson.object (fuel + 552) (SourceJson.white tail) fragment1461045Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_001"
  err.flush

noncomputable def fragment1461045Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment1461045Field002Value00 : SourceJson := .str (String.ofList ['1', '6', '1', '4', '3', '6', '4', '1', '7', '7', '4', '5', '0', '1', '0', '6', '6', '2', '6', '4', '3', '5', '2', '5', '2', '4', '3', '8', '8', '1', '9', '0', '9', '1', '4', '1', '7', '2', '1', '5', '8', '2', '3', '4', '4', '9', '8', '7', '9', '/', '1', '0', '1', '1', '7', '5', '8', '9', '7', '2', '1', '5', '8', '1', '0', '6', '7', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1461045Acc00300 : List (String × SourceJson) := (fragment1461045Field002Key00, fragment1461045Field002Value00) :: fragment1461045Acc00200
noncomputable def fragment1461045Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '6', '1', '4', '3', '6', '4', '1', '7', '7', '4', '5', '0', '1', '0', '6', '6', '2', '6', '4', '3', '5', '2', '5', '2', '4', '3', '8', '8', '1', '9', '0', '9', '1', '4', '1', '7', '2', '1', '5', '8', '2', '3', '4', '4', '9', '8', '7', '9', '/', '1', '0', '1', '1', '7', '5', '8', '9', '7', '2', '1', '5', '8', '1', '0', '6', '7', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1461045_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 552) (SourceJson.white (fragment1461045Field002Chars00 ++ tail)) fragment1461045Acc00200 =
      SourceJson.object (fuel + 551) (SourceJson.white tail) fragment1461045Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_002"
  err.flush

noncomputable def fragment1461045Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment1461045Field003Value00 : SourceJson := .str (String.ofList ['3', '0', '4', '4', '8', '6', '1', '3', '6', '2', '1', '/', '1', '7', '7', '1', '4', '3', '5', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1461045Acc00400 : List (String × SourceJson) := (fragment1461045Field003Key00, fragment1461045Field003Value00) :: fragment1461045Acc00300
noncomputable def fragment1461045Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '0', '4', '4', '8', '6', '1', '3', '6', '2', '1', '/', '1', '7', '7', '1', '4', '3', '5', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1461045_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 551) (SourceJson.white (fragment1461045Field003Chars00 ++ tail)) fragment1461045Acc00300 =
      SourceJson.object (fuel + 550) (SourceJson.white tail) fragment1461045Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_003"
  err.flush

noncomputable def fragment1461045Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment1461045Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '7', '8', '1', '6', '9', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '9', '6', '8', '7', '9', '/', '1', '6', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0'])]
noncomputable def fragment1461045Acc00500 : List (String × SourceJson) := (fragment1461045Field004Key00, fragment1461045Field004Value00) :: fragment1461045Acc00400
noncomputable def fragment1461045Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '7', '8', '1', '6', '9', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '9', '6', '8', '7', '9', '/', '1', '6', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1461045_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 550) (SourceJson.white (fragment1461045Field004Chars00 ++ tail)) fragment1461045Acc00400 =
      SourceJson.object (fuel + 549) (SourceJson.white tail) fragment1461045Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_004"
  err.flush

noncomputable def fragment1461045Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment1461045Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '2', '7', '7', '0', '6', '6', '1', '1', '9', '2', '8', '2', '8', '6', '6', '0', '5', '7', '8', '0', '1', '1', '9', '7', '8', '3', '1', '/', '2', '6', '8', '2', '9', '7', '2', '2', '6', '8', '2', '5', '9', '3', '7', '0', '9', '7', '5', '7', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '9', '6', '4', '0', '8', '0', '5', '9', '0', '1', '5', '8', '2', '3', '3', '8', '1', '5', '7', '8', '2', '2', '6', '7', '1', '/', '5', '3', '6', '5', '9', '4', '4', '5', '3', '6', '5', '1', '8', '7', '4', '1', '9', '5', '1', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '1', '1', '1', '4', '0', '5', '2', '8', '9', '3', '1', '8', '4', '7', '7', '7', '5', '1', '9', '9', '7', '2', '1', '8', '0', '9', '/', '4', '2', '3', '6', '2', '7', '2', '0', '0', '2', '5', '1', '4', '7', '9', '6', '2', '7', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '9', '8', '7', '6', '4', '4', '4', '1', '4', '4', '4', '1', '1', '4', '0', '4', '2', '5', '2', '9', '8', '9', '2', '3', '1', '9', '/', '4', '0', '2', '4', '4', '5', '8', '4', '0', '2', '3', '8', '9', '0', '5', '6', '4', '6', '3', '6', '9', '3', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '0', '9', '3', '2', '0', '7', '7', '9', '3', '3', '1', '3', '0', '3', '6', '1', '5', '3', '2', '4', '4', '0', '5', '8', '7', '1', '/', '2', '1', '1', '8', '1', '3', '6', '0', '0', '1', '2', '5', '7', '3', '9', '8', '1', '3', '8', '7', '8', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '5', '4', '7', '1', '7', '0', '1', '4', '0', '4', '6', '2', '7', '9', '4', '2', '8', '3', '7', '3', '1', '9', '7', '/', '3', '8', '5', '1', '1', '5', '6', '3', '6', '5', '9', '2', '2', '5', '4', '2', '0', '7', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '2', '0', '6', '1', '1', '2', '6', '1', '2', '8', '4', '9', '9', '7', '4', '2', '2', '0', '2', '2', '0', '6', '6', '6', '1', '/', '2', '3', '1', '0', '6', '9', '3', '8', '1', '9', '5', '5', '3', '5', '2', '5', '2', '4', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '9', '3', '3', '7', '9', '1', '1', '1', '8', '7', '4', '0', '8', '2', '0', '5', '4', '8', '6', '0', '7', '0', '2', '6', '4', '7', '/', '2', '5', '4', '1', '7', '6', '3', '2', '0', '1', '5', '0', '8', '8', '7', '7', '7', '6', '6', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '7', '4', '3', '6', '5', '7', '8', '7', '6', '3', '0', '6', '8', '9', '8', '8', '1', '1', '7', '3', '9', '7', '0', '3', '7', '1', '/', '1', '6', '0', '9', '7', '8', '3', '3', '6', '0', '9', '5', '5', '6', '2', '2', '5', '8', '5', '4', '7', '7', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '4', '2', '5', '7', '8', '4', '1', '1', '5', '2', '8', '1', '0', '9', '0', '6', '4', '2', '4', '7', '9', '0', '0', '2', '3', '7', '/', '8', '0', '4', '8', '9', '1', '6', '8', '0', '4', '7', '7', '8', '1', '1', '2', '9', '2', '7', '3', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment1461045Acc00600 : List (String × SourceJson) := (fragment1461045Field005Key00, fragment1461045Field005Value00) :: fragment1461045Acc00500
noncomputable def fragment1461045Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '7', '7', '0', '6', '6', '1', '1', '9', '2', '8', '2', '8', '6', '6', '0', '5', '7', '8', '0', '1', '1', '9', '7', '8', '3', '1', '/', '2', '6', '8', '2', '9', '7', '2', '2', '6', '8', '2', '5', '9', '3', '7', '0', '9', '7', '5', '7', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '9', '6', '4', '0', '8', '0', '5', '9', '0', '1', '5', '8', '2', '3', '3', '8', '1', '5', '7', '8', '2', '2', '6', '7', '1', '/', '5', '3', '6', '5', '9', '4', '4', '5', '3', '6', '5', '1', '8', '7', '4', '1', '9', '5', '1', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '1', '1', '1', '4', '0', '5', '2', '8', '9', '3', '1', '8', '4', '7', '7', '7', '5', '1', '9', '9', '7', '2', '1', '8', '0', '9', '/', '4', '2', '3', '6', '2', '7', '2', '0', '0', '2', '5', '1', '4', '7', '9', '6', '2', '7', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '9', '8', '7', '6', '4', '4', '4', '1', '4', '4', '4', '1', '1', '4', '0', '4', '2', '5', '2', '9', '8', '9', '2', '3', '1', '9', '/', '4', '0', '2', '4', '4', '5', '8', '4', '0', '2', '3', '8', '9', '0', '5', '6', '4', '6', '3', '6', '9', '3', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '9', '3', '2', '0', '7', '7', '9', '3', '3', '1', '3', '0', '3', '6', '1', '5', '3', '2', '4', '4', '0', '5', '8', '7', '1', '/', '2', '1', '1', '8', '1', '3', '6', '0', '0', '1', '2', '5', '7', '3', '9', '8', '1', '3', '8', '7', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '8', '4', '5', '4', '7', '1', '7', '0', '1', '4', '0', '4', '6', '2', '7', '9', '4', '2', '8', '3', '7', '3', '1', '9', '7', '/', '3', '8', '5', '1', '1', '5', '6', '3', '6', '5', '9', '2', '2', '5', '4', '2', '0', '7', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '2', '0', '6', '1', '1', '2', '6', '1', '2', '8', '4', '9', '9', '7', '4', '2', '2', '0', '2', '2', '0', '6', '6', '6', '1', '/', '2', '3', '1', '0', '6', '9', '3', '8', '1', '9', '5', '5', '3', '5', '2', '5', '2', '4', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '9', '3', '3', '7', '9', '1', '1', '1', '8', '7', '4', '0', '8', '2', '0', '5', '4', '8', '6', '0', '7', '0', '2', '6', '4', '7', '/', '2', '5', '4', '1', '7', '6', '3', '2', '0', '1', '5', '0', '8', '8', '7', '7', '7', '6', '6', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '7', '4', '3', '6', '5', '7', '8', '7', '6', '3', '0', '6', '8', '9', '8', '8', '1', '1', '7', '3', '9', '7', '0', '3', '7', '1', '/', '1', '6', '0', '9', '7', '8', '3', '3', '6', '0', '9', '5', '5', '6', '2', '2', '5', '8', '5', '4', '7', '7', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '4', '2', '5', '7', '8', '4', '1', '1', '5', '2', '8', '1', '0', '9', '0', '6', '4', '2', '4', '7', '9', '0', '0', '2', '3', '7', '/', '8', '0', '4', '8', '9', '1', '6', '8', '0', '4', '7', '7', '8', '1', '1', '2', '9', '2', '7', '3', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1461045_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 549) (SourceJson.white (fragment1461045Field005Chars00 ++ tail)) fragment1461045Acc00500 =
      SourceJson.object (fuel + 548) (SourceJson.white tail) fragment1461045Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_005"
  err.flush

noncomputable def fragment1461045Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1461045Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '2', '8', '8', '7', '8', '7', '7', '7', '0', '6', '9', '0', '4', '4', '4', '4', '1', '8', '3', '9', '4', '6', '9', '6', '5', '2', '0', '8', '0', '0', '1', '1', '4', '0', '2', '0', '2', '7', '0', '4', '7', '8', '9', '4', '8', '1', '7', '9', '2', '3', '2', '5', '5', '0', '4', '6', '4', '7', '5', '0', '/', '4', '5', '0', '8', '2', '3', '2', '4', '6', '1', '4', '9', '7', '2', '3', '6', '7', '6', '4', '1', '2', '4', '1', '6', '9', '2', '7', '3', '0', '7', '5', '9', '0', '8', '9', '4', '6', '3', '3', '6', '9', '4', '5', '1', '1', '1', '7', '5', '7', '8', '0', '5', '3', '5', '1', '1', '6', '9', '6', '9', '7', '3', '2', '2', '2', '3', '6', '2', '4', '1', '9'])
noncomputable def fragment1461045Acc00700 : List (String × SourceJson) := (fragment1461045Field006Key00, fragment1461045Field006Value00) :: fragment1461045Acc00600
noncomputable def fragment1461045Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '2', '8', '8', '7', '8', '7', '7', '7', '0', '6', '9', '0', '4', '4', '4', '4', '1', '8', '3', '9', '4', '6', '9', '6', '5', '2', '0', '8', '0', '0', '1', '1', '4', '0', '2', '0', '2', '7', '0', '4', '7', '8', '9', '4', '8', '1', '7', '9', '2', '3', '2', '5', '5', '0', '4', '6', '4', '7', '5', '0', '/', '4', '5', '0', '8', '2', '3', '2', '4', '6', '1', '4', '9', '7', '2', '3', '6', '7', '6', '4', '1', '2', '4', '1', '6', '9', '2', '7', '3', '0', '7', '5', '9', '0', '8', '9', '4', '6', '3', '3', '6', '9', '4', '5', '1', '1', '1', '7', '5', '7', '8', '0', '5', '3', '5', '1', '1', '6', '9', '6', '9', '7', '3', '2', '2', '2', '3', '6', '2', '4', '1', '9', '"', ',']

theorem object_fragment1461045_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 548) (SourceJson.white (fragment1461045Field006Chars00 ++ tail)) fragment1461045Acc00600 =
      SourceJson.object (fuel + 547) (SourceJson.white tail) fragment1461045Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_006"
  err.flush

noncomputable def fragment1461045Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1461045Field007Value00 : SourceJson := .str (String.ofList ['3', '1', '5', '3', '7', '8', '2', '0', '4', '3', '7', '0', '8', '3', '0', '7', '8', '1', '4', '4', '2', '8', '1', '5', '4', '6', '7', '0', '3', '6', '1', '8', '4', '3', '9', '9', '5', '4', '8', '4', '8', '8', '4', '4', '5', '9', '0', '5', '9', '6', '9', '2', '2', '0', '4', '8', '4', '2', '9', '1', '2', '7', '3', '6', '8', '5', '9', '0', '7', '6', '1', '0', '4', '2', '1', '0', '5', '8', '0', '4', '5', '3', '8', '1', '7', '3', '6', '5', '7', '9', '5', '9', '9', '3', '9', '3', '2', '0', '8', '1', '7', '1', '1', '7', '6', '5', '1', '4', '4', '1', '9', '6', '5', '5', '8', '3', '1', '9', '1', '0', '3', '2', '7', '1', '9', '0', '0', '8', '1', '5', '5', '3', '1', '3', '0', '0', '4', '0', '6', '5', '8', '1', '8', '0', '5', '1', '9', '0', '8', '5', '7', '8', '7', '6', '8', '9', '6', '6', '4', '5', '4', '1', '8', '2', '9', '5', '0', '1', '9', '4', '3', '1', '8', '6', '7', '8', '9', '9', '2', '3', '7', '5', '0', '4', '7', '7', '9', '8', '2', '7', '6', '9', '2', '7', '4', '0', '6', '6', '2', '3', '7', '7', '3', '3', '7', '3', '2', '0', '4', '8', '1', '3', '0', '6', '5', '1', '1', '7', '9', '5', '5', '9', '8', '8', '1', '0', '0', '6', '4', '0', '0', '5', '6', '1', '5', '2', '4', '3', '6', '2', '2', '7', '4', '5', '1', '6', '9', '0', '7', '6', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '6', '5', '0', '8', '7', '3', '1', '1', '9', '9', '7', '3', '8', '8', '7', '8', '1', '9', '2', '8', '2', '9', '2', '5', '7', '5', '9', '9', '9', '9', '9', '8', '6', '2', '8', '6', '3', '2', '9', '0', '6', '1', '8', '1', '9', '8', '2', '8', '6', '3', '7', '2', '1', '7', '0', '1', '0', '4', '2', '3', '3', '9', '9', '2', '8', '7', '7', '3', '5', '8', '6', '2', '0', '1', '5', '9', '5', '9', '6', '0', '6', '6', '7', '4', '7', '3', '5', '5', '3', '9', '4', '9', '5', '6', '9', '3', '4', '1', '2', '4', '2', '3', '0', '1', '3', '1', '9', '8', '5', '2', '5', '9', '7', '5', '9', '3', '7', '1', '8', '9', '3', '1', '8', '6', '8', '8', '3', '5', '3', '2', '7', '5', '4', '1', '9', '1', '3', '9', '3', '0', '6', '5', '4', '7', '0', '9', '2', '8', '5', '9', '2', '7', '3', '3', '2', '9', '1', '9', '6', '7', '1', '6', '7', '6', '3', '5', '7', '8', '1', '8', '4', '9', '4', '5', '2', '9', '0', '0', '6', '8', '3', '4', '7', '0', '6', '5', '3', '7', '5', '6', '4', '9', '9', '6', '3', '4', '1', '6', '6', '0', '3', '6', '0', '2', '0', '5', '0', '9', '8', '5', '5', '8', '6', '1', '9', '4', '0', '0', '4', '9', '2', '5', '2', '8', '4', '2', '0', '7', '2', '3', '5', '1', '6', '0', '2', '1', '2', '6', '6', '9', '1', '5', '6', '1', '1', '4', '4', '1', '8', '7', '2', '7', '3', '7', '8', '3', '0', '2', '1', '3', '3', '7', '1', '5', '5', '7', '1', '6', '4', '3', '8', '9', '8', '1'])
noncomputable def fragment1461045Acc00800 : List (String × SourceJson) := (fragment1461045Field007Key00, fragment1461045Field007Value00) :: fragment1461045Acc00700
noncomputable def fragment1461045Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '1', '5', '3', '7', '8', '2', '0', '4', '3', '7', '0', '8', '3', '0', '7', '8', '1', '4', '4', '2', '8', '1', '5', '4', '6', '7', '0', '3', '6', '1', '8', '4', '3', '9', '9', '5', '4', '8', '4', '8', '8', '4', '4', '5', '9', '0', '5', '9', '6', '9', '2', '2', '0', '4', '8', '4', '2', '9', '1', '2', '7', '3', '6', '8', '5', '9', '0', '7', '6', '1', '0', '4', '2', '1', '0', '5', '8', '0', '4', '5', '3', '8', '1', '7', '3', '6', '5', '7', '9', '5', '9', '9', '3', '9', '3', '2', '0', '8', '1', '7', '1', '1', '7', '6', '5', '1', '4', '4', '1', '9', '6', '5', '5', '8', '3', '1', '9', '1', '0', '3', '2', '7', '1', '9', '0', '0', '8', '1', '5', '5', '3', '1', '3', '0', '0', '4', '0', '6', '5', '8', '1', '8', '0', '5', '1', '9', '0', '8', '5', '7', '8', '7', '6', '8', '9', '6', '6', '4', '5', '4', '1', '8', '2', '9', '5', '0', '1', '9', '4', '3', '1', '8', '6', '7', '8', '9', '9', '2', '3', '7', '5', '0', '4', '7', '7', '9', '8', '2', '7', '6', '9', '2', '7', '4', '0', '6', '6', '2', '3', '7', '7', '3', '3', '7', '3', '2', '0', '4', '8', '1', '3', '0', '6', '5', '1', '1', '7', '9', '5', '5', '9', '8', '8', '1', '0', '0', '6', '4', '0', '0', '5', '6', '1', '5', '2', '4', '3', '6', '2', '2', '7', '4', '5', '1', '6', '9', '0', '7', '6', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '6', '5', '0', '8', '7', '3', '1', '1', '9', '9', '7', '3', '8', '8', '7', '8', '1', '9', '2', '8', '2', '9', '2', '5', '7', '5', '9', '9', '9', '9', '9', '8', '6', '2', '8', '6', '3', '2', '9', '0', '6', '1', '8', '1', '9', '8', '2', '8', '6', '3', '7', '2', '1', '7', '0', '1', '0', '4', '2', '3', '3', '9', '9', '2', '8', '7', '7', '3', '5', '8', '6', '2', '0', '1', '5', '9', '5', '9', '6', '0', '6', '6', '7', '4', '7', '3', '5', '5', '3', '9', '4', '9', '5', '6', '9', '3', '4', '1', '2', '4', '2', '3', '0', '1', '3', '1', '9', '8', '5', '2', '5', '9', '7', '5', '9', '3', '7', '1', '8', '9', '3', '1', '8', '6', '8', '8', '3', '5', '3', '2', '7', '5', '4', '1', '9', '1', '3', '9', '3', '0', '6', '5', '4', '7', '0', '9', '2', '8', '5', '9', '2', '7', '3', '3', '2', '9', '1', '9', '6', '7', '1', '6', '7', '6', '3', '5', '7', '8', '1', '8', '4', '9', '4', '5', '2', '9', '0', '0', '6', '8', '3', '4', '7', '0', '6', '5', '3', '7', '5', '6', '4', '9', '9', '6', '3', '4', '1', '6', '6', '0', '3', '6', '0', '2', '0', '5', '0', '9', '8', '5', '5', '8', '6', '1', '9', '4', '0', '0', '4', '9', '2', '5', '2', '8', '4', '2', '0', '7', '2', '3', '5', '1', '6', '0', '2', '1', '2', '6', '6', '9', '1', '5', '6', '1', '1', '4', '4', '1', '8', '7', '2', '7', '3', '7', '8', '3', '0', '2', '1', '3', '3', '7', '1', '5', '5', '7', '1', '6', '4', '3', '8', '9', '8', '1', '"', ',']

theorem object_fragment1461045_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 547) (SourceJson.white (fragment1461045Field007Chars00 ++ tail)) fragment1461045Acc00700 =
      SourceJson.object (fuel + 546) (SourceJson.white tail) fragment1461045Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_007"
  err.flush

noncomputable def fragment1461045Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1461045Field008Value00 : SourceJson := .str (String.ofList ['2', '1', '5', '9', '6', '4', '4', '7', '8', '9', '6', '4', '8', '2', '6', '2', '1', '2', '0', '2'])
noncomputable def fragment1461045Acc00900 : List (String × SourceJson) := (fragment1461045Field008Key00, fragment1461045Field008Value00) :: fragment1461045Acc00800
noncomputable def fragment1461045Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '1', '5', '9', '6', '4', '4', '7', '8', '9', '6', '4', '8', '2', '6', '2', '1', '2', '0', '2', '"', ',']

theorem object_fragment1461045_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 546) (SourceJson.white (fragment1461045Field008Chars00 ++ tail)) fragment1461045Acc00800 =
      SourceJson.object (fuel + 545) (SourceJson.white tail) fragment1461045Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_008"
  err.flush

noncomputable def fragment1461045Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1461045Field009Value00 : SourceJson := .str (String.ofList ['2', '1', '4', '4', '6', '3', '2', '0', '2', '6', '4', '6', '2', '6', '7', '0', '2', '5', '9', '3', '4'])
noncomputable def fragment1461045Acc01000 : List (String × SourceJson) := (fragment1461045Field009Key00, fragment1461045Field009Value00) :: fragment1461045Acc00900
noncomputable def fragment1461045Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '1', '4', '4', '6', '3', '2', '0', '2', '6', '4', '6', '2', '6', '7', '0', '2', '5', '9', '3', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment1461045_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 545) (SourceJson.white (fragment1461045Field009Chars00 ++ tail)) fragment1461045Acc00900 =
      .ok (.obj (fragment1461045Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1461045_object_field_009"
  err.flush

noncomputable def fragment1461045Chars : List Char := '{' :: (fragment1461045Field000Chars00 ++ fragment1461045Field001Chars00 ++ fragment1461045Field002Chars00 ++ fragment1461045Field003Chars00 ++ fragment1461045Field004Chars00 ++ fragment1461045Field005Chars00 ++ fragment1461045Field006Chars00 ++ fragment1461045Field007Chars00 ++ fragment1461045Field008Chars00 ++ fragment1461045Field009Chars00)
noncomputable def fragment1461045Value : SourceJson := .obj (fragment1461045Acc01000.reverse)

theorem value_fragment1461045 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 555) (fragment1461045Chars ++ tail) =
      .ok (fragment1461045Value, tail) := by
  have hinput : fragment1461045Chars ++ tail = '{' :: (fragment1461045Field000Chars00 ++ (fragment1461045Field001Chars00 ++ (fragment1461045Field002Chars00 ++ (fragment1461045Field003Chars00 ++ (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment1461045Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 555) (fragment1461045Chars ++ tail) =
        SourceJson.value (fuel + 555) ('{' :: (fragment1461045Field000Chars00 ++ (fragment1461045Field001Chars00 ++ (fragment1461045Field002Chars00 ++ (fragment1461045Field003Chars00 ++ (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 555)) hinput
    _ = SourceJson.object (fuel + 554) (SourceJson.white (fragment1461045Field000Chars00 ++ (fragment1461045Field001Chars00 ++ (fragment1461045Field002Chars00 ++ (fragment1461045Field003Chars00 ++ (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))))))))))) fragment1461045Acc00000 := by rfl
    _ = SourceJson.object (fuel + 553) (SourceJson.white (fragment1461045Field001Chars00 ++ (fragment1461045Field002Chars00 ++ (fragment1461045Field003Chars00 ++ (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail))))))))))) fragment1461045Acc00100 := object_fragment1461045_field_000 fuel (fragment1461045Field001Chars00 ++ (fragment1461045Field002Chars00 ++ (fragment1461045Field003Chars00 ++ (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 552) (SourceJson.white (fragment1461045Field002Chars00 ++ (fragment1461045Field003Chars00 ++ (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))))))))) fragment1461045Acc00200 := object_fragment1461045_field_001 fuel (fragment1461045Field002Chars00 ++ (fragment1461045Field003Chars00 ++ (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 551) (SourceJson.white (fragment1461045Field003Chars00 ++ (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail))))))))) fragment1461045Acc00300 := object_fragment1461045_field_002 fuel (fragment1461045Field003Chars00 ++ (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 550) (SourceJson.white (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))))))) fragment1461045Acc00400 := object_fragment1461045_field_003 fuel (fragment1461045Field004Chars00 ++ (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 549) (SourceJson.white (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail))))))) fragment1461045Acc00500 := object_fragment1461045_field_004 fuel (fragment1461045Field005Chars00 ++ (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 548) (SourceJson.white (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))))) fragment1461045Acc00600 := object_fragment1461045_field_005 fuel (fragment1461045Field006Chars00 ++ (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 547) (SourceJson.white (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail))))) fragment1461045Acc00700 := object_fragment1461045_field_006 fuel (fragment1461045Field007Chars00 ++ (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 546) (SourceJson.white (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))) fragment1461045Acc00800 := object_fragment1461045_field_007 fuel (fragment1461045Field008Chars00 ++ (fragment1461045Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 545) (SourceJson.white (fragment1461045Field009Chars00 ++ (tail))) fragment1461045Acc00900 := object_fragment1461045_field_008 fuel (fragment1461045Field009Chars00 ++ (tail))
    _ = .ok (fragment1461045Value, tail) := object_fragment1461045_field_009 fuel (tail)

noncomputable def fragment1463338Acc00000 : List (String × SourceJson) := []

noncomputable def fragment1463338Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment1463338Field000Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment1463338Acc00100 : List (String × SourceJson) := (fragment1463338Field000Key00, fragment1463338Field000Value00) :: fragment1463338Acc00000
noncomputable def fragment1463338Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', ',']

theorem object_fragment1463338_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 503) (SourceJson.white (fragment1463338Field000Chars00 ++ tail)) fragment1463338Acc00000 =
      SourceJson.object (fuel + 502) (SourceJson.white tail) fragment1463338Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_000"
  err.flush

noncomputable def fragment1463338Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment1463338Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['8', '5']), .number (String.ofList ['5', '0']), .number (String.ofList ['4', '7']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment1463338Acc00200 : List (String × SourceJson) := (fragment1463338Field001Key00, fragment1463338Field001Value00) :: fragment1463338Acc00100
noncomputable def fragment1463338Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1463338_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 502) (SourceJson.white (fragment1463338Field001Chars00 ++ tail)) fragment1463338Acc00100 =
      SourceJson.object (fuel + 501) (SourceJson.white tail) fragment1463338Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_001"
  err.flush

noncomputable def fragment1463338Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment1463338Field002Value00 : SourceJson := .str (String.ofList ['3', '5', '3', '4', '7', '6', '8', '1', '0', '0', '8', '6', '5', '5', '4', '9', '8', '7', '7', '9', '3', '9', '6', '0', '1', '2', '1', '1', '7', '8', '9', '9', '4', '0', '7', '1', '8', '4', '8', '6', '2', '3', '9', '5', '2', '9', '/', '3', '4', '8', '9', '4', '1', '9', '6', '4', '5', '3', '0', '0', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1463338Acc00300 : List (String × SourceJson) := (fragment1463338Field002Key00, fragment1463338Field002Value00) :: fragment1463338Acc00200
noncomputable def fragment1463338Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '5', '3', '4', '7', '6', '8', '1', '0', '0', '8', '6', '5', '5', '4', '9', '8', '7', '7', '9', '3', '9', '6', '0', '1', '2', '1', '1', '7', '8', '9', '9', '4', '0', '7', '1', '8', '4', '8', '6', '2', '3', '9', '5', '2', '9', '/', '3', '4', '8', '9', '4', '1', '9', '6', '4', '5', '3', '0', '0', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1463338_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 501) (SourceJson.white (fragment1463338Field002Chars00 ++ tail)) fragment1463338Acc00200 =
      SourceJson.object (fuel + 500) (SourceJson.white tail) fragment1463338Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_002"
  err.flush

noncomputable def fragment1463338Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment1463338Field003Value00 : SourceJson := .str (String.ofList ['3', '7', '4', '4', '5', '3', '8', '3', '0', '7', '/', '2', '1', '2', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1463338Acc00400 : List (String × SourceJson) := (fragment1463338Field003Key00, fragment1463338Field003Value00) :: fragment1463338Acc00300
noncomputable def fragment1463338Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '7', '4', '4', '5', '3', '8', '3', '0', '7', '/', '2', '1', '2', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1463338_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 500) (SourceJson.white (fragment1463338Field003Chars00 ++ tail)) fragment1463338Acc00300 =
      SourceJson.object (fuel + 499) (SourceJson.white tail) fragment1463338Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_003"
  err.flush

noncomputable def fragment1463338Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment1463338Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '7', '8', '1', '6', '9', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0'])]
noncomputable def fragment1463338Acc00500 : List (String × SourceJson) := (fragment1463338Field004Key00, fragment1463338Field004Value00) :: fragment1463338Acc00400
noncomputable def fragment1463338Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '7', '8', '1', '6', '9', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1463338_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 499) (SourceJson.white (fragment1463338Field004Chars00 ++ tail)) fragment1463338Acc00400 =
      SourceJson.object (fuel + 498) (SourceJson.white tail) fragment1463338Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_004"
  err.flush

noncomputable def fragment1463338Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment1463338Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '7', '9', '8', '0', '7', '8', '9', '2', '8', '7', '2', '8', '6', '6', '5', '6', '9', '5', '8', '2', '7', '6', '1', '9', '/', '4', '9', '3', '9', '3', '5', '7', '6', '7', '3', '6', '2', '2', '6', '7', '6', '6', '8', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '9', '6', '0', '0', '9', '2', '3', '1', '7', '0', '1', '4', '5', '0', '5', '7', '8', '6', '8', '2', '4', '9', '/', '9', '8', '7', '8', '7', '1', '5', '3', '4', '7', '2', '4', '5', '3', '5', '3', '3', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '3', '6', '0', '8', '1', '0', '8', '7', '3', '0', '3', '6', '6', '2', '8', '0', '4', '8', '0', '1', '6', '9', '9', '/', '1', '5', '5', '9', '7', '9', '7', '1', '6', '0', '0', '9', '1', '3', '7', '1', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '9', '2', '2', '9', '9', '1', '8', '1', '4', '8', '1', '5', '9', '7', '0', '4', '8', '8', '5', '5', '7', '0', '1', '7', '/', '2', '9', '6', '3', '6', '1', '4', '6', '0', '4', '1', '7', '3', '6', '0', '6', '0', '1', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '5', '1', '6', '3', '1', '7', '2', '5', '3', '0', '6', '3', '7', '2', '9', '2', '8', '0', '4', '1', '5', '4', '3', '/', '1', '5', '5', '9', '7', '9', '7', '1', '6', '0', '0', '9', '1', '3', '7', '1', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '4', '0', '0', '9', '3', '1', '9', '0', '7', '5', '0', '1', '0', '6', '9', '2', '0', '3', '3', '8', '9', '9', '/', '3', '5', '4', '4', '9', '9', '3', '5', '4', '5', '6', '6', '2', '2', '0', '8', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '8', '7', '2', '5', '3', '9', '9', '2', '5', '5', '4', '5', '9', '3', '1', '1', '7', '5', '9', '2', '7', '4', '9', '/', '8', '5', '0', '7', '9', '8', '4', '5', '0', '9', '5', '8', '9', '2', '9', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '4', '2', '1', '1', '4', '3', '4', '2', '7', '4', '5', '5', '2', '1', '2', '6', '3', '9', '1', '3', '4', '0', '0', '9', '/', '9', '3', '5', '8', '7', '8', '2', '9', '6', '0', '5', '4', '8', '2', '2', '9', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '4', '7', '4', '6', '3', '3', '2', '9', '7', '1', '4', '9', '9', '1', '4', '3', '7', '8', '7', '7', '3', '8', '2', '7', '/', '1', '4', '8', '1', '8', '0', '7', '3', '0', '2', '0', '8', '6', '8', '0', '3', '0', '0', '6', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '7', '7', '9', '0', '0', '0', '3', '9', '6', '3', '6', '5', '1', '9', '1', '6', '3', '3', '0', '7', '0', '6', '5', '9', '/', '2', '9', '6', '3', '6', '1', '4', '6', '0', '4', '1', '7', '3', '6', '0', '6', '0', '1', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment1463338Acc00600 : List (String × SourceJson) := (fragment1463338Field005Key00, fragment1463338Field005Value00) :: fragment1463338Acc00500
noncomputable def fragment1463338Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '7', '9', '8', '0', '7', '8', '9', '2', '8', '7', '2', '8', '6', '6', '5', '6', '9', '5', '8', '2', '7', '6', '1', '9', '/', '4', '9', '3', '9', '3', '5', '7', '6', '7', '3', '6', '2', '2', '6', '7', '6', '6', '8', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '9', '6', '0', '0', '9', '2', '3', '1', '7', '0', '1', '4', '5', '0', '5', '7', '8', '6', '8', '2', '4', '9', '/', '9', '8', '7', '8', '7', '1', '5', '3', '4', '7', '2', '4', '5', '3', '5', '3', '3', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '6', '0', '8', '1', '0', '8', '7', '3', '0', '3', '6', '6', '2', '8', '0', '4', '8', '0', '1', '6', '9', '9', '/', '1', '5', '5', '9', '7', '9', '7', '1', '6', '0', '0', '9', '1', '3', '7', '1', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '9', '2', '2', '9', '9', '1', '8', '1', '4', '8', '1', '5', '9', '7', '0', '4', '8', '8', '5', '5', '7', '0', '1', '7', '/', '2', '9', '6', '3', '6', '1', '4', '6', '0', '4', '1', '7', '3', '6', '0', '6', '0', '1', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '5', '1', '6', '3', '1', '7', '2', '5', '3', '0', '6', '3', '7', '2', '9', '2', '8', '0', '4', '1', '5', '4', '3', '/', '1', '5', '5', '9', '7', '9', '7', '1', '6', '0', '0', '9', '1', '3', '7', '1', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '4', '0', '0', '9', '3', '1', '9', '0', '7', '5', '0', '1', '0', '6', '9', '2', '0', '3', '3', '8', '9', '9', '/', '3', '5', '4', '4', '9', '9', '3', '5', '4', '5', '6', '6', '2', '2', '0', '8', '1', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '8', '7', '2', '5', '3', '9', '9', '2', '5', '5', '4', '5', '9', '3', '1', '1', '7', '5', '9', '2', '7', '4', '9', '/', '8', '5', '0', '7', '9', '8', '4', '5', '0', '9', '5', '8', '9', '2', '9', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '4', '2', '1', '1', '4', '3', '4', '2', '7', '4', '5', '5', '2', '1', '2', '6', '3', '9', '1', '3', '4', '0', '0', '9', '/', '9', '3', '5', '8', '7', '8', '2', '9', '6', '0', '5', '4', '8', '2', '2', '9', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '4', '7', '4', '6', '3', '3', '2', '9', '7', '1', '4', '9', '9', '1', '4', '3', '7', '8', '7', '7', '3', '8', '2', '7', '/', '1', '4', '8', '1', '8', '0', '7', '3', '0', '2', '0', '8', '6', '8', '0', '3', '0', '0', '6', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '7', '7', '9', '0', '0', '0', '3', '9', '6', '3', '6', '5', '1', '9', '1', '6', '3', '3', '0', '7', '0', '6', '5', '9', '/', '2', '9', '6', '3', '6', '1', '4', '6', '0', '4', '1', '7', '3', '6', '0', '6', '0', '1', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1463338_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 498) (SourceJson.white (fragment1463338Field005Chars00 ++ tail)) fragment1463338Acc00500 =
      SourceJson.object (fuel + 497) (SourceJson.white tail) fragment1463338Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_005"
  err.flush

noncomputable def fragment1463338Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1463338Field006Value00 : SourceJson := .str (String.ofList ['3', '0', '3', '7', '6', '7', '9', '1', '1', '1', '5', '3', '2', '0', '9', '2', '6', '7', '0', '4', '6', '2', '4', '4', '0', '5', '1', '7', '5', '8', '0', '8', '1', '6', '6', '7', '6', '7', '2', '6', '2', '7', '4', '7', '8', '9', '3', '2', '0', '8', '1', '2', '5', '3', '3', '9', '8', '8', '5', '/', '1', '6', '6', '1', '0', '2', '7', '4', '6', '3', '9', '1', '4', '0', '6', '2', '9', '0', '6', '2', '5', '2', '0', '6', '4', '9', '1', '9', '5', '7', '6', '9', '2', '9', '8', '5', '7', '3', '9', '2', '4', '7', '5', '6', '2', '7', '5', '3', '0', '5', '9', '9', '5', '3', '5', '7', '8', '2', '1', '5', '6', '0', '7', '2', '9', '6', '7', '0', '4'])
noncomputable def fragment1463338Acc00700 : List (String × SourceJson) := (fragment1463338Field006Key00, fragment1463338Field006Value00) :: fragment1463338Acc00600
noncomputable def fragment1463338Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '3', '7', '6', '7', '9', '1', '1', '1', '5', '3', '2', '0', '9', '2', '6', '7', '0', '4', '6', '2', '4', '4', '0', '5', '1', '7', '5', '8', '0', '8', '1', '6', '6', '7', '6', '7', '2', '6', '2', '7', '4', '7', '8', '9', '3', '2', '0', '8', '1', '2', '5', '3', '3', '9', '8', '8', '5', '/', '1', '6', '6', '1', '0', '2', '7', '4', '6', '3', '9', '1', '4', '0', '6', '2', '9', '0', '6', '2', '5', '2', '0', '6', '4', '9', '1', '9', '5', '7', '6', '9', '2', '9', '8', '5', '7', '3', '9', '2', '4', '7', '5', '6', '2', '7', '5', '3', '0', '5', '9', '9', '5', '3', '5', '7', '8', '2', '1', '5', '6', '0', '7', '2', '9', '6', '7', '0', '4', '"', ',']

theorem object_fragment1463338_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 497) (SourceJson.white (fragment1463338Field006Chars00 ++ tail)) fragment1463338Acc00600 =
      SourceJson.object (fuel + 496) (SourceJson.white tail) fragment1463338Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_006"
  err.flush

noncomputable def fragment1463338Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1463338Field007Value00 : SourceJson := .str (String.ofList ['1', '2', '6', '2', '7', '9', '8', '3', '1', '9', '6', '9', '7', '5', '6', '7', '7', '7', '7', '4', '9', '2', '9', '0', '5', '0', '0', '5', '3', '8', '3', '6', '9', '9', '6', '2', '3', '1', '0', '4', '3', '1', '6', '6', '8', '1', '8', '6', '0', '4', '6', '5', '0', '1', '1', '3', '7', '2', '5', '1', '5', '5', '9', '7', '5', '8', '8', '7', '7', '6', '0', '5', '1', '6', '3', '5', '8', '8', '2', '4', '8', '4', '8', '3', '4', '8', '5', '9', '7', '4', '6', '6', '5', '6', '3', '7', '5', '9', '7', '7', '6', '0', '1', '9', '2', '7', '7', '2', '6', '1', '5', '2', '1', '1', '2', '5', '6', '8', '6', '0', '0', '4', '2', '6', '4', '7', '7', '7', '4', '4', '0', '9', '4', '1', '8', '0', '9', '7', '1', '1', '6', '0', '9', '9', '3', '2', '9', '4', '2', '3', '1', '4', '8', '1', '7', '7', '2', '4', '4', '3', '8', '7', '8', '5', '0', '6', '2', '4', '7', '8', '1', '3', '3', '6', '9', '3', '8', '4', '3', '3', '8', '9', '0', '4', '7', '2', '3', '6', '6', '4', '9', '0', '3', '1', '7', '0', '6', '2', '3', '3', '7', '9', '8', '9', '6', '0', '2', '8', '7', '5', '0', '9', '6', '9', '2', '3', '5', '5', '3', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '7', '7', '0', '7', '0', '3', '3', '3', '8', '0', '3', '3', '7', '9', '1', '5', '4', '8', '4', '4', '4', '9', '3', '6', '6', '4', '2', '5', '8', '9', '4', '2', '5', '0', '4', '8', '6', '5', '4', '2', '3', '9', '0', '4', '1', '9', '2', '4', '4', '0', '4', '8', '4', '6', '5', '3', '6', '2', '8', '6', '2', '0', '8', '2', '0', '3', '7', '9', '6', '0', '7', '0', '2', '3', '8', '3', '9', '8', '9', '5', '0', '1', '0', '9', '6', '7', '4', '8', '9', '9', '0', '6', '6', '5', '3', '4', '8', '5', '0', '7', '9', '4', '5', '9', '6', '4', '6', '7', '1', '8', '3', '5', '1', '1', '3', '4', '1', '1', '7', '7', '3', '8', '3', '1', '0', '9', '2', '3', '8', '3', '8', '6', '9', '2', '4', '4', '4', '6', '2', '2', '9', '4', '9', '8', '5', '6', '6', '1', '9', '0', '3', '1', '8', '5', '7', '5', '1', '3', '7', '2', '0', '9', '8', '9', '6', '9', '1', '2', '7', '3', '2', '2', '9', '2', '2', '7', '2', '2', '4', '0', '8', '8', '6', '7', '4', '1', '9', '7', '0', '4', '9', '0', '3', '9', '1', '9', '4', '8', '3', '7', '2', '2', '5', '4', '0', '9', '1', '9', '1', '0', '7', '5', '9', '1', '4', '5', '6', '2', '9', '2', '6', '2', '3', '0', '9', '5', '1', '2', '9', '0', '5', '4', '7', '1', '7', '9', '8', '1', '2', '4', '4', '4', '4', '9', '1', '8', '1', '1', '9'])
noncomputable def fragment1463338Acc00800 : List (String × SourceJson) := (fragment1463338Field007Key00, fragment1463338Field007Value00) :: fragment1463338Acc00700
noncomputable def fragment1463338Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '6', '2', '7', '9', '8', '3', '1', '9', '6', '9', '7', '5', '6', '7', '7', '7', '7', '4', '9', '2', '9', '0', '5', '0', '0', '5', '3', '8', '3', '6', '9', '9', '6', '2', '3', '1', '0', '4', '3', '1', '6', '6', '8', '1', '8', '6', '0', '4', '6', '5', '0', '1', '1', '3', '7', '2', '5', '1', '5', '5', '9', '7', '5', '8', '8', '7', '7', '6', '0', '5', '1', '6', '3', '5', '8', '8', '2', '4', '8', '4', '8', '3', '4', '8', '5', '9', '7', '4', '6', '6', '5', '6', '3', '7', '5', '9', '7', '7', '6', '0', '1', '9', '2', '7', '7', '2', '6', '1', '5', '2', '1', '1', '2', '5', '6', '8', '6', '0', '0', '4', '2', '6', '4', '7', '7', '7', '4', '4', '0', '9', '4', '1', '8', '0', '9', '7', '1', '1', '6', '0', '9', '9', '3', '2', '9', '4', '2', '3', '1', '4', '8', '1', '7', '7', '2', '4', '4', '3', '8', '7', '8', '5', '0', '6', '2', '4', '7', '8', '1', '3', '3', '6', '9', '3', '8', '4', '3', '3', '8', '9', '0', '4', '7', '2', '3', '6', '6', '4', '9', '0', '3', '1', '7', '0', '6', '2', '3', '3', '7', '9', '8', '9', '6', '0', '2', '8', '7', '5', '0', '9', '6', '9', '2', '3', '5', '5', '3', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '7', '7', '0', '7', '0', '3', '3', '3', '8', '0', '3', '3', '7', '9', '1', '5', '4', '8', '4', '4', '4', '9', '3', '6', '6', '4', '2', '5', '8', '9', '4', '2', '5', '0', '4', '8', '6', '5', '4', '2', '3', '9', '0', '4', '1', '9', '2', '4', '4', '0', '4', '8', '4', '6', '5', '3', '6', '2', '8', '6', '2', '0', '8', '2', '0', '3', '7', '9', '6', '0', '7', '0', '2', '3', '8', '3', '9', '8', '9', '5', '0', '1', '0', '9', '6', '7', '4', '8', '9', '9', '0', '6', '6', '5', '3', '4', '8', '5', '0', '7', '9', '4', '5', '9', '6', '4', '6', '7', '1', '8', '3', '5', '1', '1', '3', '4', '1', '1', '7', '7', '3', '8', '3', '1', '0', '9', '2', '3', '8', '3', '8', '6', '9', '2', '4', '4', '4', '6', '2', '2', '9', '4', '9', '8', '5', '6', '6', '1', '9', '0', '3', '1', '8', '5', '7', '5', '1', '3', '7', '2', '0', '9', '8', '9', '6', '9', '1', '2', '7', '3', '2', '2', '9', '2', '2', '7', '2', '2', '4', '0', '8', '8', '6', '7', '4', '1', '9', '7', '0', '4', '9', '0', '3', '9', '1', '9', '4', '8', '3', '7', '2', '2', '5', '4', '0', '9', '1', '9', '1', '0', '7', '5', '9', '1', '4', '5', '6', '2', '9', '2', '6', '2', '3', '0', '9', '5', '1', '2', '9', '0', '5', '4', '7', '1', '7', '9', '8', '1', '2', '4', '4', '4', '4', '9', '1', '8', '1', '1', '9', '"', ',']

theorem object_fragment1463338_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 496) (SourceJson.white (fragment1463338Field007Chars00 ++ tail)) fragment1463338Acc00700 =
      SourceJson.object (fuel + 495) (SourceJson.white tail) fragment1463338Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_007"
  err.flush

noncomputable def fragment1463338Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1463338Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '4', '8', '9', '2', '0', '8', '6', '0', '9', '9', '2', '4', '7', '2', '7', '1', '2', '0'])
noncomputable def fragment1463338Acc00900 : List (String × SourceJson) := (fragment1463338Field008Key00, fragment1463338Field008Value00) :: fragment1463338Acc00800
noncomputable def fragment1463338Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '4', '8', '9', '2', '0', '8', '6', '0', '9', '9', '2', '4', '7', '2', '7', '1', '2', '0', '"', ',']

theorem object_fragment1463338_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 495) (SourceJson.white (fragment1463338Field008Chars00 ++ tail)) fragment1463338Acc00800 =
      SourceJson.object (fuel + 494) (SourceJson.white tail) fragment1463338Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_008"
  err.flush

noncomputable def fragment1463338Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1463338Field009Value00 : SourceJson := .str (String.ofList ['1', '4', '7', '7', '6', '7', '7', '9', '5', '3', '0', '9', '7', '1', '6', '0', '2', '2', '9', '0', '7'])
noncomputable def fragment1463338Acc01000 : List (String × SourceJson) := (fragment1463338Field009Key00, fragment1463338Field009Value00) :: fragment1463338Acc00900
noncomputable def fragment1463338Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '7', '7', '6', '7', '7', '9', '5', '3', '0', '9', '7', '1', '6', '0', '2', '2', '9', '0', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment1463338_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 494) (SourceJson.white (fragment1463338Field009Chars00 ++ tail)) fragment1463338Acc00900 =
      .ok (.obj (fragment1463338Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1463338_object_field_009"
  err.flush

noncomputable def fragment1463338Chars : List Char := '{' :: (fragment1463338Field000Chars00 ++ fragment1463338Field001Chars00 ++ fragment1463338Field002Chars00 ++ fragment1463338Field003Chars00 ++ fragment1463338Field004Chars00 ++ fragment1463338Field005Chars00 ++ fragment1463338Field006Chars00 ++ fragment1463338Field007Chars00 ++ fragment1463338Field008Chars00 ++ fragment1463338Field009Chars00)
noncomputable def fragment1463338Value : SourceJson := .obj (fragment1463338Acc01000.reverse)

theorem value_fragment1463338 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 504) (fragment1463338Chars ++ tail) =
      .ok (fragment1463338Value, tail) := by
  have hinput : fragment1463338Chars ++ tail = '{' :: (fragment1463338Field000Chars00 ++ (fragment1463338Field001Chars00 ++ (fragment1463338Field002Chars00 ++ (fragment1463338Field003Chars00 ++ (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment1463338Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 504) (fragment1463338Chars ++ tail) =
        SourceJson.value (fuel + 504) ('{' :: (fragment1463338Field000Chars00 ++ (fragment1463338Field001Chars00 ++ (fragment1463338Field002Chars00 ++ (fragment1463338Field003Chars00 ++ (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 504)) hinput
    _ = SourceJson.object (fuel + 503) (SourceJson.white (fragment1463338Field000Chars00 ++ (fragment1463338Field001Chars00 ++ (fragment1463338Field002Chars00 ++ (fragment1463338Field003Chars00 ++ (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))))))))))) fragment1463338Acc00000 := by rfl
    _ = SourceJson.object (fuel + 502) (SourceJson.white (fragment1463338Field001Chars00 ++ (fragment1463338Field002Chars00 ++ (fragment1463338Field003Chars00 ++ (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail))))))))))) fragment1463338Acc00100 := object_fragment1463338_field_000 fuel (fragment1463338Field001Chars00 ++ (fragment1463338Field002Chars00 ++ (fragment1463338Field003Chars00 ++ (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 501) (SourceJson.white (fragment1463338Field002Chars00 ++ (fragment1463338Field003Chars00 ++ (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))))))))) fragment1463338Acc00200 := object_fragment1463338_field_001 fuel (fragment1463338Field002Chars00 ++ (fragment1463338Field003Chars00 ++ (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 500) (SourceJson.white (fragment1463338Field003Chars00 ++ (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail))))))))) fragment1463338Acc00300 := object_fragment1463338_field_002 fuel (fragment1463338Field003Chars00 ++ (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 499) (SourceJson.white (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))))))) fragment1463338Acc00400 := object_fragment1463338_field_003 fuel (fragment1463338Field004Chars00 ++ (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 498) (SourceJson.white (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail))))))) fragment1463338Acc00500 := object_fragment1463338_field_004 fuel (fragment1463338Field005Chars00 ++ (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 497) (SourceJson.white (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))))) fragment1463338Acc00600 := object_fragment1463338_field_005 fuel (fragment1463338Field006Chars00 ++ (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 496) (SourceJson.white (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail))))) fragment1463338Acc00700 := object_fragment1463338_field_006 fuel (fragment1463338Field007Chars00 ++ (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 495) (SourceJson.white (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))) fragment1463338Acc00800 := object_fragment1463338_field_007 fuel (fragment1463338Field008Chars00 ++ (fragment1463338Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 494) (SourceJson.white (fragment1463338Field009Chars00 ++ (tail))) fragment1463338Acc00900 := object_fragment1463338_field_008 fuel (fragment1463338Field009Chars00 ++ (tail))
    _ = .ok (fragment1463338Value, tail) := object_fragment1463338_field_009 fuel (tail)

noncomputable def fragment1465514Acc00000 : List (String × SourceJson) := []

noncomputable def fragment1465514Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment1465514Field000Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment1465514Acc00100 : List (String × SourceJson) := (fragment1465514Field000Key00, fragment1465514Field000Value00) :: fragment1465514Acc00000
noncomputable def fragment1465514Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', ',']

theorem object_fragment1465514_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 544) (SourceJson.white (fragment1465514Field000Chars00 ++ tail)) fragment1465514Acc00000 =
      SourceJson.object (fuel + 543) (SourceJson.white tail) fragment1465514Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_000"
  err.flush

noncomputable def fragment1465514Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment1465514Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['8', '5']), .number (String.ofList ['5', '0']), .number (String.ofList ['4', '7']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['4']), .number (String.ofList ['1'])]
noncomputable def fragment1465514Acc00200 : List (String × SourceJson) := (fragment1465514Field001Key00, fragment1465514Field001Value00) :: fragment1465514Acc00100
noncomputable def fragment1465514Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1465514_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 543) (SourceJson.white (fragment1465514Field001Chars00 ++ tail)) fragment1465514Acc00100 =
      SourceJson.object (fuel + 542) (SourceJson.white tail) fragment1465514Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_001"
  err.flush

noncomputable def fragment1465514Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment1465514Field002Value00 : SourceJson := .str (String.ofList ['6', '5', '0', '8', '2', '9', '1', '9', '2', '8', '2', '0', '6', '9', '9', '3', '6', '2', '1', '5', '2', '9', '5', '5', '0', '3', '5', '4', '5', '9', '5', '0', '8', '5', '3', '6', '9', '7', '8', '4', '7', '9', '8', '2', '7', '0', '4', '3', '/', '4', '3', '0', '1', '4', '9', '0', '2', '4', '0', '9', '1', '1', '7', '1', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1465514Acc00300 : List (String × SourceJson) := (fragment1465514Field002Key00, fragment1465514Field002Value00) :: fragment1465514Acc00200
noncomputable def fragment1465514Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '5', '0', '8', '2', '9', '1', '9', '2', '8', '2', '0', '6', '9', '9', '3', '6', '2', '1', '5', '2', '9', '5', '5', '0', '3', '5', '4', '5', '9', '5', '0', '8', '5', '3', '6', '9', '7', '8', '4', '7', '9', '8', '2', '7', '0', '4', '3', '/', '4', '3', '0', '1', '4', '9', '0', '2', '4', '0', '9', '1', '1', '7', '1', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1465514_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 542) (SourceJson.white (fragment1465514Field002Chars00 ++ tail)) fragment1465514Acc00200 =
      SourceJson.object (fuel + 541) (SourceJson.white tail) fragment1465514Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_002"
  err.flush

noncomputable def fragment1465514Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment1465514Field003Value00 : SourceJson := .str (String.ofList ['3', '1', '8', '1', '0', '3', '5', '5', '2', '7', '9', '/', '1', '7', '7', '1', '4', '3', '5', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1465514Acc00400 : List (String × SourceJson) := (fragment1465514Field003Key00, fragment1465514Field003Value00) :: fragment1465514Acc00300
noncomputable def fragment1465514Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '1', '8', '1', '0', '3', '5', '5', '2', '7', '9', '/', '1', '7', '7', '1', '4', '3', '5', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1465514_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 541) (SourceJson.white (fragment1465514Field003Chars00 ++ tail)) fragment1465514Acc00300 =
      SourceJson.object (fuel + 540) (SourceJson.white tail) fragment1465514Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_003"
  err.flush

noncomputable def fragment1465514Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment1465514Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '7', '8', '1', '6', '9', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '9', '6', '8', '7', '9', '/', '1', '6', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0'])]
noncomputable def fragment1465514Acc00500 : List (String × SourceJson) := (fragment1465514Field004Key00, fragment1465514Field004Value00) :: fragment1465514Acc00400
noncomputable def fragment1465514Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '7', '8', '1', '6', '9', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '7', '3', '4', '3', '3', '9', '/', '8', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '9', '0', '5', '1', '7', '/', '3', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '9', '6', '8', '7', '9', '/', '1', '6', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1465514_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 540) (SourceJson.white (fragment1465514Field004Chars00 ++ tail)) fragment1465514Acc00400 =
      SourceJson.object (fuel + 539) (SourceJson.white tail) fragment1465514Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_004"
  err.flush

noncomputable def fragment1465514Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment1465514Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '2', '7', '1', '1', '4', '0', '0', '6', '9', '9', '3', '2', '8', '8', '5', '2', '0', '1', '1', '9', '6', '5', '4', '9', '3', '/', '4', '4', '8', '4', '7', '3', '8', '8', '9', '1', '2', '6', '6', '8', '4', '6', '3', '9', '3', '9', '9', '1', '0', '4', '0', '0', '0']), .str (String.ofList ['1', '4', '7', '6', '3', '9', '7', '5', '7', '0', '4', '6', '7', '3', '3', '5', '2', '7', '2', '7', '3', '3', '6', '9', '4', '2', '5', '1', '3', '/', '2', '8', '0', '2', '9', '6', '1', '8', '0', '7', '0', '4', '1', '7', '7', '8', '9', '9', '6', '2', '4', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '2', '8', '3', '8', '9', '1', '9', '1', '5', '7', '3', '2', '5', '5', '0', '0', '9', '3', '2', '4', '3', '9', '4', '5', '3', '1', '/', '4', '4', '2', '5', '7', '2', '9', '1', '6', '9', '0', '1', '3', '3', '3', '5', '2', '5', '7', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '5', '5', '6', '3', '3', '7', '7', '7', '4', '5', '3', '1', '3', '0', '1', '4', '1', '7', '0', '4', '8', '0', '6', '4', '8', '1', '3', '/', '4', '2', '0', '4', '4', '4', '2', '7', '1', '0', '5', '6', '2', '6', '6', '8', '4', '9', '4', '3', '6', '6', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '9', '2', '7', '4', '4', '3', '5', '9', '5', '7', '2', '6', '0', '5', '8', '2', '9', '9', '7', '1', '5', '1', '8', '5', '5', '7', '/', '2', '2', '1', '2', '8', '6', '4', '5', '8', '4', '5', '0', '6', '6', '6', '7', '6', '2', '8', '6', '1', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '0', '9', '8', '3', '1', '3', '2', '1', '6', '3', '9', '0', '1', '7', '6', '3', '7', '5', '1', '1', '8', '8', '9', '1', '/', '8', '0', '4', '6', '7', '8', '0', '3', '0', '7', '2', '9', '6', '9', '7', '3', '1', '9', '4', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '1', '9', '0', '5', '9', '5', '3', '4', '3', '4', '1', '5', '4', '0', '4', '4', '7', '8', '2', '5', '0', '1', '3', '3', '/', '4', '8', '2', '8', '0', '6', '8', '1', '8', '4', '3', '7', '8', '1', '8', '3', '9', '1', '6', '9', '7', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '1', '4', '8', '0', '6', '0', '4', '0', '7', '9', '6', '7', '7', '4', '5', '8', '3', '4', '9', '4', '0', '6', '7', '8', '9', '/', '8', '2', '9', '8', '2', '4', '2', '1', '9', '1', '9', '0', '0', '0', '0', '3', '6', '0', '7', '3', '0', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '9', '7', '0', '8', '7', '6', '9', '8', '0', '0', '3', '4', '3', '0', '3', '8', '2', '1', '3', '2', '1', '1', '2', '4', '8', '8', '3', '/', '8', '4', '0', '8', '8', '8', '5', '4', '2', '1', '1', '2', '5', '3', '3', '6', '9', '8', '8', '7', '3', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '9', '4', '4', '5', '0', '2', '4', '7', '3', '4', '7', '0', '3', '8', '8', '7', '2', '9', '6', '1', '6', '1', '6', '9', '4', '3', '1', '/', '8', '4', '0', '8', '8', '8', '5', '4', '2', '1', '1', '2', '5', '3', '3', '6', '9', '8', '8', '7', '3', '3', '2', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment1465514Acc00600 : List (String × SourceJson) := (fragment1465514Field005Key00, fragment1465514Field005Value00) :: fragment1465514Acc00500
noncomputable def fragment1465514Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '7', '1', '1', '4', '0', '0', '6', '9', '9', '3', '2', '8', '8', '5', '2', '0', '1', '1', '9', '6', '5', '4', '9', '3', '/', '4', '4', '8', '4', '7', '3', '8', '8', '9', '1', '2', '6', '6', '8', '4', '6', '3', '9', '3', '9', '9', '1', '0', '4', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '7', '6', '3', '9', '7', '5', '7', '0', '4', '6', '7', '3', '3', '5', '2', '7', '2', '7', '3', '3', '6', '9', '4', '2', '5', '1', '3', '/', '2', '8', '0', '2', '9', '6', '1', '8', '0', '7', '0', '4', '1', '7', '7', '8', '9', '9', '6', '2', '4', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '2', '8', '3', '8', '9', '1', '9', '1', '5', '7', '3', '2', '5', '5', '0', '0', '9', '3', '2', '4', '3', '9', '4', '5', '3', '1', '/', '4', '4', '2', '5', '7', '2', '9', '1', '6', '9', '0', '1', '3', '3', '3', '5', '2', '5', '7', '2', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '5', '6', '3', '3', '7', '7', '7', '4', '5', '3', '1', '3', '0', '1', '4', '1', '7', '0', '4', '8', '0', '6', '4', '8', '1', '3', '/', '4', '2', '0', '4', '4', '4', '2', '7', '1', '0', '5', '6', '2', '6', '6', '8', '4', '9', '4', '3', '6', '6', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '2', '7', '4', '4', '3', '5', '9', '5', '7', '2', '6', '0', '5', '8', '2', '9', '9', '7', '1', '5', '1', '8', '5', '5', '7', '/', '2', '2', '1', '2', '8', '6', '4', '5', '8', '4', '5', '0', '6', '6', '6', '7', '6', '2', '8', '6', '1', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '0', '9', '8', '3', '1', '3', '2', '1', '6', '3', '9', '0', '1', '7', '6', '3', '7', '5', '1', '1', '8', '8', '9', '1', '/', '8', '0', '4', '6', '7', '8', '0', '3', '0', '7', '2', '9', '6', '9', '7', '3', '1', '9', '4', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '1', '9', '0', '5', '9', '5', '3', '4', '3', '4', '1', '5', '4', '0', '4', '4', '7', '8', '2', '5', '0', '1', '3', '3', '/', '4', '8', '2', '8', '0', '6', '8', '1', '8', '4', '3', '7', '8', '1', '8', '3', '9', '1', '6', '9', '7', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '1', '4', '8', '0', '6', '0', '4', '0', '7', '9', '6', '7', '7', '4', '5', '8', '3', '4', '9', '4', '0', '6', '7', '8', '9', '/', '8', '2', '9', '8', '2', '4', '2', '1', '9', '1', '9', '0', '0', '0', '0', '3', '6', '0', '7', '3', '0', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '9', '7', '0', '8', '7', '6', '9', '8', '0', '0', '3', '4', '3', '0', '3', '8', '2', '1', '3', '2', '1', '1', '2', '4', '8', '8', '3', '/', '8', '4', '0', '8', '8', '8', '5', '4', '2', '1', '1', '2', '5', '3', '3', '6', '9', '8', '8', '7', '3', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '4', '4', '5', '0', '2', '4', '7', '3', '4', '7', '0', '3', '8', '8', '7', '2', '9', '6', '1', '6', '1', '6', '9', '4', '3', '1', '/', '8', '4', '0', '8', '8', '8', '5', '4', '2', '1', '1', '2', '5', '3', '3', '6', '9', '8', '8', '7', '3', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1465514_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 539) (SourceJson.white (fragment1465514Field005Chars00 ++ tail)) fragment1465514Acc00500 =
      SourceJson.object (fuel + 538) (SourceJson.white tail) fragment1465514Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_005"
  err.flush

noncomputable def fragment1465514Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1465514Field006Value00 : SourceJson := .str (String.ofList ['5', '1', '7', '5', '7', '7', '6', '9', '6', '2', '3', '9', '2', '8', '1', '0', '7', '1', '3', '8', '3', '3', '5', '4', '6', '5', '0', '4', '4', '1', '9', '7', '5', '2', '3', '9', '5', '0', '0', '4', '7', '3', '8', '1', '1', '8', '8', '9', '3', '0', '7', '5', '5', '0', '2', '4', '9', '9', '2', '5', '0', '/', '1', '9', '1', '6', '6', '7', '3', '6', '8', '1', '2', '3', '5', '3', '5', '2', '1', '5', '7', '2', '0', '2', '4', '9', '1', '1', '2', '8', '0', '7', '4', '1', '8', '8', '8', '3', '3', '4', '7', '2', '5', '9', '3', '4', '3', '0', '7', '4', '7', '3', '3', '0', '4', '1', '8', '7', '6', '0', '7', '6', '9', '5', '2', '0', '2', '3', '2', '1', '7', '4', '7'])
noncomputable def fragment1465514Acc00700 : List (String × SourceJson) := (fragment1465514Field006Key00, fragment1465514Field006Value00) :: fragment1465514Acc00600
noncomputable def fragment1465514Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '1', '7', '5', '7', '7', '6', '9', '6', '2', '3', '9', '2', '8', '1', '0', '7', '1', '3', '8', '3', '3', '5', '4', '6', '5', '0', '4', '4', '1', '9', '7', '5', '2', '3', '9', '5', '0', '0', '4', '7', '3', '8', '1', '1', '8', '8', '9', '3', '0', '7', '5', '5', '0', '2', '4', '9', '9', '2', '5', '0', '/', '1', '9', '1', '6', '6', '7', '3', '6', '8', '1', '2', '3', '5', '3', '5', '2', '1', '5', '7', '2', '0', '2', '4', '9', '1', '1', '2', '8', '0', '7', '4', '1', '8', '8', '8', '3', '3', '4', '7', '2', '5', '9', '3', '4', '3', '0', '7', '4', '7', '3', '3', '0', '4', '1', '8', '7', '6', '0', '7', '6', '9', '5', '2', '0', '2', '3', '2', '1', '7', '4', '7', '"', ',']

theorem object_fragment1465514_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 538) (SourceJson.white (fragment1465514Field006Chars00 ++ tail)) fragment1465514Acc00600 =
      SourceJson.object (fuel + 537) (SourceJson.white tail) fragment1465514Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_006"
  err.flush

noncomputable def fragment1465514Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1465514Field007Value00 : SourceJson := .str (String.ofList ['9', '8', '6', '4', '3', '5', '7', '2', '7', '2', '9', '6', '9', '7', '2', '5', '8', '8', '4', '1', '2', '4', '2', '6', '5', '4', '1', '8', '5', '1', '6', '3', '1', '6', '6', '1', '1', '6', '1', '3', '2', '9', '9', '2', '6', '5', '4', '5', '2', '4', '1', '3', '8', '1', '0', '5', '1', '0', '4', '6', '4', '7', '2', '6', '8', '0', '6', '2', '3', '6', '6', '0', '6', '8', '6', '1', '3', '1', '4', '6', '3', '0', '9', '1', '7', '6', '5', '5', '9', '1', '7', '2', '9', '3', '5', '9', '8', '7', '0', '1', '3', '3', '7', '9', '9', '4', '5', '7', '9', '5', '5', '7', '2', '5', '0', '0', '8', '5', '5', '9', '6', '3', '8', '6', '3', '6', '5', '6', '4', '5', '4', '9', '4', '1', '0', '4', '3', '4', '6', '3', '9', '8', '3', '6', '3', '6', '0', '5', '5', '8', '8', '3', '0', '1', '6', '4', '7', '3', '5', '4', '2', '1', '0', '6', '2', '6', '2', '9', '4', '1', '9', '4', '3', '2', '5', '0', '9', '2', '8', '3', '6', '9', '8', '6', '1', '3', '2', '5', '8', '1', '3', '1', '4', '8', '4', '3', '3', '2', '3', '5', '1', '4', '0', '4', '9', '9', '8', '6', '3', '3', '8', '0', '9', '4', '8', '4', '6', '7', '8', '8', '0', '7', '6', '7', '9', '4', '7', '7', '5', '1', '7', '3', '6', '2', '8', '5', '1', '8', '7', '3', '0', '9', '5', '9', '1', '5', '2', '2', '7', '9', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '2', '3', '2', '9', '9', '8', '1', '3', '0', '1', '3', '1', '1', '8', '8', '6', '9', '5', '9', '1', '8', '1', '3', '1', '3', '0', '4', '9', '3', '0', '1', '8', '1', '8', '3', '0', '1', '6', '1', '7', '5', '5', '9', '2', '1', '0', '3', '6', '1', '9', '0', '6', '7', '4', '6', '3', '8', '8', '3', '7', '8', '7', '8', '5', '2', '6', '8', '4', '2', '4', '0', '2', '2', '8', '1', '5', '7', '0', '1', '0', '6', '9', '1', '5', '5', '9', '6', '3', '5', '5', '8', '6', '3', '2', '1', '1', '4', '4', '0', '4', '4', '1', '8', '5', '4', '5', '3', '9', '3', '5', '2', '1', '2', '5', '0', '1', '7', '8', '8', '7', '9', '4', '3', '3', '7', '8', '7', '6', '2', '4', '4', '8', '7', '0', '4', '9', '0', '8', '7', '8', '6', '8', '5', '4', '0', '3', '2', '0', '2', '5', '6', '0', '5', '2', '7', '8', '3', '4', '8', '4', '9', '2', '1', '5', '4', '5', '0', '1', '8', '5', '2', '7', '3', '4', '7', '4', '7', '0', '7', '7', '9', '4', '0', '8', '7', '7', '0', '4', '7', '9', '6', '3', '8', '5', '0', '5', '8', '6', '5', '0', '2', '4', '6', '8', '6', '3', '0', '6', '6', '2', '5', '8', '6', '2', '8', '0', '6', '8', '8', '4', '1', '1', '9', '2', '7', '0', '6', '5', '0', '9', '6', '8', '5', '6', '3', '4', '8', '4', '3', '8', '0', '1', '2', '6', '3', '6', '1', '6', '5', '8', '3', '5', '8', '0', '3', '7', '8', '7', '5', '6', '4', '0', '4', '4', '7', '5', '3', '7', '3'])
noncomputable def fragment1465514Acc00800 : List (String × SourceJson) := (fragment1465514Field007Key00, fragment1465514Field007Value00) :: fragment1465514Acc00700
noncomputable def fragment1465514Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '8', '6', '4', '3', '5', '7', '2', '7', '2', '9', '6', '9', '7', '2', '5', '8', '8', '4', '1', '2', '4', '2', '6', '5', '4', '1', '8', '5', '1', '6', '3', '1', '6', '6', '1', '1', '6', '1', '3', '2', '9', '9', '2', '6', '5', '4', '5', '2', '4', '1', '3', '8', '1', '0', '5', '1', '0', '4', '6', '4', '7', '2', '6', '8', '0', '6', '2', '3', '6', '6', '0', '6', '8', '6', '1', '3', '1', '4', '6', '3', '0', '9', '1', '7', '6', '5', '5', '9', '1', '7', '2', '9', '3', '5', '9', '8', '7', '0', '1', '3', '3', '7', '9', '9', '4', '5', '7', '9', '5', '5', '7', '2', '5', '0', '0', '8', '5', '5', '9', '6', '3', '8', '6', '3', '6', '5', '6', '4', '5', '4', '9', '4', '1', '0', '4', '3', '4', '6', '3', '9', '8', '3', '6', '3', '6', '0', '5', '5', '8', '8', '3', '0', '1', '6', '4', '7', '3', '5', '4', '2', '1', '0', '6', '2', '6', '2', '9', '4', '1', '9', '4', '3', '2', '5', '0', '9', '2', '8', '3', '6', '9', '8', '6', '1', '3', '2', '5', '8', '1', '3', '1', '4', '8', '4', '3', '3', '2', '3', '5', '1', '4', '0', '4', '9', '9', '8', '6', '3', '3', '8', '0', '9', '4', '8', '4', '6', '7', '8', '8', '0', '7', '6', '7', '9', '4', '7', '7', '5', '1', '7', '3', '6', '2', '8', '5', '1', '8', '7', '3', '0', '9', '5', '9', '1', '5', '2', '2', '7', '9', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '2', '3', '2', '9', '9', '8', '1', '3', '0', '1', '3', '1', '1', '8', '8', '6', '9', '5', '9', '1', '8', '1', '3', '1', '3', '0', '4', '9', '3', '0', '1', '8', '1', '8', '3', '0', '1', '6', '1', '7', '5', '5', '9', '2', '1', '0', '3', '6', '1', '9', '0', '6', '7', '4', '6', '3', '8', '8', '3', '7', '8', '7', '8', '5', '2', '6', '8', '4', '2', '4', '0', '2', '2', '8', '1', '5', '7', '0', '1', '0', '6', '9', '1', '5', '5', '9', '6', '3', '5', '5', '8', '6', '3', '2', '1', '1', '4', '4', '0', '4', '4', '1', '8', '5', '4', '5', '3', '9', '3', '5', '2', '1', '2', '5', '0', '1', '7', '8', '8', '7', '9', '4', '3', '3', '7', '8', '7', '6', '2', '4', '4', '8', '7', '0', '4', '9', '0', '8', '7', '8', '6', '8', '5', '4', '0', '3', '2', '0', '2', '5', '6', '0', '5', '2', '7', '8', '3', '4', '8', '4', '9', '2', '1', '5', '4', '5', '0', '1', '8', '5', '2', '7', '3', '4', '7', '4', '7', '0', '7', '7', '9', '4', '0', '8', '7', '7', '0', '4', '7', '9', '6', '3', '8', '5', '0', '5', '8', '6', '5', '0', '2', '4', '6', '8', '6', '3', '0', '6', '6', '2', '5', '8', '6', '2', '8', '0', '6', '8', '8', '4', '1', '1', '9', '2', '7', '0', '6', '5', '0', '9', '6', '8', '5', '6', '3', '4', '8', '4', '3', '8', '0', '1', '2', '6', '3', '6', '1', '6', '5', '8', '3', '5', '8', '0', '3', '7', '8', '7', '5', '6', '4', '0', '4', '4', '7', '5', '3', '7', '3', '"', ',']

theorem object_fragment1465514_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 537) (SourceJson.white (fragment1465514Field007Chars00 ++ tail)) fragment1465514Acc00700 =
      SourceJson.object (fuel + 536) (SourceJson.white tail) fragment1465514Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_007"
  err.flush

noncomputable def fragment1465514Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1465514Field008Value00 : SourceJson := .str (String.ofList ['2', '1', '3', '9', '4', '7', '3', '7', '2', '6', '4', '2', '8', '7', '0', '8', '9', '1', '6', '4'])
noncomputable def fragment1465514Acc00900 : List (String × SourceJson) := (fragment1465514Field008Key00, fragment1465514Field008Value00) :: fragment1465514Acc00800
noncomputable def fragment1465514Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '1', '3', '9', '4', '7', '3', '7', '2', '6', '4', '2', '8', '7', '0', '8', '9', '1', '6', '4', '"', ',']

theorem object_fragment1465514_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 536) (SourceJson.white (fragment1465514Field008Chars00 ++ tail)) fragment1465514Acc00800 =
      SourceJson.object (fuel + 535) (SourceJson.white tail) fragment1465514Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_008"
  err.flush

noncomputable def fragment1465514Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1465514Field009Value00 : SourceJson := .str (String.ofList ['2', '0', '9', '9', '0', '3', '8', '3', '2', '7', '2', '1', '2', '0', '8', '0', '2', '5', '1', '5', '7'])
noncomputable def fragment1465514Acc01000 : List (String × SourceJson) := (fragment1465514Field009Key00, fragment1465514Field009Value00) :: fragment1465514Acc00900
noncomputable def fragment1465514Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '9', '9', '0', '3', '8', '3', '2', '7', '2', '1', '2', '0', '8', '0', '2', '5', '1', '5', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment1465514_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 535) (SourceJson.white (fragment1465514Field009Chars00 ++ tail)) fragment1465514Acc00900 =
      .ok (.obj (fragment1465514Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1465514_object_field_009"
  err.flush

noncomputable def fragment1465514Chars : List Char := '{' :: (fragment1465514Field000Chars00 ++ fragment1465514Field001Chars00 ++ fragment1465514Field002Chars00 ++ fragment1465514Field003Chars00 ++ fragment1465514Field004Chars00 ++ fragment1465514Field005Chars00 ++ fragment1465514Field006Chars00 ++ fragment1465514Field007Chars00 ++ fragment1465514Field008Chars00 ++ fragment1465514Field009Chars00)
noncomputable def fragment1465514Value : SourceJson := .obj (fragment1465514Acc01000.reverse)

theorem value_fragment1465514 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 545) (fragment1465514Chars ++ tail) =
      .ok (fragment1465514Value, tail) := by
  have hinput : fragment1465514Chars ++ tail = '{' :: (fragment1465514Field000Chars00 ++ (fragment1465514Field001Chars00 ++ (fragment1465514Field002Chars00 ++ (fragment1465514Field003Chars00 ++ (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment1465514Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 545) (fragment1465514Chars ++ tail) =
        SourceJson.value (fuel + 545) ('{' :: (fragment1465514Field000Chars00 ++ (fragment1465514Field001Chars00 ++ (fragment1465514Field002Chars00 ++ (fragment1465514Field003Chars00 ++ (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 545)) hinput
    _ = SourceJson.object (fuel + 544) (SourceJson.white (fragment1465514Field000Chars00 ++ (fragment1465514Field001Chars00 ++ (fragment1465514Field002Chars00 ++ (fragment1465514Field003Chars00 ++ (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))))))))))) fragment1465514Acc00000 := by rfl
    _ = SourceJson.object (fuel + 543) (SourceJson.white (fragment1465514Field001Chars00 ++ (fragment1465514Field002Chars00 ++ (fragment1465514Field003Chars00 ++ (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail))))))))))) fragment1465514Acc00100 := object_fragment1465514_field_000 fuel (fragment1465514Field001Chars00 ++ (fragment1465514Field002Chars00 ++ (fragment1465514Field003Chars00 ++ (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 542) (SourceJson.white (fragment1465514Field002Chars00 ++ (fragment1465514Field003Chars00 ++ (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))))))))) fragment1465514Acc00200 := object_fragment1465514_field_001 fuel (fragment1465514Field002Chars00 ++ (fragment1465514Field003Chars00 ++ (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 541) (SourceJson.white (fragment1465514Field003Chars00 ++ (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail))))))))) fragment1465514Acc00300 := object_fragment1465514_field_002 fuel (fragment1465514Field003Chars00 ++ (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 540) (SourceJson.white (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))))))) fragment1465514Acc00400 := object_fragment1465514_field_003 fuel (fragment1465514Field004Chars00 ++ (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 539) (SourceJson.white (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail))))))) fragment1465514Acc00500 := object_fragment1465514_field_004 fuel (fragment1465514Field005Chars00 ++ (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 538) (SourceJson.white (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))))) fragment1465514Acc00600 := object_fragment1465514_field_005 fuel (fragment1465514Field006Chars00 ++ (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 537) (SourceJson.white (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail))))) fragment1465514Acc00700 := object_fragment1465514_field_006 fuel (fragment1465514Field007Chars00 ++ (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 536) (SourceJson.white (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))) fragment1465514Acc00800 := object_fragment1465514_field_007 fuel (fragment1465514Field008Chars00 ++ (fragment1465514Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 535) (SourceJson.white (fragment1465514Field009Chars00 ++ (tail))) fragment1465514Acc00900 := object_fragment1465514_field_008 fuel (fragment1465514Field009Chars00 ++ (tail))
    _ = .ok (fragment1465514Value, tail) := object_fragment1465514_field_009 fuel (tail)

noncomputable def fragment1467781Acc00000 : List (String × SourceJson) := []

noncomputable def fragment1467781Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment1467781Field000Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment1467781Acc00100 : List (String × SourceJson) := (fragment1467781Field000Key00, fragment1467781Field000Value00) :: fragment1467781Acc00000
noncomputable def fragment1467781Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', ',']

theorem object_fragment1467781_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 508) (SourceJson.white (fragment1467781Field000Chars00 ++ tail)) fragment1467781Acc00000 =
      SourceJson.object (fuel + 507) (SourceJson.white tail) fragment1467781Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_000"
  err.flush

noncomputable def fragment1467781Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment1467781Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['8', '5']), .number (String.ofList ['5', '0']), .number (String.ofList ['4', '7']), .number (String.ofList ['1', '2']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment1467781Acc00200 : List (String × SourceJson) := (fragment1467781Field001Key00, fragment1467781Field001Value00) :: fragment1467781Acc00100
noncomputable def fragment1467781Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1467781_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 507) (SourceJson.white (fragment1467781Field001Chars00 ++ tail)) fragment1467781Acc00100 =
      SourceJson.object (fuel + 506) (SourceJson.white tail) fragment1467781Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_001"
  err.flush

noncomputable def fragment1467781Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment1467781Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '1', '6', '6', '3', '9', '7', '0', '3', '3', '9', '4', '1', '7', '8', '4', '4', '0', '6', '1', '0', '5', '8', '5', '2', '2', '4', '8', '2', '8', '3', '3', '6', '8', '3', '7', '3', '9', '1', '7', '5', '9', '1', '0', '9', '/', '4', '2', '4', '6', '2', '7', '9', '6', '8', '1', '0', '4', '2', '0', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1467781Acc00300 : List (String × SourceJson) := (fragment1467781Field002Key00, fragment1467781Field002Value00) :: fragment1467781Acc00200
noncomputable def fragment1467781Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '1', '6', '6', '3', '9', '7', '0', '3', '3', '9', '4', '1', '7', '8', '4', '4', '0', '6', '1', '0', '5', '8', '5', '2', '2', '4', '8', '2', '8', '3', '3', '6', '8', '3', '7', '3', '9', '1', '7', '5', '9', '1', '0', '9', '/', '4', '2', '4', '6', '2', '7', '9', '6', '8', '1', '0', '4', '2', '0', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1467781_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 506) (SourceJson.white (fragment1467781Field002Chars00 ++ tail)) fragment1467781Acc00200 =
      SourceJson.object (fuel + 505) (SourceJson.white tail) fragment1467781Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_002"
  err.flush

noncomputable def fragment1467781Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment1467781Field003Value00 : SourceJson := .str (String.ofList ['2', '2', '5', '3', '3', '7', '7', '7', '3', '7', '/', '2', '1', '2', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1467781Acc00400 : List (String × SourceJson) := (fragment1467781Field003Key00, fragment1467781Field003Value00) :: fragment1467781Acc00300
noncomputable def fragment1467781Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '2', '5', '3', '3', '7', '7', '7', '3', '7', '/', '2', '1', '2', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1467781_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 505) (SourceJson.white (fragment1467781Field003Chars00 ++ tail)) fragment1467781Acc00300 =
      SourceJson.object (fuel + 504) (SourceJson.white tail) fragment1467781Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_003"
  err.flush

noncomputable def fragment1467781Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment1467781Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '4', '0', '2', '6', '1', '/', '2', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '7', '1', '9', '0', '3', '/', '3', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0'])]
noncomputable def fragment1467781Acc00500 : List (String × SourceJson) := (fragment1467781Field004Key00, fragment1467781Field004Value00) :: fragment1467781Acc00400
noncomputable def fragment1467781Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '4', '0', '2', '6', '1', '/', '2', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '7', '1', '9', '0', '3', '/', '3', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1467781_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 504) (SourceJson.white (fragment1467781Field004Chars00 ++ tail)) fragment1467781Acc00400 =
      SourceJson.object (fuel + 503) (SourceJson.white tail) fragment1467781Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_004"
  err.flush

noncomputable def fragment1467781Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment1467781Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '4', '1', '8', '5', '9', '5', '7', '1', '0', '5', '4', '2', '0', '8', '0', '3', '2', '4', '8', '2', '9', '7', '7', '9', '/', '1', '8', '2', '9', '1', '6', '4', '7', '8', '5', '8', '2', '8', '8', '7', '2', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '4', '8', '0', '8', '2', '5', '7', '5', '8', '3', '6', '5', '8', '2', '9', '2', '1', '3', '3', '6', '2', '7', '3', '1', '/', '2', '3', '7', '7', '9', '1', '4', '2', '2', '1', '5', '7', '7', '5', '3', '3', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '6', '6', '0', '5', '3', '4', '9', '5', '7', '3', '7', '8', '2', '5', '4', '4', '9', '1', '9', '7', '6', '9', '/', '6', '0', '0', '7', '3', '6', '2', '2', '4', '3', '9', '8', '5', '3', '4', '8', '6', '4', '6', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '0', '7', '5', '9', '0', '7', '9', '6', '9', '2', '3', '9', '6', '1', '8', '6', '9', '2', '3', '8', '7', '7', '0', '8', '1', '/', '1', '4', '2', '6', '7', '4', '8', '5', '3', '2', '9', '4', '6', '5', '2', '0', '3', '0', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '5', '4', '0', '4', '0', '7', '7', '3', '3', '8', '8', '3', '9', '9', '0', '4', '8', '3', '2', '1', '8', '4', '9', '9', '/', '7', '5', '0', '9', '2', '0', '2', '8', '0', '4', '9', '8', '1', '6', '8', '5', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '7', '8', '1', '7', '8', '1', '5', '6', '2', '1', '6', '7', '7', '6', '0', '5', '4', '0', '9', '2', '3', '3', '/', '6', '8', '2', '6', '5', '4', '8', '0', '0', '4', '5', '2', '8', '8', '0', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '4', '4', '3', '0', '9', '7', '9', '5', '4', '3', '2', '7', '3', '4', '1', '6', '1', '6', '4', '8', '6', '1', '/', '1', '2', '7', '9', '9', '7', '7', '7', '5', '0', '8', '4', '9', '1', '5', '0', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '1', '2', '9', '9', '6', '4', '4', '5', '0', '7', '5', '1', '7', '0', '6', '0', '3', '4', '7', '5', '4', '9', '9', '/', '5', '6', '3', '1', '9', '0', '2', '1', '0', '3', '7', '3', '6', '2', '6', '4', '3', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '3', '6', '4', '6', '5', '4', '6', '5', '0', '2', '0', '2', '7', '5', '2', '2', '8', '4', '7', '8', '3', '1', '3', '/', '1', '9', '2', '8', '0', '3', '8', '5', '5', '8', '0', '3', '5', '8', '3', '8', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '4', '6', '3', '0', '6', '9', '3', '8', '5', '9', '1', '0', '8', '5', '3', '7', '7', '6', '7', '7', '5', '9', '7', '1', '/', '7', '1', '3', '3', '7', '4', '2', '6', '6', '4', '7', '3', '2', '6', '0', '1', '5', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment1467781Acc00600 : List (String × SourceJson) := (fragment1467781Field005Key00, fragment1467781Field005Value00) :: fragment1467781Acc00500
noncomputable def fragment1467781Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '1', '8', '5', '9', '5', '7', '1', '0', '5', '4', '2', '0', '8', '0', '3', '2', '4', '8', '2', '9', '7', '7', '9', '/', '1', '8', '2', '9', '1', '6', '4', '7', '8', '5', '8', '2', '8', '8', '7', '2', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '4', '8', '0', '8', '2', '5', '7', '5', '8', '3', '6', '5', '8', '2', '9', '2', '1', '3', '3', '6', '2', '7', '3', '1', '/', '2', '3', '7', '7', '9', '1', '4', '2', '2', '1', '5', '7', '7', '5', '3', '3', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '6', '6', '0', '5', '3', '4', '9', '5', '7', '3', '7', '8', '2', '5', '4', '4', '9', '1', '9', '7', '6', '9', '/', '6', '0', '0', '7', '3', '6', '2', '2', '4', '3', '9', '8', '5', '3', '4', '8', '6', '4', '6', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '0', '7', '5', '9', '0', '7', '9', '6', '9', '2', '3', '9', '6', '1', '8', '6', '9', '2', '3', '8', '7', '7', '0', '8', '1', '/', '1', '4', '2', '6', '7', '4', '8', '5', '3', '2', '9', '4', '6', '5', '2', '0', '3', '0', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '5', '4', '0', '4', '0', '7', '7', '3', '3', '8', '8', '3', '9', '9', '0', '4', '8', '3', '2', '1', '8', '4', '9', '9', '/', '7', '5', '0', '9', '2', '0', '2', '8', '0', '4', '9', '8', '1', '6', '8', '5', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '7', '8', '1', '7', '8', '1', '5', '6', '2', '1', '6', '7', '7', '6', '0', '5', '4', '0', '9', '2', '3', '3', '/', '6', '8', '2', '6', '5', '4', '8', '0', '0', '4', '5', '2', '8', '8', '0', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '4', '4', '3', '0', '9', '7', '9', '5', '4', '3', '2', '7', '3', '4', '1', '6', '1', '6', '4', '8', '6', '1', '/', '1', '2', '7', '9', '9', '7', '7', '7', '5', '0', '8', '4', '9', '1', '5', '0', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '1', '2', '9', '9', '6', '4', '4', '5', '0', '7', '5', '1', '7', '0', '6', '0', '3', '4', '7', '5', '4', '9', '9', '/', '5', '6', '3', '1', '9', '0', '2', '1', '0', '3', '7', '3', '6', '2', '6', '4', '3', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '3', '6', '4', '6', '5', '4', '6', '5', '0', '2', '0', '2', '7', '5', '2', '2', '8', '4', '7', '8', '3', '1', '3', '/', '1', '9', '2', '8', '0', '3', '8', '5', '5', '8', '0', '3', '5', '8', '3', '8', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '4', '6', '3', '0', '6', '9', '3', '8', '5', '9', '1', '0', '8', '5', '3', '7', '7', '6', '7', '7', '5', '9', '7', '1', '/', '7', '1', '3', '3', '7', '4', '2', '6', '6', '4', '7', '3', '2', '6', '0', '1', '5', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1467781_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 503) (SourceJson.white (fragment1467781Field005Chars00 ++ tail)) fragment1467781Acc00500 =
      SourceJson.object (fuel + 502) (SourceJson.white tail) fragment1467781Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_005"
  err.flush

noncomputable def fragment1467781Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1467781Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '2', '8', '9', '2', '0', '6', '5', '4', '5', '6', '2', '1', '3', '1', '2', '7', '0', '2', '9', '4', '7', '7', '1', '0', '0', '3', '2', '7', '9', '3', '4', '3', '8', '0', '9', '0', '0', '1', '5', '1', '6', '7', '4', '3', '4', '8', '2', '1', '5', '7', '8', '5', '3', '5', '6', '9', '1', '0', '5', '/', '5', '0', '5', '4', '4', '1', '1', '9', '5', '7', '7', '0', '3', '9', '3', '1', '9', '5', '5', '2', '7', '8', '2', '1', '3', '4', '7', '0', '0', '3', '8', '4', '9', '0', '6', '8', '9', '8', '7', '7', '6', '3', '7', '7', '8', '8', '4', '3', '1', '9', '1', '0', '7', '6', '6', '5', '2', '3', '3', '2', '4', '2', '3', '7', '5', '0', '1', '4', '7', '8', '4'])
noncomputable def fragment1467781Acc00700 : List (String × SourceJson) := (fragment1467781Field006Key00, fragment1467781Field006Value00) :: fragment1467781Acc00600
noncomputable def fragment1467781Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '2', '8', '9', '2', '0', '6', '5', '4', '5', '6', '2', '1', '3', '1', '2', '7', '0', '2', '9', '4', '7', '7', '1', '0', '0', '3', '2', '7', '9', '3', '4', '3', '8', '0', '9', '0', '0', '1', '5', '1', '6', '7', '4', '3', '4', '8', '2', '1', '5', '7', '8', '5', '3', '5', '6', '9', '1', '0', '5', '/', '5', '0', '5', '4', '4', '1', '1', '9', '5', '7', '7', '0', '3', '9', '3', '1', '9', '5', '5', '2', '7', '8', '2', '1', '3', '4', '7', '0', '0', '3', '8', '4', '9', '0', '6', '8', '9', '8', '7', '7', '6', '3', '7', '7', '8', '8', '4', '3', '1', '9', '1', '0', '7', '6', '6', '5', '2', '3', '3', '2', '4', '2', '3', '7', '5', '0', '1', '4', '7', '8', '4', '"', ',']

theorem object_fragment1467781_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 502) (SourceJson.white (fragment1467781Field006Chars00 ++ tail)) fragment1467781Acc00600 =
      SourceJson.object (fuel + 501) (SourceJson.white tail) fragment1467781Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_006"
  err.flush

noncomputable def fragment1467781Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1467781Field007Value00 : SourceJson := .str (String.ofList ['2', '3', '0', '6', '6', '1', '1', '0', '2', '5', '4', '7', '2', '6', '9', '1', '1', '2', '1', '7', '6', '2', '1', '5', '6', '7', '7', '3', '2', '4', '2', '9', '5', '0', '6', '5', '3', '9', '2', '8', '0', '5', '4', '1', '6', '4', '1', '3', '7', '7', '8', '0', '2', '4', '5', '5', '6', '3', '5', '5', '8', '4', '6', '6', '1', '5', '7', '8', '5', '7', '2', '8', '6', '2', '3', '4', '7', '5', '9', '6', '4', '4', '1', '7', '1', '9', '5', '9', '7', '1', '6', '6', '1', '7', '4', '8', '0', '6', '6', '8', '4', '5', '1', '8', '5', '0', '8', '9', '0', '6', '0', '9', '9', '7', '0', '6', '8', '9', '2', '0', '7', '8', '8', '4', '5', '4', '4', '1', '0', '5', '7', '8', '3', '0', '2', '7', '9', '0', '5', '5', '3', '8', '2', '9', '2', '8', '5', '2', '6', '7', '5', '3', '5', '1', '5', '9', '8', '7', '1', '4', '8', '5', '6', '1', '9', '8', '2', '7', '0', '8', '3', '7', '9', '1', '6', '1', '2', '8', '5', '2', '5', '6', '1', '8', '1', '8', '9', '7', '7', '3', '7', '0', '9', '8', '9', '5', '6', '2', '5', '7', '9', '4', '2', '6', '5', '8', '5', '6', '7', '7', '6', '2', '0', '6', '9', '9', '2', '6', '7', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '1', '9', '5', '8', '0', '4', '1', '1', '7', '8', '9', '2', '4', '1', '8', '7', '5', '5', '5', '1', '4', '8', '8', '8', '3', '9', '8', '4', '3', '6', '8', '2', '0', '5', '5', '6', '2', '1', '3', '9', '6', '1', '5', '1', '1', '3', '6', '8', '4', '4', '5', '9', '2', '6', '8', '6', '3', '9', '6', '8', '8', '0', '9', '6', '8', '0', '5', '0', '4', '0', '5', '8', '2', '9', '9', '3', '8', '0', '5', '1', '7', '6', '8', '3', '2', '4', '4', '6', '3', '4', '7', '9', '0', '6', '5', '1', '0', '4', '2', '9', '4', '0', '0', '4', '3', '1', '9', '0', '7', '8', '8', '7', '0', '8', '3', '0', '7', '7', '0', '3', '6', '3', '3', '4', '5', '6', '2', '2', '9', '2', '4', '8', '2', '6', '3', '7', '3', '0', '6', '5', '3', '1', '7', '6', '3', '0', '3', '6', '7', '5', '1', '1', '5', '5', '3', '7', '0', '4', '5', '3', '1', '9', '8', '2', '1', '0', '0', '6', '5', '8', '3', '8', '4', '8', '2', '2', '7', '2', '6', '7', '5', '9', '2', '9', '0', '8', '9', '6', '7', '8', '2', '2', '2', '8', '1', '8', '2', '8', '6', '0', '2', '4', '1', '3', '3', '7', '6', '6', '4', '9', '1', '5', '6', '3', '1', '2', '5', '8', '5', '3', '0', '7', '2', '5', '3', '8', '0', '1', '6', '8', '6', '3', '8', '2', '3', '1', '5', '1', '5', '1', '3', '7', '7', '8', '4', '2', '8', '3', '9', '0', '3', '9'])
noncomputable def fragment1467781Acc00800 : List (String × SourceJson) := (fragment1467781Field007Key00, fragment1467781Field007Value00) :: fragment1467781Acc00700
noncomputable def fragment1467781Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '3', '0', '6', '6', '1', '1', '0', '2', '5', '4', '7', '2', '6', '9', '1', '1', '2', '1', '7', '6', '2', '1', '5', '6', '7', '7', '3', '2', '4', '2', '9', '5', '0', '6', '5', '3', '9', '2', '8', '0', '5', '4', '1', '6', '4', '1', '3', '7', '7', '8', '0', '2', '4', '5', '5', '6', '3', '5', '5', '8', '4', '6', '6', '1', '5', '7', '8', '5', '7', '2', '8', '6', '2', '3', '4', '7', '5', '9', '6', '4', '4', '1', '7', '1', '9', '5', '9', '7', '1', '6', '6', '1', '7', '4', '8', '0', '6', '6', '8', '4', '5', '1', '8', '5', '0', '8', '9', '0', '6', '0', '9', '9', '7', '0', '6', '8', '9', '2', '0', '7', '8', '8', '4', '5', '4', '4', '1', '0', '5', '7', '8', '3', '0', '2', '7', '9', '0', '5', '5', '3', '8', '2', '9', '2', '8', '5', '2', '6', '7', '5', '3', '5', '1', '5', '9', '8', '7', '1', '4', '8', '5', '6', '1', '9', '8', '2', '7', '0', '8', '3', '7', '9', '1', '6', '1', '2', '8', '5', '2', '5', '6', '1', '8', '1', '8', '9', '7', '7', '3', '7', '0', '9', '8', '9', '5', '6', '2', '5', '7', '9', '4', '2', '6', '5', '8', '5', '6', '7', '7', '6', '2', '0', '6', '9', '9', '2', '6', '7', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '1', '9', '5', '8', '0', '4', '1', '1', '7', '8', '9', '2', '4', '1', '8', '7', '5', '5', '5', '1', '4', '8', '8', '8', '3', '9', '8', '4', '3', '6', '8', '2', '0', '5', '5', '6', '2', '1', '3', '9', '6', '1', '5', '1', '1', '3', '6', '8', '4', '4', '5', '9', '2', '6', '8', '6', '3', '9', '6', '8', '8', '0', '9', '6', '8', '0', '5', '0', '4', '0', '5', '8', '2', '9', '9', '3', '8', '0', '5', '1', '7', '6', '8', '3', '2', '4', '4', '6', '3', '4', '7', '9', '0', '6', '5', '1', '0', '4', '2', '9', '4', '0', '0', '4', '3', '1', '9', '0', '7', '8', '8', '7', '0', '8', '3', '0', '7', '7', '0', '3', '6', '3', '3', '4', '5', '6', '2', '2', '9', '2', '4', '8', '2', '6', '3', '7', '3', '0', '6', '5', '3', '1', '7', '6', '3', '0', '3', '6', '7', '5', '1', '1', '5', '5', '3', '7', '0', '4', '5', '3', '1', '9', '8', '2', '1', '0', '0', '6', '5', '8', '3', '8', '4', '8', '2', '2', '7', '2', '6', '7', '5', '9', '2', '9', '0', '8', '9', '6', '7', '8', '2', '2', '2', '8', '1', '8', '2', '8', '6', '0', '2', '4', '1', '3', '3', '7', '6', '6', '4', '9', '1', '5', '6', '3', '1', '2', '5', '8', '5', '3', '0', '7', '2', '5', '3', '8', '0', '1', '6', '8', '6', '3', '8', '2', '3', '1', '5', '1', '5', '1', '3', '7', '7', '8', '4', '2', '8', '3', '9', '0', '3', '9', '"', ',']

theorem object_fragment1467781_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 501) (SourceJson.white (fragment1467781Field007Chars00 ++ tail)) fragment1467781Acc00700 =
      SourceJson.object (fuel + 500) (SourceJson.white tail) fragment1467781Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_007"
  err.flush

noncomputable def fragment1467781Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1467781Field008Value00 : SourceJson := .str (String.ofList ['2', '3', '9', '6', '5', '9', '0', '8', '4', '1', '9', '1', '6', '4', '8', '0', '8', '1', '4'])
noncomputable def fragment1467781Acc00900 : List (String × SourceJson) := (fragment1467781Field008Key00, fragment1467781Field008Value00) :: fragment1467781Acc00800
noncomputable def fragment1467781Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '9', '6', '5', '9', '0', '8', '4', '1', '9', '1', '6', '4', '8', '0', '8', '1', '4', '"', ',']

theorem object_fragment1467781_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 500) (SourceJson.white (fragment1467781Field008Chars00 ++ tail)) fragment1467781Acc00800 =
      SourceJson.object (fuel + 499) (SourceJson.white tail) fragment1467781Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_008"
  err.flush

noncomputable def fragment1467781Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1467781Field009Value00 : SourceJson := .str (String.ofList ['2', '9', '4', '9', '5', '5', '3', '4', '3', '4', '9', '7', '0', '5', '7', '6', '9', '0', '8', '1'])
noncomputable def fragment1467781Acc01000 : List (String × SourceJson) := (fragment1467781Field009Key00, fragment1467781Field009Value00) :: fragment1467781Acc00900
noncomputable def fragment1467781Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '4', '9', '5', '5', '3', '4', '3', '4', '9', '7', '0', '5', '7', '6', '9', '0', '8', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment1467781_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 499) (SourceJson.white (fragment1467781Field009Chars00 ++ tail)) fragment1467781Acc00900 =
      .ok (.obj (fragment1467781Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1467781_object_field_009"
  err.flush

noncomputable def fragment1467781Chars : List Char := '{' :: (fragment1467781Field000Chars00 ++ fragment1467781Field001Chars00 ++ fragment1467781Field002Chars00 ++ fragment1467781Field003Chars00 ++ fragment1467781Field004Chars00 ++ fragment1467781Field005Chars00 ++ fragment1467781Field006Chars00 ++ fragment1467781Field007Chars00 ++ fragment1467781Field008Chars00 ++ fragment1467781Field009Chars00)
noncomputable def fragment1467781Value : SourceJson := .obj (fragment1467781Acc01000.reverse)

theorem value_fragment1467781 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 509) (fragment1467781Chars ++ tail) =
      .ok (fragment1467781Value, tail) := by
  have hinput : fragment1467781Chars ++ tail = '{' :: (fragment1467781Field000Chars00 ++ (fragment1467781Field001Chars00 ++ (fragment1467781Field002Chars00 ++ (fragment1467781Field003Chars00 ++ (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment1467781Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 509) (fragment1467781Chars ++ tail) =
        SourceJson.value (fuel + 509) ('{' :: (fragment1467781Field000Chars00 ++ (fragment1467781Field001Chars00 ++ (fragment1467781Field002Chars00 ++ (fragment1467781Field003Chars00 ++ (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 509)) hinput
    _ = SourceJson.object (fuel + 508) (SourceJson.white (fragment1467781Field000Chars00 ++ (fragment1467781Field001Chars00 ++ (fragment1467781Field002Chars00 ++ (fragment1467781Field003Chars00 ++ (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))))))))))) fragment1467781Acc00000 := by rfl
    _ = SourceJson.object (fuel + 507) (SourceJson.white (fragment1467781Field001Chars00 ++ (fragment1467781Field002Chars00 ++ (fragment1467781Field003Chars00 ++ (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail))))))))))) fragment1467781Acc00100 := object_fragment1467781_field_000 fuel (fragment1467781Field001Chars00 ++ (fragment1467781Field002Chars00 ++ (fragment1467781Field003Chars00 ++ (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 506) (SourceJson.white (fragment1467781Field002Chars00 ++ (fragment1467781Field003Chars00 ++ (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))))))))) fragment1467781Acc00200 := object_fragment1467781_field_001 fuel (fragment1467781Field002Chars00 ++ (fragment1467781Field003Chars00 ++ (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 505) (SourceJson.white (fragment1467781Field003Chars00 ++ (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail))))))))) fragment1467781Acc00300 := object_fragment1467781_field_002 fuel (fragment1467781Field003Chars00 ++ (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 504) (SourceJson.white (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))))))) fragment1467781Acc00400 := object_fragment1467781_field_003 fuel (fragment1467781Field004Chars00 ++ (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 503) (SourceJson.white (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail))))))) fragment1467781Acc00500 := object_fragment1467781_field_004 fuel (fragment1467781Field005Chars00 ++ (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 502) (SourceJson.white (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))))) fragment1467781Acc00600 := object_fragment1467781_field_005 fuel (fragment1467781Field006Chars00 ++ (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 501) (SourceJson.white (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail))))) fragment1467781Acc00700 := object_fragment1467781_field_006 fuel (fragment1467781Field007Chars00 ++ (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 500) (SourceJson.white (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))) fragment1467781Acc00800 := object_fragment1467781_field_007 fuel (fragment1467781Field008Chars00 ++ (fragment1467781Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 499) (SourceJson.white (fragment1467781Field009Chars00 ++ (tail))) fragment1467781Acc00900 := object_fragment1467781_field_008 fuel (fragment1467781Field009Chars00 ++ (tail))
    _ = .ok (fragment1467781Value, tail) := object_fragment1467781_field_009 fuel (tail)

noncomputable def fragment1469962Acc00000 : List (String × SourceJson) := []

noncomputable def fragment1469962Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment1469962Field000Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment1469962Acc00100 : List (String × SourceJson) := (fragment1469962Field000Key00, fragment1469962Field000Value00) :: fragment1469962Acc00000
noncomputable def fragment1469962Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', ',']

theorem object_fragment1469962_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 490) (SourceJson.white (fragment1469962Field000Chars00 ++ tail)) fragment1469962Acc00000 =
      SourceJson.object (fuel + 489) (SourceJson.white tail) fragment1469962Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_000"
  err.flush

noncomputable def fragment1469962Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment1469962Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '1', '5']), .number (String.ofList ['8', '5']), .number (String.ofList ['5', '0']), .number (String.ofList ['4', '7']), .number (String.ofList ['1', '2']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment1469962Acc00200 : List (String × SourceJson) := (fragment1469962Field001Key00, fragment1469962Field001Value00) :: fragment1469962Acc00100
noncomputable def fragment1469962Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1469962_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 489) (SourceJson.white (fragment1469962Field001Chars00 ++ tail)) fragment1469962Acc00100 =
      SourceJson.object (fuel + 488) (SourceJson.white tail) fragment1469962Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_001"
  err.flush

noncomputable def fragment1469962Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment1469962Field002Value00 : SourceJson := .str (String.ofList ['7', '7', '2', '0', '9', '0', '1', '0', '9', '9', '5', '6', '8', '2', '3', '4', '8', '6', '3', '2', '6', '0', '3', '6', '8', '9', '6', '4', '3', '8', '6', '3', '5', '8', '3', '2', '5', '2', '3', '2', '4', '2', '8', '4', '2', '1', '7', '/', '2', '2', '7', '9', '1', '7', '7', '8', '2', '8', '8', '0', '0', '2', '6', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1469962Acc00300 : List (String × SourceJson) := (fragment1469962Field002Key00, fragment1469962Field002Value00) :: fragment1469962Acc00200
noncomputable def fragment1469962Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '7', '2', '0', '9', '0', '1', '0', '9', '9', '5', '6', '8', '2', '3', '4', '8', '6', '3', '2', '6', '0', '3', '6', '8', '9', '6', '4', '3', '8', '6', '3', '5', '8', '3', '2', '5', '2', '3', '2', '4', '2', '8', '4', '2', '1', '7', '/', '2', '2', '7', '9', '1', '7', '7', '8', '2', '8', '8', '0', '0', '2', '6', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1469962_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 488) (SourceJson.white (fragment1469962Field002Chars00 ++ tail)) fragment1469962Acc00200 =
      SourceJson.object (fuel + 487) (SourceJson.white tail) fragment1469962Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_002"
  err.flush

noncomputable def fragment1469962Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment1469962Field003Value00 : SourceJson := .str (String.ofList ['3', '3', '5', '7', '8', '0', '1', '0', '2', '3', '/', '2', '9', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment1469962Acc00400 : List (String × SourceJson) := (fragment1469962Field003Key00, fragment1469962Field003Value00) :: fragment1469962Acc00300
noncomputable def fragment1469962Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '3', '5', '7', '8', '0', '1', '0', '2', '3', '/', '2', '9', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment1469962_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 487) (SourceJson.white (fragment1469962Field003Chars00 ++ tail)) fragment1469962Acc00300 =
      SourceJson.object (fuel + 486) (SourceJson.white tail) fragment1469962Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_003"
  err.flush

noncomputable def fragment1469962Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment1469962Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '4', '0', '2', '6', '1', '/', '2', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '7', '1', '9', '0', '3', '/', '3', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0'])]
noncomputable def fragment1469962Acc00500 : List (String × SourceJson) := (fragment1469962Field004Key00, fragment1469962Field004Value00) :: fragment1469962Acc00400
noncomputable def fragment1469962Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '5', '7', '/', '2', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '0', '9', '3', '5', '9', '/', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '4', '0', '2', '6', '1', '/', '2', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '7', '1', '9', '0', '3', '/', '3', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '1', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '2', '4', '7', '/', '1', '5', '7', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1469962_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 486) (SourceJson.white (fragment1469962Field004Chars00 ++ tail)) fragment1469962Acc00400 =
      SourceJson.object (fuel + 485) (SourceJson.white tail) fragment1469962Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_004"
  err.flush

noncomputable def fragment1469962Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment1469962Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '0', '0', '5', '0', '4', '3', '6', '0', '5', '4', '7', '4', '3', '8', '5', '4', '1', '2', '0', '1', '7', '0', '5', '1', '/', '4', '2', '6', '9', '1', '2', '6', '7', '5', '5', '7', '0', '3', '8', '4', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '3', '8', '3', '5', '8', '0', '5', '7', '3', '3', '1', '4', '3', '5', '6', '6', '6', '2', '3', '7', '7', '1', '3', '/', '1', '8', '4', '9', '9', '5', '4', '9', '2', '7', '4', '7', '1', '6', '6', '7', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '5', '7', '4', '9', '7', '4', '9', '5', '5', '3', '4', '9', '9', '0', '4', '4', '3', '9', '7', '6', '1', '7', '/', '1', '4', '0', '2', '0', '7', '1', '1', '0', '2', '9', '2', '5', '8', '9', '5', '0', '0', '1', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '2', '6', '8', '1', '3', '6', '7', '3', '7', '0', '8', '9', '0', '6', '8', '9', '0', '0', '1', '1', '6', '2', '2', '8', '9', '/', '3', '3', '2', '9', '9', '1', '8', '8', '6', '9', '4', '4', '9', '0', '0', '0', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '5', '0', '7', '0', '2', '2', '3', '4', '0', '6', '2', '4', '9', '2', '8', '3', '2', '0', '7', '8', '7', '3', '1', '/', '1', '7', '5', '2', '5', '8', '8', '8', '7', '8', '6', '5', '7', '3', '6', '8', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '5', '5', '7', '5', '6', '4', '0', '3', '0', '3', '2', '5', '5', '5', '3', '9', '9', '7', '1', '1', '7', '7', '/', '1', '5', '9', '3', '2', '6', '2', '6', '1', '6', '9', '6', '1', '2', '4', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '0', '4', '9', '1', '4', '5', '7', '7', '3', '2', '0', '6', '5', '4', '2', '6', '4', '5', '2', '9', '7', '/', '1', '4', '9', '3', '6', '8', '3', '7', '0', '3', '4', '0', '1', '1', '6', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '5', '4', '9', '8', '3', '5', '4', '1', '1', '2', '4', '0', '8', '6', '6', '4', '4', '8', '3', '9', '0', '6', '1', '/', '1', '3', '1', '4', '4', '4', '1', '6', '5', '8', '9', '9', '3', '0', '2', '6', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '1', '3', '7', '7', '6', '8', '4', '2', '4', '0', '0', '3', '1', '6', '7', '3', '4', '7', '8', '0', '3', '2', '3', '/', '5', '5', '4', '9', '8', '6', '4', '7', '8', '2', '4', '1', '5', '0', '0', '1', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '3', '7', '5', '0', '5', '8', '7', '7', '7', '2', '2', '6', '6', '6', '5', '2', '5', '7', '2', '2', '2', '3', '3', '/', '5', '5', '4', '9', '8', '6', '4', '7', '8', '2', '4', '1', '5', '0', '0', '1', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment1469962Acc00600 : List (String × SourceJson) := (fragment1469962Field005Key00, fragment1469962Field005Value00) :: fragment1469962Acc00500
noncomputable def fragment1469962Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '5', '0', '4', '3', '6', '0', '5', '4', '7', '4', '3', '8', '5', '4', '1', '2', '0', '1', '7', '0', '5', '1', '/', '4', '2', '6', '9', '1', '2', '6', '7', '5', '5', '7', '0', '3', '8', '4', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '3', '8', '3', '5', '8', '0', '5', '7', '3', '3', '1', '4', '3', '5', '6', '6', '6', '2', '3', '7', '7', '1', '3', '/', '1', '8', '4', '9', '9', '5', '4', '9', '2', '7', '4', '7', '1', '6', '6', '7', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '5', '7', '4', '9', '7', '4', '9', '5', '5', '3', '4', '9', '9', '0', '4', '4', '3', '9', '7', '6', '1', '7', '/', '1', '4', '0', '2', '0', '7', '1', '1', '0', '2', '9', '2', '5', '8', '9', '5', '0', '0', '1', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '2', '6', '8', '1', '3', '6', '7', '3', '7', '0', '8', '9', '0', '6', '8', '9', '0', '0', '1', '1', '6', '2', '2', '8', '9', '/', '3', '3', '2', '9', '9', '1', '8', '8', '6', '9', '4', '4', '9', '0', '0', '0', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '5', '0', '7', '0', '2', '2', '3', '4', '0', '6', '2', '4', '9', '2', '8', '3', '2', '0', '7', '8', '7', '3', '1', '/', '1', '7', '5', '2', '5', '8', '8', '8', '7', '8', '6', '5', '7', '3', '6', '8', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '5', '5', '7', '5', '6', '4', '0', '3', '0', '3', '2', '5', '5', '5', '3', '9', '9', '7', '1', '1', '7', '7', '/', '1', '5', '9', '3', '2', '6', '2', '6', '1', '6', '9', '6', '1', '2', '4', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '0', '4', '9', '1', '4', '5', '7', '7', '3', '2', '0', '6', '5', '4', '2', '6', '4', '5', '2', '9', '7', '/', '1', '4', '9', '3', '6', '8', '3', '7', '0', '3', '4', '0', '1', '1', '6', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '5', '4', '9', '8', '3', '5', '4', '1', '1', '2', '4', '0', '8', '6', '6', '4', '4', '8', '3', '9', '0', '6', '1', '/', '1', '3', '1', '4', '4', '4', '1', '6', '5', '8', '9', '9', '3', '0', '2', '6', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '1', '3', '7', '7', '6', '8', '4', '2', '4', '0', '0', '3', '1', '6', '7', '3', '4', '7', '8', '0', '3', '2', '3', '/', '5', '5', '4', '9', '8', '6', '4', '7', '8', '2', '4', '1', '5', '0', '0', '1', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '3', '7', '5', '0', '5', '8', '7', '7', '7', '2', '2', '6', '6', '6', '5', '2', '5', '7', '2', '2', '2', '3', '3', '/', '5', '5', '4', '9', '8', '6', '4', '7', '8', '2', '4', '1', '5', '0', '0', '1', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment1469962_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 485) (SourceJson.white (fragment1469962Field005Chars00 ++ tail)) fragment1469962Acc00500 =
      SourceJson.object (fuel + 484) (SourceJson.white tail) fragment1469962Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_005"
  err.flush

noncomputable def fragment1469962Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1469962Field006Value00 : SourceJson := .str (String.ofList ['3', '9', '6', '6', '5', '6', '3', '1', '9', '0', '4', '2', '3', '6', '4', '2', '7', '1', '3', '9', '7', '0', '4', '6', '9', '5', '9', '9', '6', '6', '8', '0', '1', '6', '5', '7', '6', '4', '1', '1', '6', '3', '2', '2', '7', '4', '6', '7', '5', '2', '5', '5', '9', '1', '6', '0', '6', '2', '3', '/', '1', '0', '4', '9', '1', '8', '1', '1', '7', '2', '8', '1', '4', '1', '4', '1', '7', '7', '6', '1', '7', '1', '8', '4', '5', '7', '3', '4', '0', '9', '1', '3', '1', '1', '0', '3', '0', '1', '2', '4', '1', '1', '4', '1', '0', '0', '3', '7', '1', '2', '6', '3', '2', '3', '0', '6', '7', '6', '2', '0', '1', '7', '2', '1', '5', '3', '1', '0', '0', '8'])
noncomputable def fragment1469962Acc00700 : List (String × SourceJson) := (fragment1469962Field006Key00, fragment1469962Field006Value00) :: fragment1469962Acc00600
noncomputable def fragment1469962Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '9', '6', '6', '5', '6', '3', '1', '9', '0', '4', '2', '3', '6', '4', '2', '7', '1', '3', '9', '7', '0', '4', '6', '9', '5', '9', '9', '6', '6', '8', '0', '1', '6', '5', '7', '6', '4', '1', '1', '6', '3', '2', '2', '7', '4', '6', '7', '5', '2', '5', '5', '9', '1', '6', '0', '6', '2', '3', '/', '1', '0', '4', '9', '1', '8', '1', '1', '7', '2', '8', '1', '4', '1', '4', '1', '7', '7', '6', '1', '7', '1', '8', '4', '5', '7', '3', '4', '0', '9', '1', '3', '1', '1', '0', '3', '0', '1', '2', '4', '1', '1', '4', '1', '0', '0', '3', '7', '1', '2', '6', '3', '2', '3', '0', '6', '7', '6', '2', '0', '1', '7', '2', '1', '5', '3', '1', '0', '0', '8', '"', ',']

theorem object_fragment1469962_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 484) (SourceJson.white (fragment1469962Field006Chars00 ++ tail)) fragment1469962Acc00600 =
      SourceJson.object (fuel + 483) (SourceJson.white tail) fragment1469962Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_006"
  err.flush

noncomputable def fragment1469962Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment1469962Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '2', '4', '8', '9', '5', '8', '4', '3', '4', '6', '4', '9', '3', '5', '2', '2', '6', '8', '7', '9', '7', '8', '5', '7', '5', '1', '2', '3', '2', '7', '9', '7', '5', '6', '0', '1', '8', '1', '6', '9', '2', '8', '0', '6', '2', '7', '0', '2', '2', '7', '5', '4', '2', '9', '9', '4', '8', '7', '8', '2', '0', '5', '2', '9', '1', '8', '4', '9', '3', '3', '5', '4', '7', '1', '4', '1', '1', '0', '0', '2', '3', '3', '3', '6', '6', '7', '3', '2', '6', '3', '9', '6', '4', '7', '0', '8', '4', '5', '5', '0', '7', '2', '9', '8', '7', '6', '7', '5', '1', '1', '1', '6', '7', '9', '7', '9', '5', '7', '6', '4', '3', '4', '3', '9', '2', '1', '7', '9', '6', '9', '6', '8', '1', '0', '9', '3', '8', '3', '0', '6', '0', '5', '3', '8', '5', '6', '0', '7', '9', '1', '8', '7', '8', '1', '1', '5', '7', '8', '4', '1', '1', '2', '3', '0', '7', '9', '9', '3', '4', '1', '7', '7', '7', '3', '9', '6', '7', '7', '2', '2', '3', '8', '9', '5', '4', '5', '1', '6', '3', '9', '0', '3', '0', '9', '7', '6', '6', '4', '0', '3', '3', '3', '9', '8', '4', '3', '0', '7', '6', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '9', '7', '5', '4', '1', '5', '0', '0', '1', '1', '3', '7', '6', '2', '6', '8', '9', '7', '7', '7', '3', '8', '5', '4', '6', '3', '7', '1', '0', '2', '2', '5', '1', '7', '6', '8', '2', '8', '2', '9', '4', '4', '7', '2', '1', '0', '6', '3', '8', '2', '1', '4', '9', '0', '0', '1', '5', '9', '1', '0', '7', '6', '2', '1', '8', '9', '2', '9', '5', '1', '3', '8', '7', '9', '6', '1', '9', '9', '2', '4', '1', '4', '5', '1', '8', '2', '7', '1', '1', '7', '3', '0', '2', '1', '7', '8', '2', '2', '4', '8', '6', '9', '0', '0', '7', '7', '4', '7', '3', '1', '4', '1', '5', '1', '5', '4', '6', '9', '6', '3', '3', '2', '8', '6', '3', '2', '6', '2', '1', '0', '2', '1', '3', '9', '3', '6', '8', '2', '0', '9', '0', '4', '6', '8', '9', '9', '1', '8', '2', '3', '0', '8', '4', '9', '1', '8', '3', '4', '5', '9', '4', '0', '4', '3', '0', '8', '3', '7', '7', '0', '8', '0', '2', '7', '6', '5', '3', '7', '3', '3', '4', '1', '6', '6', '2', '7', '2', '5', '9', '9', '4', '3', '1', '4', '8', '4', '9', '2', '2', '8', '0', '5', '5', '1', '3', '7', '1', '8', '4', '3', '7', '0', '6', '4', '4', '1', '2', '3', '6', '7', '2', '2', '6', '1', '2', '7', '8', '3', '8', '6', '6', '6', '2', '6', '3', '9', '6', '6', '9', '0', '7', '3'])
noncomputable def fragment1469962Acc00800 : List (String × SourceJson) := (fragment1469962Field007Key00, fragment1469962Field007Value00) :: fragment1469962Acc00700
noncomputable def fragment1469962Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '2', '4', '8', '9', '5', '8', '4', '3', '4', '6', '4', '9', '3', '5', '2', '2', '6', '8', '7', '9', '7', '8', '5', '7', '5', '1', '2', '3', '2', '7', '9', '7', '5', '6', '0', '1', '8', '1', '6', '9', '2', '8', '0', '6', '2', '7', '0', '2', '2', '7', '5', '4', '2', '9', '9', '4', '8', '7', '8', '2', '0', '5', '2', '9', '1', '8', '4', '9', '3', '3', '5', '4', '7', '1', '4', '1', '1', '0', '0', '2', '3', '3', '3', '6', '6', '7', '3', '2', '6', '3', '9', '6', '4', '7', '0', '8', '4', '5', '5', '0', '7', '2', '9', '8', '7', '6', '7', '5', '1', '1', '1', '6', '7', '9', '7', '9', '5', '7', '6', '4', '3', '4', '3', '9', '2', '1', '7', '9', '6', '9', '6', '8', '1', '0', '9', '3', '8', '3', '0', '6', '0', '5', '3', '8', '5', '6', '0', '7', '9', '1', '8', '7', '8', '1', '1', '5', '7', '8', '4', '1', '1', '2', '3', '0', '7', '9', '9', '3', '4', '1', '7', '7', '7', '3', '9', '6', '7', '7', '2', '2', '3', '8', '9', '5', '4', '5', '1', '6', '3', '9', '0', '3', '0', '9', '7', '6', '6', '4', '0', '3', '3', '3', '9', '8', '4', '3', '0', '7', '6', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '9', '7', '5', '4', '1', '5', '0', '0', '1', '1', '3', '7', '6', '2', '6', '8', '9', '7', '7', '7', '3', '8', '5', '4', '6', '3', '7', '1', '0', '2', '2', '5', '1', '7', '6', '8', '2', '8', '2', '9', '4', '4', '7', '2', '1', '0', '6', '3', '8', '2', '1', '4', '9', '0', '0', '1', '5', '9', '1', '0', '7', '6', '2', '1', '8', '9', '2', '9', '5', '1', '3', '8', '7', '9', '6', '1', '9', '9', '2', '4', '1', '4', '5', '1', '8', '2', '7', '1', '1', '7', '3', '0', '2', '1', '7', '8', '2', '2', '4', '8', '6', '9', '0', '0', '7', '7', '4', '7', '3', '1', '4', '1', '5', '1', '5', '4', '6', '9', '6', '3', '3', '2', '8', '6', '3', '2', '6', '2', '1', '0', '2', '1', '3', '9', '3', '6', '8', '2', '0', '9', '0', '4', '6', '8', '9', '9', '1', '8', '2', '3', '0', '8', '4', '9', '1', '8', '3', '4', '5', '9', '4', '0', '4', '3', '0', '8', '3', '7', '7', '0', '8', '0', '2', '7', '6', '5', '3', '7', '3', '3', '4', '1', '6', '6', '2', '7', '2', '5', '9', '9', '4', '3', '1', '4', '8', '4', '9', '2', '2', '8', '0', '5', '5', '1', '3', '7', '1', '8', '4', '3', '7', '0', '6', '4', '4', '1', '2', '3', '6', '7', '2', '2', '6', '1', '2', '7', '8', '3', '8', '6', '6', '6', '2', '6', '3', '9', '6', '6', '9', '0', '7', '3', '"', ',']

theorem object_fragment1469962_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 483) (SourceJson.white (fragment1469962Field007Chars00 ++ tail)) fragment1469962Acc00700 =
      SourceJson.object (fuel + 482) (SourceJson.white tail) fragment1469962Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_007"
  err.flush

noncomputable def fragment1469962Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1469962Field008Value00 : SourceJson := .str (String.ofList ['2', '9', '9', '5', '3', '2', '1', '6', '9', '6', '7', '3', '8', '5', '8', '3', '4', '1', '5'])
noncomputable def fragment1469962Acc00900 : List (String × SourceJson) := (fragment1469962Field008Key00, fragment1469962Field008Value00) :: fragment1469962Acc00800
noncomputable def fragment1469962Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '9', '5', '3', '2', '1', '6', '9', '6', '7', '3', '8', '5', '8', '3', '4', '1', '5', '"', ',']

theorem object_fragment1469962_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 482) (SourceJson.white (fragment1469962Field008Chars00 ++ tail)) fragment1469962Acc00800 =
      SourceJson.object (fuel + 481) (SourceJson.white tail) fragment1469962Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_008"
  err.flush

noncomputable def fragment1469962Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment1469962Field009Value00 : SourceJson := .str (String.ofList ['3', '6', '8', '0', '8', '0', '0', '1', '2', '6', '3', '3', '4', '6', '0', '2', '0', '8', '6', '7'])
noncomputable def fragment1469962Acc01000 : List (String × SourceJson) := (fragment1469962Field009Key00, fragment1469962Field009Value00) :: fragment1469962Acc00900
noncomputable def fragment1469962Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '6', '8', '0', '8', '0', '0', '1', '2', '6', '3', '3', '4', '6', '0', '2', '0', '8', '6', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment1469962_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 481) (SourceJson.white (fragment1469962Field009Chars00 ++ tail)) fragment1469962Acc00900 =
      .ok (.obj (fragment1469962Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment1469962_object_field_009"
  err.flush

noncomputable def fragment1469962Chars : List Char := '{' :: (fragment1469962Field000Chars00 ++ fragment1469962Field001Chars00 ++ fragment1469962Field002Chars00 ++ fragment1469962Field003Chars00 ++ fragment1469962Field004Chars00 ++ fragment1469962Field005Chars00 ++ fragment1469962Field006Chars00 ++ fragment1469962Field007Chars00 ++ fragment1469962Field008Chars00 ++ fragment1469962Field009Chars00)
noncomputable def fragment1469962Value : SourceJson := .obj (fragment1469962Acc01000.reverse)

theorem value_fragment1469962 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 491) (fragment1469962Chars ++ tail) =
      .ok (fragment1469962Value, tail) := by
  have hinput : fragment1469962Chars ++ tail = '{' :: (fragment1469962Field000Chars00 ++ (fragment1469962Field001Chars00 ++ (fragment1469962Field002Chars00 ++ (fragment1469962Field003Chars00 ++ (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment1469962Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 491) (fragment1469962Chars ++ tail) =
        SourceJson.value (fuel + 491) ('{' :: (fragment1469962Field000Chars00 ++ (fragment1469962Field001Chars00 ++ (fragment1469962Field002Chars00 ++ (fragment1469962Field003Chars00 ++ (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 491)) hinput
    _ = SourceJson.object (fuel + 490) (SourceJson.white (fragment1469962Field000Chars00 ++ (fragment1469962Field001Chars00 ++ (fragment1469962Field002Chars00 ++ (fragment1469962Field003Chars00 ++ (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))))))))))) fragment1469962Acc00000 := by rfl
    _ = SourceJson.object (fuel + 489) (SourceJson.white (fragment1469962Field001Chars00 ++ (fragment1469962Field002Chars00 ++ (fragment1469962Field003Chars00 ++ (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail))))))))))) fragment1469962Acc00100 := object_fragment1469962_field_000 fuel (fragment1469962Field001Chars00 ++ (fragment1469962Field002Chars00 ++ (fragment1469962Field003Chars00 ++ (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 488) (SourceJson.white (fragment1469962Field002Chars00 ++ (fragment1469962Field003Chars00 ++ (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))))))))) fragment1469962Acc00200 := object_fragment1469962_field_001 fuel (fragment1469962Field002Chars00 ++ (fragment1469962Field003Chars00 ++ (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 487) (SourceJson.white (fragment1469962Field003Chars00 ++ (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail))))))))) fragment1469962Acc00300 := object_fragment1469962_field_002 fuel (fragment1469962Field003Chars00 ++ (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 486) (SourceJson.white (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))))))) fragment1469962Acc00400 := object_fragment1469962_field_003 fuel (fragment1469962Field004Chars00 ++ (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 485) (SourceJson.white (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail))))))) fragment1469962Acc00500 := object_fragment1469962_field_004 fuel (fragment1469962Field005Chars00 ++ (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 484) (SourceJson.white (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))))) fragment1469962Acc00600 := object_fragment1469962_field_005 fuel (fragment1469962Field006Chars00 ++ (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 483) (SourceJson.white (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail))))) fragment1469962Acc00700 := object_fragment1469962_field_006 fuel (fragment1469962Field007Chars00 ++ (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 482) (SourceJson.white (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))) fragment1469962Acc00800 := object_fragment1469962_field_007 fuel (fragment1469962Field008Chars00 ++ (fragment1469962Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 481) (SourceJson.white (fragment1469962Field009Chars00 ++ (tail))) fragment1469962Acc00900 := object_fragment1469962_field_008 fuel (fragment1469962Field009Chars00 ++ (tail))
    _ = .ok (fragment1469962Value, tail) := object_fragment1469962_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_before_reader"
  err.flush

noncomputable def chunk0000LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0000SuffixChars00 : List Char := [',']
noncomputable def chunk0000Chars00 : List Char := chunk0000LeadChars00 ++ fragment1454530Chars ++ chunk0000SuffixChars00
noncomputable def chunk0000Push00 (acc : List SourceJson) : List SourceJson := fragment1454530Value :: acc

noncomputable def chunk0000AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0000_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7192)
      (SourceJson.white (chunk0000LeadChars00 ++ (fragment1454530Chars ++ rest))) acc =
      (SourceJson.value (fuel + 7191) (fragment1454530Chars ++ rest)).bind
        (chunk0000AfterValue00 (fuel + 7191) acc) := by rfl

theorem array_chunk0000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7192) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 7191) (SourceJson.white tail) (chunk0000Push00 acc) := by
  have hinput : chunk0000Chars00 ++ tail = chunk0000LeadChars00 ++ (fragment1454530Chars ++ (chunk0000SuffixChars00 ++ tail)) := by
    simp only [chunk0000Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 7192) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 7192)
          (SourceJson.white (chunk0000LeadChars00 ++ (fragment1454530Chars ++ (chunk0000SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 7192) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 7191) (fragment1454530Chars ++ (chunk0000SuffixChars00 ++ tail))).bind
        (chunk0000AfterValue00 (fuel + 7191) acc) := array_chunk0000_head fuel (chunk0000SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment1454530Value, chunk0000SuffixChars00 ++ tail)).bind
        (chunk0000AfterValue00 (fuel + 7191) acc) :=
      congrArg (fun result => result.bind (chunk0000AfterValue00 (fuel + 7191) acc))
        (value_fragment1454530 (fuel + 6711) (chunk0000SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 7191) (SourceJson.white tail) (chunk0000Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_before_reader"
  err.flush

noncomputable def chunk0001LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0001SuffixChars00 : List Char := [',']
noncomputable def chunk0001Chars00 : List Char := chunk0001LeadChars00 ++ fragment1456658Chars ++ chunk0001SuffixChars00
noncomputable def chunk0001Push00 (acc : List SourceJson) : List SourceJson := fragment1456658Value :: acc

noncomputable def chunk0001AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0001_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7191)
      (SourceJson.white (chunk0001LeadChars00 ++ (fragment1456658Chars ++ rest))) acc =
      (SourceJson.value (fuel + 7190) (fragment1456658Chars ++ rest)).bind
        (chunk0001AfterValue00 (fuel + 7190) acc) := by rfl

theorem array_chunk0001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7191) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 7190) (SourceJson.white tail) (chunk0001Push00 acc) := by
  have hinput : chunk0001Chars00 ++ tail = chunk0001LeadChars00 ++ (fragment1456658Chars ++ (chunk0001SuffixChars00 ++ tail)) := by
    simp only [chunk0001Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 7191) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 7191)
          (SourceJson.white (chunk0001LeadChars00 ++ (fragment1456658Chars ++ (chunk0001SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 7191) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 7190) (fragment1456658Chars ++ (chunk0001SuffixChars00 ++ tail))).bind
        (chunk0001AfterValue00 (fuel + 7190) acc) := array_chunk0001_head fuel (chunk0001SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment1456658Value, chunk0001SuffixChars00 ++ tail)).bind
        (chunk0001AfterValue00 (fuel + 7190) acc) :=
      congrArg (fun result => result.bind (chunk0001AfterValue00 (fuel + 7190) acc))
        (value_fragment1456658 (fuel + 6713) (chunk0001SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 7190) (SourceJson.white tail) (chunk0001Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_before_reader"
  err.flush

noncomputable def chunk0002LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0002SuffixChars00 : List Char := [',']
noncomputable def chunk0002Chars00 : List Char := chunk0002LeadChars00 ++ fragment1458777Chars ++ chunk0002SuffixChars00
noncomputable def chunk0002Push00 (acc : List SourceJson) : List SourceJson := fragment1458777Value :: acc

noncomputable def chunk0002AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0002_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7190)
      (SourceJson.white (chunk0002LeadChars00 ++ (fragment1458777Chars ++ rest))) acc =
      (SourceJson.value (fuel + 7189) (fragment1458777Chars ++ rest)).bind
        (chunk0002AfterValue00 (fuel + 7189) acc) := by rfl

theorem array_chunk0002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7190) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 7189) (SourceJson.white tail) (chunk0002Push00 acc) := by
  have hinput : chunk0002Chars00 ++ tail = chunk0002LeadChars00 ++ (fragment1458777Chars ++ (chunk0002SuffixChars00 ++ tail)) := by
    simp only [chunk0002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 7190) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 7190)
          (SourceJson.white (chunk0002LeadChars00 ++ (fragment1458777Chars ++ (chunk0002SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 7190) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 7189) (fragment1458777Chars ++ (chunk0002SuffixChars00 ++ tail))).bind
        (chunk0002AfterValue00 (fuel + 7189) acc) := array_chunk0002_head fuel (chunk0002SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment1458777Value, chunk0002SuffixChars00 ++ tail)).bind
        (chunk0002AfterValue00 (fuel + 7189) acc) :=
      congrArg (fun result => result.bind (chunk0002AfterValue00 (fuel + 7189) acc))
        (value_fragment1458777 (fuel + 6644) (chunk0002SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 7189) (SourceJson.white tail) (chunk0002Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_before_reader"
  err.flush

noncomputable def chunk0003LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0003SuffixChars00 : List Char := [',']
noncomputable def chunk0003Chars00 : List Char := chunk0003LeadChars00 ++ fragment1461045Chars ++ chunk0003SuffixChars00
noncomputable def chunk0003Push00 (acc : List SourceJson) : List SourceJson := fragment1461045Value :: acc

noncomputable def chunk0003AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0003_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7189)
      (SourceJson.white (chunk0003LeadChars00 ++ (fragment1461045Chars ++ rest))) acc =
      (SourceJson.value (fuel + 7188) (fragment1461045Chars ++ rest)).bind
        (chunk0003AfterValue00 (fuel + 7188) acc) := by rfl

theorem array_chunk0003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7189) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 7188) (SourceJson.white tail) (chunk0003Push00 acc) := by
  have hinput : chunk0003Chars00 ++ tail = chunk0003LeadChars00 ++ (fragment1461045Chars ++ (chunk0003SuffixChars00 ++ tail)) := by
    simp only [chunk0003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 7189) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 7189)
          (SourceJson.white (chunk0003LeadChars00 ++ (fragment1461045Chars ++ (chunk0003SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 7189) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 7188) (fragment1461045Chars ++ (chunk0003SuffixChars00 ++ tail))).bind
        (chunk0003AfterValue00 (fuel + 7188) acc) := array_chunk0003_head fuel (chunk0003SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment1461045Value, chunk0003SuffixChars00 ++ tail)).bind
        (chunk0003AfterValue00 (fuel + 7188) acc) :=
      congrArg (fun result => result.bind (chunk0003AfterValue00 (fuel + 7188) acc))
        (value_fragment1461045 (fuel + 6633) (chunk0003SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 7188) (SourceJson.white tail) (chunk0003Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_before_reader"
  err.flush

noncomputable def chunk0004LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0004SuffixChars00 : List Char := [',']
noncomputable def chunk0004Chars00 : List Char := chunk0004LeadChars00 ++ fragment1463338Chars ++ chunk0004SuffixChars00
noncomputable def chunk0004Push00 (acc : List SourceJson) : List SourceJson := fragment1463338Value :: acc

noncomputable def chunk0004AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0004_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7188)
      (SourceJson.white (chunk0004LeadChars00 ++ (fragment1463338Chars ++ rest))) acc =
      (SourceJson.value (fuel + 7187) (fragment1463338Chars ++ rest)).bind
        (chunk0004AfterValue00 (fuel + 7187) acc) := by rfl

theorem array_chunk0004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7188) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 7187) (SourceJson.white tail) (chunk0004Push00 acc) := by
  have hinput : chunk0004Chars00 ++ tail = chunk0004LeadChars00 ++ (fragment1463338Chars ++ (chunk0004SuffixChars00 ++ tail)) := by
    simp only [chunk0004Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 7188) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 7188)
          (SourceJson.white (chunk0004LeadChars00 ++ (fragment1463338Chars ++ (chunk0004SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 7188) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 7187) (fragment1463338Chars ++ (chunk0004SuffixChars00 ++ tail))).bind
        (chunk0004AfterValue00 (fuel + 7187) acc) := array_chunk0004_head fuel (chunk0004SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment1463338Value, chunk0004SuffixChars00 ++ tail)).bind
        (chunk0004AfterValue00 (fuel + 7187) acc) :=
      congrArg (fun result => result.bind (chunk0004AfterValue00 (fuel + 7187) acc))
        (value_fragment1463338 (fuel + 6683) (chunk0004SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 7187) (SourceJson.white tail) (chunk0004Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_before_reader"
  err.flush

noncomputable def chunk0005LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0005SuffixChars00 : List Char := [',']
noncomputable def chunk0005Chars00 : List Char := chunk0005LeadChars00 ++ fragment1465514Chars ++ chunk0005SuffixChars00
noncomputable def chunk0005Push00 (acc : List SourceJson) : List SourceJson := fragment1465514Value :: acc

noncomputable def chunk0005AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0005_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7187)
      (SourceJson.white (chunk0005LeadChars00 ++ (fragment1465514Chars ++ rest))) acc =
      (SourceJson.value (fuel + 7186) (fragment1465514Chars ++ rest)).bind
        (chunk0005AfterValue00 (fuel + 7186) acc) := by rfl

theorem array_chunk0005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7187) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 7186) (SourceJson.white tail) (chunk0005Push00 acc) := by
  have hinput : chunk0005Chars00 ++ tail = chunk0005LeadChars00 ++ (fragment1465514Chars ++ (chunk0005SuffixChars00 ++ tail)) := by
    simp only [chunk0005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 7187) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 7187)
          (SourceJson.white (chunk0005LeadChars00 ++ (fragment1465514Chars ++ (chunk0005SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 7187) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 7186) (fragment1465514Chars ++ (chunk0005SuffixChars00 ++ tail))).bind
        (chunk0005AfterValue00 (fuel + 7186) acc) := array_chunk0005_head fuel (chunk0005SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment1465514Value, chunk0005SuffixChars00 ++ tail)).bind
        (chunk0005AfterValue00 (fuel + 7186) acc) :=
      congrArg (fun result => result.bind (chunk0005AfterValue00 (fuel + 7186) acc))
        (value_fragment1465514 (fuel + 6641) (chunk0005SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 7186) (SourceJson.white tail) (chunk0005Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_before_reader"
  err.flush

noncomputable def chunk0006LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0006SuffixChars00 : List Char := [',']
noncomputable def chunk0006Chars00 : List Char := chunk0006LeadChars00 ++ fragment1467781Chars ++ chunk0006SuffixChars00
noncomputable def chunk0006Push00 (acc : List SourceJson) : List SourceJson := fragment1467781Value :: acc

noncomputable def chunk0006AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0006_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7186)
      (SourceJson.white (chunk0006LeadChars00 ++ (fragment1467781Chars ++ rest))) acc =
      (SourceJson.value (fuel + 7185) (fragment1467781Chars ++ rest)).bind
        (chunk0006AfterValue00 (fuel + 7185) acc) := by rfl

theorem array_chunk0006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7186) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 7185) (SourceJson.white tail) (chunk0006Push00 acc) := by
  have hinput : chunk0006Chars00 ++ tail = chunk0006LeadChars00 ++ (fragment1467781Chars ++ (chunk0006SuffixChars00 ++ tail)) := by
    simp only [chunk0006Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 7186) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 7186)
          (SourceJson.white (chunk0006LeadChars00 ++ (fragment1467781Chars ++ (chunk0006SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 7186) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 7185) (fragment1467781Chars ++ (chunk0006SuffixChars00 ++ tail))).bind
        (chunk0006AfterValue00 (fuel + 7185) acc) := array_chunk0006_head fuel (chunk0006SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment1467781Value, chunk0006SuffixChars00 ++ tail)).bind
        (chunk0006AfterValue00 (fuel + 7185) acc) :=
      congrArg (fun result => result.bind (chunk0006AfterValue00 (fuel + 7185) acc))
        (value_fragment1467781 (fuel + 6676) (chunk0006SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 7185) (SourceJson.white tail) (chunk0006Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_before_reader"
  err.flush

noncomputable def chunk0007LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0007SuffixChars00 : List Char := [',']
noncomputable def chunk0007Chars00 : List Char := chunk0007LeadChars00 ++ fragment1469962Chars ++ chunk0007SuffixChars00
noncomputable def chunk0007Push00 (acc : List SourceJson) : List SourceJson := fragment1469962Value :: acc

noncomputable def chunk0007AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0007_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7185)
      (SourceJson.white (chunk0007LeadChars00 ++ (fragment1469962Chars ++ rest))) acc =
      (SourceJson.value (fuel + 7184) (fragment1469962Chars ++ rest)).bind
        (chunk0007AfterValue00 (fuel + 7184) acc) := by rfl

theorem array_chunk0007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7185) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 7184) (SourceJson.white tail) (chunk0007Push00 acc) := by
  have hinput : chunk0007Chars00 ++ tail = chunk0007LeadChars00 ++ (fragment1469962Chars ++ (chunk0007SuffixChars00 ++ tail)) := by
    simp only [chunk0007Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 7185) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 7185)
          (SourceJson.white (chunk0007LeadChars00 ++ (fragment1469962Chars ++ (chunk0007SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 7185) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 7184) (fragment1469962Chars ++ (chunk0007SuffixChars00 ++ tail))).bind
        (chunk0007AfterValue00 (fuel + 7184) acc) := array_chunk0007_head fuel (chunk0007SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment1469962Value, chunk0007SuffixChars00 ++ tail)).bind
        (chunk0007AfterValue00 (fuel + 7184) acc) :=
      congrArg (fun result => result.bind (chunk0007AfterValue00 (fuel + 7184) acc))
        (value_fragment1469962 (fuel + 6693) (chunk0007SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 7184) (SourceJson.white tail) (chunk0007Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0000Chars00 ++ chunk0001Chars00 ++ chunk0002Chars00 ++ chunk0003Chars00 ++ chunk0004Chars00 ++ chunk0005Chars00 ++ chunk0006Chars00 ++ chunk0007Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0007Push00 (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 7192) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 7184) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 7192) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 7192) (SourceJson.white (chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 7192) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 7191) (SourceJson.white (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))))) (chunk0000Push00 (acc)) := array_chunk0000 fuel (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 7190) (SourceJson.white (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (chunk0001Push00 (chunk0000Push00 (acc))) := array_chunk0001 fuel (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0000Push00 (acc))
    _ = SourceJson.array (fuel + 7189) (SourceJson.white (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))) := array_chunk0002 fuel (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0001Push00 (chunk0000Push00 (acc)))
    _ = SourceJson.array (fuel + 7188) (SourceJson.white (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))) := array_chunk0003 fuel (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))
    _ = SourceJson.array (fuel + 7187) (SourceJson.white (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))) := array_chunk0004 fuel (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))
    _ = SourceJson.array (fuel + 7186) (SourceJson.white (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))) := array_chunk0005 fuel (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))
    _ = SourceJson.array (fuel + 7185) (SourceJson.white (chunk0007Chars00 ++ (tail))) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))) := array_chunk0006 fuel (chunk0007Chars00 ++ (tail)) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))
    _ = SourceJson.array (fuel + 7184) (SourceJson.white tail) (blockPush acc) := array_chunk0007 fuel (tail) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 1454524).take 17586 = blockChars := by rfl

theorem block_original_split : sourceRest 1454524 = blockChars ++ sourceRest 1472110 := by
  calc
    sourceRest 1454524 = (sourceRest 1454524).take 17586 ++ (sourceRest 1454524).drop 17586 :=
      (List.take_append_drop 17586 (sourceRest 1454524)).symm
    _ = blockChars ++ (sourceRest 1454524).drop 17586 :=
      congrArg (fun part => part ++ (sourceRest 1454524).drop 17586) block_original_prefix
    _ = blockChars ++ sourceRest 1472110 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 1454524 17586)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 7192) (SourceJson.white (sourceRest 1454524)) acc =
      SourceJson.array (fuel + 7184) (SourceJson.white (sourceRest 1472110)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 7192) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 1472110) acc)

#print axioms object_fragment1454530_field_000
#print axioms object_fragment1454530_field_001
#print axioms object_fragment1454530_field_002
#print axioms object_fragment1454530_field_003
#print axioms object_fragment1454530_field_004
#print axioms object_fragment1454530_field_005
#print axioms object_fragment1454530_field_006
#print axioms object_fragment1454530_field_007
#print axioms object_fragment1454530_field_008
#print axioms object_fragment1454530_field_009
#print axioms value_fragment1454530
#print axioms object_fragment1456658_field_000
#print axioms object_fragment1456658_field_001
#print axioms object_fragment1456658_field_002
#print axioms object_fragment1456658_field_003
#print axioms object_fragment1456658_field_004
#print axioms object_fragment1456658_field_005
#print axioms object_fragment1456658_field_006
#print axioms object_fragment1456658_field_007
#print axioms object_fragment1456658_field_008
#print axioms object_fragment1456658_field_009
#print axioms value_fragment1456658
#print axioms object_fragment1458777_field_000
#print axioms object_fragment1458777_field_001
#print axioms object_fragment1458777_field_002
#print axioms object_fragment1458777_field_003
#print axioms object_fragment1458777_field_004
#print axioms object_fragment1458777_field_005
#print axioms object_fragment1458777_field_006
#print axioms object_fragment1458777_field_007
#print axioms object_fragment1458777_field_008
#print axioms object_fragment1458777_field_009
#print axioms value_fragment1458777
#print axioms object_fragment1461045_field_000
#print axioms object_fragment1461045_field_001
#print axioms object_fragment1461045_field_002
#print axioms object_fragment1461045_field_003
#print axioms object_fragment1461045_field_004
#print axioms object_fragment1461045_field_005
#print axioms object_fragment1461045_field_006
#print axioms object_fragment1461045_field_007
#print axioms object_fragment1461045_field_008
#print axioms object_fragment1461045_field_009
#print axioms value_fragment1461045
#print axioms object_fragment1463338_field_000
#print axioms object_fragment1463338_field_001
#print axioms object_fragment1463338_field_002
#print axioms object_fragment1463338_field_003
#print axioms object_fragment1463338_field_004
#print axioms object_fragment1463338_field_005
#print axioms object_fragment1463338_field_006
#print axioms object_fragment1463338_field_007
#print axioms object_fragment1463338_field_008
#print axioms object_fragment1463338_field_009
#print axioms value_fragment1463338
#print axioms object_fragment1465514_field_000
#print axioms object_fragment1465514_field_001
#print axioms object_fragment1465514_field_002
#print axioms object_fragment1465514_field_003
#print axioms object_fragment1465514_field_004
#print axioms object_fragment1465514_field_005
#print axioms object_fragment1465514_field_006
#print axioms object_fragment1465514_field_007
#print axioms object_fragment1465514_field_008
#print axioms object_fragment1465514_field_009
#print axioms value_fragment1465514
#print axioms object_fragment1467781_field_000
#print axioms object_fragment1467781_field_001
#print axioms object_fragment1467781_field_002
#print axioms object_fragment1467781_field_003
#print axioms object_fragment1467781_field_004
#print axioms object_fragment1467781_field_005
#print axioms object_fragment1467781_field_006
#print axioms object_fragment1467781_field_007
#print axioms object_fragment1467781_field_008
#print axioms object_fragment1467781_field_009
#print axioms value_fragment1467781
#print axioms object_fragment1469962_field_000
#print axioms object_fragment1469962_field_001
#print axioms object_fragment1469962_field_002
#print axioms object_fragment1469962_field_003
#print axioms object_fragment1469962_field_004
#print axioms object_fragment1469962_field_005
#print axioms object_fragment1469962_field_006
#print axioms object_fragment1469962_field_007
#print axioms object_fragment1469962_field_008
#print axioms object_fragment1469962_field_009
#print axioms value_fragment1469962
#print axioms array_chunk0000_head
#print axioms array_chunk0000
#print axioms array_chunk0001_head
#print axioms array_chunk0001
#print axioms array_chunk0002_head
#print axioms array_chunk0002
#print axioms array_chunk0003_head
#print axioms array_chunk0003
#print axioms array_chunk0004_head
#print axioms array_chunk0004
#print axioms array_chunk0005_head
#print axioms array_chunk0005
#print axioms array_chunk0006_head
#print axioms array_chunk0006
#print axioms array_chunk0007_head
#print axioms array_chunk0007
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock000

end ImbalancedChen.P2OriginalSaving19Geometry12ScalableParsing
