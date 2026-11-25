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

namespace SimplicesBlock013

noncomputable def fragment0269713Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0269713Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0269713Field000Value00 : SourceJson := .number (String.ofList ['2', '6'])
noncomputable def fragment0269713Acc00100 : List (String × SourceJson) := (fragment0269713Field000Key00, fragment0269713Field000Value00) :: fragment0269713Acc00000
noncomputable def fragment0269713Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '6', ',']

theorem object_fragment0269713_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 345) (SourceJson.white (fragment0269713Field000Chars00 ++ tail)) fragment0269713Acc00000 =
      SourceJson.object (fuel + 344) (SourceJson.white tail) fragment0269713Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_000"
  err.flush

noncomputable def fragment0269713Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0269713Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '2']), .number (String.ofList ['4']), .number (String.ofList ['2'])]
noncomputable def fragment0269713Acc00200 : List (String × SourceJson) := (fragment0269713Field001Key00, fragment0269713Field001Value00) :: fragment0269713Acc00100
noncomputable def fragment0269713Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0269713_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 344) (SourceJson.white (fragment0269713Field001Chars00 ++ tail)) fragment0269713Acc00100 =
      SourceJson.object (fuel + 343) (SourceJson.white tail) fragment0269713Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_001"
  err.flush

noncomputable def fragment0269713Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0269713Field002Value00 : SourceJson := .str (String.ofList ['7', '4', '8', '0', '5', '2', '6', '9', '5', '3', '8', '1', '6', '9', '4', '6', '9', '3', '1', '8', '5', '8', '8', '7', '4', '6', '7', '0', '6', '0', '9', '2', '9', '0', '8', '8', '9', '2', '8', '1', '/', '1', '5', '6', '6', '3', '6', '9', '2', '8', '8', '0', '2', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0269713Acc00300 : List (String × SourceJson) := (fragment0269713Field002Key00, fragment0269713Field002Value00) :: fragment0269713Acc00200
noncomputable def fragment0269713Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '4', '8', '0', '5', '2', '6', '9', '5', '3', '8', '1', '6', '9', '4', '6', '9', '3', '1', '8', '5', '8', '8', '7', '4', '6', '7', '0', '6', '0', '9', '2', '9', '0', '8', '8', '9', '2', '8', '1', '/', '1', '5', '6', '6', '3', '6', '9', '2', '8', '8', '0', '2', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0269713_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 343) (SourceJson.white (fragment0269713Field002Chars00 ++ tail)) fragment0269713Acc00200 =
      SourceJson.object (fuel + 342) (SourceJson.white tail) fragment0269713Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_002"
  err.flush

noncomputable def fragment0269713Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0269713Field003Value00 : SourceJson := .str (String.ofList ['5', '9', '1', '6', '2', '9', '/', '5', '1', '7', '4', '4', '0', '0', '0', '0'])
noncomputable def fragment0269713Acc00400 : List (String × SourceJson) := (fragment0269713Field003Key00, fragment0269713Field003Value00) :: fragment0269713Acc00300
noncomputable def fragment0269713Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '9', '1', '6', '2', '9', '/', '5', '1', '7', '4', '4', '0', '0', '0', '0', '"', ',']

theorem object_fragment0269713_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 342) (SourceJson.white (fragment0269713Field003Chars00 ++ tail)) fragment0269713Acc00300 =
      SourceJson.object (fuel + 341) (SourceJson.white tail) fragment0269713Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_003"
  err.flush

noncomputable def fragment0269713Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0269713Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '2', '1', '8', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '2', '7', '8', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0269713Acc00500 : List (String × SourceJson) := (fragment0269713Field004Key00, fragment0269713Field004Value00) :: fragment0269713Acc00400
noncomputable def fragment0269713Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '8', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '2', '7', '8', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0269713_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 341) (SourceJson.white (fragment0269713Field004Chars00 ++ tail)) fragment0269713Acc00400 =
      SourceJson.object (fuel + 340) (SourceJson.white tail) fragment0269713Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_004"
  err.flush

noncomputable def fragment0269713Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0269713Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '0', '8', '9', '7', '7', '3', '8', '1', '9', '5', '8', '7', '7', '0', '5', '6', '1', '/', '3', '8', '0', '7', '8', '0', '5', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '9', '3', '2', '7', '7', '1', '7', '2', '8', '2', '3', '5', '4', '8', '9', '/', '1', '7', '7', '6', '9', '7', '6', '0', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '8', '1', '8', '6', '6', '9', '8', '5', '6', '3', '2', '0', '5', '7', '4', '9', '/', '4', '4', '4', '2', '4', '4', '0', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '5', '5', '6', '3', '8', '2', '5', '5', '3', '5', '2', '6', '2', '3', '0', '1', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '5', '0', '8', '3', '8', '9', '2', '5', '6', '3', '5', '6', '3', '0', '1', '/', '1', '7', '7', '6', '9', '7', '6', '0', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '1', '6', '9', '8', '9', '3', '7', '5', '8', '6', '5', '3', '6', '5', '8', '9', '/', '2', '6', '6', '5', '4', '6', '4', '0', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '3', '9', '2', '3', '2', '0', '4', '7', '4', '6', '8', '6', '7', '5', '5', '1', '/', '1', '3', '3', '2', '7', '3', '2', '0', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '7', '2', '4', '0', '1', '1', '7', '1', '0', '8', '9', '5', '2', '6', '7', '7', '/', '2', '6', '6', '5', '4', '6', '4', '0', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '2', '4', '1', '2', '7', '8', '0', '0', '4', '4', '2', '9', '6', '7', '5', '9', '/', '8', '8', '8', '4', '8', '8', '0', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '7', '3', '0', '8', '3', '5', '4', '8', '1', '8', '1', '4', '3', '6', '1', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0269713Acc00600 : List (String × SourceJson) := (fragment0269713Field005Key00, fragment0269713Field005Value00) :: fragment0269713Acc00500
noncomputable def fragment0269713Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '8', '9', '7', '7', '3', '8', '1', '9', '5', '8', '7', '7', '0', '5', '6', '1', '/', '3', '8', '0', '7', '8', '0', '5', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '9', '3', '2', '7', '7', '1', '7', '2', '8', '2', '3', '5', '4', '8', '9', '/', '1', '7', '7', '6', '9', '7', '6', '0', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '8', '1', '8', '6', '6', '9', '8', '5', '6', '3', '2', '0', '5', '7', '4', '9', '/', '4', '4', '4', '2', '4', '4', '0', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '5', '5', '6', '3', '8', '2', '5', '5', '3', '5', '2', '6', '2', '3', '0', '1', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '6', '5', '0', '8', '3', '8', '9', '2', '5', '6', '3', '5', '6', '3', '0', '1', '/', '1', '7', '7', '6', '9', '7', '6', '0', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '6', '9', '8', '9', '3', '7', '5', '8', '6', '5', '3', '6', '5', '8', '9', '/', '2', '6', '6', '5', '4', '6', '4', '0', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '3', '9', '2', '3', '2', '0', '4', '7', '4', '6', '8', '6', '7', '5', '5', '1', '/', '1', '3', '3', '2', '7', '3', '2', '0', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '7', '2', '4', '0', '1', '1', '7', '1', '0', '8', '9', '5', '2', '6', '7', '7', '/', '2', '6', '6', '5', '4', '6', '4', '0', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '2', '4', '1', '2', '7', '8', '0', '0', '4', '4', '2', '9', '6', '7', '5', '9', '/', '8', '8', '8', '4', '8', '8', '0', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '7', '3', '0', '8', '3', '5', '4', '8', '1', '8', '1', '4', '3', '6', '1', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0269713_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 340) (SourceJson.white (fragment0269713Field005Chars00 ++ tail)) fragment0269713Acc00500 =
      SourceJson.object (fuel + 339) (SourceJson.white tail) fragment0269713Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_005"
  err.flush

noncomputable def fragment0269713Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0269713Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '2', '3', '7', '1', '4', '7', '0', '9', '3', '5', '8', '1', '2', '4', '5', '8', '3', '4', '6', '1', '5', '7', '8', '1', '1', '4', '8', '0', '4', '6', '5', '6', '9', '1', '1', '9', '0', '4', '8', '5', '2', '9', '1', '8', '7', '5', '0', '0', '/', '1', '2', '2', '7', '2', '5', '2', '4', '2', '1', '2', '7', '8', '7', '8', '2', '2', '5', '2', '2', '5', '6', '9', '4', '3', '8', '9', '9', '3', '6', '6', '9', '2', '8', '3', '8', '1', '7', '5', '2', '4', '6', '3', '4', '9', '4', '5', '9', '0', '1', '4', '4', '3', '6', '9', '2', '3', '9', '5', '9', '1', '9', '9', '4', '3', '3'])
noncomputable def fragment0269713Acc00700 : List (String × SourceJson) := (fragment0269713Field006Key00, fragment0269713Field006Value00) :: fragment0269713Acc00600
noncomputable def fragment0269713Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '8', '2', '3', '7', '1', '4', '7', '0', '9', '3', '5', '8', '1', '2', '4', '5', '8', '3', '4', '6', '1', '5', '7', '8', '1', '1', '4', '8', '0', '4', '6', '5', '6', '9', '1', '1', '9', '0', '4', '8', '5', '2', '9', '1', '8', '7', '5', '0', '0', '/', '1', '2', '2', '7', '2', '5', '2', '4', '2', '1', '2', '7', '8', '7', '8', '2', '2', '5', '2', '2', '5', '6', '9', '4', '3', '8', '9', '9', '3', '6', '6', '9', '2', '8', '3', '8', '1', '7', '5', '2', '4', '6', '3', '4', '9', '4', '5', '9', '0', '1', '4', '4', '3', '6', '9', '2', '3', '9', '5', '9', '1', '9', '9', '4', '3', '3', '"', ',']

theorem object_fragment0269713_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 339) (SourceJson.white (fragment0269713Field006Chars00 ++ tail)) fragment0269713Acc00600 =
      SourceJson.object (fuel + 338) (SourceJson.white tail) fragment0269713Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_006"
  err.flush

noncomputable def fragment0269713Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0269713Field007Value00 : SourceJson := .str (String.ofList ['3', '0', '9', '9', '2', '0', '4', '7', '4', '2', '8', '1', '5', '2', '5', '8', '5', '3', '5', '4', '3', '4', '2', '3', '3', '7', '5', '6', '3', '8', '7', '7', '4', '3', '6', '3', '9', '0', '6', '3', '7', '6', '2', '7', '9', '5', '1', '9', '9', '7', '3', '7', '5', '1', '8', '2', '0', '7', '1', '4', '4', '3', '3', '4', '2', '0', '8', '3', '1', '1', '1', '6', '7', '9', '4', '5', '6', '1', '0', '4', '6', '7', '5', '7', '3', '4', '0', '3', '1', '3', '9', '9', '8', '3', '1', '7', '9', '6', '4', '2', '9', '5', '8', '6', '9', '5', '5', '9', '6', '9', '7', '7', '5', '6', '4', '8', '1', '3', '9', '5', '4', '3', '3', '5', '2', '0', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '4', '3', '4', '3', '3', '7', '1', '7', '1', '6', '8', '6', '6', '3', '6', '0', '3', '6', '5', '4', '8', '0', '3', '0', '2', '1', '2', '5', '8', '9', '6', '2', '6', '1', '5', '4', '4', '1', '9', '4', '0', '6', '2', '1', '3', '5', '2', '7', '3', '9', '7', '8', '0', '5', '0', '9', '2', '8', '0', '1', '5', '2', '3', '5', '7', '4', '7', '4', '3', '6', '0', '2', '2', '6', '5', '9', '4', '3', '1', '6', '4', '5', '8', '1', '7', '3', '6', '0', '6', '4', '2', '0', '0', '4', '7', '2', '6', '5', '0', '7', '5', '5', '1', '0', '7', '0', '5', '6', '4', '6', '6', '6', '5', '9', '1', '8', '8', '5', '8', '5', '7', '6', '4', '4', '7', '2', '7', '5', '3', '5', '8', '4', '8', '7', '7', '8', '0', '4', '9', '4', '2', '0', '4', '4', '5', '7', '1', '0', '0', '8', '6', '0', '5', '4', '9', '7', '5', '8', '6', '8', '9', '7', '9', '1', '1', '0', '4', '2', '0', '1', '8', '9', '3'])
noncomputable def fragment0269713Acc00800 : List (String × SourceJson) := (fragment0269713Field007Key00, fragment0269713Field007Value00) :: fragment0269713Acc00700
noncomputable def fragment0269713Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '9', '9', '2', '0', '4', '7', '4', '2', '8', '1', '5', '2', '5', '8', '5', '3', '5', '4', '3', '4', '2', '3', '3', '7', '5', '6', '3', '8', '7', '7', '4', '3', '6', '3', '9', '0', '6', '3', '7', '6', '2', '7', '9', '5', '1', '9', '9', '7', '3', '7', '5', '1', '8', '2', '0', '7', '1', '4', '4', '3', '3', '4', '2', '0', '8', '3', '1', '1', '1', '6', '7', '9', '4', '5', '6', '1', '0', '4', '6', '7', '5', '7', '3', '4', '0', '3', '1', '3', '9', '9', '8', '3', '1', '7', '9', '6', '4', '2', '9', '5', '8', '6', '9', '5', '5', '9', '6', '9', '7', '7', '5', '6', '4', '8', '1', '3', '9', '5', '4', '3', '3', '5', '2', '0', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '4', '3', '4', '3', '3', '7', '1', '7', '1', '6', '8', '6', '6', '3', '6', '0', '3', '6', '5', '4', '8', '0', '3', '0', '2', '1', '2', '5', '8', '9', '6', '2', '6', '1', '5', '4', '4', '1', '9', '4', '0', '6', '2', '1', '3', '5', '2', '7', '3', '9', '7', '8', '0', '5', '0', '9', '2', '8', '0', '1', '5', '2', '3', '5', '7', '4', '7', '4', '3', '6', '0', '2', '2', '6', '5', '9', '4', '3', '1', '6', '4', '5', '8', '1', '7', '3', '6', '0', '6', '4', '2', '0', '0', '4', '7', '2', '6', '5', '0', '7', '5', '5', '1', '0', '7', '0', '5', '6', '4', '6', '6', '6', '5', '9', '1', '8', '8', '5', '8', '5', '7', '6', '4', '4', '7', '2', '7', '5', '3', '5', '8', '4', '8', '7', '7', '8', '0', '4', '9', '4', '2', '0', '4', '4', '5', '7', '1', '0', '0', '8', '6', '0', '5', '4', '9', '7', '5', '8', '6', '8', '9', '7', '9', '1', '1', '0', '4', '2', '0', '1', '8', '9', '3', '"', ',']

theorem object_fragment0269713_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 338) (SourceJson.white (fragment0269713Field007Chars00 ++ tail)) fragment0269713Acc00700 =
      SourceJson.object (fuel + 337) (SourceJson.white tail) fragment0269713Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_007"
  err.flush

noncomputable def fragment0269713Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0269713Field008Value00 : SourceJson := .str (String.ofList ['6', '9', '8', '7', '5', '0', '3', '2', '4', '8', '1', '7', '0', '4'])
noncomputable def fragment0269713Acc00900 : List (String × SourceJson) := (fragment0269713Field008Key00, fragment0269713Field008Value00) :: fragment0269713Acc00800
noncomputable def fragment0269713Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '9', '8', '7', '5', '0', '3', '2', '4', '8', '1', '7', '0', '4', '"', ',']

theorem object_fragment0269713_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 337) (SourceJson.white (fragment0269713Field008Chars00 ++ tail)) fragment0269713Acc00800 =
      SourceJson.object (fuel + 336) (SourceJson.white tail) fragment0269713Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_008"
  err.flush

noncomputable def fragment0269713Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0269713Field009Value00 : SourceJson := .str (String.ofList ['3', '8', '1', '6', '1', '5', '5', '2', '6', '9', '4', '0', '7', '2', '0'])
noncomputable def fragment0269713Acc01000 : List (String × SourceJson) := (fragment0269713Field009Key00, fragment0269713Field009Value00) :: fragment0269713Acc00900
noncomputable def fragment0269713Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '8', '1', '6', '1', '5', '5', '2', '6', '9', '4', '0', '7', '2', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0269713_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 336) (SourceJson.white (fragment0269713Field009Chars00 ++ tail)) fragment0269713Acc00900 =
      .ok (.obj (fragment0269713Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0269713_object_field_009"
  err.flush

noncomputable def fragment0269713Chars : List Char := '{' :: (fragment0269713Field000Chars00 ++ fragment0269713Field001Chars00 ++ fragment0269713Field002Chars00 ++ fragment0269713Field003Chars00 ++ fragment0269713Field004Chars00 ++ fragment0269713Field005Chars00 ++ fragment0269713Field006Chars00 ++ fragment0269713Field007Chars00 ++ fragment0269713Field008Chars00 ++ fragment0269713Field009Chars00)
noncomputable def fragment0269713Value : SourceJson := .obj (fragment0269713Acc01000.reverse)

theorem value_fragment0269713 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 346) (fragment0269713Chars ++ tail) =
      .ok (fragment0269713Value, tail) := by
  have hinput : fragment0269713Chars ++ tail = '{' :: (fragment0269713Field000Chars00 ++ (fragment0269713Field001Chars00 ++ (fragment0269713Field002Chars00 ++ (fragment0269713Field003Chars00 ++ (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0269713Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 346) (fragment0269713Chars ++ tail) =
        SourceJson.value (fuel + 346) ('{' :: (fragment0269713Field000Chars00 ++ (fragment0269713Field001Chars00 ++ (fragment0269713Field002Chars00 ++ (fragment0269713Field003Chars00 ++ (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 346)) hinput
    _ = SourceJson.object (fuel + 345) (SourceJson.white (fragment0269713Field000Chars00 ++ (fragment0269713Field001Chars00 ++ (fragment0269713Field002Chars00 ++ (fragment0269713Field003Chars00 ++ (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))))))))))) fragment0269713Acc00000 := by rfl
    _ = SourceJson.object (fuel + 344) (SourceJson.white (fragment0269713Field001Chars00 ++ (fragment0269713Field002Chars00 ++ (fragment0269713Field003Chars00 ++ (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail))))))))))) fragment0269713Acc00100 := object_fragment0269713_field_000 fuel (fragment0269713Field001Chars00 ++ (fragment0269713Field002Chars00 ++ (fragment0269713Field003Chars00 ++ (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 343) (SourceJson.white (fragment0269713Field002Chars00 ++ (fragment0269713Field003Chars00 ++ (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))))))))) fragment0269713Acc00200 := object_fragment0269713_field_001 fuel (fragment0269713Field002Chars00 ++ (fragment0269713Field003Chars00 ++ (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 342) (SourceJson.white (fragment0269713Field003Chars00 ++ (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail))))))))) fragment0269713Acc00300 := object_fragment0269713_field_002 fuel (fragment0269713Field003Chars00 ++ (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 341) (SourceJson.white (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))))))) fragment0269713Acc00400 := object_fragment0269713_field_003 fuel (fragment0269713Field004Chars00 ++ (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 340) (SourceJson.white (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail))))))) fragment0269713Acc00500 := object_fragment0269713_field_004 fuel (fragment0269713Field005Chars00 ++ (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 339) (SourceJson.white (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))))) fragment0269713Acc00600 := object_fragment0269713_field_005 fuel (fragment0269713Field006Chars00 ++ (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 338) (SourceJson.white (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail))))) fragment0269713Acc00700 := object_fragment0269713_field_006 fuel (fragment0269713Field007Chars00 ++ (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 337) (SourceJson.white (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))) fragment0269713Acc00800 := object_fragment0269713_field_007 fuel (fragment0269713Field008Chars00 ++ (fragment0269713Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 336) (SourceJson.white (fragment0269713Field009Chars00 ++ (tail))) fragment0269713Acc00900 := object_fragment0269713_field_008 fuel (fragment0269713Field009Chars00 ++ (tail))
    _ = .ok (fragment0269713Value, tail) := object_fragment0269713_field_009 fuel (tail)

noncomputable def fragment0271545Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0271545Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0271545Field000Value00 : SourceJson := .number (String.ofList ['2', '7'])
noncomputable def fragment0271545Acc00100 : List (String × SourceJson) := (fragment0271545Field000Key00, fragment0271545Field000Value00) :: fragment0271545Acc00000
noncomputable def fragment0271545Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '7', ',']

theorem object_fragment0271545_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0271545Field000Chars00 ++ tail)) fragment0271545Acc00000 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0271545Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_000"
  err.flush

noncomputable def fragment0271545Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0271545Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0271545Acc00200 : List (String × SourceJson) := (fragment0271545Field001Key00, fragment0271545Field001Value00) :: fragment0271545Acc00100
noncomputable def fragment0271545Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0271545_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0271545Field001Chars00 ++ tail)) fragment0271545Acc00100 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0271545Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_001"
  err.flush

noncomputable def fragment0271545Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0271545Field002Value00 : SourceJson := .str (String.ofList ['2', '8', '5', '2', '8', '5', '1', '8', '3', '9', '2', '4', '1', '8', '4', '3', '9', '5', '4', '2', '9', '0', '3', '8', '2', '3', '2', '4', '4', '0', '8', '3', '3', '7', '7', '5', '3', '1', '4', '5', '1', '/', '1', '8', '0', '2', '2', '1', '4', '6', '6', '3', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0271545Acc00300 : List (String × SourceJson) := (fragment0271545Field002Key00, fragment0271545Field002Value00) :: fragment0271545Acc00200
noncomputable def fragment0271545Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '8', '5', '2', '8', '5', '1', '8', '3', '9', '2', '4', '1', '8', '4', '3', '9', '5', '4', '2', '9', '0', '3', '8', '2', '3', '2', '4', '4', '0', '8', '3', '3', '7', '7', '5', '3', '1', '4', '5', '1', '/', '1', '8', '0', '2', '2', '1', '4', '6', '6', '3', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0271545_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0271545Field002Chars00 ++ tail)) fragment0271545Acc00200 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0271545Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_002"
  err.flush

noncomputable def fragment0271545Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0271545Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0271545Acc00400 : List (String × SourceJson) := (fragment0271545Field003Key00, fragment0271545Field003Value00) :: fragment0271545Acc00300
noncomputable def fragment0271545Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0271545_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0271545Field003Chars00 ++ tail)) fragment0271545Acc00300 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0271545Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_003"
  err.flush

noncomputable def fragment0271545Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0271545Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0271545Acc00500 : List (String × SourceJson) := (fragment0271545Field004Key00, fragment0271545Field004Value00) :: fragment0271545Acc00400
noncomputable def fragment0271545Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0271545_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0271545Field004Chars00 ++ tail)) fragment0271545Acc00400 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0271545Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_004"
  err.flush

noncomputable def fragment0271545Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0271545Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '1', '3', '9', '1', '9', '8', '6', '9', '8', '3', '/', '3', '3', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '9', '4', '7', '3', '6', '9', '4', '8', '7', '2', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '4', '8', '9', '6', '9', '7', '4', '1', '/', '1', '5', '8', '3', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '2', '4', '6', '7', '9', '8', '1', '1', '3', '1', '3', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '1', '6', '0', '7', '5', '0', '1', '4', '5', '2', '9', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '6', '9', '9', '5', '7', '3', '3', '8', '7', '/', '3', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '3', '0', '4', '6', '9', '4', '3', '4', '2', '9', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '9', '1', '7', '3', '0', '4', '5', '2', '4', '1', '/', '7', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '7', '5', '1', '7', '5', '5', '2', '0', '4', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '2', '4', '5', '7', '3', '4', '2', '3', '7', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0271545Acc00600 : List (String × SourceJson) := (fragment0271545Field005Key00, fragment0271545Field005Value00) :: fragment0271545Acc00500
noncomputable def fragment0271545Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '3', '9', '1', '9', '8', '6', '9', '8', '3', '/', '3', '3', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '4', '7', '3', '6', '9', '4', '8', '7', '2', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '4', '8', '9', '6', '9', '7', '4', '1', '/', '1', '5', '8', '3', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '2', '4', '6', '7', '9', '8', '1', '1', '3', '1', '3', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '6', '0', '7', '5', '0', '1', '4', '5', '2', '9', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '6', '9', '9', '5', '7', '3', '3', '8', '7', '/', '3', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '3', '0', '4', '6', '9', '4', '3', '4', '2', '9', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '9', '1', '7', '3', '0', '4', '5', '2', '4', '1', '/', '7', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '5', '1', '7', '5', '5', '2', '0', '4', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '2', '4', '5', '7', '3', '4', '2', '3', '7', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0271545_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0271545Field005Chars00 ++ tail)) fragment0271545Acc00500 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0271545Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_005"
  err.flush

noncomputable def fragment0271545Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0271545Field006Value00 : SourceJson := .str (String.ofList ['2', '3', '5', '3', '1', '8', '2', '8', '2', '7', '5', '8', '3', '7', '8', '4', '8', '6', '2', '8', '5', '9', '4', '9', '3', '8', '7', '3', '3', '5', '8', '7', '2', '5', '7', '3', '9', '0', '2', '7', '4', '4', '4', '5', '4', '1', '2', '8', '0', '0', '0', '0', '/', '2', '2', '0', '2', '4', '3', '4', '6', '2', '0', '9', '0', '3', '3', '5', '5', '9', '1', '0', '1', '0', '9', '8', '3', '8', '9', '6', '2', '5', '8', '0', '4', '7', '5', '6', '2', '0', '8', '3', '8', '8', '3', '4', '5', '1', '7', '0', '0', '4', '6', '7', '5', '6', '9', '7', '3', '9', '4', '1', '6', '9', '5', '1', '9', '1', '0', '9'])
noncomputable def fragment0271545Acc00700 : List (String × SourceJson) := (fragment0271545Field006Key00, fragment0271545Field006Value00) :: fragment0271545Acc00600
noncomputable def fragment0271545Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '3', '5', '3', '1', '8', '2', '8', '2', '7', '5', '8', '3', '7', '8', '4', '8', '6', '2', '8', '5', '9', '4', '9', '3', '8', '7', '3', '3', '5', '8', '7', '2', '5', '7', '3', '9', '0', '2', '7', '4', '4', '4', '5', '4', '1', '2', '8', '0', '0', '0', '0', '/', '2', '2', '0', '2', '4', '3', '4', '6', '2', '0', '9', '0', '3', '3', '5', '5', '9', '1', '0', '1', '0', '9', '8', '3', '8', '9', '6', '2', '5', '8', '0', '4', '7', '5', '6', '2', '0', '8', '3', '8', '8', '3', '4', '5', '1', '7', '0', '0', '4', '6', '7', '5', '6', '9', '7', '3', '9', '4', '1', '6', '9', '5', '1', '9', '1', '0', '9', '"', ',']

theorem object_fragment0271545_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0271545Field006Chars00 ++ tail)) fragment0271545Acc00600 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0271545Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_006"
  err.flush

noncomputable def fragment0271545Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0271545Field007Value00 : SourceJson := .str (String.ofList ['5', '0', '4', '2', '6', '4', '2', '6', '9', '3', '4', '1', '2', '8', '4', '7', '5', '0', '4', '5', '3', '4', '4', '6', '6', '6', '6', '8', '3', '9', '2', '5', '9', '1', '0', '1', '4', '1', '2', '7', '9', '4', '7', '8', '4', '5', '1', '4', '3', '6', '9', '9', '0', '5', '2', '5', '6', '0', '6', '6', '2', '0', '1', '1', '4', '3', '5', '2', '3', '6', '6', '5', '6', '4', '1', '7', '6', '5', '6', '0', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '8', '2', '1', '2', '1', '6', '1', '0', '4', '2', '9', '5', '8', '8', '1', '2', '5', '7', '8', '5', '2', '8', '0', '7', '1', '8', '8', '6', '8', '6', '9', '3', '0', '5', '4', '0', '5', '1', '7', '9', '2', '2', '2', '5', '1', '7', '2', '2', '6', '3', '5', '0', '1', '4', '3', '1', '5', '8', '0', '6', '1', '2', '0', '8', '7', '0', '3', '0', '1', '5', '1', '2', '6', '5', '9', '2', '6', '8', '2', '6', '7', '3', '6', '1', '8', '8', '9', '8', '1', '9', '4', '7', '5', '1', '3', '6', '9', '6', '2', '4', '5', '6', '5', '5', '2', '0', '8', '9', '0', '8', '7', '4', '0', '4', '6', '2', '3'])
noncomputable def fragment0271545Acc00800 : List (String × SourceJson) := (fragment0271545Field007Key00, fragment0271545Field007Value00) :: fragment0271545Acc00700
noncomputable def fragment0271545Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '0', '4', '2', '6', '4', '2', '6', '9', '3', '4', '1', '2', '8', '4', '7', '5', '0', '4', '5', '3', '4', '4', '6', '6', '6', '6', '8', '3', '9', '2', '5', '9', '1', '0', '1', '4', '1', '2', '7', '9', '4', '7', '8', '4', '5', '1', '4', '3', '6', '9', '9', '0', '5', '2', '5', '6', '0', '6', '6', '2', '0', '1', '1', '4', '3', '5', '2', '3', '6', '6', '5', '6', '4', '1', '7', '6', '5', '6', '0', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '8', '2', '1', '2', '1', '6', '1', '0', '4', '2', '9', '5', '8', '8', '1', '2', '5', '7', '8', '5', '2', '8', '0', '7', '1', '8', '8', '6', '8', '6', '9', '3', '0', '5', '4', '0', '5', '1', '7', '9', '2', '2', '2', '5', '1', '7', '2', '2', '6', '3', '5', '0', '1', '4', '3', '1', '5', '8', '0', '6', '1', '2', '0', '8', '7', '0', '3', '0', '1', '5', '1', '2', '6', '5', '9', '2', '6', '8', '2', '6', '7', '3', '6', '1', '8', '8', '9', '8', '1', '9', '4', '7', '5', '1', '3', '6', '9', '6', '2', '4', '5', '6', '5', '5', '2', '0', '8', '9', '0', '8', '7', '4', '0', '4', '6', '2', '3', '"', ',']

theorem object_fragment0271545_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0271545Field007Chars00 ++ tail)) fragment0271545Acc00700 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0271545Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_007"
  err.flush

noncomputable def fragment0271545Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0271545Field008Value00 : SourceJson := .str (String.ofList ['8', '4', '6', '5', '1', '0', '2', '6', '5', '1', '4', '0', '6', '4'])
noncomputable def fragment0271545Acc00900 : List (String × SourceJson) := (fragment0271545Field008Key00, fragment0271545Field008Value00) :: fragment0271545Acc00800
noncomputable def fragment0271545Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '4', '6', '5', '1', '0', '2', '6', '5', '1', '4', '0', '6', '4', '"', ',']

theorem object_fragment0271545_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0271545Field008Chars00 ++ tail)) fragment0271545Acc00800 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0271545Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_008"
  err.flush

noncomputable def fragment0271545Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0271545Field009Value00 : SourceJson := .str (String.ofList ['5', '8', '5', '7', '0', '1', '0', '0', '8', '0', '1', '1', '5', '6', '3'])
noncomputable def fragment0271545Acc01000 : List (String × SourceJson) := (fragment0271545Field009Key00, fragment0271545Field009Value00) :: fragment0271545Acc00900
noncomputable def fragment0271545Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '5', '7', '0', '1', '0', '0', '8', '0', '1', '1', '5', '6', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0271545_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0271545Field009Chars00 ++ tail)) fragment0271545Acc00900 =
      .ok (.obj (fragment0271545Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0271545_object_field_009"
  err.flush

noncomputable def fragment0271545Chars : List Char := '{' :: (fragment0271545Field000Chars00 ++ fragment0271545Field001Chars00 ++ fragment0271545Field002Chars00 ++ fragment0271545Field003Chars00 ++ fragment0271545Field004Chars00 ++ fragment0271545Field005Chars00 ++ fragment0271545Field006Chars00 ++ fragment0271545Field007Chars00 ++ fragment0271545Field008Chars00 ++ fragment0271545Field009Chars00)
noncomputable def fragment0271545Value : SourceJson := .obj (fragment0271545Acc01000.reverse)

theorem value_fragment0271545 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 234) (fragment0271545Chars ++ tail) =
      .ok (fragment0271545Value, tail) := by
  have hinput : fragment0271545Chars ++ tail = '{' :: (fragment0271545Field000Chars00 ++ (fragment0271545Field001Chars00 ++ (fragment0271545Field002Chars00 ++ (fragment0271545Field003Chars00 ++ (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0271545Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 234) (fragment0271545Chars ++ tail) =
        SourceJson.value (fuel + 234) ('{' :: (fragment0271545Field000Chars00 ++ (fragment0271545Field001Chars00 ++ (fragment0271545Field002Chars00 ++ (fragment0271545Field003Chars00 ++ (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 234)) hinput
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0271545Field000Chars00 ++ (fragment0271545Field001Chars00 ++ (fragment0271545Field002Chars00 ++ (fragment0271545Field003Chars00 ++ (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))))))))))) fragment0271545Acc00000 := by rfl
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0271545Field001Chars00 ++ (fragment0271545Field002Chars00 ++ (fragment0271545Field003Chars00 ++ (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail))))))))))) fragment0271545Acc00100 := object_fragment0271545_field_000 fuel (fragment0271545Field001Chars00 ++ (fragment0271545Field002Chars00 ++ (fragment0271545Field003Chars00 ++ (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0271545Field002Chars00 ++ (fragment0271545Field003Chars00 ++ (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))))))))) fragment0271545Acc00200 := object_fragment0271545_field_001 fuel (fragment0271545Field002Chars00 ++ (fragment0271545Field003Chars00 ++ (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0271545Field003Chars00 ++ (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail))))))))) fragment0271545Acc00300 := object_fragment0271545_field_002 fuel (fragment0271545Field003Chars00 ++ (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))))))) fragment0271545Acc00400 := object_fragment0271545_field_003 fuel (fragment0271545Field004Chars00 ++ (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail))))))) fragment0271545Acc00500 := object_fragment0271545_field_004 fuel (fragment0271545Field005Chars00 ++ (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))))) fragment0271545Acc00600 := object_fragment0271545_field_005 fuel (fragment0271545Field006Chars00 ++ (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail))))) fragment0271545Acc00700 := object_fragment0271545_field_006 fuel (fragment0271545Field007Chars00 ++ (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))) fragment0271545Acc00800 := object_fragment0271545_field_007 fuel (fragment0271545Field008Chars00 ++ (fragment0271545Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0271545Field009Chars00 ++ (tail))) fragment0271545Acc00900 := object_fragment0271545_field_008 fuel (fragment0271545Field009Chars00 ++ (tail))
    _ = .ok (fragment0271545Value, tail) := object_fragment0271545_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_before_reader"
  err.flush

noncomputable def chunk0026LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0026SuffixChars00 : List Char := [',']
noncomputable def chunk0026Chars00 : List Char := chunk0026LeadChars00 ++ fragment0269713Chars ++ chunk0026SuffixChars00
noncomputable def chunk0026Push00 (acc : List SourceJson) : List SourceJson := fragment0269713Value :: acc

noncomputable def chunk0026AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0026_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 578)
      (SourceJson.white (chunk0026LeadChars00 ++ (fragment0269713Chars ++ rest))) acc =
      (SourceJson.value (fuel + 577) (fragment0269713Chars ++ rest)).bind
        (chunk0026AfterValue00 (fuel + 577) acc) := by rfl

theorem array_chunk0026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 578) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 577) (SourceJson.white tail) (chunk0026Push00 acc) := by
  have hinput : chunk0026Chars00 ++ tail = chunk0026LeadChars00 ++ (fragment0269713Chars ++ (chunk0026SuffixChars00 ++ tail)) := by
    simp only [chunk0026Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 578) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 578)
          (SourceJson.white (chunk0026LeadChars00 ++ (fragment0269713Chars ++ (chunk0026SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 578) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 577) (fragment0269713Chars ++ (chunk0026SuffixChars00 ++ tail))).bind
        (chunk0026AfterValue00 (fuel + 577) acc) := array_chunk0026_head fuel (chunk0026SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0269713Value, chunk0026SuffixChars00 ++ tail)).bind
        (chunk0026AfterValue00 (fuel + 577) acc) :=
      congrArg (fun result => result.bind (chunk0026AfterValue00 (fuel + 577) acc))
        (value_fragment0269713 (fuel + 231) (chunk0026SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 577) (SourceJson.white tail) (chunk0026Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_before_reader"
  err.flush

noncomputable def chunk0027LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0027SuffixChars00 : List Char := [',']
noncomputable def chunk0027Chars00 : List Char := chunk0027LeadChars00 ++ fragment0271545Chars ++ chunk0027SuffixChars00
noncomputable def chunk0027Push00 (acc : List SourceJson) : List SourceJson := fragment0271545Value :: acc

noncomputable def chunk0027AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0027_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 577)
      (SourceJson.white (chunk0027LeadChars00 ++ (fragment0271545Chars ++ rest))) acc =
      (SourceJson.value (fuel + 576) (fragment0271545Chars ++ rest)).bind
        (chunk0027AfterValue00 (fuel + 576) acc) := by rfl

theorem array_chunk0027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 577) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 576) (SourceJson.white tail) (chunk0027Push00 acc) := by
  have hinput : chunk0027Chars00 ++ tail = chunk0027LeadChars00 ++ (fragment0271545Chars ++ (chunk0027SuffixChars00 ++ tail)) := by
    simp only [chunk0027Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 577) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 577)
          (SourceJson.white (chunk0027LeadChars00 ++ (fragment0271545Chars ++ (chunk0027SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 577) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 576) (fragment0271545Chars ++ (chunk0027SuffixChars00 ++ tail))).bind
        (chunk0027AfterValue00 (fuel + 576) acc) := array_chunk0027_head fuel (chunk0027SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0271545Value, chunk0027SuffixChars00 ++ tail)).bind
        (chunk0027AfterValue00 (fuel + 576) acc) :=
      congrArg (fun result => result.bind (chunk0027AfterValue00 (fuel + 576) acc))
        (value_fragment0271545 (fuel + 342) (chunk0027SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 576) (SourceJson.white tail) (chunk0027Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0026Chars00 ++ chunk0027Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0027Push00 (chunk0026Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 578) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 576) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0026Chars00 ++ (chunk0027Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 578) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 578) (SourceJson.white (chunk0026Chars00 ++ (chunk0027Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 578) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 577) (SourceJson.white (chunk0027Chars00 ++ (tail))) (chunk0026Push00 (acc)) := array_chunk0026 fuel (chunk0027Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 576) (SourceJson.white tail) (blockPush acc) := array_chunk0027 fuel (tail) (chunk0026Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 269707).take 3437 = blockChars := by rfl

theorem block_original_split : sourceRest 269707 = blockChars ++ sourceRest 273144 := by
  calc
    sourceRest 269707 = (sourceRest 269707).take 3437 ++ (sourceRest 269707).drop 3437 :=
      (List.take_append_drop 3437 (sourceRest 269707)).symm
    _ = blockChars ++ (sourceRest 269707).drop 3437 :=
      congrArg (fun part => part ++ (sourceRest 269707).drop 3437) block_original_prefix
    _ = blockChars ++ sourceRest 273144 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 269707 3437)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 578) (SourceJson.white (sourceRest 269707)) acc =
      SourceJson.array (fuel + 576) (SourceJson.white (sourceRest 273144)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 578) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 273144) acc)

#print axioms object_fragment0269713_field_000
#print axioms object_fragment0269713_field_001
#print axioms object_fragment0269713_field_002
#print axioms object_fragment0269713_field_003
#print axioms object_fragment0269713_field_004
#print axioms object_fragment0269713_field_005
#print axioms object_fragment0269713_field_006
#print axioms object_fragment0269713_field_007
#print axioms object_fragment0269713_field_008
#print axioms object_fragment0269713_field_009
#print axioms value_fragment0269713
#print axioms object_fragment0271545_field_000
#print axioms object_fragment0271545_field_001
#print axioms object_fragment0271545_field_002
#print axioms object_fragment0271545_field_003
#print axioms object_fragment0271545_field_004
#print axioms object_fragment0271545_field_005
#print axioms object_fragment0271545_field_006
#print axioms object_fragment0271545_field_007
#print axioms object_fragment0271545_field_008
#print axioms object_fragment0271545_field_009
#print axioms value_fragment0271545
#print axioms array_chunk0026_head
#print axioms array_chunk0026
#print axioms array_chunk0027_head
#print axioms array_chunk0027
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock013

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
