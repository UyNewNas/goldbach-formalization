import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock004

noncomputable def fragment0159867Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0159867Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0159867Field000Value00 : SourceJson := .number (String.ofList ['3', '2'])
noncomputable def fragment0159867Acc00100 : List (String × SourceJson) := (fragment0159867Field000Key00, fragment0159867Field000Value00) :: fragment0159867Acc00000
noncomputable def fragment0159867Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '2', ',']

theorem object_fragment0159867_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 266) (SourceJson.white (fragment0159867Field000Chars00 ++ tail)) fragment0159867Acc00000 =
      SourceJson.object (fuel + 265) (SourceJson.white tail) fragment0159867Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_000"
  err.flush

noncomputable def fragment0159867Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0159867Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0159867Acc00200 : List (String × SourceJson) := (fragment0159867Field001Key00, fragment0159867Field001Value00) :: fragment0159867Acc00100
noncomputable def fragment0159867Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0159867_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 265) (SourceJson.white (fragment0159867Field001Chars00 ++ tail)) fragment0159867Acc00100 =
      SourceJson.object (fuel + 264) (SourceJson.white tail) fragment0159867Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_001"
  err.flush

noncomputable def fragment0159867Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0159867Field002Value00 : SourceJson := .str (String.ofList ['9', '9', '6', '4', '0', '7', '8', '6', '0', '9', '3', '7', '3', '5', '9', '7', '5', '0', '4', '7', '2', '5', '4', '5', '0', '6', '9', '0', '5', '4', '7', '2', '9', '/', '3', '2', '4', '1', '9', '1', '1', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0159867Acc00300 : List (String × SourceJson) := (fragment0159867Field002Key00, fragment0159867Field002Value00) :: fragment0159867Acc00200
noncomputable def fragment0159867Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '9', '6', '4', '0', '7', '8', '6', '0', '9', '3', '7', '3', '5', '9', '7', '5', '0', '4', '7', '2', '5', '4', '5', '0', '6', '9', '0', '5', '4', '7', '2', '9', '/', '3', '2', '4', '1', '9', '1', '1', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0159867_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0159867Field002Chars00 ++ tail)) fragment0159867Acc00200 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0159867Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_002"
  err.flush

noncomputable def fragment0159867Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0159867Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0159867Acc00400 : List (String × SourceJson) := (fragment0159867Field003Key00, fragment0159867Field003Value00) :: fragment0159867Acc00300
noncomputable def fragment0159867Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0159867_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0159867Field003Chars00 ++ tail)) fragment0159867Acc00300 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0159867Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_003"
  err.flush

noncomputable def fragment0159867Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0159867Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0159867Acc00500 : List (String × SourceJson) := (fragment0159867Field004Key00, fragment0159867Field004Value00) :: fragment0159867Acc00400
noncomputable def fragment0159867Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0159867_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0159867Field004Chars00 ++ tail)) fragment0159867Acc00400 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0159867Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_004"
  err.flush

noncomputable def fragment0159867Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0159867Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '4', '1', '6', '3', '2', '4', '9', '5', '1', '7', '9', '6', '3', '7', '/', '7', '3', '7', '7', '1', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '6', '7', '6', '6', '7', '3', '4', '6', '0', '0', '9', '9', '/', '9', '2', '2', '1', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '3', '5', '5', '1', '9', '3', '6', '0', '9', '9', '3', '1', '/', '7', '3', '7', '7', '1', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '2', '1', '7', '4', '3', '4', '0', '0', '9', '0', '9', '9', '/', '1', '8', '4', '4', '2', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '9', '9', '5', '0', '3', '3', '2', '3', '9', '2', '4', '1', '/', '1', '8', '4', '4', '2', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '8', '1', '2', '2', '3', '8', '0', '3', '2', '8', '2', '3', '/', '3', '6', '8', '8', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '1', '1', '7', '1', '1', '5', '1', '3', '9', '0', '7', '3', '/', '3', '6', '8', '8', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '7', '1', '1', '1', '1', '8', '2', '9', '8', '7', '9', '/', '1', '2', '2', '9', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '5', '4', '5', '6', '7', '4', '4', '7', '1', '4', '7', '9', '/', '1', '2', '2', '9', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '5', '9', '1', '4', '9', '1', '5', '7', '8', '1', '7', '/', '1', '0', '2', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0159867Acc00600 : List (String × SourceJson) := (fragment0159867Field005Key00, fragment0159867Field005Value00) :: fragment0159867Acc00500
noncomputable def fragment0159867Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '1', '6', '3', '2', '4', '9', '5', '1', '7', '9', '6', '3', '7', '/', '7', '3', '7', '7', '1', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '6', '7', '6', '6', '7', '3', '4', '6', '0', '0', '9', '9', '/', '9', '2', '2', '1', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '3', '5', '5', '1', '9', '3', '6', '0', '9', '9', '3', '1', '/', '7', '3', '7', '7', '1', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '2', '1', '7', '4', '3', '4', '0', '0', '9', '0', '9', '9', '/', '1', '8', '4', '4', '2', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '9', '9', '5', '0', '3', '3', '2', '3', '9', '2', '4', '1', '/', '1', '8', '4', '4', '2', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '1', '2', '2', '3', '8', '0', '3', '2', '8', '2', '3', '/', '3', '6', '8', '8', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '1', '1', '7', '1', '1', '5', '1', '3', '9', '0', '7', '3', '/', '3', '6', '8', '8', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '7', '1', '1', '1', '1', '8', '2', '9', '8', '7', '9', '/', '1', '2', '2', '9', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '4', '5', '6', '7', '4', '4', '7', '1', '4', '7', '9', '/', '1', '2', '2', '9', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '5', '9', '1', '4', '9', '1', '5', '7', '8', '1', '7', '/', '1', '0', '2', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0159867_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0159867Field005Chars00 ++ tail)) fragment0159867Acc00500 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0159867Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_005"
  err.flush

noncomputable def fragment0159867Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0159867Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '3', '1', '3', '3', '8', '9', '4', '4', '3', '4', '2', '4', '6', '5', '8', '5', '6', '2', '8', '8', '4', '8', '2', '9', '7', '5', '1', '7', '8', '2', '4', '6', '0', '2', '9', '6', '1', '0', '5', '8', '4', '1', '1', '3', '1', '5', '2', '0', '0', '0', '0', '/', '8', '0', '4', '6', '3', '6', '8', '0', '5', '2', '8', '1', '9', '3', '3', '0', '8', '2', '8', '1', '4', '2', '7', '7', '1', '8', '6', '9', '7', '1', '5', '8', '3', '4', '3', '9', '4', '7', '2', '5', '8', '6', '7', '8', '7', '8', '4', '2', '8', '6', '1', '6', '0', '7', '0', '5', '9', '4', '7', '9', '1', '3', '1', '8', '7', '1'])
noncomputable def fragment0159867Acc00700 : List (String × SourceJson) := (fragment0159867Field006Key00, fragment0159867Field006Value00) :: fragment0159867Acc00600
noncomputable def fragment0159867Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '3', '1', '3', '3', '8', '9', '4', '4', '3', '4', '2', '4', '6', '5', '8', '5', '6', '2', '8', '8', '4', '8', '2', '9', '7', '5', '1', '7', '8', '2', '4', '6', '0', '2', '9', '6', '1', '0', '5', '8', '4', '1', '1', '3', '1', '5', '2', '0', '0', '0', '0', '/', '8', '0', '4', '6', '3', '6', '8', '0', '5', '2', '8', '1', '9', '3', '3', '0', '8', '2', '8', '1', '4', '2', '7', '7', '1', '8', '6', '9', '7', '1', '5', '8', '3', '4', '3', '9', '4', '7', '2', '5', '8', '6', '7', '8', '7', '8', '4', '2', '8', '6', '1', '6', '0', '7', '0', '5', '9', '4', '7', '9', '1', '3', '1', '8', '7', '1', '"', ',']

theorem object_fragment0159867_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0159867Field006Chars00 ++ tail)) fragment0159867Acc00600 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0159867Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_006"
  err.flush

noncomputable def fragment0159867Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0159867Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '7', '4', '5', '7', '9', '8', '1', '3', '1', '6', '8', '0', '1', '8', '7', '1', '5', '3', '1', '2', '0', '8', '4', '5', '8', '4', '4', '6', '5', '2', '0', '3', '5', '9', '9', '7', '3', '9', '7', '8', '6', '3', '2', '9', '3', '3', '5', '6', '7', '8', '7', '6', '9', '1', '4', '6', '4', '2', '3', '5', '9', '6', '1', '4', '2', '7', '6', '3', '6', '8', '5', '3', '5', '2', '2', '9', '9', '1', '1', '9', '1', '1', '8', '7', '9', '2', '0', '0', '6', '1', '9', '8', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '2', '3', '7', '5', '8', '1', '3', '7', '0', '0', '6', '5', '3', '6', '4', '1', '3', '0', '5', '8', '1', '4', '2', '6', '9', '5', '2', '3', '5', '6', '6', '7', '7', '6', '1', '1', '7', '9', '0', '9', '2', '1', '9', '3', '4', '3', '2', '2', '6', '8', '6', '6', '1', '2', '3', '1', '2', '5', '8', '4', '8', '0', '7', '9', '3', '1', '7', '0', '2', '8', '7', '7', '0', '0', '6', '5', '3', '2', '8', '1', '5', '4', '0', '4', '6', '9', '9', '8', '6', '7', '4', '3', '7', '5', '3', '9', '8', '2', '7', '4', '2', '2', '0', '7', '3', '6', '3', '2', '7', '4', '8', '6', '6', '5', '1', '1', '4', '9', '7', '0', '8', '7', '0', '2', '4', '7', '8', '9', '5', '5', '3', '3'])
noncomputable def fragment0159867Acc00800 : List (String × SourceJson) := (fragment0159867Field007Key00, fragment0159867Field007Value00) :: fragment0159867Acc00700
noncomputable def fragment0159867Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '8', '7', '4', '5', '7', '9', '8', '1', '3', '1', '6', '8', '0', '1', '8', '7', '1', '5', '3', '1', '2', '0', '8', '4', '5', '8', '4', '4', '6', '5', '2', '0', '3', '5', '9', '9', '7', '3', '9', '7', '8', '6', '3', '2', '9', '3', '3', '5', '6', '7', '8', '7', '6', '9', '1', '4', '6', '4', '2', '3', '5', '9', '6', '1', '4', '2', '7', '6', '3', '6', '8', '5', '3', '5', '2', '2', '9', '9', '1', '1', '9', '1', '1', '8', '7', '9', '2', '0', '0', '6', '1', '9', '8', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '2', '3', '7', '5', '8', '1', '3', '7', '0', '0', '6', '5', '3', '6', '4', '1', '3', '0', '5', '8', '1', '4', '2', '6', '9', '5', '2', '3', '5', '6', '6', '7', '7', '6', '1', '1', '7', '9', '0', '9', '2', '1', '9', '3', '4', '3', '2', '2', '6', '8', '6', '6', '1', '2', '3', '1', '2', '5', '8', '4', '8', '0', '7', '9', '3', '1', '7', '0', '2', '8', '7', '7', '0', '0', '6', '5', '3', '2', '8', '1', '5', '4', '0', '4', '6', '9', '9', '8', '6', '7', '4', '3', '7', '5', '3', '9', '8', '2', '7', '4', '2', '2', '0', '7', '3', '6', '3', '2', '7', '4', '8', '6', '6', '5', '1', '1', '4', '9', '7', '0', '8', '7', '0', '2', '4', '7', '8', '9', '5', '5', '3', '3', '"', ',']

theorem object_fragment0159867_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0159867Field007Chars00 ++ tail)) fragment0159867Acc00700 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0159867Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_007"
  err.flush

noncomputable def fragment0159867Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0159867Field008Value00 : SourceJson := .str (String.ofList ['1', '5', '0', '7', '8', '2', '5', '2', '6', '9', '1', '1', '9', '7', '2', '7'])
noncomputable def fragment0159867Acc00900 : List (String × SourceJson) := (fragment0159867Field008Key00, fragment0159867Field008Value00) :: fragment0159867Acc00800
noncomputable def fragment0159867Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '0', '7', '8', '2', '5', '2', '6', '9', '1', '1', '9', '7', '2', '7', '"', ',']

theorem object_fragment0159867_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0159867Field008Chars00 ++ tail)) fragment0159867Acc00800 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0159867Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_008"
  err.flush

noncomputable def fragment0159867Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0159867Field009Value00 : SourceJson := .str (String.ofList ['4', '4', '7', '8', '5', '9', '3', '0', '2', '1', '3', '2', '7', '8', '5', '0'])
noncomputable def fragment0159867Acc01000 : List (String × SourceJson) := (fragment0159867Field009Key00, fragment0159867Field009Value00) :: fragment0159867Acc00900
noncomputable def fragment0159867Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '7', '8', '5', '9', '3', '0', '2', '1', '3', '2', '7', '8', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0159867_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0159867Field009Chars00 ++ tail)) fragment0159867Acc00900 =
      .ok (.obj (fragment0159867Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0159867_object_field_009"
  err.flush

noncomputable def fragment0159867Chars : List Char := '{' :: (fragment0159867Field000Chars00 ++ fragment0159867Field001Chars00 ++ fragment0159867Field002Chars00 ++ fragment0159867Field003Chars00 ++ fragment0159867Field004Chars00 ++ fragment0159867Field005Chars00 ++ fragment0159867Field006Chars00 ++ fragment0159867Field007Chars00 ++ fragment0159867Field008Chars00 ++ fragment0159867Field009Chars00)
noncomputable def fragment0159867Value : SourceJson := .obj (fragment0159867Acc01000.reverse)

theorem value_fragment0159867 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 267) (fragment0159867Chars ++ tail) =
      .ok (fragment0159867Value, tail) := by
  have hinput : fragment0159867Chars ++ tail = '{' :: (fragment0159867Field000Chars00 ++ (fragment0159867Field001Chars00 ++ (fragment0159867Field002Chars00 ++ (fragment0159867Field003Chars00 ++ (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0159867Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 267) (fragment0159867Chars ++ tail) =
        SourceJson.value (fuel + 267) ('{' :: (fragment0159867Field000Chars00 ++ (fragment0159867Field001Chars00 ++ (fragment0159867Field002Chars00 ++ (fragment0159867Field003Chars00 ++ (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 267)) hinput
    _ = SourceJson.object (fuel + 266) (SourceJson.white (fragment0159867Field000Chars00 ++ (fragment0159867Field001Chars00 ++ (fragment0159867Field002Chars00 ++ (fragment0159867Field003Chars00 ++ (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))))))))))) fragment0159867Acc00000 := by rfl
    _ = SourceJson.object (fuel + 265) (SourceJson.white (fragment0159867Field001Chars00 ++ (fragment0159867Field002Chars00 ++ (fragment0159867Field003Chars00 ++ (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail))))))))))) fragment0159867Acc00100 := object_fragment0159867_field_000 fuel (fragment0159867Field001Chars00 ++ (fragment0159867Field002Chars00 ++ (fragment0159867Field003Chars00 ++ (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0159867Field002Chars00 ++ (fragment0159867Field003Chars00 ++ (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))))))))) fragment0159867Acc00200 := object_fragment0159867_field_001 fuel (fragment0159867Field002Chars00 ++ (fragment0159867Field003Chars00 ++ (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0159867Field003Chars00 ++ (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail))))))))) fragment0159867Acc00300 := object_fragment0159867_field_002 fuel (fragment0159867Field003Chars00 ++ (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))))))) fragment0159867Acc00400 := object_fragment0159867_field_003 fuel (fragment0159867Field004Chars00 ++ (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail))))))) fragment0159867Acc00500 := object_fragment0159867_field_004 fuel (fragment0159867Field005Chars00 ++ (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))))) fragment0159867Acc00600 := object_fragment0159867_field_005 fuel (fragment0159867Field006Chars00 ++ (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail))))) fragment0159867Acc00700 := object_fragment0159867_field_006 fuel (fragment0159867Field007Chars00 ++ (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))) fragment0159867Acc00800 := object_fragment0159867_field_007 fuel (fragment0159867Field008Chars00 ++ (fragment0159867Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0159867Field009Chars00 ++ (tail))) fragment0159867Acc00900 := object_fragment0159867_field_008 fuel (fragment0159867Field009Chars00 ++ (tail))
    _ = .ok (fragment0159867Value, tail) := object_fragment0159867_field_009 fuel (tail)

noncomputable def fragment0161536Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0161536Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0161536Field000Value00 : SourceJson := .number (String.ofList ['3', '3'])
noncomputable def fragment0161536Acc00100 : List (String × SourceJson) := (fragment0161536Field000Key00, fragment0161536Field000Value00) :: fragment0161536Acc00000
noncomputable def fragment0161536Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '3', ',']

theorem object_fragment0161536_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 438) (SourceJson.white (fragment0161536Field000Chars00 ++ tail)) fragment0161536Acc00000 =
      SourceJson.object (fuel + 437) (SourceJson.white tail) fragment0161536Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_000"
  err.flush

noncomputable def fragment0161536Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0161536Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['4'])]
noncomputable def fragment0161536Acc00200 : List (String × SourceJson) := (fragment0161536Field001Key00, fragment0161536Field001Value00) :: fragment0161536Acc00100
noncomputable def fragment0161536Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0161536_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0161536Field001Chars00 ++ tail)) fragment0161536Acc00100 =
      SourceJson.object (fuel + 436) (SourceJson.white tail) fragment0161536Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_001"
  err.flush

noncomputable def fragment0161536Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0161536Field002Value00 : SourceJson := .str (String.ofList ['6', '3', '2', '9', '6', '0', '6', '5', '7', '8', '4', '5', '3', '0', '6', '1', '0', '1', '1', '2', '3', '3', '4', '9', '6', '6', '1', '1', '5', '6', '6', '5', '9', '/', '3', '6', '9', '0', '5', '6', '8', '4', '3', '2', '6', '1', '7', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0161536Acc00300 : List (String × SourceJson) := (fragment0161536Field002Key00, fragment0161536Field002Value00) :: fragment0161536Acc00200
noncomputable def fragment0161536Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '3', '2', '9', '6', '0', '6', '5', '7', '8', '4', '5', '3', '0', '6', '1', '0', '1', '1', '2', '3', '3', '4', '9', '6', '6', '1', '1', '5', '6', '6', '5', '9', '/', '3', '6', '9', '0', '5', '6', '8', '4', '3', '2', '6', '1', '7', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0161536_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0161536Field002Chars00 ++ tail)) fragment0161536Acc00200 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0161536Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_002"
  err.flush

noncomputable def fragment0161536Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0161536Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '8', '7', '1', '0', '3', '7', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0161536Acc00400 : List (String × SourceJson) := (fragment0161536Field003Key00, fragment0161536Field003Value00) :: fragment0161536Acc00300
noncomputable def fragment0161536Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '8', '7', '1', '0', '3', '7', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0161536_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0161536Field003Chars00 ++ tail)) fragment0161536Acc00300 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0161536Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_003"
  err.flush

noncomputable def fragment0161536Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0161536Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0161536Acc00500 : List (String × SourceJson) := (fragment0161536Field004Key00, fragment0161536Field004Value00) :: fragment0161536Acc00400
noncomputable def fragment0161536Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '5', '9', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0161536_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0161536Field004Chars00 ++ tail)) fragment0161536Acc00400 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0161536Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_004"
  err.flush

noncomputable def fragment0161536Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0161536Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '9', '7', '4', '4', '2', '8', '3', '9', '1', '4', '2', '1', '9', '9', '1', '6', '8', '4', '4', '8', '2', '3', '/', '9', '2', '9', '3', '1', '8', '0', '1', '3', '1', '5', '8', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '5', '1', '2', '6', '4', '6', '0', '3', '2', '1', '6', '0', '5', '7', '1', '2', '4', '0', '2', '7', '/', '1', '1', '6', '1', '6', '4', '7', '5', '1', '6', '4', '4', '7', '8', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '1', '7', '7', '8', '7', '9', '9', '3', '8', '0', '6', '2', '4', '7', '7', '4', '6', '3', '7', '9', '7', '/', '4', '6', '4', '6', '5', '9', '0', '0', '6', '5', '7', '9', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '5', '6', '0', '2', '0', '3', '4', '7', '8', '5', '9', '4', '1', '7', '6', '0', '2', '0', '2', '9', '7', '/', '2', '3', '2', '3', '2', '9', '5', '0', '3', '2', '8', '9', '5', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '6', '4', '9', '9', '8', '9', '0', '7', '5', '4', '5', '6', '3', '8', '5', '8', '1', '1', '6', '9', '9', '/', '2', '3', '2', '3', '2', '9', '5', '0', '3', '2', '8', '9', '5', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '6', '9', '0', '1', '2', '1', '0', '6', '6', '2', '9', '5', '5', '7', '3', '5', '5', '9', '6', '9', '/', '4', '6', '4', '6', '5', '9', '0', '0', '6', '5', '7', '9', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '7', '3', '2', '8', '5', '5', '8', '3', '3', '7', '4', '6', '0', '0', '1', '0', '3', '7', '9', '/', '2', '7', '3', '3', '2', '8', '8', '2', '7', '3', '9', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '3', '0', '2', '8', '0', '9', '6', '6', '6', '0', '6', '8', '0', '2', '8', '5', '9', '2', '6', '9', '/', '1', '5', '4', '8', '8', '6', '3', '3', '5', '5', '2', '6', '3', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '0', '1', '1', '0', '4', '0', '4', '0', '0', '7', '8', '4', '1', '3', '2', '5', '4', '4', '6', '9', '/', '1', '5', '4', '8', '8', '6', '3', '3', '5', '5', '2', '6', '3', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '3', '6', '8', '6', '2', '6', '7', '5', '3', '2', '9', '8', '5', '3', '2', '3', '6', '8', '3', '/', '3', '8', '7', '2', '1', '5', '8', '3', '8', '8', '1', '5', '9', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0161536Acc00600 : List (String × SourceJson) := (fragment0161536Field005Key00, fragment0161536Field005Value00) :: fragment0161536Acc00500
noncomputable def fragment0161536Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '7', '4', '4', '2', '8', '3', '9', '1', '4', '2', '1', '9', '9', '1', '6', '8', '4', '4', '8', '2', '3', '/', '9', '2', '9', '3', '1', '8', '0', '1', '3', '1', '5', '8', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '5', '1', '2', '6', '4', '6', '0', '3', '2', '1', '6', '0', '5', '7', '1', '2', '4', '0', '2', '7', '/', '1', '1', '6', '1', '6', '4', '7', '5', '1', '6', '4', '4', '7', '8', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '1', '7', '7', '8', '7', '9', '9', '3', '8', '0', '6', '2', '4', '7', '7', '4', '6', '3', '7', '9', '7', '/', '4', '6', '4', '6', '5', '9', '0', '0', '6', '5', '7', '9', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '5', '6', '0', '2', '0', '3', '4', '7', '8', '5', '9', '4', '1', '7', '6', '0', '2', '0', '2', '9', '7', '/', '2', '3', '2', '3', '2', '9', '5', '0', '3', '2', '8', '9', '5', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '6', '4', '9', '9', '8', '9', '0', '7', '5', '4', '5', '6', '3', '8', '5', '8', '1', '1', '6', '9', '9', '/', '2', '3', '2', '3', '2', '9', '5', '0', '3', '2', '8', '9', '5', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '6', '9', '0', '1', '2', '1', '0', '6', '6', '2', '9', '5', '5', '7', '3', '5', '5', '9', '6', '9', '/', '4', '6', '4', '6', '5', '9', '0', '0', '6', '5', '7', '9', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '7', '3', '2', '8', '5', '5', '8', '3', '3', '7', '4', '6', '0', '0', '1', '0', '3', '7', '9', '/', '2', '7', '3', '3', '2', '8', '8', '2', '7', '3', '9', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '3', '0', '2', '8', '0', '9', '6', '6', '6', '0', '6', '8', '0', '2', '8', '5', '9', '2', '6', '9', '/', '1', '5', '4', '8', '8', '6', '3', '3', '5', '5', '2', '6', '3', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '0', '1', '1', '0', '4', '0', '4', '0', '0', '7', '8', '4', '1', '3', '2', '5', '4', '4', '6', '9', '/', '1', '5', '4', '8', '8', '6', '3', '3', '5', '5', '2', '6', '3', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '3', '6', '8', '6', '2', '6', '7', '5', '3', '2', '9', '8', '5', '3', '2', '3', '6', '8', '3', '/', '3', '8', '7', '2', '1', '5', '8', '3', '8', '8', '1', '5', '9', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0161536_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0161536Field005Chars00 ++ tail)) fragment0161536Acc00500 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0161536Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_005"
  err.flush

noncomputable def fragment0161536Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0161536Field006Value00 : SourceJson := .str (String.ofList ['5', '2', '5', '0', '8', '3', '9', '8', '3', '6', '6', '5', '1', '5', '7', '0', '1', '1', '8', '6', '4', '5', '9', '6', '7', '1', '8', '4', '0', '8', '2', '7', '7', '0', '0', '2', '5', '6', '0', '9', '0', '1', '1', '7', '8', '9', '6', '1', '4', '2', '8', '4', '8', '0', '0', '/', '2', '0', '4', '8', '0', '5', '1', '8', '8', '8', '3', '5', '8', '0', '7', '2', '6', '0', '3', '8', '1', '3', '3', '1', '5', '5', '4', '5', '4', '1', '5', '4', '6', '9', '7', '9', '4', '2', '4', '2', '0', '7', '1', '2', '0', '0', '3', '7', '4', '6', '3', '9', '9', '4', '2', '9', '0', '7', '7', '7', '7', '2', '1', '5', '6', '9', '3', '6', '3'])
noncomputable def fragment0161536Acc00700 : List (String × SourceJson) := (fragment0161536Field006Key00, fragment0161536Field006Value00) :: fragment0161536Acc00600
noncomputable def fragment0161536Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '2', '5', '0', '8', '3', '9', '8', '3', '6', '6', '5', '1', '5', '7', '0', '1', '1', '8', '6', '4', '5', '9', '6', '7', '1', '8', '4', '0', '8', '2', '7', '7', '0', '0', '2', '5', '6', '0', '9', '0', '1', '1', '7', '8', '9', '6', '1', '4', '2', '8', '4', '8', '0', '0', '/', '2', '0', '4', '8', '0', '5', '1', '8', '8', '8', '3', '5', '8', '0', '7', '2', '6', '0', '3', '8', '1', '3', '3', '1', '5', '5', '4', '5', '4', '1', '5', '4', '6', '9', '7', '9', '4', '2', '4', '2', '0', '7', '1', '2', '0', '0', '3', '7', '4', '6', '3', '9', '9', '4', '2', '9', '0', '7', '7', '7', '7', '2', '1', '5', '6', '9', '3', '6', '3', '"', ',']

theorem object_fragment0161536_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0161536Field006Chars00 ++ tail)) fragment0161536Acc00600 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0161536Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_006"
  err.flush

noncomputable def fragment0161536Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0161536Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '6', '0', '8', '5', '4', '8', '0', '4', '7', '2', '4', '4', '0', '6', '0', '9', '3', '7', '1', '0', '6', '8', '6', '2', '2', '5', '0', '0', '8', '5', '4', '6', '4', '1', '2', '5', '7', '0', '5', '4', '6', '0', '8', '2', '3', '9', '1', '6', '6', '7', '4', '5', '5', '9', '4', '3', '4', '3', '3', '0', '7', '3', '1', '9', '7', '3', '4', '8', '8', '6', '4', '1', '5', '0', '0', '6', '0', '9', '3', '1', '4', '3', '2', '0', '3', '3', '0', '5', '0', '9', '7', '3', '8', '2', '5', '5', '8', '1', '5', '2', '6', '1', '2', '7', '9', '0', '2', '8', '4', '5', '3', '7', '3', '6', '1', '6', '7', '5', '8', '2', '4', '9', '5', '6', '1', '9', '6', '5', '2', '8', '6', '6', '6', '3', '6', '3', '8', '7', '3', '2', '0', '4', '9', '6', '5', '7', '8', '6', '3', '9', '3', '5', '7', '8', '3', '3', '6', '6', '5', '4', '5', '4', '2', '9', '8', '3', '1', '7', '9', '7', '9', '1', '4', '3', '0', '9', '9', '7', '5', '0', '8', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '5', '0', '7', '3', '2', '3', '3', '8', '5', '5', '8', '7', '9', '0', '1', '9', '8', '0', '4', '9', '7', '0', '2', '2', '8', '7', '2', '9', '8', '1', '6', '1', '3', '4', '2', '8', '6', '0', '3', '1', '2', '9', '8', '1', '6', '1', '4', '4', '2', '2', '9', '2', '0', '2', '6', '9', '2', '6', '3', '8', '9', '4', '8', '0', '0', '3', '9', '4', '2', '3', '3', '1', '2', '2', '8', '0', '6', '3', '5', '5', '2', '4', '5', '1', '5', '7', '0', '4', '7', '1', '4', '2', '3', '6', '5', '7', '6', '6', '9', '0', '9', '2', '9', '1', '2', '5', '9', '6', '6', '5', '0', '4', '8', '6', '2', '7', '6', '3', '2', '2', '3', '9', '0', '1', '3', '9', '1', '5', '6', '0', '5', '9', '7', '8', '0', '3', '8', '8', '2', '2', '1', '6', '9', '1', '8', '7', '6', '7', '7', '3', '1', '4', '0', '0', '7', '3', '1', '7', '1', '8', '6', '0', '0', '5', '8', '4', '8', '3', '7', '1', '8', '9', '4', '3', '2', '3', '2', '6', '0', '6', '9', '7', '1', '1', '5', '5', '5', '6', '7', '1', '0', '6', '8', '7', '2', '5', '7', '8', '1', '3', '8', '0', '2', '1', '5', '6', '9', '8', '1', '3', '5', '9', '5', '0', '0', '6', '4', '3'])
noncomputable def fragment0161536Acc00800 : List (String × SourceJson) := (fragment0161536Field007Key00, fragment0161536Field007Value00) :: fragment0161536Acc00700
noncomputable def fragment0161536Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '6', '0', '8', '5', '4', '8', '0', '4', '7', '2', '4', '4', '0', '6', '0', '9', '3', '7', '1', '0', '6', '8', '6', '2', '2', '5', '0', '0', '8', '5', '4', '6', '4', '1', '2', '5', '7', '0', '5', '4', '6', '0', '8', '2', '3', '9', '1', '6', '6', '7', '4', '5', '5', '9', '4', '3', '4', '3', '3', '0', '7', '3', '1', '9', '7', '3', '4', '8', '8', '6', '4', '1', '5', '0', '0', '6', '0', '9', '3', '1', '4', '3', '2', '0', '3', '3', '0', '5', '0', '9', '7', '3', '8', '2', '5', '5', '8', '1', '5', '2', '6', '1', '2', '7', '9', '0', '2', '8', '4', '5', '3', '7', '3', '6', '1', '6', '7', '5', '8', '2', '4', '9', '5', '6', '1', '9', '6', '5', '2', '8', '6', '6', '6', '3', '6', '3', '8', '7', '3', '2', '0', '4', '9', '6', '5', '7', '8', '6', '3', '9', '3', '5', '7', '8', '3', '3', '6', '6', '5', '4', '5', '4', '2', '9', '8', '3', '1', '7', '9', '7', '9', '1', '4', '3', '0', '9', '9', '7', '5', '0', '8', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '5', '0', '7', '3', '2', '3', '3', '8', '5', '5', '8', '7', '9', '0', '1', '9', '8', '0', '4', '9', '7', '0', '2', '2', '8', '7', '2', '9', '8', '1', '6', '1', '3', '4', '2', '8', '6', '0', '3', '1', '2', '9', '8', '1', '6', '1', '4', '4', '2', '2', '9', '2', '0', '2', '6', '9', '2', '6', '3', '8', '9', '4', '8', '0', '0', '3', '9', '4', '2', '3', '3', '1', '2', '2', '8', '0', '6', '3', '5', '5', '2', '4', '5', '1', '5', '7', '0', '4', '7', '1', '4', '2', '3', '6', '5', '7', '6', '6', '9', '0', '9', '2', '9', '1', '2', '5', '9', '6', '6', '5', '0', '4', '8', '6', '2', '7', '6', '3', '2', '2', '3', '9', '0', '1', '3', '9', '1', '5', '6', '0', '5', '9', '7', '8', '0', '3', '8', '8', '2', '2', '1', '6', '9', '1', '8', '7', '6', '7', '7', '3', '1', '4', '0', '0', '7', '3', '1', '7', '1', '8', '6', '0', '0', '5', '8', '4', '8', '3', '7', '1', '8', '9', '4', '3', '2', '3', '2', '6', '0', '6', '9', '7', '1', '1', '5', '5', '5', '6', '7', '1', '0', '6', '8', '7', '2', '5', '7', '8', '1', '3', '8', '0', '2', '1', '5', '6', '9', '8', '1', '3', '5', '9', '5', '0', '0', '6', '4', '3', '"', ',']

theorem object_fragment0161536_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0161536Field007Chars00 ++ tail)) fragment0161536Acc00700 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0161536Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_007"
  err.flush

noncomputable def fragment0161536Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0161536Field008Value00 : SourceJson := .str (String.ofList ['2', '0', '3', '1', '2', '6', '8', '8', '0', '8', '5', '6', '5', '7', '9', '9'])
noncomputable def fragment0161536Acc00900 : List (String × SourceJson) := (fragment0161536Field008Key00, fragment0161536Field008Value00) :: fragment0161536Acc00800
noncomputable def fragment0161536Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '3', '1', '2', '6', '8', '8', '0', '8', '5', '6', '5', '7', '9', '9', '"', ',']

theorem object_fragment0161536_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0161536Field008Chars00 ++ tail)) fragment0161536Acc00800 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0161536Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_008"
  err.flush

noncomputable def fragment0161536Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0161536Field009Value00 : SourceJson := .str (String.ofList ['4', '9', '6', '9', '5', '1', '3', '4', '8', '4', '3', '6', '4', '3', '0', '0'])
noncomputable def fragment0161536Acc01000 : List (String × SourceJson) := (fragment0161536Field009Key00, fragment0161536Field009Value00) :: fragment0161536Acc00900
noncomputable def fragment0161536Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '6', '9', '5', '1', '3', '4', '8', '4', '3', '6', '4', '3', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0161536_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0161536Field009Chars00 ++ tail)) fragment0161536Acc00900 =
      .ok (.obj (fragment0161536Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0161536_object_field_009"
  err.flush

noncomputable def fragment0161536Chars : List Char := '{' :: (fragment0161536Field000Chars00 ++ fragment0161536Field001Chars00 ++ fragment0161536Field002Chars00 ++ fragment0161536Field003Chars00 ++ fragment0161536Field004Chars00 ++ fragment0161536Field005Chars00 ++ fragment0161536Field006Chars00 ++ fragment0161536Field007Chars00 ++ fragment0161536Field008Chars00 ++ fragment0161536Field009Chars00)
noncomputable def fragment0161536Value : SourceJson := .obj (fragment0161536Acc01000.reverse)

theorem value_fragment0161536 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 439) (fragment0161536Chars ++ tail) =
      .ok (fragment0161536Value, tail) := by
  have hinput : fragment0161536Chars ++ tail = '{' :: (fragment0161536Field000Chars00 ++ (fragment0161536Field001Chars00 ++ (fragment0161536Field002Chars00 ++ (fragment0161536Field003Chars00 ++ (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0161536Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 439) (fragment0161536Chars ++ tail) =
        SourceJson.value (fuel + 439) ('{' :: (fragment0161536Field000Chars00 ++ (fragment0161536Field001Chars00 ++ (fragment0161536Field002Chars00 ++ (fragment0161536Field003Chars00 ++ (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 439)) hinput
    _ = SourceJson.object (fuel + 438) (SourceJson.white (fragment0161536Field000Chars00 ++ (fragment0161536Field001Chars00 ++ (fragment0161536Field002Chars00 ++ (fragment0161536Field003Chars00 ++ (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))))))))))) fragment0161536Acc00000 := by rfl
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0161536Field001Chars00 ++ (fragment0161536Field002Chars00 ++ (fragment0161536Field003Chars00 ++ (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail))))))))))) fragment0161536Acc00100 := object_fragment0161536_field_000 fuel (fragment0161536Field001Chars00 ++ (fragment0161536Field002Chars00 ++ (fragment0161536Field003Chars00 ++ (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0161536Field002Chars00 ++ (fragment0161536Field003Chars00 ++ (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))))))))) fragment0161536Acc00200 := object_fragment0161536_field_001 fuel (fragment0161536Field002Chars00 ++ (fragment0161536Field003Chars00 ++ (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0161536Field003Chars00 ++ (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail))))))))) fragment0161536Acc00300 := object_fragment0161536_field_002 fuel (fragment0161536Field003Chars00 ++ (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))))))) fragment0161536Acc00400 := object_fragment0161536_field_003 fuel (fragment0161536Field004Chars00 ++ (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail))))))) fragment0161536Acc00500 := object_fragment0161536_field_004 fuel (fragment0161536Field005Chars00 ++ (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))))) fragment0161536Acc00600 := object_fragment0161536_field_005 fuel (fragment0161536Field006Chars00 ++ (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail))))) fragment0161536Acc00700 := object_fragment0161536_field_006 fuel (fragment0161536Field007Chars00 ++ (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))) fragment0161536Acc00800 := object_fragment0161536_field_007 fuel (fragment0161536Field008Chars00 ++ (fragment0161536Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0161536Field009Chars00 ++ (tail))) fragment0161536Acc00900 := object_fragment0161536_field_008 fuel (fragment0161536Field009Chars00 ++ (tail))
    _ = .ok (fragment0161536Value, tail) := object_fragment0161536_field_009 fuel (tail)

noncomputable def fragment0163547Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0163547Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0163547Field000Value00 : SourceJson := .number (String.ofList ['3', '4'])
noncomputable def fragment0163547Acc00100 : List (String × SourceJson) := (fragment0163547Field000Key00, fragment0163547Field000Value00) :: fragment0163547Acc00000
noncomputable def fragment0163547Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '4', ',']

theorem object_fragment0163547_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0163547Field000Chars00 ++ tail)) fragment0163547Acc00000 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0163547Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_000"
  err.flush

noncomputable def fragment0163547Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0163547Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0163547Acc00200 : List (String × SourceJson) := (fragment0163547Field001Key00, fragment0163547Field001Value00) :: fragment0163547Acc00100
noncomputable def fragment0163547Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0163547_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0163547Field001Chars00 ++ tail)) fragment0163547Acc00100 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0163547Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_001"
  err.flush

noncomputable def fragment0163547Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0163547Field002Value00 : SourceJson := .str (String.ofList ['4', '0', '2', '5', '6', '5', '0', '9', '3', '5', '1', '1', '6', '3', '7', '4', '7', '2', '7', '9', '8', '0', '4', '0', '3', '4', '7', '3', '0', '4', '2', '9', '6', '0', '1', '/', '3', '3', '8', '5', '9', '7', '3', '5', '8', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0163547Acc00300 : List (String × SourceJson) := (fragment0163547Field002Key00, fragment0163547Field002Value00) :: fragment0163547Acc00200
noncomputable def fragment0163547Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '0', '2', '5', '6', '5', '0', '9', '3', '5', '1', '1', '6', '3', '7', '4', '7', '2', '7', '9', '8', '0', '4', '0', '3', '4', '7', '3', '0', '4', '2', '9', '6', '0', '1', '/', '3', '3', '8', '5', '9', '7', '3', '5', '8', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0163547_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0163547Field002Chars00 ++ tail)) fragment0163547Acc00200 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0163547Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_002"
  err.flush

noncomputable def fragment0163547Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0163547Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0163547Acc00400 : List (String × SourceJson) := (fragment0163547Field003Key00, fragment0163547Field003Value00) :: fragment0163547Acc00300
noncomputable def fragment0163547Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0163547_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0163547Field003Chars00 ++ tail)) fragment0163547Acc00300 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0163547Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_003"
  err.flush

noncomputable def fragment0163547Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0163547Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0163547Acc00500 : List (String × SourceJson) := (fragment0163547Field004Key00, fragment0163547Field004Value00) :: fragment0163547Acc00400
noncomputable def fragment0163547Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0163547_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0163547Field004Chars00 ++ tail)) fragment0163547Acc00400 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0163547Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_004"
  err.flush

noncomputable def fragment0163547Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0163547Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '1', '7', '5', '5', '2', '7', '4', '5', '8', '0', '3', '3', '/', '3', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '9', '5', '9', '5', '0', '2', '4', '4', '8', '3', '/', '2', '1', '9', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '8', '2', '1', '2', '4', '5', '0', '6', '3', '7', '/', '8', '1', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '2', '2', '0', '7', '8', '4', '6', '0', '6', '4', '1', '/', '3', '0', '7', '1', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '3', '9', '2', '3', '5', '7', '8', '6', '3', '/', '1', '7', '0', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '5', '3', '8', '8', '5', '5', '5', '0', '3', '/', '4', '0', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '0', '6', '0', '0', '5', '2', '0', '6', '9', '3', '/', '4', '0', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '7', '2', '2', '6', '0', '7', '1', '1', '3', '3', '/', '1', '7', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '6', '8', '7', '9', '0', '2', '8', '1', '3', '/', '1', '7', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '0', '5', '4', '8', '0', '7', '2', '0', '1', '/', '2', '1', '9', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0163547Acc00600 : List (String × SourceJson) := (fragment0163547Field005Key00, fragment0163547Field005Value00) :: fragment0163547Acc00500
noncomputable def fragment0163547Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '7', '5', '5', '2', '7', '4', '5', '8', '0', '3', '3', '/', '3', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '5', '9', '5', '0', '2', '4', '4', '8', '3', '/', '2', '1', '9', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '8', '2', '1', '2', '4', '5', '0', '6', '3', '7', '/', '8', '1', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '2', '2', '0', '7', '8', '4', '6', '0', '6', '4', '1', '/', '3', '0', '7', '1', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '3', '9', '2', '3', '5', '7', '8', '6', '3', '/', '1', '7', '0', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '3', '8', '8', '5', '5', '5', '0', '3', '/', '4', '0', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '0', '6', '0', '0', '5', '2', '0', '6', '9', '3', '/', '4', '0', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '7', '2', '2', '6', '0', '7', '1', '1', '3', '3', '/', '1', '7', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '6', '8', '7', '9', '0', '2', '8', '1', '3', '/', '1', '7', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '0', '5', '4', '8', '0', '7', '2', '0', '1', '/', '2', '1', '9', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0163547_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0163547Field005Chars00 ++ tail)) fragment0163547Acc00500 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0163547Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_005"
  err.flush

noncomputable def fragment0163547Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0163547Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '1', '7', '9', '4', '6', '7', '0', '6', '7', '8', '6', '3', '1', '4', '3', '0', '9', '5', '5', '5', '7', '3', '2', '0', '8', '1', '8', '5', '9', '4', '2', '4', '8', '7', '0', '8', '4', '1', '7', '1', '2', '0', '0', '0', '0', '0', '0', '/', '1', '9', '3', '8', '7', '3', '4', '6', '5', '6', '2', '9', '0', '4', '5', '4', '7', '6', '8', '9', '1', '2', '7', '8', '0', '0', '7', '7', '6', '1', '8', '8', '8', '2', '6', '4', '0', '7', '2', '6', '1', '0', '7', '1', '1', '9', '2', '1', '8', '9', '6', '6', '0', '1', '8', '2', '0', '0', '4', '6', '0', '9', '1', '1', '2', '7'])
noncomputable def fragment0163547Acc00700 : List (String × SourceJson) := (fragment0163547Field006Key00, fragment0163547Field006Value00) :: fragment0163547Acc00600
noncomputable def fragment0163547Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '1', '7', '9', '4', '6', '7', '0', '6', '7', '8', '6', '3', '1', '4', '3', '0', '9', '5', '5', '5', '7', '3', '2', '0', '8', '1', '8', '5', '9', '4', '2', '4', '8', '7', '0', '8', '4', '1', '7', '1', '2', '0', '0', '0', '0', '0', '0', '/', '1', '9', '3', '8', '7', '3', '4', '6', '5', '6', '2', '9', '0', '4', '5', '4', '7', '6', '8', '9', '1', '2', '7', '8', '0', '0', '7', '7', '6', '1', '8', '8', '8', '2', '6', '4', '0', '7', '2', '6', '1', '0', '7', '1', '1', '9', '2', '1', '8', '9', '6', '6', '0', '1', '8', '2', '0', '0', '4', '6', '0', '9', '1', '1', '2', '7', '"', ',']

theorem object_fragment0163547_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0163547Field006Chars00 ++ tail)) fragment0163547Acc00600 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0163547Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_006"
  err.flush

noncomputable def fragment0163547Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0163547Field007Value00 : SourceJson := .str (String.ofList ['8', '5', '6', '9', '2', '0', '0', '6', '7', '3', '3', '3', '0', '5', '3', '1', '9', '2', '9', '7', '8', '4', '0', '1', '7', '1', '7', '6', '0', '8', '1', '3', '2', '6', '9', '1', '8', '8', '0', '5', '7', '6', '8', '2', '2', '6', '2', '6', '3', '9', '7', '5', '3', '1', '9', '1', '3', '9', '0', '5', '7', '6', '8', '9', '4', '0', '3', '4', '3', '1', '3', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '7', '9', '5', '5', '1', '7', '5', '2', '8', '0', '8', '3', '3', '7', '3', '1', '7', '9', '5', '2', '2', '6', '3', '0', '9', '5', '3', '7', '3', '2', '4', '9', '5', '5', '7', '5', '5', '1', '1', '4', '2', '5', '9', '0', '8', '7', '3', '2', '6', '1', '2', '6', '2', '2', '7', '3', '3', '1', '0', '5', '8', '4', '7', '6', '4', '2', '8', '5', '2', '4', '3', '4', '6', '1', '5', '1', '1', '9', '1', '3', '8', '8', '0', '4', '9', '1', '2', '2', '3', '4', '1', '5', '2', '2', '9', '6', '9', '9', '7', '9', '5', '6', '5', '2', '1', '0', '3', '3', '8', '5', '1'])
noncomputable def fragment0163547Acc00800 : List (String × SourceJson) := (fragment0163547Field007Key00, fragment0163547Field007Value00) :: fragment0163547Acc00700
noncomputable def fragment0163547Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '5', '6', '9', '2', '0', '0', '6', '7', '3', '3', '3', '0', '5', '3', '1', '9', '2', '9', '7', '8', '4', '0', '1', '7', '1', '7', '6', '0', '8', '1', '3', '2', '6', '9', '1', '8', '8', '0', '5', '7', '6', '8', '2', '2', '6', '2', '6', '3', '9', '7', '5', '3', '1', '9', '1', '3', '9', '0', '5', '7', '6', '8', '9', '4', '0', '3', '4', '3', '1', '3', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '7', '9', '5', '5', '1', '7', '5', '2', '8', '0', '8', '3', '3', '7', '3', '1', '7', '9', '5', '2', '2', '6', '3', '0', '9', '5', '3', '7', '3', '2', '4', '9', '5', '5', '7', '5', '5', '1', '1', '4', '2', '5', '9', '0', '8', '7', '3', '2', '6', '1', '2', '6', '2', '2', '7', '3', '3', '1', '0', '5', '8', '4', '7', '6', '4', '2', '8', '5', '2', '4', '3', '4', '6', '1', '5', '1', '1', '9', '1', '3', '8', '8', '0', '4', '9', '1', '2', '2', '3', '4', '1', '5', '2', '2', '9', '6', '9', '9', '7', '9', '5', '6', '5', '2', '1', '0', '3', '3', '8', '5', '1', '"', ',']

theorem object_fragment0163547_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0163547Field007Chars00 ++ tail)) fragment0163547Acc00700 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0163547Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_007"
  err.flush

noncomputable def fragment0163547Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0163547Field008Value00 : SourceJson := .str (String.ofList ['4', '1', '5', '9', '9', '3', '2', '1', '9', '3', '6', '3'])
noncomputable def fragment0163547Acc00900 : List (String × SourceJson) := (fragment0163547Field008Key00, fragment0163547Field008Value00) :: fragment0163547Acc00800
noncomputable def fragment0163547Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '5', '9', '9', '3', '2', '1', '9', '3', '6', '3', '"', ',']

theorem object_fragment0163547_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0163547Field008Chars00 ++ tail)) fragment0163547Acc00800 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0163547Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_008"
  err.flush

noncomputable def fragment0163547Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0163547Field009Value00 : SourceJson := .str (String.ofList ['1', '5', '5', '0', '2', '0', '8', '9', '2', '9', '7', '8', '0'])
noncomputable def fragment0163547Acc01000 : List (String × SourceJson) := (fragment0163547Field009Key00, fragment0163547Field009Value00) :: fragment0163547Acc00900
noncomputable def fragment0163547Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '5', '0', '2', '0', '8', '9', '2', '9', '7', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0163547_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0163547Field009Chars00 ++ tail)) fragment0163547Acc00900 =
      .ok (.obj (fragment0163547Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0163547_object_field_009"
  err.flush

noncomputable def fragment0163547Chars : List Char := '{' :: (fragment0163547Field000Chars00 ++ fragment0163547Field001Chars00 ++ fragment0163547Field002Chars00 ++ fragment0163547Field003Chars00 ++ fragment0163547Field004Chars00 ++ fragment0163547Field005Chars00 ++ fragment0163547Field006Chars00 ++ fragment0163547Field007Chars00 ++ fragment0163547Field008Chars00 ++ fragment0163547Field009Chars00)
noncomputable def fragment0163547Value : SourceJson := .obj (fragment0163547Acc01000.reverse)

theorem value_fragment0163547 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 221) (fragment0163547Chars ++ tail) =
      .ok (fragment0163547Value, tail) := by
  have hinput : fragment0163547Chars ++ tail = '{' :: (fragment0163547Field000Chars00 ++ (fragment0163547Field001Chars00 ++ (fragment0163547Field002Chars00 ++ (fragment0163547Field003Chars00 ++ (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0163547Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 221) (fragment0163547Chars ++ tail) =
        SourceJson.value (fuel + 221) ('{' :: (fragment0163547Field000Chars00 ++ (fragment0163547Field001Chars00 ++ (fragment0163547Field002Chars00 ++ (fragment0163547Field003Chars00 ++ (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 221)) hinput
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0163547Field000Chars00 ++ (fragment0163547Field001Chars00 ++ (fragment0163547Field002Chars00 ++ (fragment0163547Field003Chars00 ++ (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))))))))))) fragment0163547Acc00000 := by rfl
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0163547Field001Chars00 ++ (fragment0163547Field002Chars00 ++ (fragment0163547Field003Chars00 ++ (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail))))))))))) fragment0163547Acc00100 := object_fragment0163547_field_000 fuel (fragment0163547Field001Chars00 ++ (fragment0163547Field002Chars00 ++ (fragment0163547Field003Chars00 ++ (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0163547Field002Chars00 ++ (fragment0163547Field003Chars00 ++ (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))))))))) fragment0163547Acc00200 := object_fragment0163547_field_001 fuel (fragment0163547Field002Chars00 ++ (fragment0163547Field003Chars00 ++ (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0163547Field003Chars00 ++ (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail))))))))) fragment0163547Acc00300 := object_fragment0163547_field_002 fuel (fragment0163547Field003Chars00 ++ (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))))))) fragment0163547Acc00400 := object_fragment0163547_field_003 fuel (fragment0163547Field004Chars00 ++ (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail))))))) fragment0163547Acc00500 := object_fragment0163547_field_004 fuel (fragment0163547Field005Chars00 ++ (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))))) fragment0163547Acc00600 := object_fragment0163547_field_005 fuel (fragment0163547Field006Chars00 ++ (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail))))) fragment0163547Acc00700 := object_fragment0163547_field_006 fuel (fragment0163547Field007Chars00 ++ (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))) fragment0163547Acc00800 := object_fragment0163547_field_007 fuel (fragment0163547Field008Chars00 ++ (fragment0163547Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0163547Field009Chars00 ++ (tail))) fragment0163547Acc00900 := object_fragment0163547_field_008 fuel (fragment0163547Field009Chars00 ++ (tail))
    _ = .ok (fragment0163547Value, tail) := object_fragment0163547_field_009 fuel (tail)

noncomputable def fragment0165118Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0165118Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0165118Field000Value00 : SourceJson := .number (String.ofList ['3', '5'])
noncomputable def fragment0165118Acc00100 : List (String × SourceJson) := (fragment0165118Field000Key00, fragment0165118Field000Value00) :: fragment0165118Acc00000
noncomputable def fragment0165118Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '5', ',']

theorem object_fragment0165118_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0165118Field000Chars00 ++ tail)) fragment0165118Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0165118Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_000"
  err.flush

noncomputable def fragment0165118Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0165118Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0165118Acc00200 : List (String × SourceJson) := (fragment0165118Field001Key00, fragment0165118Field001Value00) :: fragment0165118Acc00100
noncomputable def fragment0165118Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0165118_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0165118Field001Chars00 ++ tail)) fragment0165118Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0165118Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_001"
  err.flush

noncomputable def fragment0165118Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0165118Field002Value00 : SourceJson := .str (String.ofList ['2', '1', '2', '4', '9', '3', '8', '1', '5', '7', '5', '4', '5', '7', '8', '2', '5', '8', '7', '7', '8', '3', '8', '6', '2', '2', '6', '7', '7', '3', '0', '7', '7', '/', '2', '7', '1', '8', '7', '7', '2', '1', '9', '3', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0165118Acc00300 : List (String × SourceJson) := (fragment0165118Field002Key00, fragment0165118Field002Value00) :: fragment0165118Acc00200
noncomputable def fragment0165118Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '1', '2', '4', '9', '3', '8', '1', '5', '7', '5', '4', '5', '7', '8', '2', '5', '8', '7', '7', '8', '3', '8', '6', '2', '2', '6', '7', '7', '3', '0', '7', '7', '/', '2', '7', '1', '8', '7', '7', '2', '1', '9', '3', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0165118_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0165118Field002Chars00 ++ tail)) fragment0165118Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0165118Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_002"
  err.flush

noncomputable def fragment0165118Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0165118Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0165118Acc00400 : List (String × SourceJson) := (fragment0165118Field003Key00, fragment0165118Field003Value00) :: fragment0165118Acc00300
noncomputable def fragment0165118Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0165118_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0165118Field003Chars00 ++ tail)) fragment0165118Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0165118Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_003"
  err.flush

noncomputable def fragment0165118Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0165118Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '5', '3', '1', '2', '4', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0165118Acc00500 : List (String × SourceJson) := (fragment0165118Field004Key00, fragment0165118Field004Value00) :: fragment0165118Acc00400
noncomputable def fragment0165118Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '1', '2', '4', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0165118_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0165118Field004Chars00 ++ tail)) fragment0165118Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0165118Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_004"
  err.flush

noncomputable def fragment0165118Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0165118Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '5', '0', '3', '3', '4', '3', '5', '5', '4', '7', '5', '0', '1', '/', '1', '2', '9', '8', '9', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '6', '2', '3', '9', '6', '7', '6', '1', '7', '7', '7', '/', '1', '6', '2', '3', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '8', '3', '4', '1', '9', '1', '4', '2', '7', '8', '9', '3', '/', '9', '0', '9', '2', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '2', '8', '5', '0', '9', '5', '9', '8', '3', '8', '5', '6', '9', '/', '2', '2', '7', '3', '1', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '9', '0', '4', '1', '1', '5', '7', '0', '8', '4', '9', '1', '/', '2', '2', '7', '3', '1', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '1', '5', '6', '6', '7', '6', '0', '9', '7', '3', '1', '3', '/', '4', '5', '4', '6', '3', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '8', '7', '6', '0', '3', '2', '1', '9', '5', '2', '2', '3', '/', '4', '5', '4', '6', '3', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '3', '2', '1', '7', '1', '8', '7', '5', '6', '8', '7', '/', '2', '1', '6', '4', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '1', '4', '5', '3', '4', '4', '6', '6', '4', '0', '7', '/', '2', '1', '6', '4', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '4', '5', '0', '3', '5', '7', '2', '0', '7', '3', '/', '5', '4', '1', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0165118Acc00600 : List (String × SourceJson) := (fragment0165118Field005Key00, fragment0165118Field005Value00) :: fragment0165118Acc00500
noncomputable def fragment0165118Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '0', '3', '3', '4', '3', '5', '5', '4', '7', '5', '0', '1', '/', '1', '2', '9', '8', '9', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '6', '2', '3', '9', '6', '7', '6', '1', '7', '7', '7', '/', '1', '6', '2', '3', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '8', '3', '4', '1', '9', '1', '4', '2', '7', '8', '9', '3', '/', '9', '0', '9', '2', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '8', '5', '0', '9', '5', '9', '8', '3', '8', '5', '6', '9', '/', '2', '2', '7', '3', '1', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '9', '0', '4', '1', '1', '5', '7', '0', '8', '4', '9', '1', '/', '2', '2', '7', '3', '1', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '1', '5', '6', '6', '7', '6', '0', '9', '7', '3', '1', '3', '/', '4', '5', '4', '6', '3', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '8', '7', '6', '0', '3', '2', '1', '9', '5', '2', '2', '3', '/', '4', '5', '4', '6', '3', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '3', '2', '1', '7', '1', '8', '7', '5', '6', '8', '7', '/', '2', '1', '6', '4', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '1', '4', '5', '3', '4', '4', '6', '6', '4', '0', '7', '/', '2', '1', '6', '4', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '4', '5', '0', '3', '5', '7', '2', '0', '7', '3', '/', '5', '4', '1', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0165118_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0165118Field005Chars00 ++ tail)) fragment0165118Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0165118Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_005"
  err.flush

noncomputable def fragment0165118Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0165118Field006Value00 : SourceJson := .str (String.ofList ['8', '8', '4', '7', '5', '6', '6', '7', '0', '6', '5', '2', '2', '9', '7', '9', '6', '1', '5', '1', '7', '8', '3', '9', '9', '6', '6', '4', '1', '0', '5', '7', '2', '5', '5', '2', '6', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '/', '2', '0', '8', '4', '1', '0', '0', '4', '3', '9', '7', '8', '4', '3', '0', '2', '3', '6', '3', '8', '1', '2', '2', '4', '3', '7', '7', '1', '0', '6', '9', '7', '7', '5', '2', '0', '4', '0', '5', '7', '6', '9', '2', '7', '9', '9', '5', '4', '1', '6', '1', '2', '3', '3', '8', '5', '7', '9', '7', '7', '4', '3', '5', '0', '3'])
noncomputable def fragment0165118Acc00700 : List (String × SourceJson) := (fragment0165118Field006Key00, fragment0165118Field006Value00) :: fragment0165118Acc00600
noncomputable def fragment0165118Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '8', '4', '7', '5', '6', '6', '7', '0', '6', '5', '2', '2', '9', '7', '9', '6', '1', '5', '1', '7', '8', '3', '9', '9', '6', '6', '4', '1', '0', '5', '7', '2', '5', '5', '2', '6', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '/', '2', '0', '8', '4', '1', '0', '0', '4', '3', '9', '7', '8', '4', '3', '0', '2', '3', '6', '3', '8', '1', '2', '2', '4', '3', '7', '7', '1', '0', '6', '9', '7', '7', '5', '2', '0', '4', '0', '5', '7', '6', '9', '2', '7', '9', '9', '5', '4', '1', '6', '1', '2', '3', '3', '8', '5', '7', '9', '7', '7', '4', '3', '5', '0', '3', '"', ',']

theorem object_fragment0165118_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0165118Field006Chars00 ++ tail)) fragment0165118Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0165118Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_006"
  err.flush

noncomputable def fragment0165118Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0165118Field007Value00 : SourceJson := .str (String.ofList ['3', '4', '7', '5', '1', '5', '6', '4', '7', '0', '5', '5', '1', '9', '9', '6', '2', '7', '9', '1', '6', '6', '2', '7', '5', '7', '9', '5', '2', '1', '0', '6', '1', '7', '7', '5', '8', '1', '1', '5', '8', '8', '8', '4', '3', '7', '6', '1', '6', '9', '0', '6', '2', '0', '8', '8', '0', '5', '1', '6', '8', '6', '3', '4', '1', '5', '6', '4', '5', '2', '0', '7', '1', '7', '3', '8', '1', '5', '7', '3', '6', '7', '8', '3', '6', '0', '5', '8', '5', '8', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '5', '6', '7', '4', '4', '8', '2', '9', '6', '0', '2', '0', '2', '0', '1', '5', '1', '6', '3', '2', '6', '1', '0', '7', '9', '7', '7', '5', '2', '9', '5', '2', '6', '9', '4', '1', '1', '0', '1', '9', '4', '3', '3', '3', '5', '7', '3', '7', '1', '8', '0', '3', '1', '1', '6', '1', '0', '2', '0', '8', '8', '6', '2', '6', '5', '9', '6', '4', '2', '0', '3', '5', '3', '3', '9', '3', '5', '9', '5', '2', '3', '9', '8', '5', '7', '6', '5', '5', '7', '4', '4', '5', '4', '0', '4', '7', '6', '1', '7', '8', '2', '7', '0', '2', '0', '2', '3', '9', '7', '9', '2', '4', '5', '3', '6', '3', '9', '6', '8', '3', '1', '4', '1', '5', '0', '8', '2', '9', '8', '0', '7'])
noncomputable def fragment0165118Acc00800 : List (String × SourceJson) := (fragment0165118Field007Key00, fragment0165118Field007Value00) :: fragment0165118Acc00700
noncomputable def fragment0165118Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '7', '5', '1', '5', '6', '4', '7', '0', '5', '5', '1', '9', '9', '6', '2', '7', '9', '1', '6', '6', '2', '7', '5', '7', '9', '5', '2', '1', '0', '6', '1', '7', '7', '5', '8', '1', '1', '5', '8', '8', '8', '4', '3', '7', '6', '1', '6', '9', '0', '6', '2', '0', '8', '8', '0', '5', '1', '6', '8', '6', '3', '4', '1', '5', '6', '4', '5', '2', '0', '7', '1', '7', '3', '8', '1', '5', '7', '3', '6', '7', '8', '3', '6', '0', '5', '8', '5', '8', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '5', '6', '7', '4', '4', '8', '2', '9', '6', '0', '2', '0', '2', '0', '1', '5', '1', '6', '3', '2', '6', '1', '0', '7', '9', '7', '7', '5', '2', '9', '5', '2', '6', '9', '4', '1', '1', '0', '1', '9', '4', '3', '3', '3', '5', '7', '3', '7', '1', '8', '0', '3', '1', '1', '6', '1', '0', '2', '0', '8', '8', '6', '2', '6', '5', '9', '6', '4', '2', '0', '3', '5', '3', '3', '9', '3', '5', '9', '5', '2', '3', '9', '8', '5', '7', '6', '5', '5', '7', '4', '4', '5', '4', '0', '4', '7', '6', '1', '7', '8', '2', '7', '0', '2', '0', '2', '3', '9', '7', '9', '2', '4', '5', '3', '6', '3', '9', '6', '8', '3', '1', '4', '1', '5', '0', '8', '2', '9', '8', '0', '7', '"', ',']

theorem object_fragment0165118_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0165118Field007Chars00 ++ tail)) fragment0165118Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0165118Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_007"
  err.flush

noncomputable def fragment0165118Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0165118Field008Value00 : SourceJson := .str (String.ofList ['3', '3', '6', '3', '4', '4', '8', '5', '1', '4', '7', '5'])
noncomputable def fragment0165118Acc00900 : List (String × SourceJson) := (fragment0165118Field008Key00, fragment0165118Field008Value00) :: fragment0165118Acc00800
noncomputable def fragment0165118Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '6', '3', '4', '4', '8', '5', '1', '4', '7', '5', '"', ',']

theorem object_fragment0165118_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0165118Field008Chars00 ++ tail)) fragment0165118Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0165118Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_008"
  err.flush

noncomputable def fragment0165118Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0165118Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '6', '8', '7', '8', '1', '3', '9', '8', '2', '6'])
noncomputable def fragment0165118Acc01000 : List (String × SourceJson) := (fragment0165118Field009Key00, fragment0165118Field009Value00) :: fragment0165118Acc00900
noncomputable def fragment0165118Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '6', '8', '7', '8', '1', '3', '9', '8', '2', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0165118_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0165118Field009Chars00 ++ tail)) fragment0165118Acc00900 =
      .ok (.obj (fragment0165118Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0165118_object_field_009"
  err.flush

noncomputable def fragment0165118Chars : List Char := '{' :: (fragment0165118Field000Chars00 ++ fragment0165118Field001Chars00 ++ fragment0165118Field002Chars00 ++ fragment0165118Field003Chars00 ++ fragment0165118Field004Chars00 ++ fragment0165118Field005Chars00 ++ fragment0165118Field006Chars00 ++ fragment0165118Field007Chars00 ++ fragment0165118Field008Chars00 ++ fragment0165118Field009Chars00)
noncomputable def fragment0165118Value : SourceJson := .obj (fragment0165118Acc01000.reverse)

theorem value_fragment0165118 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0165118Chars ++ tail) =
      .ok (fragment0165118Value, tail) := by
  have hinput : fragment0165118Chars ++ tail = '{' :: (fragment0165118Field000Chars00 ++ (fragment0165118Field001Chars00 ++ (fragment0165118Field002Chars00 ++ (fragment0165118Field003Chars00 ++ (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0165118Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0165118Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0165118Field000Chars00 ++ (fragment0165118Field001Chars00 ++ (fragment0165118Field002Chars00 ++ (fragment0165118Field003Chars00 ++ (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0165118Field000Chars00 ++ (fragment0165118Field001Chars00 ++ (fragment0165118Field002Chars00 ++ (fragment0165118Field003Chars00 ++ (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))))))))))) fragment0165118Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0165118Field001Chars00 ++ (fragment0165118Field002Chars00 ++ (fragment0165118Field003Chars00 ++ (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail))))))))))) fragment0165118Acc00100 := object_fragment0165118_field_000 fuel (fragment0165118Field001Chars00 ++ (fragment0165118Field002Chars00 ++ (fragment0165118Field003Chars00 ++ (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0165118Field002Chars00 ++ (fragment0165118Field003Chars00 ++ (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))))))))) fragment0165118Acc00200 := object_fragment0165118_field_001 fuel (fragment0165118Field002Chars00 ++ (fragment0165118Field003Chars00 ++ (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0165118Field003Chars00 ++ (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail))))))))) fragment0165118Acc00300 := object_fragment0165118_field_002 fuel (fragment0165118Field003Chars00 ++ (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))))))) fragment0165118Acc00400 := object_fragment0165118_field_003 fuel (fragment0165118Field004Chars00 ++ (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail))))))) fragment0165118Acc00500 := object_fragment0165118_field_004 fuel (fragment0165118Field005Chars00 ++ (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))))) fragment0165118Acc00600 := object_fragment0165118_field_005 fuel (fragment0165118Field006Chars00 ++ (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail))))) fragment0165118Acc00700 := object_fragment0165118_field_006 fuel (fragment0165118Field007Chars00 ++ (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))) fragment0165118Acc00800 := object_fragment0165118_field_007 fuel (fragment0165118Field008Chars00 ++ (fragment0165118Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0165118Field009Chars00 ++ (tail))) fragment0165118Acc00900 := object_fragment0165118_field_008 fuel (fragment0165118Field009Chars00 ++ (tail))
    _ = .ok (fragment0165118Value, tail) := object_fragment0165118_field_009 fuel (tail)

noncomputable def fragment0166763Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0166763Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0166763Field000Value00 : SourceJson := .number (String.ofList ['3', '6'])
noncomputable def fragment0166763Acc00100 : List (String × SourceJson) := (fragment0166763Field000Key00, fragment0166763Field000Value00) :: fragment0166763Acc00000
noncomputable def fragment0166763Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '6', ',']

theorem object_fragment0166763_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0166763Field000Chars00 ++ tail)) fragment0166763Acc00000 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0166763Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_000"
  err.flush

noncomputable def fragment0166763Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0166763Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0166763Acc00200 : List (String × SourceJson) := (fragment0166763Field001Key00, fragment0166763Field001Value00) :: fragment0166763Acc00100
noncomputable def fragment0166763Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0166763_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0166763Field001Chars00 ++ tail)) fragment0166763Acc00100 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0166763Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_001"
  err.flush

noncomputable def fragment0166763Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0166763Field002Value00 : SourceJson := .str (String.ofList ['6', '2', '7', '8', '8', '7', '6', '4', '9', '3', '9', '2', '8', '9', '9', '9', '0', '7', '1', '1', '0', '2', '7', '3', '5', '3', '7', '3', '3', '/', '8', '9', '0', '5', '8', '3', '1', '3', '4', '7', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0166763Acc00300 : List (String × SourceJson) := (fragment0166763Field002Key00, fragment0166763Field002Value00) :: fragment0166763Acc00200
noncomputable def fragment0166763Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '2', '7', '8', '8', '7', '6', '4', '9', '3', '9', '2', '8', '9', '9', '9', '0', '7', '1', '1', '0', '2', '7', '3', '5', '3', '7', '3', '3', '/', '8', '9', '0', '5', '8', '3', '1', '3', '4', '7', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0166763_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0166763Field002Chars00 ++ tail)) fragment0166763Acc00200 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0166763Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_002"
  err.flush

noncomputable def fragment0166763Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0166763Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0166763Acc00400 : List (String × SourceJson) := (fragment0166763Field003Key00, fragment0166763Field003Value00) :: fragment0166763Acc00300
noncomputable def fragment0166763Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0166763_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0166763Field003Chars00 ++ tail)) fragment0166763Acc00300 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0166763Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_003"
  err.flush

noncomputable def fragment0166763Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0166763Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0166763Acc00500 : List (String × SourceJson) := (fragment0166763Field004Key00, fragment0166763Field004Value00) :: fragment0166763Acc00400
noncomputable def fragment0166763Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0166763_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0166763Field004Chars00 ++ tail)) fragment0166763Acc00400 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0166763Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_004"
  err.flush

noncomputable def fragment0166763Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0166763Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '1', '3', '7', '3', '9', '1', '3', '8', '1', '2', '5', '7', '/', '2', '4', '5', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '8', '7', '4', '4', '0', '6', '0', '7', '3', '9', '/', '3', '0', '6', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '2', '5', '2', '5', '1', '3', '7', '6', '4', '1', '7', '/', '1', '7', '1', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '7', '3', '2', '6', '6', '2', '1', '0', '8', '7', '3', '/', '4', '2', '8', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '4', '1', '0', '2', '1', '9', '0', '3', '0', '2', '7', '/', '4', '2', '8', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '3', '5', '9', '6', '0', '2', '6', '7', '3', '/', '1', '7', '1', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '9', '2', '1', '0', '6', '6', '2', '2', '6', '1', '1', '/', '8', '5', '7', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '7', '2', '7', '4', '1', '9', '2', '8', '9', '9', '/', '4', '0', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '0', '5', '4', '6', '1', '9', '1', '3', '9', '/', '4', '0', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '5', '6', '9', '3', '3', '0', '4', '1', '1', '/', '1', '0', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0166763Acc00600 : List (String × SourceJson) := (fragment0166763Field005Key00, fragment0166763Field005Value00) :: fragment0166763Acc00500
noncomputable def fragment0166763Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '3', '7', '3', '9', '1', '3', '8', '1', '2', '5', '7', '/', '2', '4', '5', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '7', '4', '4', '0', '6', '0', '7', '3', '9', '/', '3', '0', '6', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '5', '2', '5', '1', '3', '7', '6', '4', '1', '7', '/', '1', '7', '1', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '7', '3', '2', '6', '6', '2', '1', '0', '8', '7', '3', '/', '4', '2', '8', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '4', '1', '0', '2', '1', '9', '0', '3', '0', '2', '7', '/', '4', '2', '8', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '3', '5', '9', '6', '0', '2', '6', '7', '3', '/', '1', '7', '1', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '9', '2', '1', '0', '6', '6', '2', '2', '6', '1', '1', '/', '8', '5', '7', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '2', '7', '4', '1', '9', '2', '8', '9', '9', '/', '4', '0', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '0', '5', '4', '6', '1', '9', '1', '3', '9', '/', '4', '0', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '5', '6', '9', '3', '3', '0', '4', '1', '1', '/', '1', '0', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0166763_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0166763Field005Chars00 ++ tail)) fragment0166763Acc00500 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0166763Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_005"
  err.flush

noncomputable def fragment0166763Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0166763Field006Value00 : SourceJson := .str (String.ofList ['5', '1', '4', '6', '5', '3', '4', '0', '5', '3', '6', '7', '5', '3', '9', '2', '5', '3', '5', '4', '1', '3', '1', '8', '5', '9', '1', '3', '8', '0', '2', '7', '9', '8', '2', '6', '4', '0', '9', '5', '8', '6', '6', '8', '8', '0', '0', '0', '0', '/', '1', '1', '7', '8', '8', '8', '6', '4', '8', '2', '1', '5', '7', '2', '5', '0', '7', '9', '5', '7', '5', '1', '1', '5', '0', '2', '9', '7', '1', '9', '0', '9', '2', '4', '5', '7', '4', '1', '1', '0', '9', '9', '9', '2', '4', '7', '3', '0', '4', '6', '5', '7', '7', '0', '3', '3', '6', '6', '2', '1', '3', '6', '1', '1', '8', '1', '1'])
noncomputable def fragment0166763Acc00700 : List (String × SourceJson) := (fragment0166763Field006Key00, fragment0166763Field006Value00) :: fragment0166763Acc00600
noncomputable def fragment0166763Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '1', '4', '6', '5', '3', '4', '0', '5', '3', '6', '7', '5', '3', '9', '2', '5', '3', '5', '4', '1', '3', '1', '8', '5', '9', '1', '3', '8', '0', '2', '7', '9', '8', '2', '6', '4', '0', '9', '5', '8', '6', '6', '8', '8', '0', '0', '0', '0', '/', '1', '1', '7', '8', '8', '8', '6', '4', '8', '2', '1', '5', '7', '2', '5', '0', '7', '9', '5', '7', '5', '1', '1', '5', '0', '2', '9', '7', '1', '9', '0', '9', '2', '4', '5', '7', '4', '1', '1', '0', '9', '9', '9', '2', '4', '7', '3', '0', '4', '6', '5', '7', '7', '0', '3', '3', '6', '6', '2', '1', '3', '6', '1', '1', '8', '1', '1', '"', ',']

theorem object_fragment0166763_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0166763Field006Chars00 ++ tail)) fragment0166763Acc00600 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0166763Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_006"
  err.flush

noncomputable def fragment0166763Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0166763Field007Value00 : SourceJson := .str (String.ofList ['2', '5', '2', '2', '8', '1', '6', '0', '4', '1', '0', '3', '7', '8', '4', '5', '4', '4', '6', '1', '6', '8', '6', '7', '0', '2', '6', '4', '4', '7', '1', '0', '9', '2', '3', '4', '7', '9', '4', '2', '7', '9', '4', '8', '0', '3', '3', '3', '3', '8', '1', '2', '5', '5', '0', '6', '2', '8', '0', '0', '8', '7', '5', '2', '1', '7', '2', '1', '3', '1', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '3', '6', '8', '5', '4', '0', '4', '5', '3', '2', '3', '6', '6', '5', '2', '5', '1', '2', '7', '1', '5', '3', '1', '6', '4', '9', '6', '2', '5', '3', '5', '4', '1', '7', '7', '7', '3', '3', '9', '3', '4', '0', '3', '4', '0', '0', '1', '8', '3', '8', '9', '0', '3', '6', '1', '7', '4', '4', '2', '6', '0', '9', '1', '7', '9', '4', '1', '6', '8', '8', '2', '1', '9', '5', '1', '2', '0', '8', '2', '9', '6', '6', '4', '8', '5', '3', '2', '0', '2', '3', '3', '3', '6', '8', '4', '3', '7', '3', '5', '0', '5', '1', '6', '0', '7', '4', '3', '9', '4', '3'])
noncomputable def fragment0166763Acc00800 : List (String × SourceJson) := (fragment0166763Field007Key00, fragment0166763Field007Value00) :: fragment0166763Acc00700
noncomputable def fragment0166763Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '5', '2', '2', '8', '1', '6', '0', '4', '1', '0', '3', '7', '8', '4', '5', '4', '4', '6', '1', '6', '8', '6', '7', '0', '2', '6', '4', '4', '7', '1', '0', '9', '2', '3', '4', '7', '9', '4', '2', '7', '9', '4', '8', '0', '3', '3', '3', '3', '8', '1', '2', '5', '5', '0', '6', '2', '8', '0', '0', '8', '7', '5', '2', '1', '7', '2', '1', '3', '1', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '3', '6', '8', '5', '4', '0', '4', '5', '3', '2', '3', '6', '6', '5', '2', '5', '1', '2', '7', '1', '5', '3', '1', '6', '4', '9', '6', '2', '5', '3', '5', '4', '1', '7', '7', '7', '3', '3', '9', '3', '4', '0', '3', '4', '0', '0', '1', '8', '3', '8', '9', '0', '3', '6', '1', '7', '4', '4', '2', '6', '0', '9', '1', '7', '9', '4', '1', '6', '8', '8', '2', '1', '9', '5', '1', '2', '0', '8', '2', '9', '6', '6', '4', '8', '5', '3', '2', '0', '2', '3', '3', '3', '6', '8', '4', '3', '7', '3', '5', '0', '5', '1', '6', '0', '7', '4', '3', '9', '4', '3', '"', ',']

theorem object_fragment0166763_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0166763Field007Chars00 ++ tail)) fragment0166763Acc00700 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0166763Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_007"
  err.flush

noncomputable def fragment0166763Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0166763Field008Value00 : SourceJson := .str (String.ofList ['3', '4', '5', '8', '7', '7', '6', '0', '7', '8', '6', '2'])
noncomputable def fragment0166763Acc00900 : List (String × SourceJson) := (fragment0166763Field008Key00, fragment0166763Field008Value00) :: fragment0166763Acc00800
noncomputable def fragment0166763Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '5', '8', '7', '7', '6', '0', '7', '8', '6', '2', '"', ',']

theorem object_fragment0166763_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0166763Field008Chars00 ++ tail)) fragment0166763Acc00800 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0166763Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_008"
  err.flush

noncomputable def fragment0166763Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0166763Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '1', '9', '7', '2', '8', '5', '1', '9', '3', '2'])
noncomputable def fragment0166763Acc01000 : List (String × SourceJson) := (fragment0166763Field009Key00, fragment0166763Field009Value00) :: fragment0166763Acc00900
noncomputable def fragment0166763Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '3', '1', '9', '7', '2', '8', '5', '1', '9', '3', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0166763_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0166763Field009Chars00 ++ tail)) fragment0166763Acc00900 =
      .ok (.obj (fragment0166763Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166763_object_field_009"
  err.flush

noncomputable def fragment0166763Chars : List Char := '{' :: (fragment0166763Field000Chars00 ++ fragment0166763Field001Chars00 ++ fragment0166763Field002Chars00 ++ fragment0166763Field003Chars00 ++ fragment0166763Field004Chars00 ++ fragment0166763Field005Chars00 ++ fragment0166763Field006Chars00 ++ fragment0166763Field007Chars00 ++ fragment0166763Field008Chars00 ++ fragment0166763Field009Chars00)
noncomputable def fragment0166763Value : SourceJson := .obj (fragment0166763Acc01000.reverse)

theorem value_fragment0166763 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 219) (fragment0166763Chars ++ tail) =
      .ok (fragment0166763Value, tail) := by
  have hinput : fragment0166763Chars ++ tail = '{' :: (fragment0166763Field000Chars00 ++ (fragment0166763Field001Chars00 ++ (fragment0166763Field002Chars00 ++ (fragment0166763Field003Chars00 ++ (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0166763Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 219) (fragment0166763Chars ++ tail) =
        SourceJson.value (fuel + 219) ('{' :: (fragment0166763Field000Chars00 ++ (fragment0166763Field001Chars00 ++ (fragment0166763Field002Chars00 ++ (fragment0166763Field003Chars00 ++ (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 219)) hinput
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0166763Field000Chars00 ++ (fragment0166763Field001Chars00 ++ (fragment0166763Field002Chars00 ++ (fragment0166763Field003Chars00 ++ (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))))))))))) fragment0166763Acc00000 := by rfl
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0166763Field001Chars00 ++ (fragment0166763Field002Chars00 ++ (fragment0166763Field003Chars00 ++ (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail))))))))))) fragment0166763Acc00100 := object_fragment0166763_field_000 fuel (fragment0166763Field001Chars00 ++ (fragment0166763Field002Chars00 ++ (fragment0166763Field003Chars00 ++ (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0166763Field002Chars00 ++ (fragment0166763Field003Chars00 ++ (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))))))))) fragment0166763Acc00200 := object_fragment0166763_field_001 fuel (fragment0166763Field002Chars00 ++ (fragment0166763Field003Chars00 ++ (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0166763Field003Chars00 ++ (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail))))))))) fragment0166763Acc00300 := object_fragment0166763_field_002 fuel (fragment0166763Field003Chars00 ++ (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))))))) fragment0166763Acc00400 := object_fragment0166763_field_003 fuel (fragment0166763Field004Chars00 ++ (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail))))))) fragment0166763Acc00500 := object_fragment0166763_field_004 fuel (fragment0166763Field005Chars00 ++ (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))))) fragment0166763Acc00600 := object_fragment0166763_field_005 fuel (fragment0166763Field006Chars00 ++ (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail))))) fragment0166763Acc00700 := object_fragment0166763_field_006 fuel (fragment0166763Field007Chars00 ++ (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))) fragment0166763Acc00800 := object_fragment0166763_field_007 fuel (fragment0166763Field008Chars00 ++ (fragment0166763Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0166763Field009Chars00 ++ (tail))) fragment0166763Acc00900 := object_fragment0166763_field_008 fuel (fragment0166763Field009Chars00 ++ (tail))
    _ = .ok (fragment0166763Value, tail) := object_fragment0166763_field_009 fuel (tail)

noncomputable def fragment0168329Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0168329Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0168329Field000Value00 : SourceJson := .number (String.ofList ['3', '7'])
noncomputable def fragment0168329Acc00100 : List (String × SourceJson) := (fragment0168329Field000Key00, fragment0168329Field000Value00) :: fragment0168329Acc00000
noncomputable def fragment0168329Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '7', ',']

theorem object_fragment0168329_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 409) (SourceJson.white (fragment0168329Field000Chars00 ++ tail)) fragment0168329Acc00000 =
      SourceJson.object (fuel + 408) (SourceJson.white tail) fragment0168329Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_000"
  err.flush

noncomputable def fragment0168329Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0168329Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['4'])]
noncomputable def fragment0168329Acc00200 : List (String × SourceJson) := (fragment0168329Field001Key00, fragment0168329Field001Value00) :: fragment0168329Acc00100
noncomputable def fragment0168329Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0168329_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 408) (SourceJson.white (fragment0168329Field001Chars00 ++ tail)) fragment0168329Acc00100 =
      SourceJson.object (fuel + 407) (SourceJson.white tail) fragment0168329Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_001"
  err.flush

noncomputable def fragment0168329Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0168329Field002Value00 : SourceJson := .str (String.ofList ['3', '9', '8', '8', '6', '0', '9', '4', '3', '5', '8', '8', '6', '9', '9', '3', '5', '3', '1', '3', '0', '3', '8', '1', '3', '4', '3', '4', '3', '/', '1', '0', '1', '3', '8', '3', '3', '4', '7', '9', '3', '0', '9', '0', '8', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0168329Acc00300 : List (String × SourceJson) := (fragment0168329Field002Key00, fragment0168329Field002Value00) :: fragment0168329Acc00200
noncomputable def fragment0168329Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '9', '8', '8', '6', '0', '9', '4', '3', '5', '8', '8', '6', '9', '9', '3', '5', '3', '1', '3', '0', '3', '8', '1', '3', '4', '3', '4', '3', '/', '1', '0', '1', '3', '8', '3', '3', '4', '7', '9', '3', '0', '9', '0', '8', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0168329_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0168329Field002Chars00 ++ tail)) fragment0168329Acc00200 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0168329Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_002"
  err.flush

noncomputable def fragment0168329Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0168329Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '8', '7', '1', '0', '3', '7', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0168329Acc00400 : List (String × SourceJson) := (fragment0168329Field003Key00, fragment0168329Field003Value00) :: fragment0168329Acc00300
noncomputable def fragment0168329Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '8', '7', '1', '0', '3', '7', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0168329_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0168329Field003Chars00 ++ tail)) fragment0168329Acc00300 =
      SourceJson.object (fuel + 405) (SourceJson.white tail) fragment0168329Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_003"
  err.flush

noncomputable def fragment0168329Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0168329Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0168329Acc00500 : List (String × SourceJson) := (fragment0168329Field004Key00, fragment0168329Field004Value00) :: fragment0168329Acc00400
noncomputable def fragment0168329Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '9', '3', '7', '9', '/', '2', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '6', '8', '6', '3', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '0', '6', '2', '1', '/', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '5', '9', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '1', '8', '6', '3', '/', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0168329_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0168329Field004Chars00 ++ tail)) fragment0168329Acc00400 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0168329Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_004"
  err.flush

noncomputable def fragment0168329Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0168329Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '0', '1', '6', '9', '4', '7', '3', '0', '2', '4', '9', '6', '7', '9', '3', '4', '6', '4', '3', '8', '7', '/', '1', '5', '1', '2', '8', '4', '3', '2', '7', '7', '2', '3', '4', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '6', '7', '3', '3', '8', '3', '3', '6', '9', '8', '2', '2', '6', '7', '4', '4', '3', '/', '1', '8', '9', '1', '0', '5', '4', '0', '9', '6', '5', '4', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '7', '3', '9', '5', '6', '8', '5', '6', '0', '1', '9', '8', '2', '5', '3', '2', '0', '1', '5', '3', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '4', '4', '5', '9', '6', '5', '0', '3', '4', '5', '6', '7', '5', '2', '3', '9', '1', '3', '9', '/', '5', '4', '0', '3', '0', '1', '1', '7', '0', '4', '4', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '4', '8', '6', '1', '8', '2', '9', '5', '7', '1', '3', '3', '4', '2', '0', '8', '6', '7', '3', '/', '5', '4', '0', '3', '0', '1', '1', '7', '0', '4', '4', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '7', '2', '2', '0', '2', '2', '6', '4', '5', '3', '4', '5', '5', '0', '9', '3', '7', '9', '7', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '4', '8', '8', '3', '6', '6', '3', '4', '9', '1', '7', '0', '0', '8', '6', '0', '7', '1', '/', '4', '4', '4', '9', '5', '3', '9', '0', '5', '0', '6', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '0', '9', '6', '0', '5', '5', '1', '9', '0', '3', '9', '0', '8', '6', '3', '8', '0', '4', '1', '/', '2', '5', '2', '1', '4', '0', '5', '4', '6', '2', '0', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '7', '2', '5', '9', '8', '9', '2', '3', '8', '1', '0', '3', '5', '1', '3', '2', '7', '6', '1', '/', '2', '5', '2', '1', '4', '0', '5', '4', '6', '2', '0', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '6', '6', '7', '2', '0', '3', '6', '6', '4', '2', '2', '6', '3', '3', '4', '1', '1', '4', '7', '/', '6', '3', '0', '3', '5', '1', '3', '6', '5', '5', '1', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0168329Acc00600 : List (String × SourceJson) := (fragment0168329Field005Key00, fragment0168329Field005Value00) :: fragment0168329Acc00500
noncomputable def fragment0168329Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '1', '6', '9', '4', '7', '3', '0', '2', '4', '9', '6', '7', '9', '3', '4', '6', '4', '3', '8', '7', '/', '1', '5', '1', '2', '8', '4', '3', '2', '7', '7', '2', '3', '4', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '6', '7', '3', '3', '8', '3', '3', '6', '9', '8', '2', '2', '6', '7', '4', '4', '3', '/', '1', '8', '9', '1', '0', '5', '4', '0', '9', '6', '5', '4', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '7', '3', '9', '5', '6', '8', '5', '6', '0', '1', '9', '8', '2', '5', '3', '2', '0', '1', '5', '3', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '4', '4', '5', '9', '6', '5', '0', '3', '4', '5', '6', '7', '5', '2', '3', '9', '1', '3', '9', '/', '5', '4', '0', '3', '0', '1', '1', '7', '0', '4', '4', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '4', '8', '6', '1', '8', '2', '9', '5', '7', '1', '3', '3', '4', '2', '0', '8', '6', '7', '3', '/', '5', '4', '0', '3', '0', '1', '1', '7', '0', '4', '4', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '7', '2', '2', '0', '2', '2', '6', '4', '5', '3', '4', '5', '5', '0', '9', '3', '7', '9', '7', '/', '7', '5', '6', '4', '2', '1', '6', '3', '8', '6', '1', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '4', '8', '8', '3', '6', '6', '3', '4', '9', '1', '7', '0', '0', '8', '6', '0', '7', '1', '/', '4', '4', '4', '9', '5', '3', '9', '0', '5', '0', '6', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '0', '9', '6', '0', '5', '5', '1', '9', '0', '3', '9', '0', '8', '6', '3', '8', '0', '4', '1', '/', '2', '5', '2', '1', '4', '0', '5', '4', '6', '2', '0', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '7', '2', '5', '9', '8', '9', '2', '3', '8', '1', '0', '3', '5', '1', '3', '2', '7', '6', '1', '/', '2', '5', '2', '1', '4', '0', '5', '4', '6', '2', '0', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '6', '7', '2', '0', '3', '6', '6', '4', '2', '2', '6', '3', '3', '4', '1', '1', '4', '7', '/', '6', '3', '0', '3', '5', '1', '3', '6', '5', '5', '1', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0168329_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0168329Field005Chars00 ++ tail)) fragment0168329Acc00500 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0168329Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_005"
  err.flush

noncomputable def fragment0168329Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0168329Field006Value00 : SourceJson := .str (String.ofList ['5', '2', '9', '4', '1', '1', '7', '1', '7', '6', '9', '1', '1', '3', '8', '2', '7', '0', '3', '1', '8', '3', '8', '9', '5', '6', '4', '4', '8', '3', '2', '5', '6', '5', '0', '3', '5', '1', '9', '4', '7', '2', '3', '7', '0', '3', '1', '9', '3', '6', '0', '0', '/', '9', '0', '0', '1', '9', '0', '2', '4', '8', '6', '0', '3', '8', '9', '7', '0', '2', '8', '1', '8', '7', '7', '1', '3', '1', '1', '1', '8', '2', '2', '1', '4', '8', '3', '5', '1', '4', '2', '2', '6', '7', '7', '8', '0', '6', '6', '7', '6', '2', '9', '5', '2', '3', '0', '7', '1', '9', '9', '2', '9', '9', '8', '5', '5', '0', '2', '5', '4', '9'])
noncomputable def fragment0168329Acc00700 : List (String × SourceJson) := (fragment0168329Field006Key00, fragment0168329Field006Value00) :: fragment0168329Acc00600
noncomputable def fragment0168329Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '2', '9', '4', '1', '1', '7', '1', '7', '6', '9', '1', '1', '3', '8', '2', '7', '0', '3', '1', '8', '3', '8', '9', '5', '6', '4', '4', '8', '3', '2', '5', '6', '5', '0', '3', '5', '1', '9', '4', '7', '2', '3', '7', '0', '3', '1', '9', '3', '6', '0', '0', '/', '9', '0', '0', '1', '9', '0', '2', '4', '8', '6', '0', '3', '8', '9', '7', '0', '2', '8', '1', '8', '7', '7', '1', '3', '1', '1', '1', '8', '2', '2', '1', '4', '8', '3', '5', '1', '4', '2', '2', '6', '7', '7', '8', '0', '6', '6', '7', '6', '2', '9', '5', '2', '3', '0', '7', '1', '9', '9', '2', '9', '9', '8', '5', '5', '0', '2', '5', '4', '9', '"', ',']

theorem object_fragment0168329_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0168329Field006Chars00 ++ tail)) fragment0168329Acc00600 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0168329Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_006"
  err.flush

noncomputable def fragment0168329Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0168329Field007Value00 : SourceJson := .str (String.ofList ['1', '3', '1', '7', '8', '3', '2', '8', '5', '8', '1', '6', '3', '5', '7', '2', '4', '2', '4', '6', '1', '9', '1', '3', '7', '1', '6', '2', '9', '7', '6', '2', '1', '4', '0', '6', '8', '4', '3', '7', '1', '4', '4', '0', '3', '0', '4', '5', '6', '2', '1', '6', '3', '2', '7', '3', '8', '3', '6', '0', '8', '6', '0', '6', '7', '2', '1', '2', '0', '9', '2', '2', '6', '5', '9', '2', '7', '0', '5', '3', '1', '7', '5', '5', '5', '0', '6', '9', '2', '3', '2', '2', '0', '0', '8', '1', '6', '3', '9', '1', '0', '9', '8', '2', '6', '2', '2', '3', '0', '7', '4', '3', '8', '4', '4', '0', '8', '8', '8', '8', '7', '3', '2', '7', '5', '4', '6', '3', '7', '3', '9', '6', '1', '3', '8', '9', '3', '8', '4', '7', '4', '7', '1', '9', '0', '4', '4', '2', '2', '9', '3', '1', '9', '0', '4', '7', '9', '3', '1', '2', '7', '0', '2', '5', '6', '3', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '1', '1', '3', '4', '0', '5', '2', '5', '5', '4', '9', '4', '0', '5', '4', '1', '7', '8', '2', '3', '0', '1', '8', '7', '9', '8', '6', '8', '8', '5', '0', '0', '3', '0', '8', '8', '5', '9', '3', '0', '7', '6', '8', '9', '2', '1', '9', '1', '7', '8', '3', '6', '0', '8', '9', '3', '2', '0', '8', '3', '2', '0', '8', '0', '5', '9', '4', '1', '2', '7', '0', '5', '1', '7', '9', '8', '5', '7', '0', '6', '4', '9', '0', '7', '3', '0', '3', '0', '5', '6', '9', '7', '6', '7', '3', '1', '2', '5', '5', '7', '9', '9', '5', '0', '9', '1', '9', '3', '2', '7', '3', '9', '3', '4', '9', '7', '6', '5', '0', '7', '9', '9', '9', '0', '6', '6', '8', '9', '1', '9', '2', '2', '1', '3', '2', '4', '4', '1', '0', '2', '3', '2', '7', '2', '4', '5', '2', '3', '1', '3', '2', '0', '6', '3', '3', '1', '0', '9', '6', '6', '8', '7', '4', '0', '5', '3', '4', '0', '9', '1', '5', '7', '2', '7', '3', '5', '6', '7', '4', '6', '8', '1', '7', '7', '8', '1', '4', '2', '6', '9', '6', '8', '3', '8', '7', '9', '7', '9', '4', '9', '1', '3', '0', '6', '8', '1'])
noncomputable def fragment0168329Acc00800 : List (String × SourceJson) := (fragment0168329Field007Key00, fragment0168329Field007Value00) :: fragment0168329Acc00700
noncomputable def fragment0168329Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '1', '7', '8', '3', '2', '8', '5', '8', '1', '6', '3', '5', '7', '2', '4', '2', '4', '6', '1', '9', '1', '3', '7', '1', '6', '2', '9', '7', '6', '2', '1', '4', '0', '6', '8', '4', '3', '7', '1', '4', '4', '0', '3', '0', '4', '5', '6', '2', '1', '6', '3', '2', '7', '3', '8', '3', '6', '0', '8', '6', '0', '6', '7', '2', '1', '2', '0', '9', '2', '2', '6', '5', '9', '2', '7', '0', '5', '3', '1', '7', '5', '5', '5', '0', '6', '9', '2', '3', '2', '2', '0', '0', '8', '1', '6', '3', '9', '1', '0', '9', '8', '2', '6', '2', '2', '3', '0', '7', '4', '3', '8', '4', '4', '0', '8', '8', '8', '8', '7', '3', '2', '7', '5', '4', '6', '3', '7', '3', '9', '6', '1', '3', '8', '9', '3', '8', '4', '7', '4', '7', '1', '9', '0', '4', '4', '2', '2', '9', '3', '1', '9', '0', '4', '7', '9', '3', '1', '2', '7', '0', '2', '5', '6', '3', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '1', '1', '3', '4', '0', '5', '2', '5', '5', '4', '9', '4', '0', '5', '4', '1', '7', '8', '2', '3', '0', '1', '8', '7', '9', '8', '6', '8', '8', '5', '0', '0', '3', '0', '8', '8', '5', '9', '3', '0', '7', '6', '8', '9', '2', '1', '9', '1', '7', '8', '3', '6', '0', '8', '9', '3', '2', '0', '8', '3', '2', '0', '8', '0', '5', '9', '4', '1', '2', '7', '0', '5', '1', '7', '9', '8', '5', '7', '0', '6', '4', '9', '0', '7', '3', '0', '3', '0', '5', '6', '9', '7', '6', '7', '3', '1', '2', '5', '5', '7', '9', '9', '5', '0', '9', '1', '9', '3', '2', '7', '3', '9', '3', '4', '9', '7', '6', '5', '0', '7', '9', '9', '9', '0', '6', '6', '8', '9', '1', '9', '2', '2', '1', '3', '2', '4', '4', '1', '0', '2', '3', '2', '7', '2', '4', '5', '2', '3', '1', '3', '2', '0', '6', '3', '3', '1', '0', '9', '6', '6', '8', '7', '4', '0', '5', '3', '4', '0', '9', '1', '5', '7', '2', '7', '3', '5', '6', '7', '4', '6', '8', '1', '7', '7', '8', '1', '4', '2', '6', '9', '6', '8', '3', '8', '7', '9', '7', '9', '4', '9', '1', '3', '0', '6', '8', '1', '"', ',']

theorem object_fragment0168329_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0168329Field007Chars00 ++ tail)) fragment0168329Acc00700 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0168329Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_007"
  err.flush

noncomputable def fragment0168329Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0168329Field008Value00 : SourceJson := .str (String.ofList ['4', '6', '5', '9', '4', '9', '4', '7', '7', '5', '8', '2'])
noncomputable def fragment0168329Acc00900 : List (String × SourceJson) := (fragment0168329Field008Key00, fragment0168329Field008Value00) :: fragment0168329Acc00800
noncomputable def fragment0168329Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '5', '9', '4', '9', '4', '7', '7', '5', '8', '2', '"', ',']

theorem object_fragment0168329_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0168329Field008Chars00 ++ tail)) fragment0168329Acc00800 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0168329Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_008"
  err.flush

noncomputable def fragment0168329Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0168329Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '4', '5', '6', '6', '9', '1', '8', '6', '5', '0', '1'])
noncomputable def fragment0168329Acc01000 : List (String × SourceJson) := (fragment0168329Field009Key00, fragment0168329Field009Value00) :: fragment0168329Acc00900
noncomputable def fragment0168329Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '4', '5', '6', '6', '9', '1', '8', '6', '5', '0', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0168329_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0168329Field009Chars00 ++ tail)) fragment0168329Acc00900 =
      .ok (.obj (fragment0168329Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168329_object_field_009"
  err.flush

noncomputable def fragment0168329Chars : List Char := '{' :: (fragment0168329Field000Chars00 ++ fragment0168329Field001Chars00 ++ fragment0168329Field002Chars00 ++ fragment0168329Field003Chars00 ++ fragment0168329Field004Chars00 ++ fragment0168329Field005Chars00 ++ fragment0168329Field006Chars00 ++ fragment0168329Field007Chars00 ++ fragment0168329Field008Chars00 ++ fragment0168329Field009Chars00)
noncomputable def fragment0168329Value : SourceJson := .obj (fragment0168329Acc01000.reverse)

theorem value_fragment0168329 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 410) (fragment0168329Chars ++ tail) =
      .ok (fragment0168329Value, tail) := by
  have hinput : fragment0168329Chars ++ tail = '{' :: (fragment0168329Field000Chars00 ++ (fragment0168329Field001Chars00 ++ (fragment0168329Field002Chars00 ++ (fragment0168329Field003Chars00 ++ (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0168329Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 410) (fragment0168329Chars ++ tail) =
        SourceJson.value (fuel + 410) ('{' :: (fragment0168329Field000Chars00 ++ (fragment0168329Field001Chars00 ++ (fragment0168329Field002Chars00 ++ (fragment0168329Field003Chars00 ++ (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 410)) hinput
    _ = SourceJson.object (fuel + 409) (SourceJson.white (fragment0168329Field000Chars00 ++ (fragment0168329Field001Chars00 ++ (fragment0168329Field002Chars00 ++ (fragment0168329Field003Chars00 ++ (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))))))))))) fragment0168329Acc00000 := by rfl
    _ = SourceJson.object (fuel + 408) (SourceJson.white (fragment0168329Field001Chars00 ++ (fragment0168329Field002Chars00 ++ (fragment0168329Field003Chars00 ++ (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail))))))))))) fragment0168329Acc00100 := object_fragment0168329_field_000 fuel (fragment0168329Field001Chars00 ++ (fragment0168329Field002Chars00 ++ (fragment0168329Field003Chars00 ++ (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0168329Field002Chars00 ++ (fragment0168329Field003Chars00 ++ (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))))))))) fragment0168329Acc00200 := object_fragment0168329_field_001 fuel (fragment0168329Field002Chars00 ++ (fragment0168329Field003Chars00 ++ (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0168329Field003Chars00 ++ (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail))))))))) fragment0168329Acc00300 := object_fragment0168329_field_002 fuel (fragment0168329Field003Chars00 ++ (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))))))) fragment0168329Acc00400 := object_fragment0168329_field_003 fuel (fragment0168329Field004Chars00 ++ (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail))))))) fragment0168329Acc00500 := object_fragment0168329_field_004 fuel (fragment0168329Field005Chars00 ++ (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))))) fragment0168329Acc00600 := object_fragment0168329_field_005 fuel (fragment0168329Field006Chars00 ++ (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail))))) fragment0168329Acc00700 := object_fragment0168329_field_006 fuel (fragment0168329Field007Chars00 ++ (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))) fragment0168329Acc00800 := object_fragment0168329_field_007 fuel (fragment0168329Field008Chars00 ++ (fragment0168329Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0168329Field009Chars00 ++ (tail))) fragment0168329Acc00900 := object_fragment0168329_field_008 fuel (fragment0168329Field009Chars00 ++ (tail))
    _ = .ok (fragment0168329Value, tail) := object_fragment0168329_field_009 fuel (tail)

noncomputable def fragment0170276Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0170276Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0170276Field000Value00 : SourceJson := .number (String.ofList ['3', '8'])
noncomputable def fragment0170276Acc00100 : List (String × SourceJson) := (fragment0170276Field000Key00, fragment0170276Field000Value00) :: fragment0170276Acc00000
noncomputable def fragment0170276Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '8', ',']

theorem object_fragment0170276_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 264) (SourceJson.white (fragment0170276Field000Chars00 ++ tail)) fragment0170276Acc00000 =
      SourceJson.object (fuel + 263) (SourceJson.white tail) fragment0170276Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_000"
  err.flush

noncomputable def fragment0170276Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0170276Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0170276Acc00200 : List (String × SourceJson) := (fragment0170276Field001Key00, fragment0170276Field001Value00) :: fragment0170276Acc00100
noncomputable def fragment0170276Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0170276_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0170276Field001Chars00 ++ tail)) fragment0170276Acc00100 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0170276Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_001"
  err.flush

noncomputable def fragment0170276Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0170276Field002Value00 : SourceJson := .str (String.ofList ['8', '0', '2', '3', '5', '6', '8', '7', '0', '9', '0', '6', '9', '3', '2', '6', '1', '3', '1', '4', '6', '6', '4', '7', '4', '6', '6', '9', '1', '9', '1', '6', '6', '1', '3', '5', '5', '2', '8', '7', '3', '/', '5', '5', '2', '5', '9', '0', '8', '8', '9', '2', '7', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0170276Acc00300 : List (String × SourceJson) := (fragment0170276Field002Key00, fragment0170276Field002Value00) :: fragment0170276Acc00200
noncomputable def fragment0170276Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '0', '2', '3', '5', '6', '8', '7', '0', '9', '0', '6', '9', '3', '2', '6', '1', '3', '1', '4', '6', '6', '4', '7', '4', '6', '6', '9', '1', '9', '1', '6', '6', '1', '3', '5', '5', '2', '8', '7', '3', '/', '5', '5', '2', '5', '9', '0', '8', '8', '9', '2', '7', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0170276_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0170276Field002Chars00 ++ tail)) fragment0170276Acc00200 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0170276Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_002"
  err.flush

noncomputable def fragment0170276Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0170276Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0170276Acc00400 : List (String × SourceJson) := (fragment0170276Field003Key00, fragment0170276Field003Value00) :: fragment0170276Acc00300
noncomputable def fragment0170276Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0170276_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0170276Field003Chars00 ++ tail)) fragment0170276Acc00300 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0170276Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_003"
  err.flush

noncomputable def fragment0170276Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0170276Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0170276Acc00500 : List (String × SourceJson) := (fragment0170276Field004Key00, fragment0170276Field004Value00) :: fragment0170276Acc00400
noncomputable def fragment0170276Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '2', '1', '/', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0170276_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0170276Field004Chars00 ++ tail)) fragment0170276Acc00400 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0170276Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_004"
  err.flush

noncomputable def fragment0170276Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0170276Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '7', '4', '4', '0', '6', '9', '5', '1', '2', '3', '3', '7', '6', '7', '/', '4', '1', '7', '7', '7', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '3', '4', '2', '5', '6', '8', '9', '6', '4', '6', '7', '/', '2', '6', '1', '1', '0', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '6', '7', '4', '1', '1', '6', '7', '2', '2', '9', '7', '/', '2', '7', '8', '5', '1', '7', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '9', '1', '4', '7', '6', '9', '9', '6', '6', '3', '3', '/', '5', '8', '0', '2', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '5', '9', '5', '3', '1', '5', '1', '2', '6', '0', '9', '/', '4', '3', '5', '1', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '3', '9', '4', '1', '0', '4', '2', '5', '9', '1', '/', '3', '4', '8', '1', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '6', '3', '3', '0', '2', '0', '1', '6', '1', '4', '2', '1', '/', '6', '9', '6', '2', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '5', '8', '3', '3', '6', '3', '9', '3', '7', '4', '7', '/', '2', '0', '8', '8', '8', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '2', '2', '3', '4', '3', '3', '6', '2', '2', '2', '2', '7', '/', '2', '0', '8', '8', '8', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '7', '5', '3', '3', '5', '0', '1', '7', '0', '8', '3', '/', '8', '7', '0', '3', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0170276Acc00600 : List (String × SourceJson) := (fragment0170276Field005Key00, fragment0170276Field005Value00) :: fragment0170276Acc00500
noncomputable def fragment0170276Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '4', '0', '6', '9', '5', '1', '2', '3', '3', '7', '6', '7', '/', '4', '1', '7', '7', '7', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '3', '4', '2', '5', '6', '8', '9', '6', '4', '6', '7', '/', '2', '6', '1', '1', '0', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '7', '4', '1', '1', '6', '7', '2', '2', '9', '7', '/', '2', '7', '8', '5', '1', '7', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '9', '1', '4', '7', '6', '9', '9', '6', '6', '3', '3', '/', '5', '8', '0', '2', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '9', '5', '3', '1', '5', '1', '2', '6', '0', '9', '/', '4', '3', '5', '1', '8', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '3', '9', '4', '1', '0', '4', '2', '5', '9', '1', '/', '3', '4', '8', '1', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '3', '3', '0', '2', '0', '1', '6', '1', '4', '2', '1', '/', '6', '9', '6', '2', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '3', '5', '8', '3', '3', '6', '3', '9', '3', '7', '4', '7', '/', '2', '0', '8', '8', '8', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '2', '2', '3', '4', '3', '3', '6', '2', '2', '2', '2', '7', '/', '2', '0', '8', '8', '8', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '5', '3', '3', '5', '0', '1', '7', '0', '8', '3', '/', '8', '7', '0', '3', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0170276_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0170276Field005Chars00 ++ tail)) fragment0170276Acc00500 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0170276Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_005"
  err.flush

noncomputable def fragment0170276Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0170276Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '1', '4', '0', '3', '8', '3', '6', '2', '6', '8', '5', '9', '0', '5', '8', '8', '7', '3', '1', '3', '5', '9', '0', '4', '6', '5', '2', '8', '5', '0', '0', '9', '1', '9', '9', '6', '2', '6', '4', '9', '5', '9', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '/', '3', '5', '2', '0', '6', '4', '4', '3', '6', '0', '1', '6', '2', '6', '6', '7', '4', '3', '4', '9', '4', '5', '0', '2', '4', '4', '8', '4', '5', '5', '6', '2', '9', '9', '7', '6', '6', '4', '9', '5', '0', '4', '9', '3', '1', '1', '9', '9', '9', '7', '0', '7', '4', '8', '6', '5', '7', '0', '6', '4', '1', '4', '0', '5', '9', '2', '1'])
noncomputable def fragment0170276Acc00700 : List (String × SourceJson) := (fragment0170276Field006Key00, fragment0170276Field006Value00) :: fragment0170276Acc00600
noncomputable def fragment0170276Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '1', '4', '0', '3', '8', '3', '6', '2', '6', '8', '5', '9', '0', '5', '8', '8', '7', '3', '1', '3', '5', '9', '0', '4', '6', '5', '2', '8', '5', '0', '0', '9', '1', '9', '9', '6', '2', '6', '4', '9', '5', '9', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '/', '3', '5', '2', '0', '6', '4', '4', '3', '6', '0', '1', '6', '2', '6', '6', '7', '4', '3', '4', '9', '4', '5', '0', '2', '4', '4', '8', '4', '5', '5', '6', '2', '9', '9', '7', '6', '6', '4', '9', '5', '0', '4', '9', '3', '1', '1', '9', '9', '9', '7', '0', '7', '4', '8', '6', '5', '7', '0', '6', '4', '1', '4', '0', '5', '9', '2', '1', '"', ',']

theorem object_fragment0170276_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0170276Field006Chars00 ++ tail)) fragment0170276Acc00600 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0170276Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_006"
  err.flush

noncomputable def fragment0170276Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0170276Field007Value00 : SourceJson := .str (String.ofList ['3', '5', '0', '3', '9', '7', '6', '8', '9', '8', '3', '8', '5', '1', '6', '3', '5', '4', '1', '5', '8', '8', '4', '4', '5', '3', '1', '4', '1', '5', '3', '1', '9', '8', '3', '1', '7', '4', '9', '2', '9', '3', '0', '6', '7', '6', '7', '5', '3', '8', '8', '9', '5', '6', '0', '9', '3', '0', '5', '6', '1', '1', '0', '9', '3', '7', '5', '7', '1', '0', '6', '0', '0', '9', '7', '5', '9', '5', '7', '0', '3', '3', '7', '7', '8', '1', '7', '0', '2', '5', '5', '4', '7', '4', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '3', '3', '1', '6', '2', '2', '7', '9', '0', '5', '1', '2', '2', '5', '2', '3', '1', '0', '4', '1', '1', '9', '5', '7', '7', '9', '2', '2', '1', '4', '2', '1', '5', '4', '3', '1', '5', '8', '4', '7', '7', '5', '8', '0', '7', '8', '4', '1', '6', '8', '7', '6', '7', '6', '2', '5', '3', '7', '9', '5', '9', '8', '2', '0', '2', '3', '1', '6', '6', '9', '6', '4', '3', '0', '8', '4', '1', '1', '7', '7', '5', '4', '9', '2', '0', '7', '5', '5', '0', '5', '3', '8', '4', '3', '5', '7', '2', '6', '3', '7', '7', '9', '9', '1', '1', '5', '9', '5', '3', '2', '2', '4', '6', '2', '5', '4', '5', '7', '7', '7', '1', '2', '5', '0', '3', '3', '6', '3', '9', '1'])
noncomputable def fragment0170276Acc00800 : List (String × SourceJson) := (fragment0170276Field007Key00, fragment0170276Field007Value00) :: fragment0170276Acc00700
noncomputable def fragment0170276Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '5', '0', '3', '9', '7', '6', '8', '9', '8', '3', '8', '5', '1', '6', '3', '5', '4', '1', '5', '8', '8', '4', '4', '5', '3', '1', '4', '1', '5', '3', '1', '9', '8', '3', '1', '7', '4', '9', '2', '9', '3', '0', '6', '7', '6', '7', '5', '3', '8', '8', '9', '5', '6', '0', '9', '3', '0', '5', '6', '1', '1', '0', '9', '3', '7', '5', '7', '1', '0', '6', '0', '0', '9', '7', '5', '9', '5', '7', '0', '3', '3', '7', '7', '8', '1', '7', '0', '2', '5', '5', '4', '7', '4', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '3', '3', '1', '6', '2', '2', '7', '9', '0', '5', '1', '2', '2', '5', '2', '3', '1', '0', '4', '1', '1', '9', '5', '7', '7', '9', '2', '2', '1', '4', '2', '1', '5', '4', '3', '1', '5', '8', '4', '7', '7', '5', '8', '0', '7', '8', '4', '1', '6', '8', '7', '6', '7', '6', '2', '5', '3', '7', '9', '5', '9', '8', '2', '0', '2', '3', '1', '6', '6', '9', '6', '4', '3', '0', '8', '4', '1', '1', '7', '7', '5', '4', '9', '2', '0', '7', '5', '5', '0', '5', '3', '8', '4', '3', '5', '7', '2', '6', '3', '7', '7', '9', '9', '1', '1', '5', '9', '5', '3', '2', '2', '4', '6', '2', '5', '4', '5', '7', '7', '7', '1', '2', '5', '0', '3', '3', '6', '3', '9', '1', '"', ',']

theorem object_fragment0170276_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0170276Field007Chars00 ++ tail)) fragment0170276Acc00700 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0170276Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_007"
  err.flush

noncomputable def fragment0170276Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0170276Field008Value00 : SourceJson := .str (String.ofList ['4', '3', '0', '7', '3', '2', '9', '1', '9', '7', '2', '7', '2', '5', '3', '4'])
noncomputable def fragment0170276Acc00900 : List (String × SourceJson) := (fragment0170276Field008Key00, fragment0170276Field008Value00) :: fragment0170276Acc00800
noncomputable def fragment0170276Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '0', '7', '3', '2', '9', '1', '9', '7', '2', '7', '2', '5', '3', '4', '"', ',']

theorem object_fragment0170276_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0170276Field008Chars00 ++ tail)) fragment0170276Acc00800 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0170276Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_008"
  err.flush

noncomputable def fragment0170276Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0170276Field009Value00 : SourceJson := .str (String.ofList ['1', '7', '7', '5', '7', '9', '9', '7', '1', '4', '7', '0', '9', '6', '4', '5', '8'])
noncomputable def fragment0170276Acc01000 : List (String × SourceJson) := (fragment0170276Field009Key00, fragment0170276Field009Value00) :: fragment0170276Acc00900
noncomputable def fragment0170276Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '7', '5', '7', '9', '9', '7', '1', '4', '7', '0', '9', '6', '4', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0170276_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0170276Field009Chars00 ++ tail)) fragment0170276Acc00900 =
      .ok (.obj (fragment0170276Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170276_object_field_009"
  err.flush

noncomputable def fragment0170276Chars : List Char := '{' :: (fragment0170276Field000Chars00 ++ fragment0170276Field001Chars00 ++ fragment0170276Field002Chars00 ++ fragment0170276Field003Chars00 ++ fragment0170276Field004Chars00 ++ fragment0170276Field005Chars00 ++ fragment0170276Field006Chars00 ++ fragment0170276Field007Chars00 ++ fragment0170276Field008Chars00 ++ fragment0170276Field009Chars00)
noncomputable def fragment0170276Value : SourceJson := .obj (fragment0170276Acc01000.reverse)

theorem value_fragment0170276 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 265) (fragment0170276Chars ++ tail) =
      .ok (fragment0170276Value, tail) := by
  have hinput : fragment0170276Chars ++ tail = '{' :: (fragment0170276Field000Chars00 ++ (fragment0170276Field001Chars00 ++ (fragment0170276Field002Chars00 ++ (fragment0170276Field003Chars00 ++ (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0170276Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 265) (fragment0170276Chars ++ tail) =
        SourceJson.value (fuel + 265) ('{' :: (fragment0170276Field000Chars00 ++ (fragment0170276Field001Chars00 ++ (fragment0170276Field002Chars00 ++ (fragment0170276Field003Chars00 ++ (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 265)) hinput
    _ = SourceJson.object (fuel + 264) (SourceJson.white (fragment0170276Field000Chars00 ++ (fragment0170276Field001Chars00 ++ (fragment0170276Field002Chars00 ++ (fragment0170276Field003Chars00 ++ (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))))))))))) fragment0170276Acc00000 := by rfl
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0170276Field001Chars00 ++ (fragment0170276Field002Chars00 ++ (fragment0170276Field003Chars00 ++ (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail))))))))))) fragment0170276Acc00100 := object_fragment0170276_field_000 fuel (fragment0170276Field001Chars00 ++ (fragment0170276Field002Chars00 ++ (fragment0170276Field003Chars00 ++ (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0170276Field002Chars00 ++ (fragment0170276Field003Chars00 ++ (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))))))))) fragment0170276Acc00200 := object_fragment0170276_field_001 fuel (fragment0170276Field002Chars00 ++ (fragment0170276Field003Chars00 ++ (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0170276Field003Chars00 ++ (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail))))))))) fragment0170276Acc00300 := object_fragment0170276_field_002 fuel (fragment0170276Field003Chars00 ++ (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))))))) fragment0170276Acc00400 := object_fragment0170276_field_003 fuel (fragment0170276Field004Chars00 ++ (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail))))))) fragment0170276Acc00500 := object_fragment0170276_field_004 fuel (fragment0170276Field005Chars00 ++ (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))))) fragment0170276Acc00600 := object_fragment0170276_field_005 fuel (fragment0170276Field006Chars00 ++ (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail))))) fragment0170276Acc00700 := object_fragment0170276_field_006 fuel (fragment0170276Field007Chars00 ++ (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))) fragment0170276Acc00800 := object_fragment0170276_field_007 fuel (fragment0170276Field008Chars00 ++ (fragment0170276Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0170276Field009Chars00 ++ (tail))) fragment0170276Acc00900 := object_fragment0170276_field_008 fuel (fragment0170276Field009Chars00 ++ (tail))
    _ = .ok (fragment0170276Value, tail) := object_fragment0170276_field_009 fuel (tail)

noncomputable def fragment0171938Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0171938Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0171938Field000Value00 : SourceJson := .number (String.ofList ['3', '9'])
noncomputable def fragment0171938Acc00100 : List (String × SourceJson) := (fragment0171938Field000Key00, fragment0171938Field000Value00) :: fragment0171938Acc00000
noncomputable def fragment0171938Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '9', ',']

theorem object_fragment0171938_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0171938Field000Chars00 ++ tail)) fragment0171938Acc00000 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0171938Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_000"
  err.flush

noncomputable def fragment0171938Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0171938Field001Value00 : SourceJson := .arr [.number (String.ofList ['2', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0171938Acc00200 : List (String × SourceJson) := (fragment0171938Field001Key00, fragment0171938Field001Value00) :: fragment0171938Acc00100
noncomputable def fragment0171938Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0171938_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0171938Field001Chars00 ++ tail)) fragment0171938Acc00100 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0171938Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_001"
  err.flush

noncomputable def fragment0171938Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0171938Field002Value00 : SourceJson := .str (String.ofList ['3', '3', '0', '1', '3', '5', '8', '3', '4', '7', '8', '7', '0', '3', '3', '8', '5', '0', '1', '3', '6', '9', '8', '7', '6', '9', '3', '0', '5', '1', '9', '9', '1', '5', '2', '9', '1', '2', '5', '1', '/', '2', '5', '1', '8', '3', '1', '7', '8', '5', '4', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0171938Acc00300 : List (String × SourceJson) := (fragment0171938Field002Key00, fragment0171938Field002Value00) :: fragment0171938Acc00200
noncomputable def fragment0171938Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '3', '0', '1', '3', '5', '8', '3', '4', '7', '8', '7', '0', '3', '3', '8', '5', '0', '1', '3', '6', '9', '8', '7', '6', '9', '3', '0', '5', '1', '9', '9', '1', '5', '2', '9', '1', '2', '5', '1', '/', '2', '5', '1', '8', '3', '1', '7', '8', '5', '4', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0171938_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0171938Field002Chars00 ++ tail)) fragment0171938Acc00200 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0171938Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_002"
  err.flush

noncomputable def fragment0171938Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0171938Field003Value00 : SourceJson := .str (String.ofList ['3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0171938Acc00400 : List (String × SourceJson) := (fragment0171938Field003Key00, fragment0171938Field003Value00) :: fragment0171938Acc00300
noncomputable def fragment0171938Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '2', '8', '0', '0', '9', '/', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0171938_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0171938Field003Chars00 ++ tail)) fragment0171938Acc00300 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0171938Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_003"
  err.flush

noncomputable def fragment0171938Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0171938Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0171938Acc00500 : List (String × SourceJson) := (fragment0171938Field004Key00, fragment0171938Field004Value00) :: fragment0171938Acc00400
noncomputable def fragment0171938Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '2', '7', '8', '8', '1', '/', '1', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '7', '9', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '3', '3', '3', '/', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '1', '0', '1', '/', '2', '6', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '2', '9', '9', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0171938_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0171938Field004Chars00 ++ tail)) fragment0171938Acc00400 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0171938Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_004"
  err.flush

noncomputable def fragment0171938Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0171938Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '3', '4', '1', '9', '9', '5', '5', '5', '7', '5', '6', '8', '1', '/', '5', '9', '6', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '5', '7', '8', '6', '4', '7', '1', '5', '5', '3', '1', '/', '3', '7', '3', '0', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '5', '8', '9', '7', '3', '7', '8', '9', '9', '8', '3', '/', '4', '6', '4', '1', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '1', '6', '7', '2', '4', '8', '5', '0', '9', '9', '3', '7', '/', '5', '2', '2', '2', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '8', '9', '0', '2', '4', '4', '7', '1', '1', '7', '3', '/', '8', '7', '0', '3', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '4', '5', '3', '0', '0', '3', '8', '7', '3', '/', '4', '6', '4', '1', '9', '5', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '9', '7', '2', '6', '4', '3', '6', '3', '6', '1', '0', '1', '/', '6', '9', '6', '2', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '6', '8', '1', '7', '2', '4', '0', '2', '5', '4', '1', '/', '2', '9', '8', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '0', '6', '0', '4', '3', '4', '3', '5', '1', '8', '1', '/', '2', '9', '8', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '5', '1', '8', '1', '4', '8', '8', '8', '5', '7', '/', '3', '7', '3', '0', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0171938Acc00600 : List (String × SourceJson) := (fragment0171938Field005Key00, fragment0171938Field005Value00) :: fragment0171938Acc00500
noncomputable def fragment0171938Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '1', '9', '9', '5', '5', '5', '7', '5', '6', '8', '1', '/', '5', '9', '6', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '5', '7', '8', '6', '4', '7', '1', '5', '5', '3', '1', '/', '3', '7', '3', '0', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '5', '8', '9', '7', '3', '7', '8', '9', '9', '8', '3', '/', '4', '6', '4', '1', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '1', '6', '7', '2', '4', '8', '5', '0', '9', '9', '3', '7', '/', '5', '2', '2', '2', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '8', '9', '0', '2', '4', '4', '7', '1', '1', '7', '3', '/', '8', '7', '0', '3', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '5', '3', '0', '0', '3', '8', '7', '3', '/', '4', '6', '4', '1', '9', '5', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '9', '7', '2', '6', '4', '3', '6', '3', '6', '1', '0', '1', '/', '6', '9', '6', '2', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '6', '8', '1', '7', '2', '4', '0', '2', '5', '4', '1', '/', '2', '9', '8', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '0', '6', '0', '4', '3', '4', '3', '5', '1', '8', '1', '/', '2', '9', '8', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '5', '1', '8', '1', '4', '8', '8', '8', '5', '7', '/', '3', '7', '3', '0', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0171938_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0171938Field005Chars00 ++ tail)) fragment0171938Acc00500 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0171938Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_005"
  err.flush

noncomputable def fragment0171938Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0171938Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '3', '5', '6', '7', '7', '3', '9', '9', '6', '7', '5', '5', '7', '5', '8', '2', '3', '3', '4', '3', '2', '2', '2', '5', '5', '1', '0', '7', '3', '8', '4', '0', '0', '6', '8', '0', '1', '9', '2', '3', '0', '5', '0', '4', '1', '9', '2', '0', '0', '0', '0', '0', '0', '/', '2', '3', '0', '7', '0', '9', '4', '2', '4', '0', '9', '8', '5', '6', '4', '1', '1', '7', '5', '0', '0', '6', '2', '0', '8', '2', '9', '2', '3', '6', '6', '4', '7', '0', '3', '4', '2', '4', '6', '4', '0', '6', '7', '4', '7', '1', '8', '7', '0', '5', '6', '9', '5', '6', '1', '6', '5', '8', '5', '4', '8', '4', '8', '4', '4', '1', '1', '3'])
noncomputable def fragment0171938Acc00700 : List (String × SourceJson) := (fragment0171938Field006Key00, fragment0171938Field006Value00) :: fragment0171938Acc00600
noncomputable def fragment0171938Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '3', '5', '6', '7', '7', '3', '9', '9', '6', '7', '5', '5', '7', '5', '8', '2', '3', '3', '4', '3', '2', '2', '2', '5', '5', '1', '0', '7', '3', '8', '4', '0', '0', '6', '8', '0', '1', '9', '2', '3', '0', '5', '0', '4', '1', '9', '2', '0', '0', '0', '0', '0', '0', '/', '2', '3', '0', '7', '0', '9', '4', '2', '4', '0', '9', '8', '5', '6', '4', '1', '1', '7', '5', '0', '0', '6', '2', '0', '8', '2', '9', '2', '3', '6', '6', '4', '7', '0', '3', '4', '2', '4', '6', '4', '0', '6', '7', '4', '7', '1', '8', '7', '0', '5', '6', '9', '5', '6', '1', '6', '5', '8', '5', '4', '8', '4', '8', '4', '4', '1', '1', '3', '"', ',']

theorem object_fragment0171938_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0171938Field006Chars00 ++ tail)) fragment0171938Acc00600 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0171938Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_006"
  err.flush

noncomputable def fragment0171938Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0171938Field007Value00 : SourceJson := .str (String.ofList ['5', '1', '2', '1', '9', '1', '0', '1', '7', '7', '7', '5', '4', '7', '9', '4', '0', '4', '6', '4', '9', '9', '1', '1', '9', '1', '5', '8', '4', '5', '8', '7', '9', '2', '1', '8', '3', '8', '6', '5', '7', '3', '6', '4', '1', '1', '4', '0', '0', '8', '9', '7', '9', '2', '4', '9', '5', '1', '2', '4', '0', '5', '3', '4', '5', '7', '9', '2', '4', '0', '1', '0', '6', '7', '8', '9', '1', '9', '9', '8', '9', '8', '8', '9', '4', '7', '1', '6', '1', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '8', '7', '7', '7', '6', '1', '2', '6', '5', '8', '4', '4', '0', '2', '7', '6', '9', '2', '0', '1', '8', '8', '8', '4', '8', '2', '8', '0', '3', '1', '9', '5', '4', '4', '4', '8', '3', '4', '1', '7', '9', '8', '5', '7', '7', '2', '0', '7', '3', '6', '6', '3', '8', '1', '6', '2', '0', '3', '2', '8', '4', '1', '2', '9', '2', '4', '3', '0', '3', '1', '7', '3', '8', '4', '2', '6', '2', '0', '4', '8', '8', '6', '3', '8', '5', '9', '3', '6', '4', '8', '0', '5', '9', '1', '9', '5', '2', '9', '6', '7', '8', '5', '1', '3', '1', '3', '2', '1', '1', '0', '9', '2', '5', '6', '9', '9', '5', '7', '6', '5', '7', '9', '9', '9'])
noncomputable def fragment0171938Acc00800 : List (String × SourceJson) := (fragment0171938Field007Key00, fragment0171938Field007Value00) :: fragment0171938Acc00700
noncomputable def fragment0171938Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '1', '2', '1', '9', '1', '0', '1', '7', '7', '7', '5', '4', '7', '9', '4', '0', '4', '6', '4', '9', '9', '1', '1', '9', '1', '5', '8', '4', '5', '8', '7', '9', '2', '1', '8', '3', '8', '6', '5', '7', '3', '6', '4', '1', '1', '4', '0', '0', '8', '9', '7', '9', '2', '4', '9', '5', '1', '2', '4', '0', '5', '3', '4', '5', '7', '9', '2', '4', '0', '1', '0', '6', '7', '8', '9', '1', '9', '9', '8', '9', '8', '8', '9', '4', '7', '1', '6', '1', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '8', '7', '7', '7', '6', '1', '2', '6', '5', '8', '4', '4', '0', '2', '7', '6', '9', '2', '0', '1', '8', '8', '8', '4', '8', '2', '8', '0', '3', '1', '9', '5', '4', '4', '4', '8', '3', '4', '1', '7', '9', '8', '5', '7', '7', '2', '0', '7', '3', '6', '6', '3', '8', '1', '6', '2', '0', '3', '2', '8', '4', '1', '2', '9', '2', '4', '3', '0', '3', '1', '7', '3', '8', '4', '2', '6', '2', '0', '4', '8', '8', '6', '3', '8', '5', '9', '3', '6', '4', '8', '0', '5', '9', '1', '9', '5', '2', '9', '6', '7', '8', '5', '1', '3', '1', '3', '2', '1', '1', '0', '9', '2', '5', '6', '9', '9', '5', '7', '6', '5', '7', '9', '9', '9', '"', ',']

theorem object_fragment0171938_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0171938Field007Chars00 ++ tail)) fragment0171938Acc00700 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0171938Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_007"
  err.flush

noncomputable def fragment0171938Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0171938Field008Value00 : SourceJson := .str (String.ofList ['4', '5', '8', '6', '8', '6', '3', '6', '0', '5', '6', '6', '3', '3', '9', '5'])
noncomputable def fragment0171938Acc00900 : List (String × SourceJson) := (fragment0171938Field008Key00, fragment0171938Field008Value00) :: fragment0171938Acc00800
noncomputable def fragment0171938Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '8', '6', '8', '6', '3', '6', '0', '5', '6', '6', '3', '3', '9', '5', '"', ',']

theorem object_fragment0171938_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0171938Field008Chars00 ++ tail)) fragment0171938Acc00800 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0171938Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_008"
  err.flush

noncomputable def fragment0171938Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0171938Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '9', '9', '4', '8', '7', '3', '4', '9', '0', '3', '8', '4', '4', '5', '2'])
noncomputable def fragment0171938Acc01000 : List (String × SourceJson) := (fragment0171938Field009Key00, fragment0171938Field009Value00) :: fragment0171938Acc00900
noncomputable def fragment0171938Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '9', '9', '4', '8', '7', '3', '4', '9', '0', '3', '8', '4', '4', '5', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0171938_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0171938Field009Chars00 ++ tail)) fragment0171938Acc00900 =
      .ok (.obj (fragment0171938Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171938_object_field_009"
  err.flush

noncomputable def fragment0171938Chars : List Char := '{' :: (fragment0171938Field000Chars00 ++ fragment0171938Field001Chars00 ++ fragment0171938Field002Chars00 ++ fragment0171938Field003Chars00 ++ fragment0171938Field004Chars00 ++ fragment0171938Field005Chars00 ++ fragment0171938Field006Chars00 ++ fragment0171938Field007Chars00 ++ fragment0171938Field008Chars00 ++ fragment0171938Field009Chars00)
noncomputable def fragment0171938Value : SourceJson := .obj (fragment0171938Acc01000.reverse)

theorem value_fragment0171938 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 251) (fragment0171938Chars ++ tail) =
      .ok (fragment0171938Value, tail) := by
  have hinput : fragment0171938Chars ++ tail = '{' :: (fragment0171938Field000Chars00 ++ (fragment0171938Field001Chars00 ++ (fragment0171938Field002Chars00 ++ (fragment0171938Field003Chars00 ++ (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0171938Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 251) (fragment0171938Chars ++ tail) =
        SourceJson.value (fuel + 251) ('{' :: (fragment0171938Field000Chars00 ++ (fragment0171938Field001Chars00 ++ (fragment0171938Field002Chars00 ++ (fragment0171938Field003Chars00 ++ (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 251)) hinput
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0171938Field000Chars00 ++ (fragment0171938Field001Chars00 ++ (fragment0171938Field002Chars00 ++ (fragment0171938Field003Chars00 ++ (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))))))))))) fragment0171938Acc00000 := by rfl
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0171938Field001Chars00 ++ (fragment0171938Field002Chars00 ++ (fragment0171938Field003Chars00 ++ (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail))))))))))) fragment0171938Acc00100 := object_fragment0171938_field_000 fuel (fragment0171938Field001Chars00 ++ (fragment0171938Field002Chars00 ++ (fragment0171938Field003Chars00 ++ (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0171938Field002Chars00 ++ (fragment0171938Field003Chars00 ++ (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))))))))) fragment0171938Acc00200 := object_fragment0171938_field_001 fuel (fragment0171938Field002Chars00 ++ (fragment0171938Field003Chars00 ++ (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0171938Field003Chars00 ++ (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail))))))))) fragment0171938Acc00300 := object_fragment0171938_field_002 fuel (fragment0171938Field003Chars00 ++ (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))))))) fragment0171938Acc00400 := object_fragment0171938_field_003 fuel (fragment0171938Field004Chars00 ++ (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail))))))) fragment0171938Acc00500 := object_fragment0171938_field_004 fuel (fragment0171938Field005Chars00 ++ (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))))) fragment0171938Acc00600 := object_fragment0171938_field_005 fuel (fragment0171938Field006Chars00 ++ (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail))))) fragment0171938Acc00700 := object_fragment0171938_field_006 fuel (fragment0171938Field007Chars00 ++ (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))) fragment0171938Acc00800 := object_fragment0171938_field_007 fuel (fragment0171938Field008Chars00 ++ (fragment0171938Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0171938Field009Chars00 ++ (tail))) fragment0171938Acc00900 := object_fragment0171938_field_008 fuel (fragment0171938Field009Chars00 ++ (tail))
    _ = .ok (fragment0171938Value, tail) := object_fragment0171938_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_before_reader"
  err.flush

noncomputable def chunk0032LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0032SuffixChars00 : List Char := [',']
noncomputable def chunk0032Chars00 : List Char := chunk0032LeadChars00 ++ fragment0159867Chars ++ chunk0032SuffixChars00
noncomputable def chunk0032Push00 (acc : List SourceJson) : List SourceJson := fragment0159867Value :: acc

noncomputable def chunk0032AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0032_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 441)
      (SourceJson.white (chunk0032LeadChars00 ++ (fragment0159867Chars ++ rest))) acc =
      (SourceJson.value (fuel + 440) (fragment0159867Chars ++ rest)).bind
        (chunk0032AfterValue00 (fuel + 440) acc) := by rfl

theorem array_chunk0032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 441) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 440) (SourceJson.white tail) (chunk0032Push00 acc) := by
  have hinput : chunk0032Chars00 ++ tail = chunk0032LeadChars00 ++ (fragment0159867Chars ++ (chunk0032SuffixChars00 ++ tail)) := by
    simp only [chunk0032Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 441) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 441)
          (SourceJson.white (chunk0032LeadChars00 ++ (fragment0159867Chars ++ (chunk0032SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 441) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 440) (fragment0159867Chars ++ (chunk0032SuffixChars00 ++ tail))).bind
        (chunk0032AfterValue00 (fuel + 440) acc) := array_chunk0032_head fuel (chunk0032SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0159867Value, chunk0032SuffixChars00 ++ tail)).bind
        (chunk0032AfterValue00 (fuel + 440) acc) :=
      congrArg (fun result => result.bind (chunk0032AfterValue00 (fuel + 440) acc))
        (value_fragment0159867 (fuel + 173) (chunk0032SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 440) (SourceJson.white tail) (chunk0032Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_before_reader"
  err.flush

noncomputable def chunk0033LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0033SuffixChars00 : List Char := [',']
noncomputable def chunk0033Chars00 : List Char := chunk0033LeadChars00 ++ fragment0161536Chars ++ chunk0033SuffixChars00
noncomputable def chunk0033Push00 (acc : List SourceJson) : List SourceJson := fragment0161536Value :: acc

noncomputable def chunk0033AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0033_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 440)
      (SourceJson.white (chunk0033LeadChars00 ++ (fragment0161536Chars ++ rest))) acc =
      (SourceJson.value (fuel + 439) (fragment0161536Chars ++ rest)).bind
        (chunk0033AfterValue00 (fuel + 439) acc) := by rfl

theorem array_chunk0033 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 440) (SourceJson.white (chunk0033Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 439) (SourceJson.white tail) (chunk0033Push00 acc) := by
  have hinput : chunk0033Chars00 ++ tail = chunk0033LeadChars00 ++ (fragment0161536Chars ++ (chunk0033SuffixChars00 ++ tail)) := by
    simp only [chunk0033Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 440) (SourceJson.white (chunk0033Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 440)
          (SourceJson.white (chunk0033LeadChars00 ++ (fragment0161536Chars ++ (chunk0033SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 440) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 439) (fragment0161536Chars ++ (chunk0033SuffixChars00 ++ tail))).bind
        (chunk0033AfterValue00 (fuel + 439) acc) := array_chunk0033_head fuel (chunk0033SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0161536Value, chunk0033SuffixChars00 ++ tail)).bind
        (chunk0033AfterValue00 (fuel + 439) acc) :=
      congrArg (fun result => result.bind (chunk0033AfterValue00 (fuel + 439) acc))
        (value_fragment0161536 (fuel + 0) (chunk0033SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 439) (SourceJson.white tail) (chunk0033Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_before_reader"
  err.flush

noncomputable def chunk0034LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0034SuffixChars00 : List Char := [',']
noncomputable def chunk0034Chars00 : List Char := chunk0034LeadChars00 ++ fragment0163547Chars ++ chunk0034SuffixChars00
noncomputable def chunk0034Push00 (acc : List SourceJson) : List SourceJson := fragment0163547Value :: acc

noncomputable def chunk0034AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0034_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 439)
      (SourceJson.white (chunk0034LeadChars00 ++ (fragment0163547Chars ++ rest))) acc =
      (SourceJson.value (fuel + 438) (fragment0163547Chars ++ rest)).bind
        (chunk0034AfterValue00 (fuel + 438) acc) := by rfl

theorem array_chunk0034 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 439) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 438) (SourceJson.white tail) (chunk0034Push00 acc) := by
  have hinput : chunk0034Chars00 ++ tail = chunk0034LeadChars00 ++ (fragment0163547Chars ++ (chunk0034SuffixChars00 ++ tail)) := by
    simp only [chunk0034Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 439) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 439)
          (SourceJson.white (chunk0034LeadChars00 ++ (fragment0163547Chars ++ (chunk0034SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 439) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 438) (fragment0163547Chars ++ (chunk0034SuffixChars00 ++ tail))).bind
        (chunk0034AfterValue00 (fuel + 438) acc) := array_chunk0034_head fuel (chunk0034SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0163547Value, chunk0034SuffixChars00 ++ tail)).bind
        (chunk0034AfterValue00 (fuel + 438) acc) :=
      congrArg (fun result => result.bind (chunk0034AfterValue00 (fuel + 438) acc))
        (value_fragment0163547 (fuel + 217) (chunk0034SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 438) (SourceJson.white tail) (chunk0034Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_before_reader"
  err.flush

noncomputable def chunk0035LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0035SuffixChars00 : List Char := [',']
noncomputable def chunk0035Chars00 : List Char := chunk0035LeadChars00 ++ fragment0165118Chars ++ chunk0035SuffixChars00
noncomputable def chunk0035Push00 (acc : List SourceJson) : List SourceJson := fragment0165118Value :: acc

noncomputable def chunk0035AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0035_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 438)
      (SourceJson.white (chunk0035LeadChars00 ++ (fragment0165118Chars ++ rest))) acc =
      (SourceJson.value (fuel + 437) (fragment0165118Chars ++ rest)).bind
        (chunk0035AfterValue00 (fuel + 437) acc) := by rfl

theorem array_chunk0035 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 438) (SourceJson.white (chunk0035Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 437) (SourceJson.white tail) (chunk0035Push00 acc) := by
  have hinput : chunk0035Chars00 ++ tail = chunk0035LeadChars00 ++ (fragment0165118Chars ++ (chunk0035SuffixChars00 ++ tail)) := by
    simp only [chunk0035Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 438) (SourceJson.white (chunk0035Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 438)
          (SourceJson.white (chunk0035LeadChars00 ++ (fragment0165118Chars ++ (chunk0035SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 438) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 437) (fragment0165118Chars ++ (chunk0035SuffixChars00 ++ tail))).bind
        (chunk0035AfterValue00 (fuel + 437) acc) := array_chunk0035_head fuel (chunk0035SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0165118Value, chunk0035SuffixChars00 ++ tail)).bind
        (chunk0035AfterValue00 (fuel + 437) acc) :=
      congrArg (fun result => result.bind (chunk0035AfterValue00 (fuel + 437) acc))
        (value_fragment0165118 (fuel + 176) (chunk0035SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 437) (SourceJson.white tail) (chunk0035Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_before_reader"
  err.flush

noncomputable def chunk0036LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0036SuffixChars00 : List Char := [',']
noncomputable def chunk0036Chars00 : List Char := chunk0036LeadChars00 ++ fragment0166763Chars ++ chunk0036SuffixChars00
noncomputable def chunk0036Push00 (acc : List SourceJson) : List SourceJson := fragment0166763Value :: acc

noncomputable def chunk0036AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0036_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 437)
      (SourceJson.white (chunk0036LeadChars00 ++ (fragment0166763Chars ++ rest))) acc =
      (SourceJson.value (fuel + 436) (fragment0166763Chars ++ rest)).bind
        (chunk0036AfterValue00 (fuel + 436) acc) := by rfl

theorem array_chunk0036 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 437) (SourceJson.white (chunk0036Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 436) (SourceJson.white tail) (chunk0036Push00 acc) := by
  have hinput : chunk0036Chars00 ++ tail = chunk0036LeadChars00 ++ (fragment0166763Chars ++ (chunk0036SuffixChars00 ++ tail)) := by
    simp only [chunk0036Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 437) (SourceJson.white (chunk0036Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 437)
          (SourceJson.white (chunk0036LeadChars00 ++ (fragment0166763Chars ++ (chunk0036SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 437) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 436) (fragment0166763Chars ++ (chunk0036SuffixChars00 ++ tail))).bind
        (chunk0036AfterValue00 (fuel + 436) acc) := array_chunk0036_head fuel (chunk0036SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0166763Value, chunk0036SuffixChars00 ++ tail)).bind
        (chunk0036AfterValue00 (fuel + 436) acc) :=
      congrArg (fun result => result.bind (chunk0036AfterValue00 (fuel + 436) acc))
        (value_fragment0166763 (fuel + 217) (chunk0036SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 436) (SourceJson.white tail) (chunk0036Push00 acc) := by rfl

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
noncomputable def chunk0037Chars00 : List Char := chunk0037LeadChars00 ++ fragment0168329Chars ++ chunk0037SuffixChars00
noncomputable def chunk0037Push00 (acc : List SourceJson) : List SourceJson := fragment0168329Value :: acc

noncomputable def chunk0037AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0037_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 436)
      (SourceJson.white (chunk0037LeadChars00 ++ (fragment0168329Chars ++ rest))) acc =
      (SourceJson.value (fuel + 435) (fragment0168329Chars ++ rest)).bind
        (chunk0037AfterValue00 (fuel + 435) acc) := by rfl

theorem array_chunk0037 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 436) (SourceJson.white (chunk0037Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 435) (SourceJson.white tail) (chunk0037Push00 acc) := by
  have hinput : chunk0037Chars00 ++ tail = chunk0037LeadChars00 ++ (fragment0168329Chars ++ (chunk0037SuffixChars00 ++ tail)) := by
    simp only [chunk0037Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 436) (SourceJson.white (chunk0037Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 436)
          (SourceJson.white (chunk0037LeadChars00 ++ (fragment0168329Chars ++ (chunk0037SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 436) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 435) (fragment0168329Chars ++ (chunk0037SuffixChars00 ++ tail))).bind
        (chunk0037AfterValue00 (fuel + 435) acc) := array_chunk0037_head fuel (chunk0037SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0168329Value, chunk0037SuffixChars00 ++ tail)).bind
        (chunk0037AfterValue00 (fuel + 435) acc) :=
      congrArg (fun result => result.bind (chunk0037AfterValue00 (fuel + 435) acc))
        (value_fragment0168329 (fuel + 25) (chunk0037SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 435) (SourceJson.white tail) (chunk0037Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0038_before_reader"
  err.flush

noncomputable def chunk0038LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0038SuffixChars00 : List Char := [',']
noncomputable def chunk0038Chars00 : List Char := chunk0038LeadChars00 ++ fragment0170276Chars ++ chunk0038SuffixChars00
noncomputable def chunk0038Push00 (acc : List SourceJson) : List SourceJson := fragment0170276Value :: acc

noncomputable def chunk0038AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0038_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 435)
      (SourceJson.white (chunk0038LeadChars00 ++ (fragment0170276Chars ++ rest))) acc =
      (SourceJson.value (fuel + 434) (fragment0170276Chars ++ rest)).bind
        (chunk0038AfterValue00 (fuel + 434) acc) := by rfl

theorem array_chunk0038 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 435) (SourceJson.white (chunk0038Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 434) (SourceJson.white tail) (chunk0038Push00 acc) := by
  have hinput : chunk0038Chars00 ++ tail = chunk0038LeadChars00 ++ (fragment0170276Chars ++ (chunk0038SuffixChars00 ++ tail)) := by
    simp only [chunk0038Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 435) (SourceJson.white (chunk0038Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 435)
          (SourceJson.white (chunk0038LeadChars00 ++ (fragment0170276Chars ++ (chunk0038SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 435) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 434) (fragment0170276Chars ++ (chunk0038SuffixChars00 ++ tail))).bind
        (chunk0038AfterValue00 (fuel + 434) acc) := array_chunk0038_head fuel (chunk0038SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0170276Value, chunk0038SuffixChars00 ++ tail)).bind
        (chunk0038AfterValue00 (fuel + 434) acc) :=
      congrArg (fun result => result.bind (chunk0038AfterValue00 (fuel + 434) acc))
        (value_fragment0170276 (fuel + 169) (chunk0038SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 434) (SourceJson.white tail) (chunk0038Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0038_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0039_before_reader"
  err.flush

noncomputable def chunk0039LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0039SuffixChars00 : List Char := [',']
noncomputable def chunk0039Chars00 : List Char := chunk0039LeadChars00 ++ fragment0171938Chars ++ chunk0039SuffixChars00
noncomputable def chunk0039Push00 (acc : List SourceJson) : List SourceJson := fragment0171938Value :: acc

noncomputable def chunk0039AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0039_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 434)
      (SourceJson.white (chunk0039LeadChars00 ++ (fragment0171938Chars ++ rest))) acc =
      (SourceJson.value (fuel + 433) (fragment0171938Chars ++ rest)).bind
        (chunk0039AfterValue00 (fuel + 433) acc) := by rfl

theorem array_chunk0039 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 434) (SourceJson.white (chunk0039Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 433) (SourceJson.white tail) (chunk0039Push00 acc) := by
  have hinput : chunk0039Chars00 ++ tail = chunk0039LeadChars00 ++ (fragment0171938Chars ++ (chunk0039SuffixChars00 ++ tail)) := by
    simp only [chunk0039Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 434) (SourceJson.white (chunk0039Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 434)
          (SourceJson.white (chunk0039LeadChars00 ++ (fragment0171938Chars ++ (chunk0039SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 434) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 433) (fragment0171938Chars ++ (chunk0039SuffixChars00 ++ tail))).bind
        (chunk0039AfterValue00 (fuel + 433) acc) := array_chunk0039_head fuel (chunk0039SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0171938Value, chunk0039SuffixChars00 ++ tail)).bind
        (chunk0039AfterValue00 (fuel + 433) acc) :=
      congrArg (fun result => result.bind (chunk0039AfterValue00 (fuel + 433) acc))
        (value_fragment0171938 (fuel + 182) (chunk0039SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 433) (SourceJson.white tail) (chunk0039Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0039_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0032Chars00 ++ chunk0033Chars00 ++ chunk0034Chars00 ++ chunk0035Chars00 ++ chunk0036Chars00 ++ chunk0037Chars00 ++ chunk0038Chars00 ++ chunk0039Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0039Push00 (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 441) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 433) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 441) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 441) (SourceJson.white (chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 441) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 440) (SourceJson.white (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))))) (chunk0032Push00 (acc)) := array_chunk0032 fuel (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 439) (SourceJson.white (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))) (chunk0033Push00 (chunk0032Push00 (acc))) := array_chunk0033 fuel (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))) (chunk0032Push00 (acc))
    _ = SourceJson.array (fuel + 438) (SourceJson.white (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))) (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))) := array_chunk0034 fuel (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))) (chunk0033Push00 (chunk0032Push00 (acc)))
    _ = SourceJson.array (fuel + 437) (SourceJson.white (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))) (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))) := array_chunk0035 fuel (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))) (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))
    _ = SourceJson.array (fuel + 436) (SourceJson.white (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))) (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))) := array_chunk0036 fuel (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))) (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))
    _ = SourceJson.array (fuel + 435) (SourceJson.white (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))) (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))) := array_chunk0037 fuel (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))) (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))
    _ = SourceJson.array (fuel + 434) (SourceJson.white (chunk0039Chars00 ++ (tail))) (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))))) := array_chunk0038 fuel (chunk0039Chars00 ++ (tail)) (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))))
    _ = SourceJson.array (fuel + 433) (SourceJson.white tail) (blockPush acc) := array_chunk0039 fuel (tail) (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 159861).take 13713 = blockChars := by rfl

theorem block_original_split : sourceRest 159861 = blockChars ++ sourceRest 173574 := by
  calc
    sourceRest 159861 = (sourceRest 159861).take 13713 ++ (sourceRest 159861).drop 13713 :=
      (List.take_append_drop 13713 (sourceRest 159861)).symm
    _ = blockChars ++ (sourceRest 159861).drop 13713 :=
      congrArg (fun part => part ++ (sourceRest 159861).drop 13713) block_original_prefix
    _ = blockChars ++ sourceRest 173574 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 159861 13713)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 441) (SourceJson.white (sourceRest 159861)) acc =
      SourceJson.array (fuel + 433) (SourceJson.white (sourceRest 173574)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 441) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 173574) acc)

#print axioms object_fragment0159867_field_000
#print axioms object_fragment0159867_field_001
#print axioms object_fragment0159867_field_002
#print axioms object_fragment0159867_field_003
#print axioms object_fragment0159867_field_004
#print axioms object_fragment0159867_field_005
#print axioms object_fragment0159867_field_006
#print axioms object_fragment0159867_field_007
#print axioms object_fragment0159867_field_008
#print axioms object_fragment0159867_field_009
#print axioms value_fragment0159867
#print axioms object_fragment0161536_field_000
#print axioms object_fragment0161536_field_001
#print axioms object_fragment0161536_field_002
#print axioms object_fragment0161536_field_003
#print axioms object_fragment0161536_field_004
#print axioms object_fragment0161536_field_005
#print axioms object_fragment0161536_field_006
#print axioms object_fragment0161536_field_007
#print axioms object_fragment0161536_field_008
#print axioms object_fragment0161536_field_009
#print axioms value_fragment0161536
#print axioms object_fragment0163547_field_000
#print axioms object_fragment0163547_field_001
#print axioms object_fragment0163547_field_002
#print axioms object_fragment0163547_field_003
#print axioms object_fragment0163547_field_004
#print axioms object_fragment0163547_field_005
#print axioms object_fragment0163547_field_006
#print axioms object_fragment0163547_field_007
#print axioms object_fragment0163547_field_008
#print axioms object_fragment0163547_field_009
#print axioms value_fragment0163547
#print axioms object_fragment0165118_field_000
#print axioms object_fragment0165118_field_001
#print axioms object_fragment0165118_field_002
#print axioms object_fragment0165118_field_003
#print axioms object_fragment0165118_field_004
#print axioms object_fragment0165118_field_005
#print axioms object_fragment0165118_field_006
#print axioms object_fragment0165118_field_007
#print axioms object_fragment0165118_field_008
#print axioms object_fragment0165118_field_009
#print axioms value_fragment0165118
#print axioms object_fragment0166763_field_000
#print axioms object_fragment0166763_field_001
#print axioms object_fragment0166763_field_002
#print axioms object_fragment0166763_field_003
#print axioms object_fragment0166763_field_004
#print axioms object_fragment0166763_field_005
#print axioms object_fragment0166763_field_006
#print axioms object_fragment0166763_field_007
#print axioms object_fragment0166763_field_008
#print axioms object_fragment0166763_field_009
#print axioms value_fragment0166763
#print axioms object_fragment0168329_field_000
#print axioms object_fragment0168329_field_001
#print axioms object_fragment0168329_field_002
#print axioms object_fragment0168329_field_003
#print axioms object_fragment0168329_field_004
#print axioms object_fragment0168329_field_005
#print axioms object_fragment0168329_field_006
#print axioms object_fragment0168329_field_007
#print axioms object_fragment0168329_field_008
#print axioms object_fragment0168329_field_009
#print axioms value_fragment0168329
#print axioms object_fragment0170276_field_000
#print axioms object_fragment0170276_field_001
#print axioms object_fragment0170276_field_002
#print axioms object_fragment0170276_field_003
#print axioms object_fragment0170276_field_004
#print axioms object_fragment0170276_field_005
#print axioms object_fragment0170276_field_006
#print axioms object_fragment0170276_field_007
#print axioms object_fragment0170276_field_008
#print axioms object_fragment0170276_field_009
#print axioms value_fragment0170276
#print axioms object_fragment0171938_field_000
#print axioms object_fragment0171938_field_001
#print axioms object_fragment0171938_field_002
#print axioms object_fragment0171938_field_003
#print axioms object_fragment0171938_field_004
#print axioms object_fragment0171938_field_005
#print axioms object_fragment0171938_field_006
#print axioms object_fragment0171938_field_007
#print axioms object_fragment0171938_field_008
#print axioms object_fragment0171938_field_009
#print axioms value_fragment0171938
#print axioms array_chunk0032_head
#print axioms array_chunk0032
#print axioms array_chunk0033_head
#print axioms array_chunk0033
#print axioms array_chunk0034_head
#print axioms array_chunk0034
#print axioms array_chunk0035_head
#print axioms array_chunk0035
#print axioms array_chunk0036_head
#print axioms array_chunk0036
#print axioms array_chunk0037_head
#print axioms array_chunk0037
#print axioms array_chunk0038_head
#print axioms array_chunk0038
#print axioms array_chunk0039_head
#print axioms array_chunk0039
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock004

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
