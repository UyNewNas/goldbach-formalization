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

namespace SimplicesBlock001

noncomputable def fragment0229028Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0229028Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0229028Field000Value00 : SourceJson := .number (String.ofList ['2'])
noncomputable def fragment0229028Acc00100 : List (String × SourceJson) := (fragment0229028Field000Key00, fragment0229028Field000Value00) :: fragment0229028Acc00000
noncomputable def fragment0229028Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', ',']

theorem object_fragment0229028_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0229028Field000Chars00 ++ tail)) fragment0229028Acc00000 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0229028Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_000"
  err.flush

noncomputable def fragment0229028Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0229028Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '2']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0229028Acc00200 : List (String × SourceJson) := (fragment0229028Field001Key00, fragment0229028Field001Value00) :: fragment0229028Acc00100
noncomputable def fragment0229028Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0229028_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0229028Field001Chars00 ++ tail)) fragment0229028Acc00100 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0229028Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_001"
  err.flush

noncomputable def fragment0229028Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0229028Field002Value00 : SourceJson := .str (String.ofList ['3', '1', '7', '2', '0', '5', '8', '1', '4', '7', '3', '7', '7', '7', '1', '8', '0', '6', '2', '5', '4', '6', '3', '0', '5', '5', '6', '9', '4', '0', '4', '2', '7', '3', '7', '1', '0', '8', '8', '2', '3', '6', '1', '/', '1', '8', '8', '0', '1', '8', '4', '5', '3', '6', '9', '9', '8', '8', '7', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0229028Acc00300 : List (String × SourceJson) := (fragment0229028Field002Key00, fragment0229028Field002Value00) :: fragment0229028Acc00200
noncomputable def fragment0229028Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '1', '7', '2', '0', '5', '8', '1', '4', '7', '3', '7', '7', '7', '1', '8', '0', '6', '2', '5', '4', '6', '3', '0', '5', '5', '6', '9', '4', '0', '4', '2', '7', '3', '7', '1', '0', '8', '8', '2', '3', '6', '1', '/', '1', '8', '8', '0', '1', '8', '4', '5', '3', '6', '9', '9', '8', '8', '7', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0229028_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0229028Field002Chars00 ++ tail)) fragment0229028Acc00200 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0229028Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_002"
  err.flush

noncomputable def fragment0229028Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0229028Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0229028Acc00400 : List (String × SourceJson) := (fragment0229028Field003Key00, fragment0229028Field003Value00) :: fragment0229028Acc00300
noncomputable def fragment0229028Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0229028_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0229028Field003Chars00 ++ tail)) fragment0229028Acc00300 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0229028Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_003"
  err.flush

noncomputable def fragment0229028Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0229028Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0229028Acc00500 : List (String × SourceJson) := (fragment0229028Field004Key00, fragment0229028Field004Value00) :: fragment0229028Acc00400
noncomputable def fragment0229028Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0229028_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0229028Field004Chars00 ++ tail)) fragment0229028Acc00400 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0229028Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_004"
  err.flush

noncomputable def fragment0229028Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0229028Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '9', '6', '9', '0', '9', '7', '7', '5', '5', '1', '/', '1', '6', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '4', '2', '3', '1', '6', '8', '4', '3', '1', '/', '1', '6', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '1', '4', '3', '5', '3', '8', '6', '1', '3', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '7', '8', '4', '2', '5', '3', '2', '7', '1', '/', '5', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '3', '9', '9', '6', '6', '3', '6', '8', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '7', '0', '3', '3', '7', '0', '7', '8', '9', '/', '2', '4', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '8', '7', '1', '7', '9', '2', '9', '3', '/', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '5', '0', '6', '2', '2', '6', '6', '3', '/', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '5', '8', '2', '0', '6', '4', '2', '2', '6', '3', '/', '4', '9', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '2', '3', '5', '4', '2', '8', '4', '8', '2', '3', '/', '4', '9', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0229028Acc00600 : List (String × SourceJson) := (fragment0229028Field005Key00, fragment0229028Field005Value00) :: fragment0229028Acc00500
noncomputable def fragment0229028Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '6', '9', '0', '9', '7', '7', '5', '5', '1', '/', '1', '6', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '4', '2', '3', '1', '6', '8', '4', '3', '1', '/', '1', '6', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '1', '4', '3', '5', '3', '8', '6', '1', '3', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '7', '8', '4', '2', '5', '3', '2', '7', '1', '/', '5', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '3', '9', '9', '6', '6', '3', '6', '8', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '7', '0', '3', '3', '7', '0', '7', '8', '9', '/', '2', '4', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '8', '7', '1', '7', '9', '2', '9', '3', '/', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '5', '0', '6', '2', '2', '6', '6', '3', '/', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '5', '8', '2', '0', '6', '4', '2', '2', '6', '3', '/', '4', '9', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '3', '5', '4', '2', '8', '4', '8', '2', '3', '/', '4', '9', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0229028_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0229028Field005Chars00 ++ tail)) fragment0229028Acc00500 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0229028Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_005"
  err.flush

noncomputable def fragment0229028Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0229028Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '8', '1', '1', '6', '6', '0', '9', '1', '9', '6', '9', '6', '5', '9', '7', '3', '4', '7', '4', '5', '5', '1', '0', '5', '9', '8', '9', '1', '1', '9', '0', '3', '2', '4', '2', '3', '9', '2', '1', '5', '8', '9', '6', '4', '0', '3', '1', '2', '5', '0', '/', '1', '2', '5', '0', '5', '3', '6', '5', '7', '5', '6', '7', '2', '0', '4', '7', '4', '9', '3', '1', '0', '7', '4', '6', '3', '1', '3', '5', '0', '1', '9', '6', '5', '5', '9', '0', '6', '9', '3', '6', '7', '2', '7', '1', '9', '3', '9', '5', '6', '0', '4', '7', '8', '1', '7', '7', '6', '3', '7', '2', '3', '7', '1', '1', '4', '5', '1'])
noncomputable def fragment0229028Acc00700 : List (String × SourceJson) := (fragment0229028Field006Key00, fragment0229028Field006Value00) :: fragment0229028Acc00600
noncomputable def fragment0229028Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '8', '1', '1', '6', '6', '0', '9', '1', '9', '6', '9', '6', '5', '9', '7', '3', '4', '7', '4', '5', '5', '1', '0', '5', '9', '8', '9', '1', '1', '9', '0', '3', '2', '4', '2', '3', '9', '2', '1', '5', '8', '9', '6', '4', '0', '3', '1', '2', '5', '0', '/', '1', '2', '5', '0', '5', '3', '6', '5', '7', '5', '6', '7', '2', '0', '4', '7', '4', '9', '3', '1', '0', '7', '4', '6', '3', '1', '3', '5', '0', '1', '9', '6', '5', '5', '9', '0', '6', '9', '3', '6', '7', '2', '7', '1', '9', '3', '9', '5', '6', '0', '4', '7', '8', '1', '7', '7', '6', '3', '7', '2', '3', '7', '1', '1', '4', '5', '1', '"', ',']

theorem object_fragment0229028_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0229028Field006Chars00 ++ tail)) fragment0229028Acc00600 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0229028Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_006"
  err.flush

noncomputable def fragment0229028Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0229028Field007Value00 : SourceJson := .str (String.ofList ['9', '7', '3', '0', '5', '0', '6', '2', '5', '6', '0', '3', '5', '0', '0', '6', '4', '7', '3', '2', '7', '3', '0', '5', '6', '8', '6', '2', '3', '1', '6', '2', '3', '8', '1', '8', '1', '4', '9', '4', '5', '5', '3', '5', '1', '1', '9', '1', '1', '8', '8', '6', '7', '7', '5', '9', '3', '0', '4', '3', '4', '3', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '8', '6', '2', '3', '9', '2', '7', '0', '2', '5', '0', '2', '4', '9', '1', '3', '8', '2', '2', '6', '9', '9', '5', '5', '5', '5', '7', '7', '7', '2', '8', '8', '8', '7', '1', '1', '6', '7', '0', '0', '0', '9', '5', '5', '5', '7', '3', '3', '8', '2', '7', '4', '6', '2', '9', '5', '2', '1', '7', '6', '4', '1', '2', '8', '3', '7', '4', '6', '9', '9', '4', '9', '0', '3', '5', '4', '7', '8', '7', '4', '5', '7', '7', '9', '1', '0', '8', '3', '7', '5', '1', '1', '4', '5', '2', '4', '9', '9', '0', '7', '0', '5', '7'])
noncomputable def fragment0229028Acc00800 : List (String × SourceJson) := (fragment0229028Field007Key00, fragment0229028Field007Value00) :: fragment0229028Acc00700
noncomputable def fragment0229028Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '7', '3', '0', '5', '0', '6', '2', '5', '6', '0', '3', '5', '0', '0', '6', '4', '7', '3', '2', '7', '3', '0', '5', '6', '8', '6', '2', '3', '1', '6', '2', '3', '8', '1', '8', '1', '4', '9', '4', '5', '5', '3', '5', '1', '1', '9', '1', '1', '8', '8', '6', '7', '7', '5', '9', '3', '0', '4', '3', '4', '3', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '8', '6', '2', '3', '9', '2', '7', '0', '2', '5', '0', '2', '4', '9', '1', '3', '8', '2', '2', '6', '9', '9', '5', '5', '5', '5', '7', '7', '7', '2', '8', '8', '8', '7', '1', '1', '6', '7', '0', '0', '0', '9', '5', '5', '5', '7', '3', '3', '8', '2', '7', '4', '6', '2', '9', '5', '2', '1', '7', '6', '4', '1', '2', '8', '3', '7', '4', '6', '9', '9', '4', '9', '0', '3', '5', '4', '7', '8', '7', '4', '5', '7', '7', '9', '1', '0', '8', '3', '7', '5', '1', '1', '4', '5', '2', '4', '9', '9', '0', '7', '0', '5', '7', '"', ',']

theorem object_fragment0229028_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0229028Field007Chars00 ++ tail)) fragment0229028Acc00700 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0229028Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_007"
  err.flush

noncomputable def fragment0229028Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0229028Field008Value00 : SourceJson := .str (String.ofList ['8', '7', '5', '0', '4', '2', '3', '9', '1', '5', '8', '2', '6', '4'])
noncomputable def fragment0229028Acc00900 : List (String × SourceJson) := (fragment0229028Field008Key00, fragment0229028Field008Value00) :: fragment0229028Acc00800
noncomputable def fragment0229028Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '7', '5', '0', '4', '2', '3', '9', '1', '5', '8', '2', '6', '4', '"', ',']

theorem object_fragment0229028_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0229028Field008Chars00 ++ tail)) fragment0229028Acc00800 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0229028Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_008"
  err.flush

noncomputable def fragment0229028Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0229028Field009Value00 : SourceJson := .str (String.ofList ['6', '4', '9', '8', '9', '4', '2', '9', '2', '2', '6', '7', '5', '0', '5'])
noncomputable def fragment0229028Acc01000 : List (String × SourceJson) := (fragment0229028Field009Key00, fragment0229028Field009Value00) :: fragment0229028Acc00900
noncomputable def fragment0229028Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '4', '9', '8', '9', '4', '2', '9', '2', '2', '6', '7', '5', '0', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0229028_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0229028Field009Chars00 ++ tail)) fragment0229028Acc00900 =
      .ok (.obj (fragment0229028Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0229028_object_field_009"
  err.flush

noncomputable def fragment0229028Chars : List Char := '{' :: (fragment0229028Field000Chars00 ++ fragment0229028Field001Chars00 ++ fragment0229028Field002Chars00 ++ fragment0229028Field003Chars00 ++ fragment0229028Field004Chars00 ++ fragment0229028Field005Chars00 ++ fragment0229028Field006Chars00 ++ fragment0229028Field007Chars00 ++ fragment0229028Field008Chars00 ++ fragment0229028Field009Chars00)
noncomputable def fragment0229028Value : SourceJson := .obj (fragment0229028Acc01000.reverse)

theorem value_fragment0229028 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 207) (fragment0229028Chars ++ tail) =
      .ok (fragment0229028Value, tail) := by
  have hinput : fragment0229028Chars ++ tail = '{' :: (fragment0229028Field000Chars00 ++ (fragment0229028Field001Chars00 ++ (fragment0229028Field002Chars00 ++ (fragment0229028Field003Chars00 ++ (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0229028Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 207) (fragment0229028Chars ++ tail) =
        SourceJson.value (fuel + 207) ('{' :: (fragment0229028Field000Chars00 ++ (fragment0229028Field001Chars00 ++ (fragment0229028Field002Chars00 ++ (fragment0229028Field003Chars00 ++ (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 207)) hinput
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0229028Field000Chars00 ++ (fragment0229028Field001Chars00 ++ (fragment0229028Field002Chars00 ++ (fragment0229028Field003Chars00 ++ (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))))))))))) fragment0229028Acc00000 := by rfl
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0229028Field001Chars00 ++ (fragment0229028Field002Chars00 ++ (fragment0229028Field003Chars00 ++ (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail))))))))))) fragment0229028Acc00100 := object_fragment0229028_field_000 fuel (fragment0229028Field001Chars00 ++ (fragment0229028Field002Chars00 ++ (fragment0229028Field003Chars00 ++ (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0229028Field002Chars00 ++ (fragment0229028Field003Chars00 ++ (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))))))))) fragment0229028Acc00200 := object_fragment0229028_field_001 fuel (fragment0229028Field002Chars00 ++ (fragment0229028Field003Chars00 ++ (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0229028Field003Chars00 ++ (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail))))))))) fragment0229028Acc00300 := object_fragment0229028_field_002 fuel (fragment0229028Field003Chars00 ++ (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))))))) fragment0229028Acc00400 := object_fragment0229028_field_003 fuel (fragment0229028Field004Chars00 ++ (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail))))))) fragment0229028Acc00500 := object_fragment0229028_field_004 fuel (fragment0229028Field005Chars00 ++ (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))))) fragment0229028Acc00600 := object_fragment0229028_field_005 fuel (fragment0229028Field006Chars00 ++ (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail))))) fragment0229028Acc00700 := object_fragment0229028_field_006 fuel (fragment0229028Field007Chars00 ++ (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))) fragment0229028Acc00800 := object_fragment0229028_field_007 fuel (fragment0229028Field008Chars00 ++ (fragment0229028Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0229028Field009Chars00 ++ (tail))) fragment0229028Acc00900 := object_fragment0229028_field_008 fuel (fragment0229028Field009Chars00 ++ (tail))
    _ = .ok (fragment0229028Value, tail) := object_fragment0229028_field_009 fuel (tail)

noncomputable def fragment0230592Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0230592Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0230592Field000Value00 : SourceJson := .number (String.ofList ['3'])
noncomputable def fragment0230592Acc00100 : List (String × SourceJson) := (fragment0230592Field000Key00, fragment0230592Field000Value00) :: fragment0230592Acc00000
noncomputable def fragment0230592Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', ',']

theorem object_fragment0230592_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 325) (SourceJson.white (fragment0230592Field000Chars00 ++ tail)) fragment0230592Acc00000 =
      SourceJson.object (fuel + 324) (SourceJson.white tail) fragment0230592Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_000"
  err.flush

noncomputable def fragment0230592Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0230592Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '2']), .number (String.ofList ['4']), .number (String.ofList ['2'])]
noncomputable def fragment0230592Acc00200 : List (String × SourceJson) := (fragment0230592Field001Key00, fragment0230592Field001Value00) :: fragment0230592Acc00100
noncomputable def fragment0230592Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0230592_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 324) (SourceJson.white (fragment0230592Field001Chars00 ++ tail)) fragment0230592Acc00100 =
      SourceJson.object (fuel + 323) (SourceJson.white tail) fragment0230592Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_001"
  err.flush

noncomputable def fragment0230592Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0230592Field002Value00 : SourceJson := .str (String.ofList ['5', '4', '5', '3', '1', '3', '9', '8', '8', '0', '1', '1', '2', '8', '7', '0', '9', '3', '9', '5', '9', '6', '3', '6', '2', '2', '3', '2', '8', '1', '3', '6', '3', '6', '5', '3', '6', '9', '8', '9', '4', '8', '9', '/', '1', '5', '3', '2', '0', '0', '2', '2', '1', '5', '3', '3', '2', '4', '1', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0230592Acc00300 : List (String × SourceJson) := (fragment0230592Field002Key00, fragment0230592Field002Value00) :: fragment0230592Acc00200
noncomputable def fragment0230592Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '4', '5', '3', '1', '3', '9', '8', '8', '0', '1', '1', '2', '8', '7', '0', '9', '3', '9', '5', '9', '6', '3', '6', '2', '2', '3', '2', '8', '1', '3', '6', '3', '6', '5', '3', '6', '9', '8', '9', '4', '8', '9', '/', '1', '5', '3', '2', '0', '0', '2', '2', '1', '5', '3', '3', '2', '4', '1', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0230592_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 323) (SourceJson.white (fragment0230592Field002Chars00 ++ tail)) fragment0230592Acc00200 =
      SourceJson.object (fuel + 322) (SourceJson.white tail) fragment0230592Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_002"
  err.flush

noncomputable def fragment0230592Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0230592Field003Value00 : SourceJson := .str (String.ofList ['5', '9', '1', '6', '2', '9', '/', '5', '1', '7', '4', '4', '0', '0', '0', '0'])
noncomputable def fragment0230592Acc00400 : List (String × SourceJson) := (fragment0230592Field003Key00, fragment0230592Field003Value00) :: fragment0230592Acc00300
noncomputable def fragment0230592Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '9', '1', '6', '2', '9', '/', '5', '1', '7', '4', '4', '0', '0', '0', '0', '"', ',']

theorem object_fragment0230592_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 322) (SourceJson.white (fragment0230592Field003Chars00 ++ tail)) fragment0230592Acc00300 =
      SourceJson.object (fuel + 321) (SourceJson.white tail) fragment0230592Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_003"
  err.flush

noncomputable def fragment0230592Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0230592Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '2', '1', '8', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '2', '7', '8', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0230592Acc00500 : List (String × SourceJson) := (fragment0230592Field004Key00, fragment0230592Field004Value00) :: fragment0230592Acc00400
noncomputable def fragment0230592Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '8', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '2', '7', '8', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0230592_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 321) (SourceJson.white (fragment0230592Field004Chars00 ++ tail)) fragment0230592Acc00400 =
      SourceJson.object (fuel + 320) (SourceJson.white tail) fragment0230592Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_004"
  err.flush

noncomputable def fragment0230592Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0230592Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '5', '3', '5', '8', '5', '1', '5', '6', '4', '9', '9', '1', '3', '1', '6', '8', '9', '/', '1', '8', '4', '7', '3', '5', '1', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '2', '9', '1', '4', '1', '9', '9', '4', '6', '5', '1', '6', '6', '3', '/', '1', '2', '3', '1', '5', '6', '7', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '6', '4', '2', '0', '4', '3', '6', '9', '5', '9', '3', '5', '1', '9', '1', '/', '3', '9', '5', '8', '6', '1', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '0', '8', '1', '8', '1', '8', '5', '3', '0', '4', '1', '2', '7', '4', '1', '/', '1', '1', '0', '8', '4', '1', '0', '8', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '3', '7', '3', '2', '3', '8', '8', '1', '6', '9', '0', '2', '4', '9', '/', '1', '5', '8', '3', '4', '4', '4', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '1', '0', '2', '6', '2', '4', '8', '3', '9', '2', '3', '6', '9', '9', '/', '5', '5', '4', '2', '0', '5', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '9', '9', '5', '8', '3', '9', '8', '7', '0', '3', '0', '0', '9', '0', '7', '/', '4', '5', '2', '4', '1', '2', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '0', '5', '7', '1', '7', '7', '3', '2', '0', '8', '2', '6', '2', '5', '7', '/', '4', '5', '2', '4', '1', '2', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '4', '4', '0', '8', '6', '0', '7', '3', '8', '5', '9', '0', '9', '4', '1', '7', '/', '5', '5', '4', '2', '0', '5', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '4', '6', '8', '2', '9', '5', '8', '1', '5', '3', '3', '3', '6', '7', '/', '3', '6', '9', '4', '7', '0', '2', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0230592Acc00600 : List (String × SourceJson) := (fragment0230592Field005Key00, fragment0230592Field005Value00) :: fragment0230592Acc00500
noncomputable def fragment0230592Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '3', '5', '8', '5', '1', '5', '6', '4', '9', '9', '1', '3', '1', '6', '8', '9', '/', '1', '8', '4', '7', '3', '5', '1', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '2', '9', '1', '4', '1', '9', '9', '4', '6', '5', '1', '6', '6', '3', '/', '1', '2', '3', '1', '5', '6', '7', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '6', '4', '2', '0', '4', '3', '6', '9', '5', '9', '3', '5', '1', '9', '1', '/', '3', '9', '5', '8', '6', '1', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '0', '8', '1', '8', '1', '8', '5', '3', '0', '4', '1', '2', '7', '4', '1', '/', '1', '1', '0', '8', '4', '1', '0', '8', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '3', '7', '3', '2', '3', '8', '8', '1', '6', '9', '0', '2', '4', '9', '/', '1', '5', '8', '3', '4', '4', '4', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '1', '0', '2', '6', '2', '4', '8', '3', '9', '2', '3', '6', '9', '9', '/', '5', '5', '4', '2', '0', '5', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '9', '5', '8', '3', '9', '8', '7', '0', '3', '0', '0', '9', '0', '7', '/', '4', '5', '2', '4', '1', '2', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '0', '5', '7', '1', '7', '7', '3', '2', '0', '8', '2', '6', '2', '5', '7', '/', '4', '5', '2', '4', '1', '2', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '4', '4', '0', '8', '6', '0', '7', '3', '8', '5', '9', '0', '9', '4', '1', '7', '/', '5', '5', '4', '2', '0', '5', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '4', '6', '8', '2', '9', '5', '8', '1', '5', '3', '3', '3', '6', '7', '/', '3', '6', '9', '4', '7', '0', '2', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0230592_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 320) (SourceJson.white (fragment0230592Field005Chars00 ++ tail)) fragment0230592Acc00500 =
      SourceJson.object (fuel + 319) (SourceJson.white tail) fragment0230592Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_005"
  err.flush

noncomputable def fragment0230592Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0230592Field006Value00 : SourceJson := .str (String.ofList ['2', '1', '9', '1', '7', '3', '6', '2', '0', '5', '2', '5', '2', '2', '4', '0', '2', '9', '9', '6', '7', '5', '5', '8', '1', '6', '5', '1', '7', '9', '1', '6', '4', '3', '3', '2', '2', '5', '1', '5', '3', '2', '2', '2', '7', '4', '1', '7', '1', '8', '7', '5', '/', '3', '3', '3', '4', '2', '3', '2', '3', '9', '4', '6', '4', '4', '6', '3', '8', '8', '7', '3', '8', '7', '2', '0', '2', '2', '6', '9', '1', '8', '0', '6', '7', '9', '5', '8', '9', '8', '7', '3', '7', '2', '7', '2', '8', '4', '6', '1', '6', '8', '8', '1', '2', '7', '9', '4', '5', '9', '5', '6', '2', '2', '5', '6', '8', '4', '0', '8'])
noncomputable def fragment0230592Acc00700 : List (String × SourceJson) := (fragment0230592Field006Key00, fragment0230592Field006Value00) :: fragment0230592Acc00600
noncomputable def fragment0230592Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '9', '1', '7', '3', '6', '2', '0', '5', '2', '5', '2', '2', '4', '0', '2', '9', '9', '6', '7', '5', '5', '8', '1', '6', '5', '1', '7', '9', '1', '6', '4', '3', '3', '2', '2', '5', '1', '5', '3', '2', '2', '2', '7', '4', '1', '7', '1', '8', '7', '5', '/', '3', '3', '3', '4', '2', '3', '2', '3', '9', '4', '6', '4', '4', '6', '3', '8', '8', '7', '3', '8', '7', '2', '0', '2', '2', '6', '9', '1', '8', '0', '6', '7', '9', '5', '8', '9', '8', '7', '3', '7', '2', '7', '2', '8', '4', '6', '1', '6', '8', '8', '1', '2', '7', '9', '4', '5', '9', '5', '6', '2', '2', '5', '6', '8', '4', '0', '8', '"', ',']

theorem object_fragment0230592_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 319) (SourceJson.white (fragment0230592Field006Chars00 ++ tail)) fragment0230592Acc00600 =
      SourceJson.object (fuel + 318) (SourceJson.white tail) fragment0230592Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_006"
  err.flush

noncomputable def fragment0230592Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0230592Field007Value00 : SourceJson := .str (String.ofList ['2', '0', '6', '1', '0', '2', '3', '6', '6', '8', '5', '5', '0', '6', '8', '7', '2', '9', '2', '2', '3', '2', '2', '6', '4', '4', '1', '5', '7', '7', '5', '0', '2', '6', '0', '8', '0', '2', '5', '9', '5', '1', '6', '3', '3', '0', '5', '3', '3', '4', '5', '4', '2', '2', '1', '9', '2', '1', '9', '5', '4', '4', '4', '9', '9', '7', '6', '8', '6', '8', '4', '8', '5', '9', '1', '1', '8', '0', '2', '0', '4', '7', '5', '7', '5', '5', '0', '3', '9', '7', '0', '0', '9', '9', '6', '1', '8', '3', '3', '8', '5', '9', '8', '8', '4', '2', '5', '2', '7', '4', '4', '7', '1', '9', '2', '5', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '7', '5', '2', '6', '7', '2', '4', '1', '4', '0', '4', '6', '2', '7', '9', '2', '0', '3', '0', '7', '8', '8', '4', '4', '5', '2', '8', '2', '5', '0', '6', '0', '3', '9', '2', '4', '0', '9', '9', '7', '0', '4', '6', '6', '3', '4', '2', '5', '8', '1', '8', '7', '7', '2', '1', '8', '1', '5', '6', '1', '3', '2', '0', '2', '1', '4', '3', '7', '2', '5', '3', '7', '7', '4', '7', '8', '7', '8', '0', '5', '0', '8', '1', '3', '3', '0', '0', '0', '6', '2', '2', '7', '6', '1', '2', '0', '3', '4', '1', '7', '5', '5', '7', '0', '6', '0', '7', '2', '8', '1', '6', '8', '5', '8', '9', '6', '2', '7', '3', '3', '5', '7', '0', '0', '9', '2', '3', '8', '0', '0', '3', '0', '9', '0', '0', '3', '4', '4', '3', '1', '6', '5', '0', '3', '2', '9', '9', '0', '8', '8', '3', '6', '0', '2', '5', '8', '1', '4', '7', '5', '1', '0', '3'])
noncomputable def fragment0230592Acc00800 : List (String × SourceJson) := (fragment0230592Field007Key00, fragment0230592Field007Value00) :: fragment0230592Acc00700
noncomputable def fragment0230592Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '0', '6', '1', '0', '2', '3', '6', '6', '8', '5', '5', '0', '6', '8', '7', '2', '9', '2', '2', '3', '2', '2', '6', '4', '4', '1', '5', '7', '7', '5', '0', '2', '6', '0', '8', '0', '2', '5', '9', '5', '1', '6', '3', '3', '0', '5', '3', '3', '4', '5', '4', '2', '2', '1', '9', '2', '1', '9', '5', '4', '4', '4', '9', '9', '7', '6', '8', '6', '8', '4', '8', '5', '9', '1', '1', '8', '0', '2', '0', '4', '7', '5', '7', '5', '5', '0', '3', '9', '7', '0', '0', '9', '9', '6', '1', '8', '3', '3', '8', '5', '9', '8', '8', '4', '2', '5', '2', '7', '4', '4', '7', '1', '9', '2', '5', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '7', '5', '2', '6', '7', '2', '4', '1', '4', '0', '4', '6', '2', '7', '9', '2', '0', '3', '0', '7', '8', '8', '4', '4', '5', '2', '8', '2', '5', '0', '6', '0', '3', '9', '2', '4', '0', '9', '9', '7', '0', '4', '6', '6', '3', '4', '2', '5', '8', '1', '8', '7', '7', '2', '1', '8', '1', '5', '6', '1', '3', '2', '0', '2', '1', '4', '3', '7', '2', '5', '3', '7', '7', '4', '7', '8', '7', '8', '0', '5', '0', '8', '1', '3', '3', '0', '0', '0', '6', '2', '2', '7', '6', '1', '2', '0', '3', '4', '1', '7', '5', '5', '7', '0', '6', '0', '7', '2', '8', '1', '6', '8', '5', '8', '9', '6', '2', '7', '3', '3', '5', '7', '0', '0', '9', '2', '3', '8', '0', '0', '3', '0', '9', '0', '0', '3', '4', '4', '3', '1', '6', '5', '0', '3', '2', '9', '9', '0', '8', '8', '3', '6', '0', '2', '5', '8', '1', '4', '7', '5', '1', '0', '3', '"', ',']

theorem object_fragment0230592_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 318) (SourceJson.white (fragment0230592Field007Chars00 ++ tail)) fragment0230592Acc00700 =
      SourceJson.object (fuel + 317) (SourceJson.white tail) fragment0230592Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_007"
  err.flush

noncomputable def fragment0230592Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0230592Field008Value00 : SourceJson := .str (String.ofList ['5', '2', '0', '8', '0', '1', '2', '2', '7', '1', '0', '4', '1', '1'])
noncomputable def fragment0230592Acc00900 : List (String × SourceJson) := (fragment0230592Field008Key00, fragment0230592Field008Value00) :: fragment0230592Acc00800
noncomputable def fragment0230592Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '2', '0', '8', '0', '1', '2', '2', '7', '1', '0', '4', '1', '1', '"', ',']

theorem object_fragment0230592_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 317) (SourceJson.white (fragment0230592Field008Chars00 ++ tail)) fragment0230592Acc00800 =
      SourceJson.object (fuel + 316) (SourceJson.white tail) fragment0230592Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_008"
  err.flush

noncomputable def fragment0230592Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0230592Field009Value00 : SourceJson := .str (String.ofList ['2', '8', '3', '8', '5', '2', '6', '2', '7', '7', '9', '6', '0', '3', '4'])
noncomputable def fragment0230592Acc01000 : List (String × SourceJson) := (fragment0230592Field009Key00, fragment0230592Field009Value00) :: fragment0230592Acc00900
noncomputable def fragment0230592Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '8', '3', '8', '5', '2', '6', '2', '7', '7', '9', '6', '0', '3', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0230592_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 316) (SourceJson.white (fragment0230592Field009Chars00 ++ tail)) fragment0230592Acc00900 =
      .ok (.obj (fragment0230592Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230592_object_field_009"
  err.flush

noncomputable def fragment0230592Chars : List Char := '{' :: (fragment0230592Field000Chars00 ++ fragment0230592Field001Chars00 ++ fragment0230592Field002Chars00 ++ fragment0230592Field003Chars00 ++ fragment0230592Field004Chars00 ++ fragment0230592Field005Chars00 ++ fragment0230592Field006Chars00 ++ fragment0230592Field007Chars00 ++ fragment0230592Field008Chars00 ++ fragment0230592Field009Chars00)
noncomputable def fragment0230592Value : SourceJson := .obj (fragment0230592Acc01000.reverse)

theorem value_fragment0230592 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 326) (fragment0230592Chars ++ tail) =
      .ok (fragment0230592Value, tail) := by
  have hinput : fragment0230592Chars ++ tail = '{' :: (fragment0230592Field000Chars00 ++ (fragment0230592Field001Chars00 ++ (fragment0230592Field002Chars00 ++ (fragment0230592Field003Chars00 ++ (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0230592Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 326) (fragment0230592Chars ++ tail) =
        SourceJson.value (fuel + 326) ('{' :: (fragment0230592Field000Chars00 ++ (fragment0230592Field001Chars00 ++ (fragment0230592Field002Chars00 ++ (fragment0230592Field003Chars00 ++ (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 326)) hinput
    _ = SourceJson.object (fuel + 325) (SourceJson.white (fragment0230592Field000Chars00 ++ (fragment0230592Field001Chars00 ++ (fragment0230592Field002Chars00 ++ (fragment0230592Field003Chars00 ++ (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))))))))))) fragment0230592Acc00000 := by rfl
    _ = SourceJson.object (fuel + 324) (SourceJson.white (fragment0230592Field001Chars00 ++ (fragment0230592Field002Chars00 ++ (fragment0230592Field003Chars00 ++ (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail))))))))))) fragment0230592Acc00100 := object_fragment0230592_field_000 fuel (fragment0230592Field001Chars00 ++ (fragment0230592Field002Chars00 ++ (fragment0230592Field003Chars00 ++ (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 323) (SourceJson.white (fragment0230592Field002Chars00 ++ (fragment0230592Field003Chars00 ++ (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))))))))) fragment0230592Acc00200 := object_fragment0230592_field_001 fuel (fragment0230592Field002Chars00 ++ (fragment0230592Field003Chars00 ++ (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 322) (SourceJson.white (fragment0230592Field003Chars00 ++ (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail))))))))) fragment0230592Acc00300 := object_fragment0230592_field_002 fuel (fragment0230592Field003Chars00 ++ (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 321) (SourceJson.white (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))))))) fragment0230592Acc00400 := object_fragment0230592_field_003 fuel (fragment0230592Field004Chars00 ++ (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 320) (SourceJson.white (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail))))))) fragment0230592Acc00500 := object_fragment0230592_field_004 fuel (fragment0230592Field005Chars00 ++ (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 319) (SourceJson.white (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))))) fragment0230592Acc00600 := object_fragment0230592_field_005 fuel (fragment0230592Field006Chars00 ++ (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 318) (SourceJson.white (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail))))) fragment0230592Acc00700 := object_fragment0230592_field_006 fuel (fragment0230592Field007Chars00 ++ (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 317) (SourceJson.white (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))) fragment0230592Acc00800 := object_fragment0230592_field_007 fuel (fragment0230592Field008Chars00 ++ (fragment0230592Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 316) (SourceJson.white (fragment0230592Field009Chars00 ++ (tail))) fragment0230592Acc00900 := object_fragment0230592_field_008 fuel (fragment0230592Field009Chars00 ++ (tail))
    _ = .ok (fragment0230592Value, tail) := object_fragment0230592_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_before_reader"
  err.flush

noncomputable def chunk0002LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0002SuffixChars00 : List Char := [',']
noncomputable def chunk0002Chars00 : List Char := chunk0002LeadChars00 ++ fragment0229028Chars ++ chunk0002SuffixChars00
noncomputable def chunk0002Push00 (acc : List SourceJson) : List SourceJson := fragment0229028Value :: acc

noncomputable def chunk0002AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0002_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 602)
      (SourceJson.white (chunk0002LeadChars00 ++ (fragment0229028Chars ++ rest))) acc =
      (SourceJson.value (fuel + 601) (fragment0229028Chars ++ rest)).bind
        (chunk0002AfterValue00 (fuel + 601) acc) := by rfl

theorem array_chunk0002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 602) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 601) (SourceJson.white tail) (chunk0002Push00 acc) := by
  have hinput : chunk0002Chars00 ++ tail = chunk0002LeadChars00 ++ (fragment0229028Chars ++ (chunk0002SuffixChars00 ++ tail)) := by
    simp only [chunk0002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 602) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 602)
          (SourceJson.white (chunk0002LeadChars00 ++ (fragment0229028Chars ++ (chunk0002SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 602) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 601) (fragment0229028Chars ++ (chunk0002SuffixChars00 ++ tail))).bind
        (chunk0002AfterValue00 (fuel + 601) acc) := array_chunk0002_head fuel (chunk0002SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0229028Value, chunk0002SuffixChars00 ++ tail)).bind
        (chunk0002AfterValue00 (fuel + 601) acc) :=
      congrArg (fun result => result.bind (chunk0002AfterValue00 (fuel + 601) acc))
        (value_fragment0229028 (fuel + 394) (chunk0002SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 601) (SourceJson.white tail) (chunk0002Push00 acc) := by rfl

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
noncomputable def chunk0003Chars00 : List Char := chunk0003LeadChars00 ++ fragment0230592Chars ++ chunk0003SuffixChars00
noncomputable def chunk0003Push00 (acc : List SourceJson) : List SourceJson := fragment0230592Value :: acc

noncomputable def chunk0003AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0003_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 601)
      (SourceJson.white (chunk0003LeadChars00 ++ (fragment0230592Chars ++ rest))) acc =
      (SourceJson.value (fuel + 600) (fragment0230592Chars ++ rest)).bind
        (chunk0003AfterValue00 (fuel + 600) acc) := by rfl

theorem array_chunk0003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 601) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 600) (SourceJson.white tail) (chunk0003Push00 acc) := by
  have hinput : chunk0003Chars00 ++ tail = chunk0003LeadChars00 ++ (fragment0230592Chars ++ (chunk0003SuffixChars00 ++ tail)) := by
    simp only [chunk0003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 601) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 601)
          (SourceJson.white (chunk0003LeadChars00 ++ (fragment0230592Chars ++ (chunk0003SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 601) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 600) (fragment0230592Chars ++ (chunk0003SuffixChars00 ++ tail))).bind
        (chunk0003AfterValue00 (fuel + 600) acc) := array_chunk0003_head fuel (chunk0003SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0230592Value, chunk0003SuffixChars00 ++ tail)).bind
        (chunk0003AfterValue00 (fuel + 600) acc) :=
      congrArg (fun result => result.bind (chunk0003AfterValue00 (fuel + 600) acc))
        (value_fragment0230592 (fuel + 274) (chunk0003SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 600) (SourceJson.white tail) (chunk0003Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0002Chars00 ++ chunk0003Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0003Push00 (chunk0002Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 602) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 600) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0002Chars00 ++ (chunk0003Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 602) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 602) (SourceJson.white (chunk0002Chars00 ++ (chunk0003Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 602) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 601) (SourceJson.white (chunk0003Chars00 ++ (tail))) (chunk0002Push00 (acc)) := array_chunk0002 fuel (chunk0003Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 600) (SourceJson.white tail) (blockPush acc) := array_chunk0003 fuel (tail) (chunk0002Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 229022).take 3367 = blockChars := by rfl

theorem block_original_split : sourceRest 229022 = blockChars ++ sourceRest 232389 := by
  calc
    sourceRest 229022 = (sourceRest 229022).take 3367 ++ (sourceRest 229022).drop 3367 :=
      (List.take_append_drop 3367 (sourceRest 229022)).symm
    _ = blockChars ++ (sourceRest 229022).drop 3367 :=
      congrArg (fun part => part ++ (sourceRest 229022).drop 3367) block_original_prefix
    _ = blockChars ++ sourceRest 232389 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 229022 3367)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 602) (SourceJson.white (sourceRest 229022)) acc =
      SourceJson.array (fuel + 600) (SourceJson.white (sourceRest 232389)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 602) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 232389) acc)

#print axioms object_fragment0229028_field_000
#print axioms object_fragment0229028_field_001
#print axioms object_fragment0229028_field_002
#print axioms object_fragment0229028_field_003
#print axioms object_fragment0229028_field_004
#print axioms object_fragment0229028_field_005
#print axioms object_fragment0229028_field_006
#print axioms object_fragment0229028_field_007
#print axioms object_fragment0229028_field_008
#print axioms object_fragment0229028_field_009
#print axioms value_fragment0229028
#print axioms object_fragment0230592_field_000
#print axioms object_fragment0230592_field_001
#print axioms object_fragment0230592_field_002
#print axioms object_fragment0230592_field_003
#print axioms object_fragment0230592_field_004
#print axioms object_fragment0230592_field_005
#print axioms object_fragment0230592_field_006
#print axioms object_fragment0230592_field_007
#print axioms object_fragment0230592_field_008
#print axioms object_fragment0230592_field_009
#print axioms value_fragment0230592
#print axioms array_chunk0002_head
#print axioms array_chunk0002
#print axioms array_chunk0003_head
#print axioms array_chunk0003
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock001

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
