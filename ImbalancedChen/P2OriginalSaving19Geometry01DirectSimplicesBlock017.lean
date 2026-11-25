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

namespace SimplicesBlock017

noncomputable def fragment0282872Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0282872Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0282872Field000Value00 : SourceJson := .number (String.ofList ['3', '4'])
noncomputable def fragment0282872Acc00100 : List (String × SourceJson) := (fragment0282872Field000Key00, fragment0282872Field000Value00) :: fragment0282872Acc00000
noncomputable def fragment0282872Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '4', ',']

theorem object_fragment0282872_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0282872Field000Chars00 ++ tail)) fragment0282872Acc00000 =
      SourceJson.object (fuel + 207) (SourceJson.white tail) fragment0282872Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_000"
  err.flush

noncomputable def fragment0282872Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0282872Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0282872Acc00200 : List (String × SourceJson) := (fragment0282872Field001Key00, fragment0282872Field001Value00) :: fragment0282872Acc00100
noncomputable def fragment0282872Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0282872_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 207) (SourceJson.white (fragment0282872Field001Chars00 ++ tail)) fragment0282872Acc00100 =
      SourceJson.object (fuel + 206) (SourceJson.white tail) fragment0282872Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_001"
  err.flush

noncomputable def fragment0282872Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0282872Field002Value00 : SourceJson := .str (String.ofList ['8', '0', '2', '2', '1', '7', '8', '8', '5', '8', '8', '3', '2', '0', '1', '8', '7', '2', '8', '3', '8', '1', '8', '9', '8', '8', '4', '8', '9', '9', '4', '3', '5', '8', '5', '1', '9', '9', '4', '2', '7', '/', '1', '7', '1', '6', '3', '4', '1', '8', '1', '1', '6', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0282872Acc00300 : List (String × SourceJson) := (fragment0282872Field002Key00, fragment0282872Field002Value00) :: fragment0282872Acc00200
noncomputable def fragment0282872Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '0', '2', '2', '1', '7', '8', '8', '5', '8', '8', '3', '2', '0', '1', '8', '7', '2', '8', '3', '8', '1', '8', '9', '8', '8', '4', '8', '9', '9', '4', '3', '5', '8', '5', '1', '9', '9', '4', '2', '7', '/', '1', '7', '1', '6', '3', '4', '1', '8', '1', '1', '6', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0282872_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0282872Field002Chars00 ++ tail)) fragment0282872Acc00200 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0282872Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_002"
  err.flush

noncomputable def fragment0282872Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0282872Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0282872Acc00400 : List (String × SourceJson) := (fragment0282872Field003Key00, fragment0282872Field003Value00) :: fragment0282872Acc00300
noncomputable def fragment0282872Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0282872_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0282872Field003Chars00 ++ tail)) fragment0282872Acc00300 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0282872Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_003"
  err.flush

noncomputable def fragment0282872Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0282872Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0282872Acc00500 : List (String × SourceJson) := (fragment0282872Field004Key00, fragment0282872Field004Value00) :: fragment0282872Acc00400
noncomputable def fragment0282872Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0282872_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0282872Field004Chars00 ++ tail)) fragment0282872Acc00400 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0282872Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_004"
  err.flush

noncomputable def fragment0282872Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0282872Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '5', '1', '2', '4', '8', '5', '9', '5', '3', '/', '1', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '7', '6', '2', '8', '1', '6', '9', '1', '1', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '9', '0', '6', '5', '8', '1', '6', '1', '9', '/', '2', '2', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '7', '4', '8', '3', '1', '6', '4', '3', '2', '9', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '3', '9', '5', '9', '1', '1', '1', '5', '9', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '4', '9', '4', '3', '6', '1', '3', '5', '7', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '4', '6', '0', '2', '7', '5', '0', '6', '3', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '3', '7', '8', '4', '7', '6', '6', '8', '3', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '3', '7', '8', '3', '2', '7', '7', '2', '3', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '6', '9', '1', '5', '9', '0', '2', '6', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0282872Acc00600 : List (String × SourceJson) := (fragment0282872Field005Key00, fragment0282872Field005Value00) :: fragment0282872Acc00500
noncomputable def fragment0282872Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '1', '2', '4', '8', '5', '9', '5', '3', '/', '1', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '6', '2', '8', '1', '6', '9', '1', '1', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '9', '0', '6', '5', '8', '1', '6', '1', '9', '/', '2', '2', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '4', '8', '3', '1', '6', '4', '3', '2', '9', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '3', '9', '5', '9', '1', '1', '1', '5', '9', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '4', '9', '4', '3', '6', '1', '3', '5', '7', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '6', '0', '2', '7', '5', '0', '6', '3', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '3', '7', '8', '4', '7', '6', '6', '8', '3', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '3', '7', '8', '3', '2', '7', '7', '2', '3', '/', '1', '1', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '6', '9', '1', '5', '9', '0', '2', '6', '7', '/', '3', '3', '5', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0282872_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0282872Field005Chars00 ++ tail)) fragment0282872Acc00500 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0282872Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_005"
  err.flush

noncomputable def fragment0282872Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0282872Field006Value00 : SourceJson := .str (String.ofList ['4', '7', '7', '7', '5', '5', '8', '2', '5', '2', '9', '2', '9', '6', '6', '1', '4', '6', '2', '7', '4', '1', '4', '5', '5', '5', '8', '6', '6', '0', '4', '8', '5', '6', '6', '9', '0', '3', '7', '1', '3', '4', '3', '3', '7', '6', '7', '5', '2', '3', '2', '0', '0', '0', '/', '2', '5', '8', '0', '7', '8', '4', '8', '7', '1', '6', '5', '9', '3', '8', '1', '3', '4', '1', '5', '9', '8', '4', '1', '8', '6', '2', '0', '3', '5', '7', '1', '5', '6', '8', '6', '0', '6', '3', '3', '2', '4', '6', '4', '5', '3', '1', '8', '6', '7', '1', '6', '3', '2', '9', '6', '3', '0', '6', '1', '9', '0', '5', '2', '5', '6', '2', '5', '9'])
noncomputable def fragment0282872Acc00700 : List (String × SourceJson) := (fragment0282872Field006Key00, fragment0282872Field006Value00) :: fragment0282872Acc00600
noncomputable def fragment0282872Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '7', '7', '7', '5', '5', '8', '2', '5', '2', '9', '2', '9', '6', '6', '1', '4', '6', '2', '7', '4', '1', '4', '5', '5', '5', '8', '6', '6', '0', '4', '8', '5', '6', '6', '9', '0', '3', '7', '1', '3', '4', '3', '3', '7', '6', '7', '5', '2', '3', '2', '0', '0', '0', '/', '2', '5', '8', '0', '7', '8', '4', '8', '7', '1', '6', '5', '9', '3', '8', '1', '3', '4', '1', '5', '9', '8', '4', '1', '8', '6', '2', '0', '3', '5', '7', '1', '5', '6', '8', '6', '0', '6', '3', '3', '2', '4', '6', '4', '5', '3', '1', '8', '6', '7', '1', '6', '3', '2', '9', '6', '3', '0', '6', '1', '9', '0', '5', '2', '5', '6', '2', '5', '9', '"', ',']

theorem object_fragment0282872_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0282872Field006Chars00 ++ tail)) fragment0282872Acc00600 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0282872Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_006"
  err.flush

noncomputable def fragment0282872Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0282872Field007Value00 : SourceJson := .str (String.ofList ['1', '3', '3', '4', '1', '3', '4', '1', '2', '0', '3', '2', '5', '4', '0', '7', '9', '7', '4', '4', '5', '3', '5', '1', '7', '6', '5', '4', '3', '5', '3', '0', '9', '3', '6', '2', '3', '6', '0', '3', '9', '2', '9', '0', '4', '8', '1', '4', '0', '3', '2', '8', '4', '4', '4', '5', '4', '4', '4', '7', '1', '1', '5', '8', '4', '2', '0', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '0', '9', '5', '8', '7', '3', '6', '0', '9', '4', '8', '9', '8', '2', '2', '2', '2', '7', '3', '8', '0', '0', '0', '9', '4', '6', '9', '0', '7', '3', '1', '9', '3', '0', '0', '7', '0', '7', '8', '7', '1', '4', '9', '3', '2', '8', '1', '9', '2', '6', '3', '9', '3', '8', '9', '5', '7', '9', '9', '1', '1', '8', '6', '0', '3', '9', '2', '9', '7', '8', '1', '2', '0', '0', '2', '1', '9', '1', '7', '9', '0', '3', '8', '1', '4', '6', '3', '1', '3', '4', '7', '5', '7', '4', '2', '4', '5', '8', '9', '1', '1', '4', '9'])
noncomputable def fragment0282872Acc00800 : List (String × SourceJson) := (fragment0282872Field007Key00, fragment0282872Field007Value00) :: fragment0282872Acc00700
noncomputable def fragment0282872Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '3', '4', '1', '3', '4', '1', '2', '0', '3', '2', '5', '4', '0', '7', '9', '7', '4', '4', '5', '3', '5', '1', '7', '6', '5', '4', '3', '5', '3', '0', '9', '3', '6', '2', '3', '6', '0', '3', '9', '2', '9', '0', '4', '8', '1', '4', '0', '3', '2', '8', '4', '4', '4', '5', '4', '4', '4', '7', '1', '1', '5', '8', '4', '2', '0', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '0', '9', '5', '8', '7', '3', '6', '0', '9', '4', '8', '9', '8', '2', '2', '2', '2', '7', '3', '8', '0', '0', '0', '9', '4', '6', '9', '0', '7', '3', '1', '9', '3', '0', '0', '7', '0', '7', '8', '7', '1', '4', '9', '3', '2', '8', '1', '9', '2', '6', '3', '9', '3', '8', '9', '5', '7', '9', '9', '1', '1', '8', '6', '0', '3', '9', '2', '9', '7', '8', '1', '2', '0', '0', '2', '1', '9', '1', '7', '9', '0', '3', '8', '1', '4', '6', '3', '1', '3', '4', '7', '5', '7', '4', '2', '4', '5', '8', '9', '1', '1', '4', '9', '"', ',']

theorem object_fragment0282872_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0282872Field007Chars00 ++ tail)) fragment0282872Acc00700 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0282872Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_007"
  err.flush

noncomputable def fragment0282872Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0282872Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '6', '6', '6', '7', '4', '5', '9', '9', '0', '3', '8', '1', '5'])
noncomputable def fragment0282872Acc00900 : List (String × SourceJson) := (fragment0282872Field008Key00, fragment0282872Field008Value00) :: fragment0282872Acc00800
noncomputable def fragment0282872Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '6', '6', '6', '7', '4', '5', '9', '9', '0', '3', '8', '1', '5', '"', ',']

theorem object_fragment0282872_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0282872Field008Chars00 ++ tail)) fragment0282872Acc00800 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0282872Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_008"
  err.flush

noncomputable def fragment0282872Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0282872Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '8', '9', '0', '5', '0', '2', '8', '4', '6', '8', '9', '6', '1', '1'])
noncomputable def fragment0282872Acc01000 : List (String × SourceJson) := (fragment0282872Field009Key00, fragment0282872Field009Value00) :: fragment0282872Acc00900
noncomputable def fragment0282872Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '8', '9', '0', '5', '0', '2', '8', '4', '6', '8', '9', '6', '1', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0282872_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0282872Field009Chars00 ++ tail)) fragment0282872Acc00900 =
      .ok (.obj (fragment0282872Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282872_object_field_009"
  err.flush

noncomputable def fragment0282872Chars : List Char := '{' :: (fragment0282872Field000Chars00 ++ fragment0282872Field001Chars00 ++ fragment0282872Field002Chars00 ++ fragment0282872Field003Chars00 ++ fragment0282872Field004Chars00 ++ fragment0282872Field005Chars00 ++ fragment0282872Field006Chars00 ++ fragment0282872Field007Chars00 ++ fragment0282872Field008Chars00 ++ fragment0282872Field009Chars00)
noncomputable def fragment0282872Value : SourceJson := .obj (fragment0282872Acc01000.reverse)

theorem value_fragment0282872 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 209) (fragment0282872Chars ++ tail) =
      .ok (fragment0282872Value, tail) := by
  have hinput : fragment0282872Chars ++ tail = '{' :: (fragment0282872Field000Chars00 ++ (fragment0282872Field001Chars00 ++ (fragment0282872Field002Chars00 ++ (fragment0282872Field003Chars00 ++ (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0282872Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 209) (fragment0282872Chars ++ tail) =
        SourceJson.value (fuel + 209) ('{' :: (fragment0282872Field000Chars00 ++ (fragment0282872Field001Chars00 ++ (fragment0282872Field002Chars00 ++ (fragment0282872Field003Chars00 ++ (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 209)) hinput
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0282872Field000Chars00 ++ (fragment0282872Field001Chars00 ++ (fragment0282872Field002Chars00 ++ (fragment0282872Field003Chars00 ++ (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))))))))))) fragment0282872Acc00000 := by rfl
    _ = SourceJson.object (fuel + 207) (SourceJson.white (fragment0282872Field001Chars00 ++ (fragment0282872Field002Chars00 ++ (fragment0282872Field003Chars00 ++ (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail))))))))))) fragment0282872Acc00100 := object_fragment0282872_field_000 fuel (fragment0282872Field001Chars00 ++ (fragment0282872Field002Chars00 ++ (fragment0282872Field003Chars00 ++ (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0282872Field002Chars00 ++ (fragment0282872Field003Chars00 ++ (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))))))))) fragment0282872Acc00200 := object_fragment0282872_field_001 fuel (fragment0282872Field002Chars00 ++ (fragment0282872Field003Chars00 ++ (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0282872Field003Chars00 ++ (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail))))))))) fragment0282872Acc00300 := object_fragment0282872_field_002 fuel (fragment0282872Field003Chars00 ++ (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))))))) fragment0282872Acc00400 := object_fragment0282872_field_003 fuel (fragment0282872Field004Chars00 ++ (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail))))))) fragment0282872Acc00500 := object_fragment0282872_field_004 fuel (fragment0282872Field005Chars00 ++ (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))))) fragment0282872Acc00600 := object_fragment0282872_field_005 fuel (fragment0282872Field006Chars00 ++ (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail))))) fragment0282872Acc00700 := object_fragment0282872_field_006 fuel (fragment0282872Field007Chars00 ++ (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))) fragment0282872Acc00800 := object_fragment0282872_field_007 fuel (fragment0282872Field008Chars00 ++ (fragment0282872Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0282872Field009Chars00 ++ (tail))) fragment0282872Acc00900 := object_fragment0282872_field_008 fuel (fragment0282872Field009Chars00 ++ (tail))
    _ = .ok (fragment0282872Value, tail) := object_fragment0282872_field_009 fuel (tail)

noncomputable def fragment0284442Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0284442Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0284442Field000Value00 : SourceJson := .number (String.ofList ['3', '5'])
noncomputable def fragment0284442Acc00100 : List (String × SourceJson) := (fragment0284442Field000Key00, fragment0284442Field000Value00) :: fragment0284442Acc00000
noncomputable def fragment0284442Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '5', ',']

theorem object_fragment0284442_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0284442Field000Chars00 ++ tail)) fragment0284442Acc00000 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0284442Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_000"
  err.flush

noncomputable def fragment0284442Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0284442Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0284442Acc00200 : List (String × SourceJson) := (fragment0284442Field001Key00, fragment0284442Field001Value00) :: fragment0284442Acc00100
noncomputable def fragment0284442Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0284442_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0284442Field001Chars00 ++ tail)) fragment0284442Acc00100 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0284442Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_001"
  err.flush

noncomputable def fragment0284442Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0284442Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '3', '9', '7', '5', '7', '3', '7', '4', '7', '9', '9', '8', '1', '6', '2', '9', '7', '8', '7', '8', '1', '8', '3', '9', '5', '0', '8', '9', '1', '6', '4', '8', '9', '3', '/', '2', '7', '1', '4', '8', '1', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0284442Acc00300 : List (String × SourceJson) := (fragment0284442Field002Key00, fragment0284442Field002Value00) :: fragment0284442Acc00200
noncomputable def fragment0284442Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '3', '9', '7', '5', '7', '3', '7', '4', '7', '9', '9', '8', '1', '6', '2', '9', '7', '8', '7', '8', '1', '8', '3', '9', '5', '0', '8', '9', '1', '6', '4', '8', '9', '3', '/', '2', '7', '1', '4', '8', '1', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0284442_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0284442Field002Chars00 ++ tail)) fragment0284442Acc00200 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0284442Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_002"
  err.flush

noncomputable def fragment0284442Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0284442Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0284442Acc00400 : List (String × SourceJson) := (fragment0284442Field003Key00, fragment0284442Field003Value00) :: fragment0284442Acc00300
noncomputable def fragment0284442Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0284442_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0284442Field003Chars00 ++ tail)) fragment0284442Acc00300 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0284442Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_003"
  err.flush

noncomputable def fragment0284442Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0284442Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0284442Acc00500 : List (String × SourceJson) := (fragment0284442Field004Key00, fragment0284442Field004Value00) :: fragment0284442Acc00400
noncomputable def fragment0284442Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0284442_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0284442Field004Chars00 ++ tail)) fragment0284442Acc00400 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0284442Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_004"
  err.flush

noncomputable def fragment0284442Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0284442Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '0', '4', '4', '2', '2', '4', '2', '3', '7', '2', '3', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '6', '3', '0', '7', '0', '8', '5', '6', '0', '3', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '1', '7', '8', '6', '0', '1', '1', '8', '2', '1', '/', '8', '1', '3', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '6', '6', '6', '1', '5', '7', '9', '0', '6', '1', '/', '1', '7', '6', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '5', '5', '6', '5', '1', '3', '5', '8', '3', '7', '/', '6', '2', '2', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '7', '9', '6', '6', '2', '7', '6', '3', '7', '4', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '7', '1', '8', '2', '3', '6', '9', '6', '3', '/', '5', '5', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '8', '0', '1', '4', '4', '8', '3', '3', '4', '3', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '5', '7', '4', '0', '5', '3', '8', '5', '7', '0', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '5', '7', '3', '8', '4', '2', '2', '2', '7', '4', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0284442Acc00600 : List (String × SourceJson) := (fragment0284442Field005Key00, fragment0284442Field005Value00) :: fragment0284442Acc00500
noncomputable def fragment0284442Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '4', '4', '2', '2', '4', '2', '3', '7', '2', '3', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '6', '3', '0', '7', '0', '8', '5', '6', '0', '3', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '1', '7', '8', '6', '0', '1', '1', '8', '2', '1', '/', '8', '1', '3', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '6', '6', '6', '1', '5', '7', '9', '0', '6', '1', '/', '1', '7', '6', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '5', '6', '5', '1', '3', '5', '8', '3', '7', '/', '6', '2', '2', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '7', '9', '6', '6', '2', '7', '6', '3', '7', '4', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '7', '1', '8', '2', '3', '6', '9', '6', '3', '/', '5', '5', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '8', '0', '1', '4', '4', '8', '3', '3', '4', '3', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '7', '4', '0', '5', '3', '8', '5', '7', '0', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '5', '7', '3', '8', '4', '2', '2', '2', '7', '4', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0284442_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0284442Field005Chars00 ++ tail)) fragment0284442Acc00500 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0284442Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_005"
  err.flush

noncomputable def fragment0284442Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0284442Field006Value00 : SourceJson := .str (String.ofList ['5', '3', '2', '4', '4', '1', '4', '3', '4', '5', '2', '3', '3', '4', '7', '1', '0', '7', '2', '5', '9', '3', '5', '1', '9', '9', '1', '6', '7', '8', '1', '9', '9', '7', '8', '8', '5', '3', '9', '6', '1', '0', '6', '8', '0', '0', '0', '0', '/', '1', '8', '0', '0', '8', '1', '2', '8', '1', '5', '0', '3', '6', '2', '2', '3', '4', '3', '7', '2', '6', '5', '9', '2', '6', '6', '8', '1', '6', '4', '6', '0', '5', '8', '9', '0', '1', '8', '3', '4', '1', '4', '4', '2', '6', '1', '5', '5', '8', '8', '0', '1', '4', '0', '6', '4', '9', '4', '2', '5', '0', '1', '7', '1'])
noncomputable def fragment0284442Acc00700 : List (String × SourceJson) := (fragment0284442Field006Key00, fragment0284442Field006Value00) :: fragment0284442Acc00600
noncomputable def fragment0284442Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '3', '2', '4', '4', '1', '4', '3', '4', '5', '2', '3', '3', '4', '7', '1', '0', '7', '2', '5', '9', '3', '5', '1', '9', '9', '1', '6', '7', '8', '1', '9', '9', '7', '8', '8', '5', '3', '9', '6', '1', '0', '6', '8', '0', '0', '0', '0', '/', '1', '8', '0', '0', '8', '1', '2', '8', '1', '5', '0', '3', '6', '2', '2', '3', '4', '3', '7', '2', '6', '5', '9', '2', '6', '6', '8', '1', '6', '4', '6', '0', '5', '8', '9', '0', '1', '8', '3', '4', '1', '4', '4', '2', '6', '1', '5', '5', '8', '8', '0', '1', '4', '0', '6', '4', '9', '4', '2', '5', '0', '1', '7', '1', '"', ',']

theorem object_fragment0284442_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0284442Field006Chars00 ++ tail)) fragment0284442Acc00600 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0284442Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_006"
  err.flush

noncomputable def fragment0284442Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0284442Field007Value00 : SourceJson := .str (String.ofList ['4', '5', '8', '6', '9', '1', '8', '6', '1', '1', '2', '0', '5', '7', '2', '7', '1', '7', '0', '3', '8', '9', '8', '2', '1', '8', '8', '3', '2', '0', '4', '0', '9', '9', '4', '2', '4', '3', '9', '4', '6', '4', '0', '6', '3', '0', '1', '5', '6', '8', '5', '1', '4', '3', '2', '5', '8', '7', '8', '7', '1', '6', '9', '8', '9', '8', '9', '6', '4', '9', '4', '7', '9', '1', '4', '9', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '9', '0', '7', '6', '4', '0', '3', '2', '4', '4', '1', '2', '0', '9', '3', '9', '5', '5', '2', '9', '2', '6', '2', '7', '8', '6', '4', '9', '9', '6', '8', '7', '7', '4', '2', '8', '8', '0', '7', '2', '7', '8', '5', '9', '5', '0', '3', '3', '6', '9', '6', '8', '8', '2', '2', '6', '4', '6', '8', '7', '0', '8', '1', '3', '6', '1', '4', '1', '8', '7', '0', '4', '1', '2', '3', '5', '8', '2', '2', '6', '3', '7', '4', '8', '6', '9', '4', '3', '1', '4', '4', '9', '8', '9', '8', '1', '7', '5', '1', '4', '0', '1', '7', '7', '2', '2', '0', '9', '5', '7', '5', '5', '9', '7', '9', '7', '3'])
noncomputable def fragment0284442Acc00800 : List (String × SourceJson) := (fragment0284442Field007Key00, fragment0284442Field007Value00) :: fragment0284442Acc00700
noncomputable def fragment0284442Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '5', '8', '6', '9', '1', '8', '6', '1', '1', '2', '0', '5', '7', '2', '7', '1', '7', '0', '3', '8', '9', '8', '2', '1', '8', '8', '3', '2', '0', '4', '0', '9', '9', '4', '2', '4', '3', '9', '4', '6', '4', '0', '6', '3', '0', '1', '5', '6', '8', '5', '1', '4', '3', '2', '5', '8', '7', '8', '7', '1', '6', '9', '8', '9', '8', '9', '6', '4', '9', '4', '7', '9', '1', '4', '9', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '9', '0', '7', '6', '4', '0', '3', '2', '4', '4', '1', '2', '0', '9', '3', '9', '5', '5', '2', '9', '2', '6', '2', '7', '8', '6', '4', '9', '9', '6', '8', '7', '7', '4', '2', '8', '8', '0', '7', '2', '7', '8', '5', '9', '5', '0', '3', '3', '6', '9', '6', '8', '8', '2', '2', '6', '4', '6', '8', '7', '0', '8', '1', '3', '6', '1', '4', '1', '8', '7', '0', '4', '1', '2', '3', '5', '8', '2', '2', '6', '3', '7', '4', '8', '6', '9', '4', '3', '1', '4', '4', '9', '8', '9', '8', '1', '7', '5', '1', '4', '0', '1', '7', '7', '2', '2', '0', '9', '5', '7', '5', '5', '9', '7', '9', '7', '3', '"', ',']

theorem object_fragment0284442_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0284442Field007Chars00 ++ tail)) fragment0284442Acc00700 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0284442Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_007"
  err.flush

noncomputable def fragment0284442Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0284442Field008Value00 : SourceJson := .str (String.ofList ['2', '3', '4', '2', '5', '1', '7', '5', '6', '4', '9', '3', '0', '5'])
noncomputable def fragment0284442Acc00900 : List (String × SourceJson) := (fragment0284442Field008Key00, fragment0284442Field008Value00) :: fragment0284442Acc00800
noncomputable def fragment0284442Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '4', '2', '5', '1', '7', '5', '6', '4', '9', '3', '0', '5', '"', ',']

theorem object_fragment0284442_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0284442Field008Chars00 ++ tail)) fragment0284442Acc00800 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0284442Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_008"
  err.flush

noncomputable def fragment0284442Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0284442Field009Value00 : SourceJson := .str (String.ofList ['2', '0', '2', '9', '3', '7', '4', '7', '6', '1', '7', '4', '8', '4', '7'])
noncomputable def fragment0284442Acc01000 : List (String × SourceJson) := (fragment0284442Field009Key00, fragment0284442Field009Value00) :: fragment0284442Acc00900
noncomputable def fragment0284442Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '2', '9', '3', '7', '4', '7', '6', '1', '7', '4', '8', '4', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0284442_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0284442Field009Chars00 ++ tail)) fragment0284442Acc00900 =
      .ok (.obj (fragment0284442Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284442_object_field_009"
  err.flush

noncomputable def fragment0284442Chars : List Char := '{' :: (fragment0284442Field000Chars00 ++ fragment0284442Field001Chars00 ++ fragment0284442Field002Chars00 ++ fragment0284442Field003Chars00 ++ fragment0284442Field004Chars00 ++ fragment0284442Field005Chars00 ++ fragment0284442Field006Chars00 ++ fragment0284442Field007Chars00 ++ fragment0284442Field008Chars00 ++ fragment0284442Field009Chars00)
noncomputable def fragment0284442Value : SourceJson := .obj (fragment0284442Acc01000.reverse)

theorem value_fragment0284442 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 235) (fragment0284442Chars ++ tail) =
      .ok (fragment0284442Value, tail) := by
  have hinput : fragment0284442Chars ++ tail = '{' :: (fragment0284442Field000Chars00 ++ (fragment0284442Field001Chars00 ++ (fragment0284442Field002Chars00 ++ (fragment0284442Field003Chars00 ++ (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0284442Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 235) (fragment0284442Chars ++ tail) =
        SourceJson.value (fuel + 235) ('{' :: (fragment0284442Field000Chars00 ++ (fragment0284442Field001Chars00 ++ (fragment0284442Field002Chars00 ++ (fragment0284442Field003Chars00 ++ (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 235)) hinput
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0284442Field000Chars00 ++ (fragment0284442Field001Chars00 ++ (fragment0284442Field002Chars00 ++ (fragment0284442Field003Chars00 ++ (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))))))))))) fragment0284442Acc00000 := by rfl
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0284442Field001Chars00 ++ (fragment0284442Field002Chars00 ++ (fragment0284442Field003Chars00 ++ (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail))))))))))) fragment0284442Acc00100 := object_fragment0284442_field_000 fuel (fragment0284442Field001Chars00 ++ (fragment0284442Field002Chars00 ++ (fragment0284442Field003Chars00 ++ (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0284442Field002Chars00 ++ (fragment0284442Field003Chars00 ++ (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))))))))) fragment0284442Acc00200 := object_fragment0284442_field_001 fuel (fragment0284442Field002Chars00 ++ (fragment0284442Field003Chars00 ++ (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0284442Field003Chars00 ++ (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail))))))))) fragment0284442Acc00300 := object_fragment0284442_field_002 fuel (fragment0284442Field003Chars00 ++ (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))))))) fragment0284442Acc00400 := object_fragment0284442_field_003 fuel (fragment0284442Field004Chars00 ++ (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail))))))) fragment0284442Acc00500 := object_fragment0284442_field_004 fuel (fragment0284442Field005Chars00 ++ (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))))) fragment0284442Acc00600 := object_fragment0284442_field_005 fuel (fragment0284442Field006Chars00 ++ (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail))))) fragment0284442Acc00700 := object_fragment0284442_field_006 fuel (fragment0284442Field007Chars00 ++ (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))) fragment0284442Acc00800 := object_fragment0284442_field_007 fuel (fragment0284442Field008Chars00 ++ (fragment0284442Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0284442Field009Chars00 ++ (tail))) fragment0284442Acc00900 := object_fragment0284442_field_008 fuel (fragment0284442Field009Chars00 ++ (tail))
    _ = .ok (fragment0284442Value, tail) := object_fragment0284442_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_before_reader"
  err.flush

noncomputable def chunk0034LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0034SuffixChars00 : List Char := [',']
noncomputable def chunk0034Chars00 : List Char := chunk0034LeadChars00 ++ fragment0282872Chars ++ chunk0034SuffixChars00
noncomputable def chunk0034Push00 (acc : List SourceJson) : List SourceJson := fragment0282872Value :: acc

noncomputable def chunk0034AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0034_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 570)
      (SourceJson.white (chunk0034LeadChars00 ++ (fragment0282872Chars ++ rest))) acc =
      (SourceJson.value (fuel + 569) (fragment0282872Chars ++ rest)).bind
        (chunk0034AfterValue00 (fuel + 569) acc) := by rfl

theorem array_chunk0034 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 570) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 569) (SourceJson.white tail) (chunk0034Push00 acc) := by
  have hinput : chunk0034Chars00 ++ tail = chunk0034LeadChars00 ++ (fragment0282872Chars ++ (chunk0034SuffixChars00 ++ tail)) := by
    simp only [chunk0034Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 570) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 570)
          (SourceJson.white (chunk0034LeadChars00 ++ (fragment0282872Chars ++ (chunk0034SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 570) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 569) (fragment0282872Chars ++ (chunk0034SuffixChars00 ++ tail))).bind
        (chunk0034AfterValue00 (fuel + 569) acc) := array_chunk0034_head fuel (chunk0034SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0282872Value, chunk0034SuffixChars00 ++ tail)).bind
        (chunk0034AfterValue00 (fuel + 569) acc) :=
      congrArg (fun result => result.bind (chunk0034AfterValue00 (fuel + 569) acc))
        (value_fragment0282872 (fuel + 360) (chunk0034SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 569) (SourceJson.white tail) (chunk0034Push00 acc) := by rfl

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
noncomputable def chunk0035Chars00 : List Char := chunk0035LeadChars00 ++ fragment0284442Chars ++ chunk0035SuffixChars00
noncomputable def chunk0035Push00 (acc : List SourceJson) : List SourceJson := fragment0284442Value :: acc

noncomputable def chunk0035AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0035_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 569)
      (SourceJson.white (chunk0035LeadChars00 ++ (fragment0284442Chars ++ rest))) acc =
      (SourceJson.value (fuel + 568) (fragment0284442Chars ++ rest)).bind
        (chunk0035AfterValue00 (fuel + 568) acc) := by rfl

theorem array_chunk0035 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 569) (SourceJson.white (chunk0035Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 568) (SourceJson.white tail) (chunk0035Push00 acc) := by
  have hinput : chunk0035Chars00 ++ tail = chunk0035LeadChars00 ++ (fragment0284442Chars ++ (chunk0035SuffixChars00 ++ tail)) := by
    simp only [chunk0035Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 569) (SourceJson.white (chunk0035Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 569)
          (SourceJson.white (chunk0035LeadChars00 ++ (fragment0284442Chars ++ (chunk0035SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 569) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 568) (fragment0284442Chars ++ (chunk0035SuffixChars00 ++ tail))).bind
        (chunk0035AfterValue00 (fuel + 568) acc) := array_chunk0035_head fuel (chunk0035SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0284442Value, chunk0035SuffixChars00 ++ tail)).bind
        (chunk0035AfterValue00 (fuel + 568) acc) :=
      congrArg (fun result => result.bind (chunk0035AfterValue00 (fuel + 568) acc))
        (value_fragment0284442 (fuel + 333) (chunk0035SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 568) (SourceJson.white tail) (chunk0035Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0034Chars00 ++ chunk0035Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0035Push00 (chunk0034Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 570) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 568) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0034Chars00 ++ (chunk0035Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 570) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 570) (SourceJson.white (chunk0034Chars00 ++ (chunk0035Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 570) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 569) (SourceJson.white (chunk0035Chars00 ++ (tail))) (chunk0034Push00 (acc)) := array_chunk0034 fuel (chunk0035Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 568) (SourceJson.white tail) (blockPush acc) := array_chunk0035 fuel (tail) (chunk0034Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 282866).take 3169 = blockChars := by rfl

theorem block_original_split : sourceRest 282866 = blockChars ++ sourceRest 286035 := by
  calc
    sourceRest 282866 = (sourceRest 282866).take 3169 ++ (sourceRest 282866).drop 3169 :=
      (List.take_append_drop 3169 (sourceRest 282866)).symm
    _ = blockChars ++ (sourceRest 282866).drop 3169 :=
      congrArg (fun part => part ++ (sourceRest 282866).drop 3169) block_original_prefix
    _ = blockChars ++ sourceRest 286035 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 282866 3169)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 570) (SourceJson.white (sourceRest 282866)) acc =
      SourceJson.array (fuel + 568) (SourceJson.white (sourceRest 286035)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 570) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 286035) acc)

#print axioms object_fragment0282872_field_000
#print axioms object_fragment0282872_field_001
#print axioms object_fragment0282872_field_002
#print axioms object_fragment0282872_field_003
#print axioms object_fragment0282872_field_004
#print axioms object_fragment0282872_field_005
#print axioms object_fragment0282872_field_006
#print axioms object_fragment0282872_field_007
#print axioms object_fragment0282872_field_008
#print axioms object_fragment0282872_field_009
#print axioms value_fragment0282872
#print axioms object_fragment0284442_field_000
#print axioms object_fragment0284442_field_001
#print axioms object_fragment0284442_field_002
#print axioms object_fragment0284442_field_003
#print axioms object_fragment0284442_field_004
#print axioms object_fragment0284442_field_005
#print axioms object_fragment0284442_field_006
#print axioms object_fragment0284442_field_007
#print axioms object_fragment0284442_field_008
#print axioms object_fragment0284442_field_009
#print axioms value_fragment0284442
#print axioms array_chunk0034_head
#print axioms array_chunk0034
#print axioms array_chunk0035_head
#print axioms array_chunk0035
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock017

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
