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

namespace SimplicesBlock051

noncomputable def fragment0397549Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0397549Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0397549Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '0'])
noncomputable def fragment0397549Acc00100 : List (String × SourceJson) := (fragment0397549Field000Key00, fragment0397549Field000Value00) :: fragment0397549Acc00000
noncomputable def fragment0397549Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '0', ',']

theorem object_fragment0397549_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0397549Field000Chars00 ++ tail)) fragment0397549Acc00000 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0397549Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_000"
  err.flush

noncomputable def fragment0397549Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0397549Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['7']), .number (String.ofList ['0'])]
noncomputable def fragment0397549Acc00200 : List (String × SourceJson) := (fragment0397549Field001Key00, fragment0397549Field001Value00) :: fragment0397549Acc00100
noncomputable def fragment0397549Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0397549_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0397549Field001Chars00 ++ tail)) fragment0397549Acc00100 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0397549Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_001"
  err.flush

noncomputable def fragment0397549Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0397549Field002Value00 : SourceJson := .str (String.ofList ['3', '6', '0', '5', '1', '6', '9', '9', '2', '1', '7', '9', '4', '4', '9', '7', '0', '9', '9', '0', '1', '4', '6', '5', '8', '2', '5', '1', '1', '9', '6', '7', '2', '9', '3', '6', '7', '4', '8', '6', '5', '3', '0', '9', '7', '/', '1', '5', '2', '3', '6', '2', '4', '1', '2', '0', '4', '6', '0', '4', '9', '0', '3', '0', '9', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0397549Acc00300 : List (String × SourceJson) := (fragment0397549Field002Key00, fragment0397549Field002Value00) :: fragment0397549Acc00200
noncomputable def fragment0397549Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '6', '0', '5', '1', '6', '9', '9', '2', '1', '7', '9', '4', '4', '9', '7', '0', '9', '9', '0', '1', '4', '6', '5', '8', '2', '5', '1', '1', '9', '6', '7', '2', '9', '3', '6', '7', '4', '8', '6', '5', '3', '0', '9', '7', '/', '1', '5', '2', '3', '6', '2', '4', '1', '2', '0', '4', '6', '0', '4', '9', '0', '3', '0', '9', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0397549_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0397549Field002Chars00 ++ tail)) fragment0397549Acc00200 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0397549Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_002"
  err.flush

noncomputable def fragment0397549Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0397549Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0397549Acc00400 : List (String × SourceJson) := (fragment0397549Field003Key00, fragment0397549Field003Value00) :: fragment0397549Acc00300
noncomputable def fragment0397549Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0397549_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0397549Field003Chars00 ++ tail)) fragment0397549Acc00300 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0397549Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_003"
  err.flush

noncomputable def fragment0397549Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0397549Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0397549Acc00500 : List (String × SourceJson) := (fragment0397549Field004Key00, fragment0397549Field004Value00) :: fragment0397549Acc00400
noncomputable def fragment0397549Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '3', '7', '9', '/', '1', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0397549_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0397549Field004Chars00 ++ tail)) fragment0397549Acc00400 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0397549Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_004"
  err.flush

noncomputable def fragment0397549Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0397549Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '0', '7', '7', '7', '5', '6', '1', '4', '3', '/', '5', '1', '9', '9', '4', '6', '8', '7', '5', '0', '0']), .str (String.ofList ['5', '2', '3', '4', '1', '0', '2', '9', '8', '9', '9', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '1', '8', '1', '2', '6', '4', '5', '9', '5', '9', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '8', '0', '9', '3', '2', '0', '5', '1', '0', '7', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '8', '8', '0', '8', '3', '9', '2', '8', '7', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '3', '5', '2', '3', '4', '0', '5', '6', '1', '/', '2', '4', '9', '5', '7', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '3', '6', '3', '8', '7', '2', '5', '4', '7', '/', '1', '0', '5', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '2', '2', '5', '2', '4', '0', '3', '7', '7', '1', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '2', '9', '7', '8', '8', '5', '8', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '9', '5', '7', '1', '4', '5', '3', '9', '9', '1', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0397549Acc00600 : List (String × SourceJson) := (fragment0397549Field005Key00, fragment0397549Field005Value00) :: fragment0397549Acc00500
noncomputable def fragment0397549Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '7', '7', '7', '5', '6', '1', '4', '3', '/', '5', '1', '9', '9', '4', '6', '8', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '3', '4', '1', '0', '2', '9', '8', '9', '9', '/', '6', '6', '5', '5', '3', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '1', '8', '1', '2', '6', '4', '5', '9', '5', '9', '/', '9', '9', '8', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '8', '0', '9', '3', '2', '0', '5', '1', '0', '7', '/', '2', '2', '1', '8', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '8', '8', '0', '8', '3', '9', '2', '8', '7', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '3', '5', '2', '3', '4', '0', '5', '6', '1', '/', '2', '4', '9', '5', '7', '4', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '3', '6', '3', '8', '7', '2', '5', '4', '7', '/', '1', '0', '5', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '2', '2', '5', '2', '4', '0', '3', '7', '7', '1', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '2', '9', '7', '8', '8', '5', '8', '3', '/', '4', '9', '9', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '9', '5', '7', '1', '4', '5', '3', '9', '9', '1', '/', '1', '9', '9', '6', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0397549_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0397549Field005Chars00 ++ tail)) fragment0397549Acc00500 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0397549Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_005"
  err.flush

noncomputable def fragment0397549Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0397549Field006Value00 : SourceJson := .str (String.ofList ['3', '0', '2', '7', '4', '4', '2', '6', '8', '4', '9', '8', '8', '9', '7', '0', '9', '3', '7', '0', '0', '0', '0', '0', '7', '2', '0', '2', '5', '3', '1', '5', '0', '5', '6', '2', '3', '1', '5', '0', '0', '4', '4', '5', '4', '9', '8', '2', '6', '8', '/', '1', '2', '8', '0', '4', '4', '8', '7', '7', '5', '9', '4', '3', '8', '8', '4', '3', '3', '6', '2', '9', '3', '7', '8', '1', '6', '6', '3', '0', '1', '4', '4', '5', '4', '6', '8', '5', '4', '9', '7', '4', '9', '7', '8', '9', '6', '1', '9', '8', '9', '8', '6', '4', '3', '7', '5', '5', '2', '6', '9', '1', '1', '7', '9'])
noncomputable def fragment0397549Acc00700 : List (String × SourceJson) := (fragment0397549Field006Key00, fragment0397549Field006Value00) :: fragment0397549Acc00600
noncomputable def fragment0397549Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '2', '7', '4', '4', '2', '6', '8', '4', '9', '8', '8', '9', '7', '0', '9', '3', '7', '0', '0', '0', '0', '0', '7', '2', '0', '2', '5', '3', '1', '5', '0', '5', '6', '2', '3', '1', '5', '0', '0', '4', '4', '5', '4', '9', '8', '2', '6', '8', '/', '1', '2', '8', '0', '4', '4', '8', '7', '7', '5', '9', '4', '3', '8', '8', '4', '3', '3', '6', '2', '9', '3', '7', '8', '1', '6', '6', '3', '0', '1', '4', '4', '5', '4', '6', '8', '5', '4', '9', '7', '4', '9', '7', '8', '9', '6', '1', '9', '8', '9', '8', '6', '4', '3', '7', '5', '5', '2', '6', '9', '1', '1', '7', '9', '"', ',']

theorem object_fragment0397549_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0397549Field006Chars00 ++ tail)) fragment0397549Acc00600 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0397549Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_006"
  err.flush

noncomputable def fragment0397549Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0397549Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '8', '6', '6', '8', '4', '8', '2', '4', '2', '2', '2', '0', '5', '1', '1', '4', '6', '7', '6', '5', '1', '7', '9', '1', '2', '6', '9', '3', '6', '9', '9', '6', '0', '1', '4', '1', '4', '3', '5', '0', '5', '8', '8', '7', '5', '8', '2', '5', '3', '1', '8', '1', '5', '1', '0', '1', '2', '6', '8', '0', '0', '9', '3', '4', '9', '1', '6', '3', '0', '2', '9', '4', '9', '9', '0', '5', '1', '0', '3', '7', '8', '5', '0', '9', '5', '2', '1', '4', '8', '4', '3', '7', '5', '0', '0', '/', '1', '3', '3', '1', '8', '4', '6', '7', '1', '2', '4', '9', '2', '7', '3', '9', '2', '7', '6', '3', '3', '5', '4', '2', '3', '7', '8', '8', '3', '7', '8', '7', '0', '4', '5', '5', '1', '3', '0', '9', '2', '6', '9', '0', '7', '6', '7', '3', '0', '8', '4', '5', '9', '5', '5', '7', '0', '1', '9', '4', '8', '3', '8', '2', '5', '8', '4', '1', '4', '0', '5', '3', '2', '0', '6', '4', '6', '2', '6', '5', '8', '7', '5', '8', '0', '4', '5', '8', '2', '8', '0', '3', '4', '8', '9', '4', '0', '8', '8', '6', '6', '8', '8', '4', '7', '9', '9', '9', '2', '7'])
noncomputable def fragment0397549Acc00800 : List (String × SourceJson) := (fragment0397549Field007Key00, fragment0397549Field007Value00) :: fragment0397549Acc00700
noncomputable def fragment0397549Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '8', '6', '6', '8', '4', '8', '2', '4', '2', '2', '2', '0', '5', '1', '1', '4', '6', '7', '6', '5', '1', '7', '9', '1', '2', '6', '9', '3', '6', '9', '9', '6', '0', '1', '4', '1', '4', '3', '5', '0', '5', '8', '8', '7', '5', '8', '2', '5', '3', '1', '8', '1', '5', '1', '0', '1', '2', '6', '8', '0', '0', '9', '3', '4', '9', '1', '6', '3', '0', '2', '9', '4', '9', '9', '0', '5', '1', '0', '3', '7', '8', '5', '0', '9', '5', '2', '1', '4', '8', '4', '3', '7', '5', '0', '0', '/', '1', '3', '3', '1', '8', '4', '6', '7', '1', '2', '4', '9', '2', '7', '3', '9', '2', '7', '6', '3', '3', '5', '4', '2', '3', '7', '8', '8', '3', '7', '8', '7', '0', '4', '5', '5', '1', '3', '0', '9', '2', '6', '9', '0', '7', '6', '7', '3', '0', '8', '4', '5', '9', '5', '5', '7', '0', '1', '9', '4', '8', '3', '8', '2', '5', '8', '4', '1', '4', '0', '5', '3', '2', '0', '6', '4', '6', '2', '6', '5', '8', '7', '5', '8', '0', '4', '5', '8', '2', '8', '0', '3', '4', '8', '9', '4', '0', '8', '8', '6', '6', '8', '8', '4', '7', '9', '9', '9', '2', '7', '"', ',']

theorem object_fragment0397549_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0397549Field007Chars00 ++ tail)) fragment0397549Acc00700 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0397549Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_007"
  err.flush

noncomputable def fragment0397549Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0397549Field008Value00 : SourceJson := .str (String.ofList ['1', '8', '7', '3', '2', '3', '9', '4', '8', '8', '8', '0', '4', '3', '4', '3'])
noncomputable def fragment0397549Acc00900 : List (String × SourceJson) := (fragment0397549Field008Key00, fragment0397549Field008Value00) :: fragment0397549Acc00800
noncomputable def fragment0397549Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '7', '3', '2', '3', '9', '4', '8', '8', '8', '0', '4', '3', '4', '3', '"', ',']

theorem object_fragment0397549_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0397549Field008Chars00 ++ tail)) fragment0397549Acc00800 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0397549Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_008"
  err.flush

noncomputable def fragment0397549Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0397549Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '0', '0', '8', '0', '3', '0', '0', '5', '2', '9', '9', '9', '4', '1', '3'])
noncomputable def fragment0397549Acc01000 : List (String × SourceJson) := (fragment0397549Field009Key00, fragment0397549Field009Value00) :: fragment0397549Acc00900
noncomputable def fragment0397549Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '0', '0', '8', '0', '3', '0', '0', '5', '2', '9', '9', '9', '4', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0397549_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0397549Field009Chars00 ++ tail)) fragment0397549Acc00900 =
      .ok (.obj (fragment0397549Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0397549_object_field_009"
  err.flush

noncomputable def fragment0397549Chars : List Char := '{' :: (fragment0397549Field000Chars00 ++ fragment0397549Field001Chars00 ++ fragment0397549Field002Chars00 ++ fragment0397549Field003Chars00 ++ fragment0397549Field004Chars00 ++ fragment0397549Field005Chars00 ++ fragment0397549Field006Chars00 ++ fragment0397549Field007Chars00 ++ fragment0397549Field008Chars00 ++ fragment0397549Field009Chars00)
noncomputable def fragment0397549Value : SourceJson := .obj (fragment0397549Acc01000.reverse)

theorem value_fragment0397549 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 219) (fragment0397549Chars ++ tail) =
      .ok (fragment0397549Value, tail) := by
  have hinput : fragment0397549Chars ++ tail = '{' :: (fragment0397549Field000Chars00 ++ (fragment0397549Field001Chars00 ++ (fragment0397549Field002Chars00 ++ (fragment0397549Field003Chars00 ++ (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0397549Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 219) (fragment0397549Chars ++ tail) =
        SourceJson.value (fuel + 219) ('{' :: (fragment0397549Field000Chars00 ++ (fragment0397549Field001Chars00 ++ (fragment0397549Field002Chars00 ++ (fragment0397549Field003Chars00 ++ (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 219)) hinput
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0397549Field000Chars00 ++ (fragment0397549Field001Chars00 ++ (fragment0397549Field002Chars00 ++ (fragment0397549Field003Chars00 ++ (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))))))))))) fragment0397549Acc00000 := by rfl
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0397549Field001Chars00 ++ (fragment0397549Field002Chars00 ++ (fragment0397549Field003Chars00 ++ (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail))))))))))) fragment0397549Acc00100 := object_fragment0397549_field_000 fuel (fragment0397549Field001Chars00 ++ (fragment0397549Field002Chars00 ++ (fragment0397549Field003Chars00 ++ (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0397549Field002Chars00 ++ (fragment0397549Field003Chars00 ++ (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))))))))) fragment0397549Acc00200 := object_fragment0397549_field_001 fuel (fragment0397549Field002Chars00 ++ (fragment0397549Field003Chars00 ++ (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0397549Field003Chars00 ++ (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail))))))))) fragment0397549Acc00300 := object_fragment0397549_field_002 fuel (fragment0397549Field003Chars00 ++ (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))))))) fragment0397549Acc00400 := object_fragment0397549_field_003 fuel (fragment0397549Field004Chars00 ++ (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail))))))) fragment0397549Acc00500 := object_fragment0397549_field_004 fuel (fragment0397549Field005Chars00 ++ (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))))) fragment0397549Acc00600 := object_fragment0397549_field_005 fuel (fragment0397549Field006Chars00 ++ (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail))))) fragment0397549Acc00700 := object_fragment0397549_field_006 fuel (fragment0397549Field007Chars00 ++ (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))) fragment0397549Acc00800 := object_fragment0397549_field_007 fuel (fragment0397549Field008Chars00 ++ (fragment0397549Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0397549Field009Chars00 ++ (tail))) fragment0397549Acc00900 := object_fragment0397549_field_008 fuel (fragment0397549Field009Chars00 ++ (tail))
    _ = .ok (fragment0397549Value, tail) := object_fragment0397549_field_009 fuel (tail)

noncomputable def fragment0399129Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0399129Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0399129Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '1'])
noncomputable def fragment0399129Acc00100 : List (String × SourceJson) := (fragment0399129Field000Key00, fragment0399129Field000Value00) :: fragment0399129Acc00000
noncomputable def fragment0399129Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '1', ',']

theorem object_fragment0399129_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0399129Field000Chars00 ++ tail)) fragment0399129Acc00000 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0399129Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_000"
  err.flush

noncomputable def fragment0399129Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0399129Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['7'])]
noncomputable def fragment0399129Acc00200 : List (String × SourceJson) := (fragment0399129Field001Key00, fragment0399129Field001Value00) :: fragment0399129Acc00100
noncomputable def fragment0399129Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0399129_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0399129Field001Chars00 ++ tail)) fragment0399129Acc00100 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0399129Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_001"
  err.flush

noncomputable def fragment0399129Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0399129Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '2', '7', '1', '5', '8', '4', '2', '5', '3', '9', '5', '6', '9', '4', '4', '9', '8', '8', '4', '3', '9', '0', '8', '4', '5', '8', '7', '7', '0', '5', '1', '1', '3', '2', '8', '5', '6', '2', '8', '5', '8', '1', '3', '/', '5', '3', '3', '2', '6', '8', '4', '4', '2', '1', '6', '1', '1', '7', '1', '6', '0', '8', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0399129Acc00300 : List (String × SourceJson) := (fragment0399129Field002Key00, fragment0399129Field002Value00) :: fragment0399129Acc00200
noncomputable def fragment0399129Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '2', '7', '1', '5', '8', '4', '2', '5', '3', '9', '5', '6', '9', '4', '4', '9', '8', '8', '4', '3', '9', '0', '8', '4', '5', '8', '7', '7', '0', '5', '1', '1', '3', '2', '8', '5', '6', '2', '8', '5', '8', '1', '3', '/', '5', '3', '3', '2', '6', '8', '4', '4', '2', '1', '6', '1', '1', '7', '1', '6', '0', '8', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0399129_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0399129Field002Chars00 ++ tail)) fragment0399129Acc00200 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0399129Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_002"
  err.flush

noncomputable def fragment0399129Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0399129Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0399129Acc00400 : List (String × SourceJson) := (fragment0399129Field003Key00, fragment0399129Field003Value00) :: fragment0399129Acc00300
noncomputable def fragment0399129Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0399129_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0399129Field003Chars00 ++ tail)) fragment0399129Acc00300 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0399129Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_003"
  err.flush

noncomputable def fragment0399129Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0399129Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '3', '1', '1', '7', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0399129Acc00500 : List (String × SourceJson) := (fragment0399129Field004Key00, fragment0399129Field004Value00) :: fragment0399129Acc00400
noncomputable def fragment0399129Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '3', '1', '1', '7', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0399129_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0399129Field004Chars00 ++ tail)) fragment0399129Acc00400 =
      SourceJson.object (fuel + 208) (SourceJson.white tail) fragment0399129Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_004"
  err.flush

noncomputable def fragment0399129Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0399129Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '4', '3', '0', '2', '7', '5', '1', '9', '9', '9', '9', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '6', '8', '8', '7', '9', '0', '4', '3', '9', '/', '3', '8', '0', '3', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '1', '4', '2', '3', '3', '5', '9', '4', '9', '3', '/', '5', '7', '0', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '9', '5', '0', '1', '8', '2', '6', '8', '1', '/', '3', '6', '9', '7', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '7', '2', '1', '9', '0', '9', '2', '0', '5', '1', '/', '7', '9', '8', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '8', '9', '8', '9', '2', '1', '6', '6', '2', '3', '/', '5', '7', '0', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '9', '7', '5', '7', '9', '4', '1', '7', '9', '/', '2', '1', '0', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '7', '2', '1', '7', '7', '4', '0', '1', '5', '7', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '6', '5', '5', '1', '2', '4', '1', '2', '7', '9', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '7', '1', '6', '5', '5', '2', '1', '1', '9', '/', '1', '5', '9', '7', '2', '7', '6', '8', '0', '0', '0', '0', '0'])]
noncomputable def fragment0399129Acc00600 : List (String × SourceJson) := (fragment0399129Field005Key00, fragment0399129Field005Value00) :: fragment0399129Acc00500
noncomputable def fragment0399129Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '0', '2', '7', '5', '1', '9', '9', '9', '9', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '8', '8', '7', '9', '0', '4', '3', '9', '/', '3', '8', '0', '3', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '1', '4', '2', '3', '3', '5', '9', '4', '9', '3', '/', '5', '7', '0', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '9', '5', '0', '1', '8', '2', '6', '8', '1', '/', '3', '6', '9', '7', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '7', '2', '1', '9', '0', '9', '2', '0', '5', '1', '/', '7', '9', '8', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '9', '8', '9', '2', '1', '6', '6', '2', '3', '/', '5', '7', '0', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '9', '7', '5', '7', '9', '4', '1', '7', '9', '/', '2', '1', '0', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '7', '2', '1', '7', '7', '4', '0', '1', '5', '7', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '6', '5', '5', '1', '2', '4', '1', '2', '7', '9', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '7', '1', '6', '5', '5', '2', '1', '1', '9', '/', '1', '5', '9', '7', '2', '7', '6', '8', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0399129_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0399129Field005Chars00 ++ tail)) fragment0399129Acc00500 =
      SourceJson.object (fuel + 207) (SourceJson.white tail) fragment0399129Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_005"
  err.flush

noncomputable def fragment0399129Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0399129Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '9', '7', '0', '8', '8', '4', '8', '2', '7', '4', '0', '2', '1', '8', '9', '9', '4', '2', '6', '9', '8', '4', '1', '8', '7', '7', '0', '8', '6', '7', '2', '5', '0', '2', '8', '6', '5', '6', '0', '1', '0', '4', '5', '4', '7', '/', '5', '5', '0', '5', '7', '3', '6', '2', '5', '1', '0', '2', '4', '1', '8', '5', '3', '4', '7', '2', '3', '0', '5', '8', '9', '4', '0', '4', '0', '1', '8', '4', '2', '9', '5', '2', '3', '7', '6', '5', '5', '1', '2', '2', '7', '6', '4', '0', '5', '7', '2', '9', '4', '2', '1', '0', '6', '5', '6', '9', '9'])
noncomputable def fragment0399129Acc00700 : List (String × SourceJson) := (fragment0399129Field006Key00, fragment0399129Field006Value00) :: fragment0399129Acc00600
noncomputable def fragment0399129Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '9', '7', '0', '8', '8', '4', '8', '2', '7', '4', '0', '2', '1', '8', '9', '9', '4', '2', '6', '9', '8', '4', '1', '8', '7', '7', '0', '8', '6', '7', '2', '5', '0', '2', '8', '6', '5', '6', '0', '1', '0', '4', '5', '4', '7', '/', '5', '5', '0', '5', '7', '3', '6', '2', '5', '1', '0', '2', '4', '1', '8', '5', '3', '4', '7', '2', '3', '0', '5', '8', '9', '4', '0', '4', '0', '1', '8', '4', '2', '9', '5', '2', '3', '7', '6', '5', '5', '1', '2', '2', '7', '6', '4', '0', '5', '7', '2', '9', '4', '2', '1', '0', '6', '5', '6', '9', '9', '"', ',']

theorem object_fragment0399129_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 207) (SourceJson.white (fragment0399129Field006Chars00 ++ tail)) fragment0399129Acc00600 =
      SourceJson.object (fuel + 206) (SourceJson.white tail) fragment0399129Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_006"
  err.flush

noncomputable def fragment0399129Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0399129Field007Value00 : SourceJson := .str (String.ofList ['4', '2', '4', '2', '8', '5', '8', '9', '6', '4', '4', '3', '3', '7', '8', '6', '7', '9', '3', '3', '4', '4', '2', '6', '8', '9', '9', '5', '3', '8', '1', '8', '2', '6', '6', '3', '6', '1', '9', '4', '9', '3', '6', '3', '1', '1', '1', '5', '3', '5', '7', '5', '4', '2', '5', '3', '5', '0', '3', '8', '3', '9', '2', '5', '4', '4', '0', '8', '5', '7', '7', '2', '4', '0', '7', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '7', '6', '0', '6', '9', '1', '7', '1', '5', '1', '9', '6', '5', '4', '5', '9', '7', '7', '5', '1', '7', '3', '5', '2', '7', '0', '7', '4', '8', '3', '7', '6', '8', '3', '7', '3', '8', '2', '4', '8', '2', '2', '6', '8', '3', '4', '4', '4', '7', '8', '6', '9', '5', '2', '3', '8', '4', '5', '6', '6', '0', '9', '2', '1', '3', '0', '6', '3', '8', '4', '9', '0', '3', '6', '2', '4', '8', '6', '6', '6', '1', '3', '9', '2', '2', '8', '4', '2', '4', '2', '5', '7', '6', '1', '1', '6', '5', '8', '3', '5', '0', '0', '4', '2', '7', '1'])
noncomputable def fragment0399129Acc00800 : List (String × SourceJson) := (fragment0399129Field007Key00, fragment0399129Field007Value00) :: fragment0399129Acc00700
noncomputable def fragment0399129Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '2', '4', '2', '8', '5', '8', '9', '6', '4', '4', '3', '3', '7', '8', '6', '7', '9', '3', '3', '4', '4', '2', '6', '8', '9', '9', '5', '3', '8', '1', '8', '2', '6', '6', '3', '6', '1', '9', '4', '9', '3', '6', '3', '1', '1', '1', '5', '3', '5', '7', '5', '4', '2', '5', '3', '5', '0', '3', '8', '3', '9', '2', '5', '4', '4', '0', '8', '5', '7', '7', '2', '4', '0', '7', '9', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '7', '6', '0', '6', '9', '1', '7', '1', '5', '1', '9', '6', '5', '4', '5', '9', '7', '7', '5', '1', '7', '3', '5', '2', '7', '0', '7', '4', '8', '3', '7', '6', '8', '3', '7', '3', '8', '2', '4', '8', '2', '2', '6', '8', '3', '4', '4', '4', '7', '8', '6', '9', '5', '2', '3', '8', '4', '5', '6', '6', '0', '9', '2', '1', '3', '0', '6', '3', '8', '4', '9', '0', '3', '6', '2', '4', '8', '6', '6', '6', '1', '3', '9', '2', '2', '8', '4', '2', '4', '2', '5', '7', '6', '1', '1', '6', '5', '8', '3', '5', '0', '0', '4', '2', '7', '1', '"', ',']

theorem object_fragment0399129_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0399129Field007Chars00 ++ tail)) fragment0399129Acc00700 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0399129Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_007"
  err.flush

noncomputable def fragment0399129Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0399129Field008Value00 : SourceJson := .str (String.ofList ['2', '7', '2', '9', '9', '3', '1', '6', '1', '6', '0', '7', '6', '2', '6'])
noncomputable def fragment0399129Acc00900 : List (String × SourceJson) := (fragment0399129Field008Key00, fragment0399129Field008Value00) :: fragment0399129Acc00800
noncomputable def fragment0399129Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '2', '9', '9', '3', '1', '6', '1', '6', '0', '7', '6', '2', '6', '"', ',']

theorem object_fragment0399129_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0399129Field008Chars00 ++ tail)) fragment0399129Acc00800 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0399129Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_008"
  err.flush

noncomputable def fragment0399129Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0399129Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '1', '9', '1', '8', '4', '5', '8', '2', '9', '1', '6', '3', '9', '3'])
noncomputable def fragment0399129Acc01000 : List (String × SourceJson) := (fragment0399129Field009Key00, fragment0399129Field009Value00) :: fragment0399129Acc00900
noncomputable def fragment0399129Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '1', '9', '1', '8', '4', '5', '8', '2', '9', '1', '6', '3', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0399129_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0399129Field009Chars00 ++ tail)) fragment0399129Acc00900 =
      .ok (.obj (fragment0399129Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0399129_object_field_009"
  err.flush

noncomputable def fragment0399129Chars : List Char := '{' :: (fragment0399129Field000Chars00 ++ fragment0399129Field001Chars00 ++ fragment0399129Field002Chars00 ++ fragment0399129Field003Chars00 ++ fragment0399129Field004Chars00 ++ fragment0399129Field005Chars00 ++ fragment0399129Field006Chars00 ++ fragment0399129Field007Chars00 ++ fragment0399129Field008Chars00 ++ fragment0399129Field009Chars00)
noncomputable def fragment0399129Value : SourceJson := .obj (fragment0399129Acc01000.reverse)

theorem value_fragment0399129 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 214) (fragment0399129Chars ++ tail) =
      .ok (fragment0399129Value, tail) := by
  have hinput : fragment0399129Chars ++ tail = '{' :: (fragment0399129Field000Chars00 ++ (fragment0399129Field001Chars00 ++ (fragment0399129Field002Chars00 ++ (fragment0399129Field003Chars00 ++ (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0399129Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 214) (fragment0399129Chars ++ tail) =
        SourceJson.value (fuel + 214) ('{' :: (fragment0399129Field000Chars00 ++ (fragment0399129Field001Chars00 ++ (fragment0399129Field002Chars00 ++ (fragment0399129Field003Chars00 ++ (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 214)) hinput
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0399129Field000Chars00 ++ (fragment0399129Field001Chars00 ++ (fragment0399129Field002Chars00 ++ (fragment0399129Field003Chars00 ++ (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))))))))))) fragment0399129Acc00000 := by rfl
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0399129Field001Chars00 ++ (fragment0399129Field002Chars00 ++ (fragment0399129Field003Chars00 ++ (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail))))))))))) fragment0399129Acc00100 := object_fragment0399129_field_000 fuel (fragment0399129Field001Chars00 ++ (fragment0399129Field002Chars00 ++ (fragment0399129Field003Chars00 ++ (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0399129Field002Chars00 ++ (fragment0399129Field003Chars00 ++ (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))))))))) fragment0399129Acc00200 := object_fragment0399129_field_001 fuel (fragment0399129Field002Chars00 ++ (fragment0399129Field003Chars00 ++ (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0399129Field003Chars00 ++ (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail))))))))) fragment0399129Acc00300 := object_fragment0399129_field_002 fuel (fragment0399129Field003Chars00 ++ (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))))))) fragment0399129Acc00400 := object_fragment0399129_field_003 fuel (fragment0399129Field004Chars00 ++ (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail))))))) fragment0399129Acc00500 := object_fragment0399129_field_004 fuel (fragment0399129Field005Chars00 ++ (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 207) (SourceJson.white (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))))) fragment0399129Acc00600 := object_fragment0399129_field_005 fuel (fragment0399129Field006Chars00 ++ (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail))))) fragment0399129Acc00700 := object_fragment0399129_field_006 fuel (fragment0399129Field007Chars00 ++ (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))) fragment0399129Acc00800 := object_fragment0399129_field_007 fuel (fragment0399129Field008Chars00 ++ (fragment0399129Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0399129Field009Chars00 ++ (tail))) fragment0399129Acc00900 := object_fragment0399129_field_008 fuel (fragment0399129Field009Chars00 ++ (tail))
    _ = .ok (fragment0399129Value, tail) := object_fragment0399129_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0100_before_reader"
  err.flush

noncomputable def chunk0100LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0100SuffixChars00 : List Char := [',']
noncomputable def chunk0100Chars00 : List Char := chunk0100LeadChars00 ++ fragment0397549Chars ++ chunk0100SuffixChars00
noncomputable def chunk0100Push00 (acc : List SourceJson) : List SourceJson := fragment0397549Value :: acc

noncomputable def chunk0100AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0100_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 504)
      (SourceJson.white (chunk0100LeadChars00 ++ (fragment0397549Chars ++ rest))) acc =
      (SourceJson.value (fuel + 503) (fragment0397549Chars ++ rest)).bind
        (chunk0100AfterValue00 (fuel + 503) acc) := by rfl

theorem array_chunk0100 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 504) (SourceJson.white (chunk0100Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 503) (SourceJson.white tail) (chunk0100Push00 acc) := by
  have hinput : chunk0100Chars00 ++ tail = chunk0100LeadChars00 ++ (fragment0397549Chars ++ (chunk0100SuffixChars00 ++ tail)) := by
    simp only [chunk0100Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 504) (SourceJson.white (chunk0100Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 504)
          (SourceJson.white (chunk0100LeadChars00 ++ (fragment0397549Chars ++ (chunk0100SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 504) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 503) (fragment0397549Chars ++ (chunk0100SuffixChars00 ++ tail))).bind
        (chunk0100AfterValue00 (fuel + 503) acc) := array_chunk0100_head fuel (chunk0100SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0397549Value, chunk0100SuffixChars00 ++ tail)).bind
        (chunk0100AfterValue00 (fuel + 503) acc) :=
      congrArg (fun result => result.bind (chunk0100AfterValue00 (fuel + 503) acc))
        (value_fragment0397549 (fuel + 284) (chunk0100SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 503) (SourceJson.white tail) (chunk0100Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0100_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0101_before_reader"
  err.flush

noncomputable def chunk0101LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0101SuffixChars00 : List Char := [',']
noncomputable def chunk0101Chars00 : List Char := chunk0101LeadChars00 ++ fragment0399129Chars ++ chunk0101SuffixChars00
noncomputable def chunk0101Push00 (acc : List SourceJson) : List SourceJson := fragment0399129Value :: acc

noncomputable def chunk0101AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0101_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 503)
      (SourceJson.white (chunk0101LeadChars00 ++ (fragment0399129Chars ++ rest))) acc =
      (SourceJson.value (fuel + 502) (fragment0399129Chars ++ rest)).bind
        (chunk0101AfterValue00 (fuel + 502) acc) := by rfl

theorem array_chunk0101 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 503) (SourceJson.white (chunk0101Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 502) (SourceJson.white tail) (chunk0101Push00 acc) := by
  have hinput : chunk0101Chars00 ++ tail = chunk0101LeadChars00 ++ (fragment0399129Chars ++ (chunk0101SuffixChars00 ++ tail)) := by
    simp only [chunk0101Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 503) (SourceJson.white (chunk0101Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 503)
          (SourceJson.white (chunk0101LeadChars00 ++ (fragment0399129Chars ++ (chunk0101SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 503) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 502) (fragment0399129Chars ++ (chunk0101SuffixChars00 ++ tail))).bind
        (chunk0101AfterValue00 (fuel + 502) acc) := array_chunk0101_head fuel (chunk0101SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0399129Value, chunk0101SuffixChars00 ++ tail)).bind
        (chunk0101AfterValue00 (fuel + 502) acc) :=
      congrArg (fun result => result.bind (chunk0101AfterValue00 (fuel + 502) acc))
        (value_fragment0399129 (fuel + 288) (chunk0101SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 502) (SourceJson.white tail) (chunk0101Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0101_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0100Chars00 ++ chunk0101Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0101Push00 (chunk0100Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 504) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 502) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0100Chars00 ++ (chunk0101Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 504) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 504) (SourceJson.white (chunk0100Chars00 ++ (chunk0101Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 504) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 503) (SourceJson.white (chunk0101Chars00 ++ (tail))) (chunk0100Push00 (acc)) := array_chunk0100 fuel (chunk0101Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 502) (SourceJson.white tail) (blockPush acc) := array_chunk0101 fuel (tail) (chunk0100Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 397543).take 3149 = blockChars := by rfl

theorem block_original_split : sourceRest 397543 = blockChars ++ sourceRest 400692 := by
  calc
    sourceRest 397543 = (sourceRest 397543).take 3149 ++ (sourceRest 397543).drop 3149 :=
      (List.take_append_drop 3149 (sourceRest 397543)).symm
    _ = blockChars ++ (sourceRest 397543).drop 3149 :=
      congrArg (fun part => part ++ (sourceRest 397543).drop 3149) block_original_prefix
    _ = blockChars ++ sourceRest 400692 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 397543 3149)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 504) (SourceJson.white (sourceRest 397543)) acc =
      SourceJson.array (fuel + 502) (SourceJson.white (sourceRest 400692)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 504) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 400692) acc)

#print axioms object_fragment0397549_field_000
#print axioms object_fragment0397549_field_001
#print axioms object_fragment0397549_field_002
#print axioms object_fragment0397549_field_003
#print axioms object_fragment0397549_field_004
#print axioms object_fragment0397549_field_005
#print axioms object_fragment0397549_field_006
#print axioms object_fragment0397549_field_007
#print axioms object_fragment0397549_field_008
#print axioms object_fragment0397549_field_009
#print axioms value_fragment0397549
#print axioms object_fragment0399129_field_000
#print axioms object_fragment0399129_field_001
#print axioms object_fragment0399129_field_002
#print axioms object_fragment0399129_field_003
#print axioms object_fragment0399129_field_004
#print axioms object_fragment0399129_field_005
#print axioms object_fragment0399129_field_006
#print axioms object_fragment0399129_field_007
#print axioms object_fragment0399129_field_008
#print axioms object_fragment0399129_field_009
#print axioms value_fragment0399129
#print axioms array_chunk0100_head
#print axioms array_chunk0100
#print axioms array_chunk0101_head
#print axioms array_chunk0101
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock051

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
