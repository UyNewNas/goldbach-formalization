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

namespace SimplicesBlock019

noncomputable def fragment0289560Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0289560Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0289560Field000Value00 : SourceJson := .number (String.ofList ['3', '8'])
noncomputable def fragment0289560Acc00100 : List (String × SourceJson) := (fragment0289560Field000Key00, fragment0289560Field000Value00) :: fragment0289560Acc00000
noncomputable def fragment0289560Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '8', ',']

theorem object_fragment0289560_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0289560Field000Chars00 ++ tail)) fragment0289560Acc00000 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0289560Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_000"
  err.flush

noncomputable def fragment0289560Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0289560Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0289560Acc00200 : List (String × SourceJson) := (fragment0289560Field001Key00, fragment0289560Field001Value00) :: fragment0289560Acc00100
noncomputable def fragment0289560Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0289560_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0289560Field001Chars00 ++ tail)) fragment0289560Acc00100 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0289560Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_001"
  err.flush

noncomputable def fragment0289560Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0289560Field002Value00 : SourceJson := .str (String.ofList ['6', '9', '7', '6', '4', '4', '5', '8', '8', '1', '0', '8', '1', '0', '7', '9', '6', '0', '2', '4', '4', '1', '7', '7', '9', '5', '3', '8', '1', '9', '0', '8', '8', '9', '6', '9', '2', '3', '4', '2', '2', '9', '4', '0', '8', '7', '/', '3', '7', '2', '6', '9', '1', '3', '6', '4', '8', '0', '6', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0289560Acc00300 : List (String × SourceJson) := (fragment0289560Field002Key00, fragment0289560Field002Value00) :: fragment0289560Acc00200
noncomputable def fragment0289560Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '9', '7', '6', '4', '4', '5', '8', '8', '1', '0', '8', '1', '0', '7', '9', '6', '0', '2', '4', '4', '1', '7', '7', '9', '5', '3', '8', '1', '9', '0', '8', '8', '9', '6', '9', '2', '3', '4', '2', '2', '9', '4', '0', '8', '7', '/', '3', '7', '2', '6', '9', '1', '3', '6', '4', '8', '0', '6', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0289560_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0289560Field002Chars00 ++ tail)) fragment0289560Acc00200 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0289560Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_002"
  err.flush

noncomputable def fragment0289560Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0289560Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0289560Acc00400 : List (String × SourceJson) := (fragment0289560Field003Key00, fragment0289560Field003Value00) :: fragment0289560Acc00300
noncomputable def fragment0289560Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0289560_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0289560Field003Chars00 ++ tail)) fragment0289560Acc00300 =
      SourceJson.object (fuel + 193) (SourceJson.white tail) fragment0289560Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_003"
  err.flush

noncomputable def fragment0289560Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0289560Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0289560Acc00500 : List (String × SourceJson) := (fragment0289560Field004Key00, fragment0289560Field004Value00) :: fragment0289560Acc00400
noncomputable def fragment0289560Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0289560_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment0289560Field004Chars00 ++ tail)) fragment0289560Acc00400 =
      SourceJson.object (fuel + 192) (SourceJson.white tail) fragment0289560Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_004"
  err.flush

noncomputable def fragment0289560Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0289560Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '7', '3', '5', '2', '6', '3', '9', '1', '/', '3', '3', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '7', '8', '3', '4', '5', '1', '0', '9', '/', '4', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '1', '3', '8', '8', '5', '9', '7', '/', '2', '2', '3', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '3', '4', '1', '9', '9', '8', '8', '3', '/', '2', '0', '9', '4', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '1', '4', '8', '4', '7', '3', '5', '1', '/', '2', '7', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '4', '7', '8', '9', '1', '9', '8', '0', '1', '/', '5', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '4', '5', '8', '3', '4', '7', '1', '/', '2', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '8', '2', '8', '8', '1', '1', '6', '7', '9', '/', '5', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '9', '6', '9', '5', '4', '6', '2', '7', '/', '2', '7', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '7', '6', '0', '1', '4', '3', '0', '3', '1', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0289560Acc00600 : List (String × SourceJson) := (fragment0289560Field005Key00, fragment0289560Field005Value00) :: fragment0289560Acc00500
noncomputable def fragment0289560Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '5', '2', '6', '3', '9', '1', '/', '3', '3', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '7', '8', '3', '4', '5', '1', '0', '9', '/', '4', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '1', '3', '8', '8', '5', '9', '7', '/', '2', '2', '3', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '3', '4', '1', '9', '9', '8', '8', '3', '/', '2', '0', '9', '4', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '1', '4', '8', '4', '7', '3', '5', '1', '/', '2', '7', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '4', '7', '8', '9', '1', '9', '8', '0', '1', '/', '5', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '4', '5', '8', '3', '4', '7', '1', '/', '2', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '2', '8', '8', '1', '1', '6', '7', '9', '/', '5', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '9', '6', '9', '5', '4', '6', '2', '7', '/', '2', '7', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '7', '6', '0', '1', '4', '3', '0', '3', '1', '/', '1', '6', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0289560_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (fragment0289560Field005Chars00 ++ tail)) fragment0289560Acc00500 =
      SourceJson.object (fuel + 191) (SourceJson.white tail) fragment0289560Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_005"
  err.flush

noncomputable def fragment0289560Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0289560Field006Value00 : SourceJson := .str (String.ofList ['3', '8', '9', '5', '1', '0', '4', '8', '8', '4', '5', '8', '7', '5', '1', '6', '1', '0', '4', '1', '7', '2', '5', '2', '4', '2', '1', '8', '9', '0', '7', '1', '2', '3', '5', '4', '2', '4', '3', '0', '5', '7', '0', '7', '8', '9', '0', '5', '0', '3', '0', '0', '7', '9', '3', '0', '0', '0', '/', '5', '0', '8', '0', '3', '0', '0', '5', '6', '9', '0', '2', '3', '4', '6', '8', '1', '0', '0', '9', '3', '0', '3', '5', '3', '9', '3', '5', '2', '6', '0', '9', '8', '2', '4', '7', '6', '5', '2', '8', '1', '3', '6', '6', '7', '3', '0', '9', '7', '6', '2', '6', '5', '9', '0', '0', '3', '1', '0', '5', '1', '5', '4', '6', '2', '3', '5', '4', '3'])
noncomputable def fragment0289560Acc00700 : List (String × SourceJson) := (fragment0289560Field006Key00, fragment0289560Field006Value00) :: fragment0289560Acc00600
noncomputable def fragment0289560Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '8', '9', '5', '1', '0', '4', '8', '8', '4', '5', '8', '7', '5', '1', '6', '1', '0', '4', '1', '7', '2', '5', '2', '4', '2', '1', '8', '9', '0', '7', '1', '2', '3', '5', '4', '2', '4', '3', '0', '5', '7', '0', '7', '8', '9', '0', '5', '0', '3', '0', '0', '7', '9', '3', '0', '0', '0', '/', '5', '0', '8', '0', '3', '0', '0', '5', '6', '9', '0', '2', '3', '4', '6', '8', '1', '0', '0', '9', '3', '0', '3', '5', '3', '9', '3', '5', '2', '6', '0', '9', '8', '2', '4', '7', '6', '5', '2', '8', '1', '3', '6', '6', '7', '3', '0', '9', '7', '6', '2', '6', '5', '9', '0', '0', '3', '1', '0', '5', '1', '5', '4', '6', '2', '3', '5', '4', '3', '"', ',']

theorem object_fragment0289560_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 191) (SourceJson.white (fragment0289560Field006Chars00 ++ tail)) fragment0289560Acc00600 =
      SourceJson.object (fuel + 190) (SourceJson.white tail) fragment0289560Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_006"
  err.flush

noncomputable def fragment0289560Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0289560Field007Value00 : SourceJson := .str (String.ofList ['3', '4', '5', '6', '6', '6', '9', '0', '2', '5', '0', '5', '0', '3', '9', '4', '3', '8', '9', '2', '7', '5', '3', '9', '3', '8', '4', '5', '3', '1', '3', '0', '2', '4', '1', '6', '0', '9', '2', '1', '5', '4', '8', '5', '9', '6', '8', '3', '3', '6', '8', '9', '8', '6', '0', '3', '9', '2', '4', '7', '1', '4', '8', '6', '1', '8', '5', '3', '3', '3', '6', '1', '8', '1', '6', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '0', '7', '8', '2', '4', '3', '0', '6', '2', '5', '0', '7', '2', '6', '0', '1', '2', '8', '0', '3', '7', '2', '1', '8', '4', '8', '1', '6', '2', '8', '7', '3', '4', '9', '3', '0', '5', '3', '7', '6', '4', '5', '8', '6', '4', '9', '2', '6', '7', '4', '7', '2', '0', '3', '0', '4', '9', '7', '4', '4', '0', '6', '7', '4', '6', '1', '9', '8', '6', '2', '1', '8', '7', '2', '2', '5', '6', '3', '8', '4', '9', '7', '9', '1', '2', '9', '7', '9', '8', '8', '0', '8', '2', '7', '9', '5', '7'])
noncomputable def fragment0289560Acc00800 : List (String × SourceJson) := (fragment0289560Field007Key00, fragment0289560Field007Value00) :: fragment0289560Acc00700
noncomputable def fragment0289560Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '5', '6', '6', '6', '9', '0', '2', '5', '0', '5', '0', '3', '9', '4', '3', '8', '9', '2', '7', '5', '3', '9', '3', '8', '4', '5', '3', '1', '3', '0', '2', '4', '1', '6', '0', '9', '2', '1', '5', '4', '8', '5', '9', '6', '8', '3', '3', '6', '8', '9', '8', '6', '0', '3', '9', '2', '4', '7', '1', '4', '8', '6', '1', '8', '5', '3', '3', '3', '6', '1', '8', '1', '6', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '0', '7', '8', '2', '4', '3', '0', '6', '2', '5', '0', '7', '2', '6', '0', '1', '2', '8', '0', '3', '7', '2', '1', '8', '4', '8', '1', '6', '2', '8', '7', '3', '4', '9', '3', '0', '5', '3', '7', '6', '4', '5', '8', '6', '4', '9', '2', '6', '7', '4', '7', '2', '0', '3', '0', '4', '9', '7', '4', '4', '0', '6', '7', '4', '6', '1', '9', '8', '6', '2', '1', '8', '7', '2', '2', '5', '6', '3', '8', '4', '9', '7', '9', '1', '2', '9', '7', '9', '8', '8', '0', '8', '2', '7', '9', '5', '7', '"', ',']

theorem object_fragment0289560_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 190) (SourceJson.white (fragment0289560Field007Chars00 ++ tail)) fragment0289560Acc00700 =
      SourceJson.object (fuel + 189) (SourceJson.white tail) fragment0289560Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_007"
  err.flush

noncomputable def fragment0289560Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0289560Field008Value00 : SourceJson := .str (String.ofList ['6', '0', '7', '4', '4', '8', '3', '1', '6', '5', '1', '8', '6', '5', '0', '0', '5', '3'])
noncomputable def fragment0289560Acc00900 : List (String × SourceJson) := (fragment0289560Field008Key00, fragment0289560Field008Value00) :: fragment0289560Acc00800
noncomputable def fragment0289560Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '0', '7', '4', '4', '8', '3', '1', '6', '5', '1', '8', '6', '5', '0', '0', '5', '3', '"', ',']

theorem object_fragment0289560_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 189) (SourceJson.white (fragment0289560Field008Chars00 ++ tail)) fragment0289560Acc00800 =
      SourceJson.object (fuel + 188) (SourceJson.white tail) fragment0289560Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_008"
  err.flush

noncomputable def fragment0289560Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0289560Field009Value00 : SourceJson := .str (String.ofList ['5', '3', '9', '2', '9', '1', '9', '0', '0', '5', '7', '2', '2', '0', '6', '5', '6', '8', '0'])
noncomputable def fragment0289560Acc01000 : List (String × SourceJson) := (fragment0289560Field009Key00, fragment0289560Field009Value00) :: fragment0289560Acc00900
noncomputable def fragment0289560Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '3', '9', '2', '9', '1', '9', '0', '0', '5', '7', '2', '2', '0', '6', '5', '6', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0289560_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 188) (SourceJson.white (fragment0289560Field009Chars00 ++ tail)) fragment0289560Acc00900 =
      .ok (.obj (fragment0289560Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0289560_object_field_009"
  err.flush

noncomputable def fragment0289560Chars : List Char := '{' :: (fragment0289560Field000Chars00 ++ fragment0289560Field001Chars00 ++ fragment0289560Field002Chars00 ++ fragment0289560Field003Chars00 ++ fragment0289560Field004Chars00 ++ fragment0289560Field005Chars00 ++ fragment0289560Field006Chars00 ++ fragment0289560Field007Chars00 ++ fragment0289560Field008Chars00 ++ fragment0289560Field009Chars00)
noncomputable def fragment0289560Value : SourceJson := .obj (fragment0289560Acc01000.reverse)

theorem value_fragment0289560 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 198) (fragment0289560Chars ++ tail) =
      .ok (fragment0289560Value, tail) := by
  have hinput : fragment0289560Chars ++ tail = '{' :: (fragment0289560Field000Chars00 ++ (fragment0289560Field001Chars00 ++ (fragment0289560Field002Chars00 ++ (fragment0289560Field003Chars00 ++ (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0289560Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 198) (fragment0289560Chars ++ tail) =
        SourceJson.value (fuel + 198) ('{' :: (fragment0289560Field000Chars00 ++ (fragment0289560Field001Chars00 ++ (fragment0289560Field002Chars00 ++ (fragment0289560Field003Chars00 ++ (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 198)) hinput
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0289560Field000Chars00 ++ (fragment0289560Field001Chars00 ++ (fragment0289560Field002Chars00 ++ (fragment0289560Field003Chars00 ++ (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))))))))))) fragment0289560Acc00000 := by rfl
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0289560Field001Chars00 ++ (fragment0289560Field002Chars00 ++ (fragment0289560Field003Chars00 ++ (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail))))))))))) fragment0289560Acc00100 := object_fragment0289560_field_000 fuel (fragment0289560Field001Chars00 ++ (fragment0289560Field002Chars00 ++ (fragment0289560Field003Chars00 ++ (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0289560Field002Chars00 ++ (fragment0289560Field003Chars00 ++ (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))))))))) fragment0289560Acc00200 := object_fragment0289560_field_001 fuel (fragment0289560Field002Chars00 ++ (fragment0289560Field003Chars00 ++ (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0289560Field003Chars00 ++ (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail))))))))) fragment0289560Acc00300 := object_fragment0289560_field_002 fuel (fragment0289560Field003Chars00 ++ (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))))))) fragment0289560Acc00400 := object_fragment0289560_field_003 fuel (fragment0289560Field004Chars00 ++ (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 192) (SourceJson.white (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail))))))) fragment0289560Acc00500 := object_fragment0289560_field_004 fuel (fragment0289560Field005Chars00 ++ (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 191) (SourceJson.white (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))))) fragment0289560Acc00600 := object_fragment0289560_field_005 fuel (fragment0289560Field006Chars00 ++ (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 190) (SourceJson.white (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail))))) fragment0289560Acc00700 := object_fragment0289560_field_006 fuel (fragment0289560Field007Chars00 ++ (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 189) (SourceJson.white (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))) fragment0289560Acc00800 := object_fragment0289560_field_007 fuel (fragment0289560Field008Chars00 ++ (fragment0289560Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 188) (SourceJson.white (fragment0289560Field009Chars00 ++ (tail))) fragment0289560Acc00900 := object_fragment0289560_field_008 fuel (fragment0289560Field009Chars00 ++ (tail))
    _ = .ok (fragment0289560Value, tail) := object_fragment0289560_field_009 fuel (tail)

noncomputable def fragment0291118Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0291118Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0291118Field000Value00 : SourceJson := .number (String.ofList ['3', '9'])
noncomputable def fragment0291118Acc00100 : List (String × SourceJson) := (fragment0291118Field000Key00, fragment0291118Field000Value00) :: fragment0291118Acc00000
noncomputable def fragment0291118Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '9', ',']

theorem object_fragment0291118_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0291118Field000Chars00 ++ tail)) fragment0291118Acc00000 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0291118Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_000"
  err.flush

noncomputable def fragment0291118Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0291118Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0291118Acc00200 : List (String × SourceJson) := (fragment0291118Field001Key00, fragment0291118Field001Value00) :: fragment0291118Acc00100
noncomputable def fragment0291118Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0291118_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0291118Field001Chars00 ++ tail)) fragment0291118Acc00100 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0291118Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_001"
  err.flush

noncomputable def fragment0291118Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0291118Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '8', '9', '1', '1', '5', '2', '5', '0', '3', '9', '2', '9', '2', '8', '0', '2', '6', '6', '7', '2', '3', '5', '5', '4', '8', '1', '6', '6', '0', '1', '4', '9', '4', '3', '4', '5', '7', '/', '1', '2', '4', '4', '0', '6', '2', '7', '8', '9', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0291118Acc00300 : List (String × SourceJson) := (fragment0291118Field002Key00, fragment0291118Field002Value00) :: fragment0291118Acc00200
noncomputable def fragment0291118Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '8', '9', '1', '1', '5', '2', '5', '0', '3', '9', '2', '9', '2', '8', '0', '2', '6', '6', '7', '2', '3', '5', '5', '4', '8', '1', '6', '6', '0', '1', '4', '9', '4', '3', '4', '5', '7', '/', '1', '2', '4', '4', '0', '6', '2', '7', '8', '9', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0291118_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0291118Field002Chars00 ++ tail)) fragment0291118Acc00200 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0291118Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_002"
  err.flush

noncomputable def fragment0291118Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0291118Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0291118Acc00400 : List (String × SourceJson) := (fragment0291118Field003Key00, fragment0291118Field003Value00) :: fragment0291118Acc00300
noncomputable def fragment0291118Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0291118_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0291118Field003Chars00 ++ tail)) fragment0291118Acc00300 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0291118Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_003"
  err.flush

noncomputable def fragment0291118Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0291118Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0291118Acc00500 : List (String × SourceJson) := (fragment0291118Field004Key00, fragment0291118Field004Value00) :: fragment0291118Acc00400
noncomputable def fragment0291118Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '4', '3', '7', '9', '9', '/', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0291118_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0291118Field004Chars00 ++ tail)) fragment0291118Acc00400 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0291118Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_004"
  err.flush

noncomputable def fragment0291118Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0291118Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '1', '7', '7', '5', '8', '0', '6', '8', '6', '7', '9', '/', '1', '1', '0', '5', '1', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '4', '4', '6', '4', '8', '2', '5', '4', '2', '3', '1', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '4', '8', '1', '3', '1', '6', '6', '7', '8', '3', '/', '4', '7', '8', '2', '0', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '4', '2', '4', '1', '7', '8', '0', '0', '6', '1', '8', '7', '/', '2', '0', '7', '2', '2', '0', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '6', '2', '8', '4', '7', '3', '4', '2', '4', '6', '3', '/', '1', '4', '6', '2', '7', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '6', '4', '3', '1', '9', '8', '8', '2', '9', '9', '2', '7', '/', '6', '2', '1', '6', '6', '1', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '7', '5', '5', '1', '2', '4', '3', '8', '6', '5', '3', '/', '1', '3', '0', '8', '7', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '0', '0', '6', '9', '4', '7', '1', '1', '6', '1', '9', '7', '/', '2', '4', '8', '6', '6', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '0', '1', '1', '3', '4', '8', '3', '1', '3', '3', '2', '9', '/', '6', '2', '1', '6', '6', '1', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '0', '1', '1', '2', '2', '3', '9', '8', '0', '9', '3', '9', '/', '6', '2', '1', '6', '6', '1', '9', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0291118Acc00600 : List (String × SourceJson) := (fragment0291118Field005Key00, fragment0291118Field005Value00) :: fragment0291118Acc00500
noncomputable def fragment0291118Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '7', '7', '5', '8', '0', '6', '8', '6', '7', '9', '/', '1', '1', '0', '5', '1', '7', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '4', '6', '4', '8', '2', '5', '4', '2', '3', '1', '/', '5', '5', '2', '5', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '4', '8', '1', '3', '1', '6', '6', '7', '8', '3', '/', '4', '7', '8', '2', '0', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '2', '4', '1', '7', '8', '0', '0', '6', '1', '8', '7', '/', '2', '0', '7', '2', '2', '0', '6', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '6', '2', '8', '4', '7', '3', '4', '2', '4', '6', '3', '/', '1', '4', '6', '2', '7', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '6', '4', '3', '1', '9', '8', '8', '2', '9', '9', '2', '7', '/', '6', '2', '1', '6', '6', '1', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '7', '5', '5', '1', '2', '4', '3', '8', '6', '5', '3', '/', '1', '3', '0', '8', '7', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '0', '0', '6', '9', '4', '7', '1', '1', '6', '1', '9', '7', '/', '2', '4', '8', '6', '6', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '1', '1', '3', '4', '8', '3', '1', '3', '3', '2', '9', '/', '6', '2', '1', '6', '6', '1', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '1', '1', '2', '2', '3', '9', '8', '0', '9', '3', '9', '/', '6', '2', '1', '6', '6', '1', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0291118_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0291118Field005Chars00 ++ tail)) fragment0291118Acc00500 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0291118Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_005"
  err.flush

noncomputable def fragment0291118Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0291118Field006Value00 : SourceJson := .str (String.ofList ['1', '7', '1', '3', '4', '0', '8', '2', '8', '8', '9', '6', '3', '3', '4', '3', '3', '0', '6', '5', '0', '8', '3', '2', '0', '2', '8', '2', '6', '6', '6', '6', '8', '7', '7', '8', '2', '9', '5', '0', '2', '4', '1', '5', '2', '5', '0', '0', '0', '/', '2', '6', '6', '9', '6', '4', '2', '1', '9', '9', '7', '1', '4', '7', '2', '6', '6', '9', '0', '7', '1', '5', '3', '6', '3', '4', '0', '0', '0', '5', '8', '1', '6', '1', '1', '7', '3', '1', '5', '0', '3', '5', '5', '1', '0', '7', '7', '0', '6', '4', '5', '9', '2', '6', '6', '2', '8', '5', '5', '5', '0', '4', '0', '4', '9'])
noncomputable def fragment0291118Acc00700 : List (String × SourceJson) := (fragment0291118Field006Key00, fragment0291118Field006Value00) :: fragment0291118Acc00600
noncomputable def fragment0291118Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '1', '3', '4', '0', '8', '2', '8', '8', '9', '6', '3', '3', '4', '3', '3', '0', '6', '5', '0', '8', '3', '2', '0', '2', '8', '2', '6', '6', '6', '6', '8', '7', '7', '8', '2', '9', '5', '0', '2', '4', '1', '5', '2', '5', '0', '0', '0', '/', '2', '6', '6', '9', '6', '4', '2', '1', '9', '9', '7', '1', '4', '7', '2', '6', '6', '9', '0', '7', '1', '5', '3', '6', '3', '4', '0', '0', '0', '5', '8', '1', '6', '1', '1', '7', '3', '1', '5', '0', '3', '5', '5', '1', '0', '7', '7', '0', '6', '4', '5', '9', '2', '6', '6', '2', '8', '5', '5', '5', '0', '4', '0', '4', '9', '"', ',']

theorem object_fragment0291118_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0291118Field006Chars00 ++ tail)) fragment0291118Acc00600 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0291118Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_006"
  err.flush

noncomputable def fragment0291118Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0291118Field007Value00 : SourceJson := .str (String.ofList ['2', '6', '1', '0', '7', '8', '5', '3', '6', '0', '5', '4', '8', '4', '8', '4', '3', '8', '2', '1', '9', '7', '2', '4', '8', '6', '4', '8', '6', '2', '8', '8', '2', '4', '1', '8', '7', '6', '9', '6', '2', '9', '2', '6', '8', '0', '5', '6', '9', '2', '3', '1', '6', '8', '0', '2', '0', '2', '4', '7', '1', '6', '3', '7', '4', '4', '6', '7', '8', '0', '7', '9', '9', '5', '0', '5', '9', '8', '9', '4', '3', '5', '2', '8', '4', '9', '9', '5', '9', '4', '9', '1', '8', '9', '7', '8', '4', '8', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '7', '2', '9', '0', '5', '5', '1', '9', '2', '2', '3', '6', '7', '3', '7', '4', '3', '3', '3', '1', '8', '4', '7', '3', '5', '1', '5', '9', '8', '1', '1', '4', '3', '8', '0', '8', '0', '3', '3', '5', '4', '0', '6', '8', '4', '9', '7', '9', '5', '8', '9', '3', '0', '7', '5', '2', '5', '1', '6', '4', '7', '3', '1', '8', '5', '4', '2', '5', '3', '7', '1', '4', '0', '1', '1', '3', '5', '9', '8', '2', '5', '6', '3', '0', '9', '4', '0', '3', '2', '3', '8', '3', '4', '8', '0', '0', '9', '2', '8', '6', '5', '4', '3', '9', '0', '2', '4', '7', '2', '7', '2', '0', '2', '2', '8', '4', '8', '6', '6', '3', '9', '6', '8', '0', '0', '5', '5', '9'])
noncomputable def fragment0291118Acc00800 : List (String × SourceJson) := (fragment0291118Field007Key00, fragment0291118Field007Value00) :: fragment0291118Acc00700
noncomputable def fragment0291118Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '1', '0', '7', '8', '5', '3', '6', '0', '5', '4', '8', '4', '8', '4', '3', '8', '2', '1', '9', '7', '2', '4', '8', '6', '4', '8', '6', '2', '8', '8', '2', '4', '1', '8', '7', '6', '9', '6', '2', '9', '2', '6', '8', '0', '5', '6', '9', '2', '3', '1', '6', '8', '0', '2', '0', '2', '4', '7', '1', '6', '3', '7', '4', '4', '6', '7', '8', '0', '7', '9', '9', '5', '0', '5', '9', '8', '9', '4', '3', '5', '2', '8', '4', '9', '9', '5', '9', '4', '9', '1', '8', '9', '7', '8', '4', '8', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '7', '2', '9', '0', '5', '5', '1', '9', '2', '2', '3', '6', '7', '3', '7', '4', '3', '3', '3', '1', '8', '4', '7', '3', '5', '1', '5', '9', '8', '1', '1', '4', '3', '8', '0', '8', '0', '3', '3', '5', '4', '0', '6', '8', '4', '9', '7', '9', '5', '8', '9', '3', '0', '7', '5', '2', '5', '1', '6', '4', '7', '3', '1', '8', '5', '4', '2', '5', '3', '7', '1', '4', '0', '1', '1', '3', '5', '9', '8', '2', '5', '6', '3', '0', '9', '4', '0', '3', '2', '3', '8', '3', '4', '8', '0', '0', '9', '2', '8', '6', '5', '4', '3', '9', '0', '2', '4', '7', '2', '7', '2', '0', '2', '2', '8', '4', '8', '6', '6', '3', '9', '6', '8', '0', '0', '5', '5', '9', '"', ',']

theorem object_fragment0291118_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0291118Field007Chars00 ++ tail)) fragment0291118Acc00700 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0291118Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_007"
  err.flush

noncomputable def fragment0291118Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0291118Field008Value00 : SourceJson := .str (String.ofList ['5', '0', '8', '4', '9', '5', '8', '2', '1', '5', '9', '6', '5'])
noncomputable def fragment0291118Acc00900 : List (String × SourceJson) := (fragment0291118Field008Key00, fragment0291118Field008Value00) :: fragment0291118Acc00800
noncomputable def fragment0291118Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '8', '4', '9', '5', '8', '2', '1', '5', '9', '6', '5', '"', ',']

theorem object_fragment0291118_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0291118Field008Chars00 ++ tail)) fragment0291118Acc00800 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0291118Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_008"
  err.flush

noncomputable def fragment0291118Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0291118Field009Value00 : SourceJson := .str (String.ofList ['4', '4', '2', '6', '5', '3', '3', '4', '7', '0', '1', '1', '7', '3'])
noncomputable def fragment0291118Acc01000 : List (String × SourceJson) := (fragment0291118Field009Key00, fragment0291118Field009Value00) :: fragment0291118Acc00900
noncomputable def fragment0291118Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '4', '2', '6', '5', '3', '3', '4', '7', '0', '1', '1', '7', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0291118_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0291118Field009Chars00 ++ tail)) fragment0291118Acc00900 =
      .ok (.obj (fragment0291118Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0291118_object_field_009"
  err.flush

noncomputable def fragment0291118Chars : List Char := '{' :: (fragment0291118Field000Chars00 ++ fragment0291118Field001Chars00 ++ fragment0291118Field002Chars00 ++ fragment0291118Field003Chars00 ++ fragment0291118Field004Chars00 ++ fragment0291118Field005Chars00 ++ fragment0291118Field006Chars00 ++ fragment0291118Field007Chars00 ++ fragment0291118Field008Chars00 ++ fragment0291118Field009Chars00)
noncomputable def fragment0291118Value : SourceJson := .obj (fragment0291118Acc01000.reverse)

theorem value_fragment0291118 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 257) (fragment0291118Chars ++ tail) =
      .ok (fragment0291118Value, tail) := by
  have hinput : fragment0291118Chars ++ tail = '{' :: (fragment0291118Field000Chars00 ++ (fragment0291118Field001Chars00 ++ (fragment0291118Field002Chars00 ++ (fragment0291118Field003Chars00 ++ (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0291118Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 257) (fragment0291118Chars ++ tail) =
        SourceJson.value (fuel + 257) ('{' :: (fragment0291118Field000Chars00 ++ (fragment0291118Field001Chars00 ++ (fragment0291118Field002Chars00 ++ (fragment0291118Field003Chars00 ++ (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 257)) hinput
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0291118Field000Chars00 ++ (fragment0291118Field001Chars00 ++ (fragment0291118Field002Chars00 ++ (fragment0291118Field003Chars00 ++ (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))))))))))) fragment0291118Acc00000 := by rfl
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0291118Field001Chars00 ++ (fragment0291118Field002Chars00 ++ (fragment0291118Field003Chars00 ++ (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail))))))))))) fragment0291118Acc00100 := object_fragment0291118_field_000 fuel (fragment0291118Field001Chars00 ++ (fragment0291118Field002Chars00 ++ (fragment0291118Field003Chars00 ++ (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0291118Field002Chars00 ++ (fragment0291118Field003Chars00 ++ (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))))))))) fragment0291118Acc00200 := object_fragment0291118_field_001 fuel (fragment0291118Field002Chars00 ++ (fragment0291118Field003Chars00 ++ (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0291118Field003Chars00 ++ (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail))))))))) fragment0291118Acc00300 := object_fragment0291118_field_002 fuel (fragment0291118Field003Chars00 ++ (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))))))) fragment0291118Acc00400 := object_fragment0291118_field_003 fuel (fragment0291118Field004Chars00 ++ (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail))))))) fragment0291118Acc00500 := object_fragment0291118_field_004 fuel (fragment0291118Field005Chars00 ++ (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))))) fragment0291118Acc00600 := object_fragment0291118_field_005 fuel (fragment0291118Field006Chars00 ++ (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail))))) fragment0291118Acc00700 := object_fragment0291118_field_006 fuel (fragment0291118Field007Chars00 ++ (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))) fragment0291118Acc00800 := object_fragment0291118_field_007 fuel (fragment0291118Field008Chars00 ++ (fragment0291118Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0291118Field009Chars00 ++ (tail))) fragment0291118Acc00900 := object_fragment0291118_field_008 fuel (fragment0291118Field009Chars00 ++ (tail))
    _ = .ok (fragment0291118Value, tail) := object_fragment0291118_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0038_before_reader"
  err.flush

noncomputable def chunk0038LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0038SuffixChars00 : List Char := [',']
noncomputable def chunk0038Chars00 : List Char := chunk0038LeadChars00 ++ fragment0289560Chars ++ chunk0038SuffixChars00
noncomputable def chunk0038Push00 (acc : List SourceJson) : List SourceJson := fragment0289560Value :: acc

noncomputable def chunk0038AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0038_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 566)
      (SourceJson.white (chunk0038LeadChars00 ++ (fragment0289560Chars ++ rest))) acc =
      (SourceJson.value (fuel + 565) (fragment0289560Chars ++ rest)).bind
        (chunk0038AfterValue00 (fuel + 565) acc) := by rfl

theorem array_chunk0038 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 566) (SourceJson.white (chunk0038Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 565) (SourceJson.white tail) (chunk0038Push00 acc) := by
  have hinput : chunk0038Chars00 ++ tail = chunk0038LeadChars00 ++ (fragment0289560Chars ++ (chunk0038SuffixChars00 ++ tail)) := by
    simp only [chunk0038Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 566) (SourceJson.white (chunk0038Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 566)
          (SourceJson.white (chunk0038LeadChars00 ++ (fragment0289560Chars ++ (chunk0038SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 566) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 565) (fragment0289560Chars ++ (chunk0038SuffixChars00 ++ tail))).bind
        (chunk0038AfterValue00 (fuel + 565) acc) := array_chunk0038_head fuel (chunk0038SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0289560Value, chunk0038SuffixChars00 ++ tail)).bind
        (chunk0038AfterValue00 (fuel + 565) acc) :=
      congrArg (fun result => result.bind (chunk0038AfterValue00 (fuel + 565) acc))
        (value_fragment0289560 (fuel + 367) (chunk0038SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 565) (SourceJson.white tail) (chunk0038Push00 acc) := by rfl

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
noncomputable def chunk0039Chars00 : List Char := chunk0039LeadChars00 ++ fragment0291118Chars ++ chunk0039SuffixChars00
noncomputable def chunk0039Push00 (acc : List SourceJson) : List SourceJson := fragment0291118Value :: acc

noncomputable def chunk0039AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0039_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 565)
      (SourceJson.white (chunk0039LeadChars00 ++ (fragment0291118Chars ++ rest))) acc =
      (SourceJson.value (fuel + 564) (fragment0291118Chars ++ rest)).bind
        (chunk0039AfterValue00 (fuel + 564) acc) := by rfl

theorem array_chunk0039 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 565) (SourceJson.white (chunk0039Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 564) (SourceJson.white tail) (chunk0039Push00 acc) := by
  have hinput : chunk0039Chars00 ++ tail = chunk0039LeadChars00 ++ (fragment0291118Chars ++ (chunk0039SuffixChars00 ++ tail)) := by
    simp only [chunk0039Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 565) (SourceJson.white (chunk0039Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 565)
          (SourceJson.white (chunk0039LeadChars00 ++ (fragment0291118Chars ++ (chunk0039SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 565) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 564) (fragment0291118Chars ++ (chunk0039SuffixChars00 ++ tail))).bind
        (chunk0039AfterValue00 (fuel + 564) acc) := array_chunk0039_head fuel (chunk0039SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0291118Value, chunk0039SuffixChars00 ++ tail)).bind
        (chunk0039AfterValue00 (fuel + 564) acc) :=
      congrArg (fun result => result.bind (chunk0039AfterValue00 (fuel + 564) acc))
        (value_fragment0291118 (fuel + 307) (chunk0039SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 564) (SourceJson.white tail) (chunk0039Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0039_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0038Chars00 ++ chunk0039Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0039Push00 (chunk0038Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 566) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 564) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 566) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 566) (SourceJson.white (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 566) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 565) (SourceJson.white (chunk0039Chars00 ++ (tail))) (chunk0038Push00 (acc)) := array_chunk0038 fuel (chunk0039Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 564) (SourceJson.white tail) (blockPush acc) := array_chunk0039 fuel (tail) (chunk0038Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 289554).take 3197 = blockChars := by rfl

theorem block_original_split : sourceRest 289554 = blockChars ++ sourceRest 292751 := by
  calc
    sourceRest 289554 = (sourceRest 289554).take 3197 ++ (sourceRest 289554).drop 3197 :=
      (List.take_append_drop 3197 (sourceRest 289554)).symm
    _ = blockChars ++ (sourceRest 289554).drop 3197 :=
      congrArg (fun part => part ++ (sourceRest 289554).drop 3197) block_original_prefix
    _ = blockChars ++ sourceRest 292751 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 289554 3197)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 566) (SourceJson.white (sourceRest 289554)) acc =
      SourceJson.array (fuel + 564) (SourceJson.white (sourceRest 292751)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 566) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 292751) acc)

#print axioms object_fragment0289560_field_000
#print axioms object_fragment0289560_field_001
#print axioms object_fragment0289560_field_002
#print axioms object_fragment0289560_field_003
#print axioms object_fragment0289560_field_004
#print axioms object_fragment0289560_field_005
#print axioms object_fragment0289560_field_006
#print axioms object_fragment0289560_field_007
#print axioms object_fragment0289560_field_008
#print axioms object_fragment0289560_field_009
#print axioms value_fragment0289560
#print axioms object_fragment0291118_field_000
#print axioms object_fragment0291118_field_001
#print axioms object_fragment0291118_field_002
#print axioms object_fragment0291118_field_003
#print axioms object_fragment0291118_field_004
#print axioms object_fragment0291118_field_005
#print axioms object_fragment0291118_field_006
#print axioms object_fragment0291118_field_007
#print axioms object_fragment0291118_field_008
#print axioms object_fragment0291118_field_009
#print axioms value_fragment0291118
#print axioms array_chunk0038_head
#print axioms array_chunk0038
#print axioms array_chunk0039_head
#print axioms array_chunk0039
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock019

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
