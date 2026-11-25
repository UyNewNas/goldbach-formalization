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

namespace SimplicesBlock070

noncomputable def fragment0460224Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0460224Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0460224Field000Value00 : SourceJson := .number (String.ofList ['1', '3', '8'])
noncomputable def fragment0460224Acc00100 : List (String × SourceJson) := (fragment0460224Field000Key00, fragment0460224Field000Value00) :: fragment0460224Acc00000
noncomputable def fragment0460224Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '8', ',']

theorem object_fragment0460224_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0460224Field000Chars00 ++ tail)) fragment0460224Acc00000 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0460224Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_000"
  err.flush

noncomputable def fragment0460224Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0460224Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5'])]
noncomputable def fragment0460224Acc00200 : List (String × SourceJson) := (fragment0460224Field001Key00, fragment0460224Field001Value00) :: fragment0460224Acc00100
noncomputable def fragment0460224Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0460224_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0460224Field001Chars00 ++ tail)) fragment0460224Acc00100 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0460224Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_001"
  err.flush

noncomputable def fragment0460224Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0460224Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '6', '4', '3', '4', '2', '3', '9', '1', '0', '3', '5', '0', '2', '7', '8', '1', '0', '7', '8', '8', '0', '7', '1', '3', '9', '0', '1', '8', '3', '2', '4', '0', '5', '7', '2', '6', '2', '9', '3', '1', '/', '1', '4', '7', '4', '9', '3', '7', '9', '6', '0', '5', '1', '3', '3', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0460224Acc00300 : List (String × SourceJson) := (fragment0460224Field002Key00, fragment0460224Field002Value00) :: fragment0460224Acc00200
noncomputable def fragment0460224Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '6', '4', '3', '4', '2', '3', '9', '1', '0', '3', '5', '0', '2', '7', '8', '1', '0', '7', '8', '8', '0', '7', '1', '3', '9', '0', '1', '8', '3', '2', '4', '0', '5', '7', '2', '6', '2', '9', '3', '1', '/', '1', '4', '7', '4', '9', '3', '7', '9', '6', '0', '5', '1', '3', '3', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0460224_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0460224Field002Chars00 ++ tail)) fragment0460224Acc00200 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0460224Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_002"
  err.flush

noncomputable def fragment0460224Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0460224Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0460224Acc00400 : List (String × SourceJson) := (fragment0460224Field003Key00, fragment0460224Field003Value00) :: fragment0460224Acc00300
noncomputable def fragment0460224Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0460224_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0460224Field003Chars00 ++ tail)) fragment0460224Acc00300 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0460224Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_003"
  err.flush

noncomputable def fragment0460224Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0460224Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '1', '5', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0460224Acc00500 : List (String × SourceJson) := (fragment0460224Field004Key00, fragment0460224Field004Value00) :: fragment0460224Acc00400
noncomputable def fragment0460224Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '1', '5', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '7', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0460224_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0460224Field004Chars00 ++ tail)) fragment0460224Acc00400 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0460224Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_004"
  err.flush

noncomputable def fragment0460224Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0460224Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '1', '9', '5', '5', '8', '8', '1', '5', '4', '6', '4', '7', '7', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '0', '7', '0', '0', '3', '5', '3', '7', '0', '6', '6', '7', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '3', '3', '2', '9', '1', '2', '7', '1', '6', '3', '8', '1', '7', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '8', '5', '7', '9', '2', '4', '7', '8', '4', '0', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '4', '1', '7', '0', '9', '0', '6', '5', '4', '7', '/', '1', '3', '7', '5', '5', '3', '2', '5', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '7', '0', '5', '4', '5', '8', '6', '2', '1', '6', '6', '9', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '8', '8', '7', '8', '6', '9', '6', '1', '1', '/', '5', '3', '6', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '8', '3', '6', '9', '4', '3', '1', '3', '1', '1', '1', '/', '1', '5', '2', '8', '3', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '2', '9', '8', '7', '9', '3', '9', '1', '6', '4', '1', '/', '2', '0', '3', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '7', '8', '9', '4', '7', '5', '1', '4', '8', '8', '4', '3', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0460224Acc00600 : List (String × SourceJson) := (fragment0460224Field005Key00, fragment0460224Field005Value00) :: fragment0460224Acc00500
noncomputable def fragment0460224Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '9', '5', '5', '8', '8', '1', '5', '4', '6', '4', '7', '7', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '0', '7', '0', '0', '3', '5', '3', '7', '0', '6', '6', '7', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '3', '3', '2', '9', '1', '2', '7', '1', '6', '3', '8', '1', '7', '/', '5', '5', '0', '2', '1', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '8', '5', '7', '9', '2', '4', '7', '8', '4', '0', '1', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '4', '1', '7', '0', '9', '0', '6', '5', '4', '7', '/', '1', '3', '7', '5', '5', '3', '2', '5', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '7', '0', '5', '4', '5', '8', '6', '2', '1', '6', '6', '9', '/', '1', '1', '0', '0', '4', '2', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '0', '8', '8', '7', '8', '6', '9', '6', '1', '1', '/', '5', '3', '6', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '8', '3', '6', '9', '4', '3', '1', '3', '1', '1', '1', '/', '1', '5', '2', '8', '3', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '2', '9', '8', '7', '9', '3', '9', '1', '6', '4', '1', '/', '2', '0', '3', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '8', '9', '4', '7', '5', '1', '4', '8', '8', '4', '3', '/', '6', '1', '1', '3', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0460224_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0460224Field005Chars00 ++ tail)) fragment0460224Acc00500 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0460224Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_005"
  err.flush

noncomputable def fragment0460224Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0460224Field006Value00 : SourceJson := .str (String.ofList ['3', '0', '1', '6', '9', '6', '6', '4', '2', '9', '7', '2', '8', '2', '1', '9', '7', '1', '7', '5', '4', '0', '0', '8', '0', '9', '4', '8', '9', '1', '8', '3', '2', '9', '9', '8', '4', '2', '8', '3', '1', '1', '5', '3', '6', '6', '8', '2', '9', '6', '0', '0', '/', '2', '5', '1', '3', '3', '1', '4', '1', '7', '6', '5', '6', '7', '5', '4', '3', '4', '8', '2', '6', '5', '4', '0', '1', '0', '9', '9', '1', '1', '0', '7', '5', '3', '4', '0', '4', '4', '6', '3', '9', '7', '6', '9', '6', '7', '1', '8', '2', '5', '6', '5', '6', '5', '3', '7', '1', '3', '0', '9', '8', '3', '9', '8', '4', '5', '2', '7', '3', '5', '4', '3'])
noncomputable def fragment0460224Acc00700 : List (String × SourceJson) := (fragment0460224Field006Key00, fragment0460224Field006Value00) :: fragment0460224Acc00600
noncomputable def fragment0460224Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '1', '6', '9', '6', '6', '4', '2', '9', '7', '2', '8', '2', '1', '9', '7', '1', '7', '5', '4', '0', '0', '8', '0', '9', '4', '8', '9', '1', '8', '3', '2', '9', '9', '8', '4', '2', '8', '3', '1', '1', '5', '3', '6', '6', '8', '2', '9', '6', '0', '0', '/', '2', '5', '1', '3', '3', '1', '4', '1', '7', '6', '5', '6', '7', '5', '4', '3', '4', '8', '2', '6', '5', '4', '0', '1', '0', '9', '9', '1', '1', '0', '7', '5', '3', '4', '0', '4', '4', '6', '3', '9', '7', '6', '9', '6', '7', '1', '8', '2', '5', '6', '5', '6', '5', '3', '7', '1', '3', '0', '9', '8', '3', '9', '8', '4', '5', '2', '7', '3', '5', '4', '3', '"', ',']

theorem object_fragment0460224_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0460224Field006Chars00 ++ tail)) fragment0460224Acc00600 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0460224Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_006"
  err.flush

noncomputable def fragment0460224Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0460224Field007Value00 : SourceJson := .str (String.ofList ['4', '1', '4', '6', '9', '3', '0', '5', '8', '8', '8', '0', '5', '7', '6', '8', '3', '8', '8', '2', '8', '1', '1', '4', '0', '6', '1', '3', '2', '1', '6', '0', '8', '4', '7', '0', '8', '8', '8', '6', '2', '2', '5', '3', '6', '5', '7', '3', '5', '1', '1', '0', '7', '5', '0', '6', '7', '8', '9', '1', '8', '9', '9', '8', '1', '5', '1', '8', '6', '2', '8', '5', '0', '3', '5', '9', '8', '7', '5', '1', '4', '3', '8', '9', '2', '3', '8', '2', '4', '2', '3', '5', '8', '1', '5', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '0', '4', '5', '2', '6', '2', '7', '1', '6', '1', '8', '2', '2', '8', '8', '7', '0', '3', '4', '4', '7', '7', '6', '7', '6', '4', '4', '3', '3', '6', '0', '4', '0', '7', '4', '5', '7', '8', '9', '9', '2', '6', '4', '0', '6', '8', '1', '5', '7', '4', '5', '2', '3', '7', '4', '5', '6', '3', '8', '1', '6', '9', '0', '1', '6', '2', '9', '8', '3', '4', '7', '3', '7', '9', '1', '5', '7', '0', '9', '1', '2', '8', '3', '9', '8', '5', '2', '7', '1', '5', '4', '6', '9', '1', '0', '4', '1', '8', '5', '4', '7', '0', '2', '8', '6', '8', '2', '6', '8', '4', '2', '7', '6', '2', '6', '8', '3', '9', '8', '7', '4', '2', '9', '8', '1', '2', '9', '9', '8', '9'])
noncomputable def fragment0460224Acc00800 : List (String × SourceJson) := (fragment0460224Field007Key00, fragment0460224Field007Value00) :: fragment0460224Acc00700
noncomputable def fragment0460224Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '1', '4', '6', '9', '3', '0', '5', '8', '8', '8', '0', '5', '7', '6', '8', '3', '8', '8', '2', '8', '1', '1', '4', '0', '6', '1', '3', '2', '1', '6', '0', '8', '4', '7', '0', '8', '8', '8', '6', '2', '2', '5', '3', '6', '5', '7', '3', '5', '1', '1', '0', '7', '5', '0', '6', '7', '8', '9', '1', '8', '9', '9', '8', '1', '5', '1', '8', '6', '2', '8', '5', '0', '3', '5', '9', '8', '7', '5', '1', '4', '3', '8', '9', '2', '3', '8', '2', '4', '2', '3', '5', '8', '1', '5', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '0', '4', '5', '2', '6', '2', '7', '1', '6', '1', '8', '2', '2', '8', '8', '7', '0', '3', '4', '4', '7', '7', '6', '7', '6', '4', '4', '3', '3', '6', '0', '4', '0', '7', '4', '5', '7', '8', '9', '9', '2', '6', '4', '0', '6', '8', '1', '5', '7', '4', '5', '2', '3', '7', '4', '5', '6', '3', '8', '1', '6', '9', '0', '1', '6', '2', '9', '8', '3', '4', '7', '3', '7', '9', '1', '5', '7', '0', '9', '1', '2', '8', '3', '9', '8', '5', '2', '7', '1', '5', '4', '6', '9', '1', '0', '4', '1', '8', '5', '4', '7', '0', '2', '8', '6', '8', '2', '6', '8', '4', '2', '7', '6', '2', '6', '8', '3', '9', '8', '7', '4', '2', '9', '8', '1', '2', '9', '9', '8', '9', '"', ',']

theorem object_fragment0460224_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0460224Field007Chars00 ++ tail)) fragment0460224Acc00700 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0460224Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_007"
  err.flush

noncomputable def fragment0460224Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0460224Field008Value00 : SourceJson := .str (String.ofList ['9', '5', '1', '0', '4', '9', '8', '4', '8', '1'])
noncomputable def fragment0460224Acc00900 : List (String × SourceJson) := (fragment0460224Field008Key00, fragment0460224Field008Value00) :: fragment0460224Acc00800
noncomputable def fragment0460224Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '5', '1', '0', '4', '9', '8', '4', '8', '1', '"', ',']

theorem object_fragment0460224_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0460224Field008Chars00 ++ tail)) fragment0460224Acc00800 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0460224Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_008"
  err.flush

noncomputable def fragment0460224Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0460224Field009Value00 : SourceJson := .str (String.ofList ['4', '0', '8', '3', '8', '1', '5', '5', '5', '9', '7'])
noncomputable def fragment0460224Acc01000 : List (String × SourceJson) := (fragment0460224Field009Key00, fragment0460224Field009Value00) :: fragment0460224Acc00900
noncomputable def fragment0460224Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '8', '3', '8', '1', '5', '5', '5', '9', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0460224_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0460224Field009Chars00 ++ tail)) fragment0460224Acc00900 =
      .ok (.obj (fragment0460224Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0460224_object_field_009"
  err.flush

noncomputable def fragment0460224Chars : List Char := '{' :: (fragment0460224Field000Chars00 ++ fragment0460224Field001Chars00 ++ fragment0460224Field002Chars00 ++ fragment0460224Field003Chars00 ++ fragment0460224Field004Chars00 ++ fragment0460224Field005Chars00 ++ fragment0460224Field006Chars00 ++ fragment0460224Field007Chars00 ++ fragment0460224Field008Chars00 ++ fragment0460224Field009Chars00)
noncomputable def fragment0460224Value : SourceJson := .obj (fragment0460224Acc01000.reverse)

theorem value_fragment0460224 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 256) (fragment0460224Chars ++ tail) =
      .ok (fragment0460224Value, tail) := by
  have hinput : fragment0460224Chars ++ tail = '{' :: (fragment0460224Field000Chars00 ++ (fragment0460224Field001Chars00 ++ (fragment0460224Field002Chars00 ++ (fragment0460224Field003Chars00 ++ (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0460224Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 256) (fragment0460224Chars ++ tail) =
        SourceJson.value (fuel + 256) ('{' :: (fragment0460224Field000Chars00 ++ (fragment0460224Field001Chars00 ++ (fragment0460224Field002Chars00 ++ (fragment0460224Field003Chars00 ++ (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 256)) hinput
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0460224Field000Chars00 ++ (fragment0460224Field001Chars00 ++ (fragment0460224Field002Chars00 ++ (fragment0460224Field003Chars00 ++ (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))))))))))) fragment0460224Acc00000 := by rfl
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0460224Field001Chars00 ++ (fragment0460224Field002Chars00 ++ (fragment0460224Field003Chars00 ++ (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail))))))))))) fragment0460224Acc00100 := object_fragment0460224_field_000 fuel (fragment0460224Field001Chars00 ++ (fragment0460224Field002Chars00 ++ (fragment0460224Field003Chars00 ++ (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0460224Field002Chars00 ++ (fragment0460224Field003Chars00 ++ (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))))))))) fragment0460224Acc00200 := object_fragment0460224_field_001 fuel (fragment0460224Field002Chars00 ++ (fragment0460224Field003Chars00 ++ (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0460224Field003Chars00 ++ (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail))))))))) fragment0460224Acc00300 := object_fragment0460224_field_002 fuel (fragment0460224Field003Chars00 ++ (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))))))) fragment0460224Acc00400 := object_fragment0460224_field_003 fuel (fragment0460224Field004Chars00 ++ (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail))))))) fragment0460224Acc00500 := object_fragment0460224_field_004 fuel (fragment0460224Field005Chars00 ++ (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))))) fragment0460224Acc00600 := object_fragment0460224_field_005 fuel (fragment0460224Field006Chars00 ++ (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail))))) fragment0460224Acc00700 := object_fragment0460224_field_006 fuel (fragment0460224Field007Chars00 ++ (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))) fragment0460224Acc00800 := object_fragment0460224_field_007 fuel (fragment0460224Field008Chars00 ++ (fragment0460224Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0460224Field009Chars00 ++ (tail))) fragment0460224Acc00900 := object_fragment0460224_field_008 fuel (fragment0460224Field009Chars00 ++ (tail))
    _ = .ok (fragment0460224Value, tail) := object_fragment0460224_field_009 fuel (tail)

noncomputable def fragment0461886Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0461886Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0461886Field000Value00 : SourceJson := .number (String.ofList ['1', '3', '9'])
noncomputable def fragment0461886Acc00100 : List (String × SourceJson) := (fragment0461886Field000Key00, fragment0461886Field000Value00) :: fragment0461886Acc00000
noncomputable def fragment0461886Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '9', ',']

theorem object_fragment0461886_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0461886Field000Chars00 ++ tail)) fragment0461886Acc00000 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0461886Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_000"
  err.flush

noncomputable def fragment0461886Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0461886Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '5'])]
noncomputable def fragment0461886Acc00200 : List (String × SourceJson) := (fragment0461886Field001Key00, fragment0461886Field001Value00) :: fragment0461886Acc00100
noncomputable def fragment0461886Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0461886_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0461886Field001Chars00 ++ tail)) fragment0461886Acc00100 =
      SourceJson.object (fuel + 428) (SourceJson.white tail) fragment0461886Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_001"
  err.flush

noncomputable def fragment0461886Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0461886Field002Value00 : SourceJson := .str (String.ofList ['1', '6', '4', '3', '9', '0', '4', '3', '2', '3', '0', '1', '3', '6', '2', '1', '9', '1', '9', '5', '8', '7', '4', '6', '0', '4', '4', '8', '2', '0', '0', '5', '1', '3', '9', '3', '6', '2', '9', '5', '9', '5', '9', '/', '1', '7', '4', '9', '4', '7', '3', '0', '7', '9', '5', '6', '3', '5', '2', '1', '6', '2', '2', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0461886Acc00300 : List (String × SourceJson) := (fragment0461886Field002Key00, fragment0461886Field002Value00) :: fragment0461886Acc00200
noncomputable def fragment0461886Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '6', '4', '3', '9', '0', '4', '3', '2', '3', '0', '1', '3', '6', '2', '1', '9', '1', '9', '5', '8', '7', '4', '6', '0', '4', '4', '8', '2', '0', '0', '5', '1', '3', '9', '3', '6', '2', '9', '5', '9', '5', '9', '/', '1', '7', '4', '9', '4', '7', '3', '0', '7', '9', '5', '6', '3', '5', '2', '1', '6', '2', '2', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0461886_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 428) (SourceJson.white (fragment0461886Field002Chars00 ++ tail)) fragment0461886Acc00200 =
      SourceJson.object (fuel + 427) (SourceJson.white tail) fragment0461886Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_002"
  err.flush

noncomputable def fragment0461886Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0461886Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '2', '4', '9', '9', '7', '/', '4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0461886Acc00400 : List (String × SourceJson) := (fragment0461886Field003Key00, fragment0461886Field003Value00) :: fragment0461886Acc00300
noncomputable def fragment0461886Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '2', '4', '9', '9', '7', '/', '4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0461886_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 427) (SourceJson.white (fragment0461886Field003Chars00 ++ tail)) fragment0461886Acc00300 =
      SourceJson.object (fuel + 426) (SourceJson.white tail) fragment0461886Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_003"
  err.flush

noncomputable def fragment0461886Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0461886Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '1', '5', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0461886Acc00500 : List (String × SourceJson) := (fragment0461886Field004Key00, fragment0461886Field004Value00) :: fragment0461886Acc00400
noncomputable def fragment0461886Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '1', '5', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '5', '5', '7', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0461886_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 426) (SourceJson.white (fragment0461886Field004Chars00 ++ tail)) fragment0461886Acc00400 =
      SourceJson.object (fuel + 425) (SourceJson.white tail) fragment0461886Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_004"
  err.flush

noncomputable def fragment0461886Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0461886Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '4', '1', '2', '4', '2', '6', '1', '9', '6', '0', '9', '9', '2', '8', '7', '1', '0', '6', '4', '0', '2', '9', '/', '4', '9', '8', '6', '0', '9', '0', '7', '0', '8', '9', '2', '7', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '8', '4', '5', '3', '8', '1', '7', '8', '3', '6', '6', '7', '9', '0', '2', '7', '8', '2', '0', '3', '/', '6', '2', '3', '2', '6', '1', '3', '3', '8', '6', '1', '5', '9', '2', '8', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '8', '6', '2', '6', '4', '7', '1', '8', '4', '9', '9', '1', '7', '1', '2', '3', '7', '2', '5', '1', '/', '8', '3', '1', '0', '1', '5', '1', '1', '8', '1', '5', '4', '5', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '3', '3', '1', '7', '4', '6', '5', '7', '4', '0', '7', '0', '5', '9', '1', '0', '3', '0', '8', '4', '7', '/', '2', '9', '9', '1', '6', '5', '4', '4', '2', '5', '3', '5', '6', '4', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '3', '5', '3', '9', '6', '4', '1', '1', '2', '7', '4', '0', '6', '4', '7', '7', '0', '9', '/', '6', '6', '4', '8', '1', '2', '0', '9', '4', '5', '2', '3', '6', '5', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '6', '5', '7', '7', '8', '0', '2', '6', '2', '2', '8', '2', '6', '9', '7', '9', '0', '7', '9', '/', '1', '6', '6', '2', '0', '3', '0', '2', '3', '6', '3', '0', '9', '1', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '6', '7', '6', '5', '1', '6', '8', '1', '9', '2', '2', '5', '3', '3', '2', '5', '3', '4', '6', '3', '/', '3', '9', '3', '6', '3', '8', '7', '4', '0', '1', '7', '8', '4', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '4', '1', '2', '6', '2', '7', '2', '8', '2', '0', '7', '5', '1', '4', '1', '6', '6', '3', '7', '/', '4', '6', '7', '4', '4', '6', '0', '0', '3', '9', '6', '1', '9', '4', '6', '1', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '9', '4', '4', '9', '3', '2', '2', '9', '9', '6', '7', '3', '5', '7', '8', '0', '4', '9', '7', '7', '/', '3', '7', '3', '9', '5', '6', '8', '0', '3', '1', '6', '9', '5', '5', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '4', '0', '9', '2', '8', '4', '5', '1', '2', '7', '0', '6', '1', '9', '0', '5', '4', '1', '4', '5', '3', '/', '1', '4', '9', '5', '8', '2', '7', '2', '1', '2', '6', '7', '8', '2', '2', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0461886Acc00600 : List (String × SourceJson) := (fragment0461886Field005Key00, fragment0461886Field005Value00) :: fragment0461886Acc00500
noncomputable def fragment0461886Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '2', '4', '2', '6', '1', '9', '6', '0', '9', '9', '2', '8', '7', '1', '0', '6', '4', '0', '2', '9', '/', '4', '9', '8', '6', '0', '9', '0', '7', '0', '8', '9', '2', '7', '4', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '8', '4', '5', '3', '8', '1', '7', '8', '3', '6', '6', '7', '9', '0', '2', '7', '8', '2', '0', '3', '/', '6', '2', '3', '2', '6', '1', '3', '3', '8', '6', '1', '5', '9', '2', '8', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '8', '6', '2', '6', '4', '7', '1', '8', '4', '9', '9', '1', '7', '1', '2', '3', '7', '2', '5', '1', '/', '8', '3', '1', '0', '1', '5', '1', '1', '8', '1', '5', '4', '5', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '3', '3', '1', '7', '4', '6', '5', '7', '4', '0', '7', '0', '5', '9', '1', '0', '3', '0', '8', '4', '7', '/', '2', '9', '9', '1', '6', '5', '4', '4', '2', '5', '3', '5', '6', '4', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '3', '5', '3', '9', '6', '4', '1', '1', '2', '7', '4', '0', '6', '4', '7', '7', '0', '9', '/', '6', '6', '4', '8', '1', '2', '0', '9', '4', '5', '2', '3', '6', '5', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '5', '7', '7', '8', '0', '2', '6', '2', '2', '8', '2', '6', '9', '7', '9', '0', '7', '9', '/', '1', '6', '6', '2', '0', '3', '0', '2', '3', '6', '3', '0', '9', '1', '4', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '6', '7', '6', '5', '1', '6', '8', '1', '9', '2', '2', '5', '3', '3', '2', '5', '3', '4', '6', '3', '/', '3', '9', '3', '6', '3', '8', '7', '4', '0', '1', '7', '8', '4', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '4', '1', '2', '6', '2', '7', '2', '8', '2', '0', '7', '5', '1', '4', '1', '6', '6', '3', '7', '/', '4', '6', '7', '4', '4', '6', '0', '0', '3', '9', '6', '1', '9', '4', '6', '1', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '9', '4', '4', '9', '3', '2', '2', '9', '9', '6', '7', '3', '5', '7', '8', '0', '4', '9', '7', '7', '/', '3', '7', '3', '9', '5', '6', '8', '0', '3', '1', '6', '9', '5', '5', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '4', '0', '9', '2', '8', '4', '5', '1', '2', '7', '0', '6', '1', '9', '0', '5', '4', '1', '4', '5', '3', '/', '1', '4', '9', '5', '8', '2', '7', '2', '1', '2', '6', '7', '8', '2', '2', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0461886_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 425) (SourceJson.white (fragment0461886Field005Chars00 ++ tail)) fragment0461886Acc00500 =
      SourceJson.object (fuel + 424) (SourceJson.white tail) fragment0461886Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_005"
  err.flush

noncomputable def fragment0461886Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0461886Field006Value00 : SourceJson := .str (String.ofList ['2', '4', '2', '3', '7', '9', '0', '2', '1', '2', '1', '4', '5', '4', '6', '5', '4', '8', '9', '3', '4', '3', '1', '6', '3', '8', '6', '3', '8', '2', '4', '5', '8', '0', '7', '0', '3', '9', '7', '0', '7', '8', '4', '5', '7', '8', '4', '5', '1', '4', '0', '/', '8', '4', '9', '2', '2', '8', '7', '5', '6', '9', '9', '2', '8', '9', '4', '2', '5', '6', '0', '3', '9', '8', '7', '9', '5', '2', '5', '9', '1', '2', '3', '9', '2', '8', '0', '7', '2', '6', '9', '9', '2', '5', '5', '7', '8', '2', '0', '7', '1', '7', '7', '1', '0', '8', '1', '1', '3', '3', '4', '9', '3', '0', '4', '1', '3', '3'])
noncomputable def fragment0461886Acc00700 : List (String × SourceJson) := (fragment0461886Field006Key00, fragment0461886Field006Value00) :: fragment0461886Acc00600
noncomputable def fragment0461886Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '2', '3', '7', '9', '0', '2', '1', '2', '1', '4', '5', '4', '6', '5', '4', '8', '9', '3', '4', '3', '1', '6', '3', '8', '6', '3', '8', '2', '4', '5', '8', '0', '7', '0', '3', '9', '7', '0', '7', '8', '4', '5', '7', '8', '4', '5', '1', '4', '0', '/', '8', '4', '9', '2', '2', '8', '7', '5', '6', '9', '9', '2', '8', '9', '4', '2', '5', '6', '0', '3', '9', '8', '7', '9', '5', '2', '5', '9', '1', '2', '3', '9', '2', '8', '0', '7', '2', '6', '9', '9', '2', '5', '5', '7', '8', '2', '0', '7', '1', '7', '7', '1', '0', '8', '1', '1', '3', '3', '4', '9', '3', '0', '4', '1', '3', '3', '"', ',']

theorem object_fragment0461886_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 424) (SourceJson.white (fragment0461886Field006Chars00 ++ tail)) fragment0461886Acc00600 =
      SourceJson.object (fuel + 423) (SourceJson.white tail) fragment0461886Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_006"
  err.flush

noncomputable def fragment0461886Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0461886Field007Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '6', '1', '8', '4', '3', '4', '8', '6', '2', '3', '2', '6', '5', '7', '2', '4', '3', '0', '1', '9', '9', '4', '7', '2', '5', '0', '9', '1', '6', '2', '3', '6', '7', '7', '7', '2', '8', '9', '7', '1', '3', '0', '7', '3', '1', '1', '4', '6', '4', '0', '7', '5', '3', '8', '7', '2', '8', '4', '0', '2', '3', '9', '0', '5', '2', '4', '8', '7', '6', '2', '9', '6', '7', '5', '7', '8', '5', '5', '4', '2', '8', '5', '3', '9', '7', '5', '6', '4', '4', '1', '7', '8', '7', '5', '8', '8', '7', '5', '5', '7', '1', '3', '5', '8', '8', '1', '2', '9', '1', '8', '0', '7', '0', '1', '8', '2', '0', '0', '6', '3', '5', '2', '7', '3', '8', '4', '0', '4', '3', '3', '7', '1', '8', '9', '2', '3', '9', '9', '2', '8', '6', '2', '2', '1', '8', '3', '5', '3', '4', '4', '5', '5', '2', '9', '7', '2', '9', '8', '7', '3', '2', '5', '0', '6', '5', '0', '5', '2', '7', '0', '6', '7', '7', '8', '0', '2', '4', '3', '6', '0', '6', '5', '6', '7', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '3', '1', '1', '5', '9', '0', '1', '0', '2', '9', '6', '9', '6', '5', '5', '7', '3', '1', '3', '1', '0', '7', '0', '5', '4', '3', '7', '1', '8', '8', '0', '6', '8', '3', '5', '0', '5', '8', '8', '7', '5', '4', '4', '8', '3', '3', '9', '4', '6', '1', '9', '7', '6', '7', '8', '2', '1', '4', '3', '5', '5', '3', '5', '0', '8', '0', '9', '5', '2', '2', '2', '5', '9', '9', '2', '9', '6', '5', '0', '9', '5', '5', '9', '0', '0', '0', '5', '0', '7', '8', '4', '6', '2', '0', '9', '7', '2', '1', '1', '8', '3', '9', '7', '4', '6', '9', '8', '4', '7', '0', '7', '9', '4', '4', '9', '8', '3', '6', '0', '2', '9', '7', '8', '9', '6', '3', '9', '5', '6', '4', '2', '3', '1', '3', '9', '8', '3', '9', '9', '9', '9', '3', '6', '1', '4', '0', '0', '7', '4', '1', '7', '9', '3', '3', '1', '1', '4', '3', '7', '3', '9', '0', '4', '5', '3', '3', '8', '4', '6', '2', '0', '7', '0', '1', '9', '7', '1', '7', '3', '1', '3', '6', '4', '7', '4', '3', '3', '1', '1', '9', '1', '5', '5', '0', '8', '6', '9', '8', '9', '6', '1', '7', '9', '5', '4', '3', '8', '4', '1', '0', '3', '3', '5', '6', '3'])
noncomputable def fragment0461886Acc00800 : List (String × SourceJson) := (fragment0461886Field007Key00, fragment0461886Field007Value00) :: fragment0461886Acc00700
noncomputable def fragment0461886Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '7', '2', '6', '1', '8', '4', '3', '4', '8', '6', '2', '3', '2', '6', '5', '7', '2', '4', '3', '0', '1', '9', '9', '4', '7', '2', '5', '0', '9', '1', '6', '2', '3', '6', '7', '7', '7', '2', '8', '9', '7', '1', '3', '0', '7', '3', '1', '1', '4', '6', '4', '0', '7', '5', '3', '8', '7', '2', '8', '4', '0', '2', '3', '9', '0', '5', '2', '4', '8', '7', '6', '2', '9', '6', '7', '5', '7', '8', '5', '5', '4', '2', '8', '5', '3', '9', '7', '5', '6', '4', '4', '1', '7', '8', '7', '5', '8', '8', '7', '5', '5', '7', '1', '3', '5', '8', '8', '1', '2', '9', '1', '8', '0', '7', '0', '1', '8', '2', '0', '0', '6', '3', '5', '2', '7', '3', '8', '4', '0', '4', '3', '3', '7', '1', '8', '9', '2', '3', '9', '9', '2', '8', '6', '2', '2', '1', '8', '3', '5', '3', '4', '4', '5', '5', '2', '9', '7', '2', '9', '8', '7', '3', '2', '5', '0', '6', '5', '0', '5', '2', '7', '0', '6', '7', '7', '8', '0', '2', '4', '3', '6', '0', '6', '5', '6', '7', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '3', '1', '1', '5', '9', '0', '1', '0', '2', '9', '6', '9', '6', '5', '5', '7', '3', '1', '3', '1', '0', '7', '0', '5', '4', '3', '7', '1', '8', '8', '0', '6', '8', '3', '5', '0', '5', '8', '8', '7', '5', '4', '4', '8', '3', '3', '9', '4', '6', '1', '9', '7', '6', '7', '8', '2', '1', '4', '3', '5', '5', '3', '5', '0', '8', '0', '9', '5', '2', '2', '2', '5', '9', '9', '2', '9', '6', '5', '0', '9', '5', '5', '9', '0', '0', '0', '5', '0', '7', '8', '4', '6', '2', '0', '9', '7', '2', '1', '1', '8', '3', '9', '7', '4', '6', '9', '8', '4', '7', '0', '7', '9', '4', '4', '9', '8', '3', '6', '0', '2', '9', '7', '8', '9', '6', '3', '9', '5', '6', '4', '2', '3', '1', '3', '9', '8', '3', '9', '9', '9', '9', '3', '6', '1', '4', '0', '0', '7', '4', '1', '7', '9', '3', '3', '1', '1', '4', '3', '7', '3', '9', '0', '4', '5', '3', '3', '8', '4', '6', '2', '0', '7', '0', '1', '9', '7', '1', '7', '3', '1', '3', '6', '4', '7', '4', '3', '3', '1', '1', '9', '1', '5', '5', '0', '8', '6', '9', '8', '9', '6', '1', '7', '9', '5', '4', '3', '8', '4', '1', '0', '3', '3', '5', '6', '3', '"', ',']

theorem object_fragment0461886_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 423) (SourceJson.white (fragment0461886Field007Chars00 ++ tail)) fragment0461886Acc00700 =
      SourceJson.object (fuel + 422) (SourceJson.white tail) fragment0461886Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_007"
  err.flush

noncomputable def fragment0461886Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0461886Field008Value00 : SourceJson := .str (String.ofList ['2', '2', '6', '1', '2', '5', '6', '9', '7', '2', '8', '3', '6', '4'])
noncomputable def fragment0461886Acc00900 : List (String × SourceJson) := (fragment0461886Field008Key00, fragment0461886Field008Value00) :: fragment0461886Acc00800
noncomputable def fragment0461886Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '6', '1', '2', '5', '6', '9', '7', '2', '8', '3', '6', '4', '"', ',']

theorem object_fragment0461886_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 422) (SourceJson.white (fragment0461886Field008Chars00 ++ tail)) fragment0461886Acc00800 =
      SourceJson.object (fuel + 421) (SourceJson.white tail) fragment0461886Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_008"
  err.flush

noncomputable def fragment0461886Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0461886Field009Value00 : SourceJson := .str (String.ofList ['9', '7', '9', '6', '1', '4', '5', '2', '6', '6', '2', '4', '2', '3'])
noncomputable def fragment0461886Acc01000 : List (String × SourceJson) := (fragment0461886Field009Key00, fragment0461886Field009Value00) :: fragment0461886Acc00900
noncomputable def fragment0461886Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '9', '6', '1', '4', '5', '2', '6', '6', '2', '4', '2', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0461886_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0461886Field009Chars00 ++ tail)) fragment0461886Acc00900 =
      .ok (.obj (fragment0461886Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0461886_object_field_009"
  err.flush

noncomputable def fragment0461886Chars : List Char := '{' :: (fragment0461886Field000Chars00 ++ fragment0461886Field001Chars00 ++ fragment0461886Field002Chars00 ++ fragment0461886Field003Chars00 ++ fragment0461886Field004Chars00 ++ fragment0461886Field005Chars00 ++ fragment0461886Field006Chars00 ++ fragment0461886Field007Chars00 ++ fragment0461886Field008Chars00 ++ fragment0461886Field009Chars00)
noncomputable def fragment0461886Value : SourceJson := .obj (fragment0461886Acc01000.reverse)

theorem value_fragment0461886 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 431) (fragment0461886Chars ++ tail) =
      .ok (fragment0461886Value, tail) := by
  have hinput : fragment0461886Chars ++ tail = '{' :: (fragment0461886Field000Chars00 ++ (fragment0461886Field001Chars00 ++ (fragment0461886Field002Chars00 ++ (fragment0461886Field003Chars00 ++ (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0461886Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 431) (fragment0461886Chars ++ tail) =
        SourceJson.value (fuel + 431) ('{' :: (fragment0461886Field000Chars00 ++ (fragment0461886Field001Chars00 ++ (fragment0461886Field002Chars00 ++ (fragment0461886Field003Chars00 ++ (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 431)) hinput
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0461886Field000Chars00 ++ (fragment0461886Field001Chars00 ++ (fragment0461886Field002Chars00 ++ (fragment0461886Field003Chars00 ++ (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))))))))))) fragment0461886Acc00000 := by rfl
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0461886Field001Chars00 ++ (fragment0461886Field002Chars00 ++ (fragment0461886Field003Chars00 ++ (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail))))))))))) fragment0461886Acc00100 := object_fragment0461886_field_000 fuel (fragment0461886Field001Chars00 ++ (fragment0461886Field002Chars00 ++ (fragment0461886Field003Chars00 ++ (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 428) (SourceJson.white (fragment0461886Field002Chars00 ++ (fragment0461886Field003Chars00 ++ (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))))))))) fragment0461886Acc00200 := object_fragment0461886_field_001 fuel (fragment0461886Field002Chars00 ++ (fragment0461886Field003Chars00 ++ (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 427) (SourceJson.white (fragment0461886Field003Chars00 ++ (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail))))))))) fragment0461886Acc00300 := object_fragment0461886_field_002 fuel (fragment0461886Field003Chars00 ++ (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 426) (SourceJson.white (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))))))) fragment0461886Acc00400 := object_fragment0461886_field_003 fuel (fragment0461886Field004Chars00 ++ (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 425) (SourceJson.white (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail))))))) fragment0461886Acc00500 := object_fragment0461886_field_004 fuel (fragment0461886Field005Chars00 ++ (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 424) (SourceJson.white (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))))) fragment0461886Acc00600 := object_fragment0461886_field_005 fuel (fragment0461886Field006Chars00 ++ (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 423) (SourceJson.white (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail))))) fragment0461886Acc00700 := object_fragment0461886_field_006 fuel (fragment0461886Field007Chars00 ++ (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 422) (SourceJson.white (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))) fragment0461886Acc00800 := object_fragment0461886_field_007 fuel (fragment0461886Field008Chars00 ++ (fragment0461886Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0461886Field009Chars00 ++ (tail))) fragment0461886Acc00900 := object_fragment0461886_field_008 fuel (fragment0461886Field009Chars00 ++ (tail))
    _ = .ok (fragment0461886Value, tail) := object_fragment0461886_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0138_before_reader"
  err.flush

noncomputable def chunk0138LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0138SuffixChars00 : List Char := [',']
noncomputable def chunk0138Chars00 : List Char := chunk0138LeadChars00 ++ fragment0460224Chars ++ chunk0138SuffixChars00
noncomputable def chunk0138Push00 (acc : List SourceJson) : List SourceJson := fragment0460224Value :: acc

noncomputable def chunk0138AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0138_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 466)
      (SourceJson.white (chunk0138LeadChars00 ++ (fragment0460224Chars ++ rest))) acc =
      (SourceJson.value (fuel + 465) (fragment0460224Chars ++ rest)).bind
        (chunk0138AfterValue00 (fuel + 465) acc) := by rfl

theorem array_chunk0138 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 466) (SourceJson.white (chunk0138Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 465) (SourceJson.white tail) (chunk0138Push00 acc) := by
  have hinput : chunk0138Chars00 ++ tail = chunk0138LeadChars00 ++ (fragment0460224Chars ++ (chunk0138SuffixChars00 ++ tail)) := by
    simp only [chunk0138Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 466) (SourceJson.white (chunk0138Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 466)
          (SourceJson.white (chunk0138LeadChars00 ++ (fragment0460224Chars ++ (chunk0138SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 466) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 465) (fragment0460224Chars ++ (chunk0138SuffixChars00 ++ tail))).bind
        (chunk0138AfterValue00 (fuel + 465) acc) := array_chunk0138_head fuel (chunk0138SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0460224Value, chunk0138SuffixChars00 ++ tail)).bind
        (chunk0138AfterValue00 (fuel + 465) acc) :=
      congrArg (fun result => result.bind (chunk0138AfterValue00 (fuel + 465) acc))
        (value_fragment0460224 (fuel + 209) (chunk0138SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 465) (SourceJson.white tail) (chunk0138Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0138_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0139_before_reader"
  err.flush

noncomputable def chunk0139LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0139SuffixChars00 : List Char := [',']
noncomputable def chunk0139Chars00 : List Char := chunk0139LeadChars00 ++ fragment0461886Chars ++ chunk0139SuffixChars00
noncomputable def chunk0139Push00 (acc : List SourceJson) : List SourceJson := fragment0461886Value :: acc

noncomputable def chunk0139AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0139_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 465)
      (SourceJson.white (chunk0139LeadChars00 ++ (fragment0461886Chars ++ rest))) acc =
      (SourceJson.value (fuel + 464) (fragment0461886Chars ++ rest)).bind
        (chunk0139AfterValue00 (fuel + 464) acc) := by rfl

theorem array_chunk0139 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 465) (SourceJson.white (chunk0139Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 464) (SourceJson.white tail) (chunk0139Push00 acc) := by
  have hinput : chunk0139Chars00 ++ tail = chunk0139LeadChars00 ++ (fragment0461886Chars ++ (chunk0139SuffixChars00 ++ tail)) := by
    simp only [chunk0139Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 465) (SourceJson.white (chunk0139Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 465)
          (SourceJson.white (chunk0139LeadChars00 ++ (fragment0461886Chars ++ (chunk0139SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 465) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 464) (fragment0461886Chars ++ (chunk0139SuffixChars00 ++ tail))).bind
        (chunk0139AfterValue00 (fuel + 464) acc) := array_chunk0139_head fuel (chunk0139SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0461886Value, chunk0139SuffixChars00 ++ tail)).bind
        (chunk0139AfterValue00 (fuel + 464) acc) :=
      congrArg (fun result => result.bind (chunk0139AfterValue00 (fuel + 464) acc))
        (value_fragment0461886 (fuel + 33) (chunk0139SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 464) (SourceJson.white tail) (chunk0139Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0139_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0138Chars00 ++ chunk0139Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0139Push00 (chunk0138Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 466) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 464) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0138Chars00 ++ (chunk0139Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 466) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 466) (SourceJson.white (chunk0138Chars00 ++ (chunk0139Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 466) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 465) (SourceJson.white (chunk0139Chars00 ++ (tail))) (chunk0138Push00 (acc)) := array_chunk0138 fuel (chunk0139Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 464) (SourceJson.white tail) (blockPush acc) := array_chunk0139 fuel (tail) (chunk0138Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 460218).take 3668 = blockChars := by rfl

theorem block_original_split : sourceRest 460218 = blockChars ++ sourceRest 463886 := by
  calc
    sourceRest 460218 = (sourceRest 460218).take 3668 ++ (sourceRest 460218).drop 3668 :=
      (List.take_append_drop 3668 (sourceRest 460218)).symm
    _ = blockChars ++ (sourceRest 460218).drop 3668 :=
      congrArg (fun part => part ++ (sourceRest 460218).drop 3668) block_original_prefix
    _ = blockChars ++ sourceRest 463886 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 460218 3668)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 466) (SourceJson.white (sourceRest 460218)) acc =
      SourceJson.array (fuel + 464) (SourceJson.white (sourceRest 463886)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 466) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 463886) acc)

#print axioms object_fragment0460224_field_000
#print axioms object_fragment0460224_field_001
#print axioms object_fragment0460224_field_002
#print axioms object_fragment0460224_field_003
#print axioms object_fragment0460224_field_004
#print axioms object_fragment0460224_field_005
#print axioms object_fragment0460224_field_006
#print axioms object_fragment0460224_field_007
#print axioms object_fragment0460224_field_008
#print axioms object_fragment0460224_field_009
#print axioms value_fragment0460224
#print axioms object_fragment0461886_field_000
#print axioms object_fragment0461886_field_001
#print axioms object_fragment0461886_field_002
#print axioms object_fragment0461886_field_003
#print axioms object_fragment0461886_field_004
#print axioms object_fragment0461886_field_005
#print axioms object_fragment0461886_field_006
#print axioms object_fragment0461886_field_007
#print axioms object_fragment0461886_field_008
#print axioms object_fragment0461886_field_009
#print axioms value_fragment0461886
#print axioms array_chunk0138_head
#print axioms array_chunk0138
#print axioms array_chunk0139_head
#print axioms array_chunk0139
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock070

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
