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

namespace SimplicesBlock031

noncomputable def fragment0330086Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0330086Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0330086Field000Value00 : SourceJson := .number (String.ofList ['6', '1'])
noncomputable def fragment0330086Acc00100 : List (String × SourceJson) := (fragment0330086Field000Key00, fragment0330086Field000Value00) :: fragment0330086Acc00000
noncomputable def fragment0330086Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '1', ',']

theorem object_fragment0330086_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0330086Field000Chars00 ++ tail)) fragment0330086Acc00000 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment0330086Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_000"
  err.flush

noncomputable def fragment0330086Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0330086Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['5']), .number (String.ofList ['3'])]
noncomputable def fragment0330086Acc00200 : List (String × SourceJson) := (fragment0330086Field001Key00, fragment0330086Field001Value00) :: fragment0330086Acc00100
noncomputable def fragment0330086Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0330086_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0330086Field001Chars00 ++ tail)) fragment0330086Acc00100 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0330086Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_001"
  err.flush

noncomputable def fragment0330086Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0330086Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '8', '6', '1', '4', '5', '7', '5', '7', '1', '4', '5', '8', '6', '8', '5', '9', '3', '1', '6', '8', '5', '1', '7', '5', '3', '0', '6', '8', '1', '8', '1', '0', '6', '5', '3', '2', '8', '7', '3', '9', '2', '8', '9', '/', '3', '1', '3', '1', '0', '8', '2', '8', '2', '0', '7', '9', '8', '1', '1', '9', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0330086Acc00300 : List (String × SourceJson) := (fragment0330086Field002Key00, fragment0330086Field002Value00) :: fragment0330086Acc00200
noncomputable def fragment0330086Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '8', '6', '1', '4', '5', '7', '5', '7', '1', '4', '5', '8', '6', '8', '5', '9', '3', '1', '6', '8', '5', '1', '7', '5', '3', '0', '6', '8', '1', '8', '1', '0', '6', '5', '3', '2', '8', '7', '3', '9', '2', '8', '9', '/', '3', '1', '3', '1', '0', '8', '2', '8', '2', '0', '7', '9', '8', '1', '1', '9', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0330086_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0330086Field002Chars00 ++ tail)) fragment0330086Acc00200 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0330086Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_002"
  err.flush

noncomputable def fragment0330086Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0330086Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '0', '8', '3', '0', '3', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0330086Acc00400 : List (String × SourceJson) := (fragment0330086Field003Key00, fragment0330086Field003Value00) :: fragment0330086Acc00300
noncomputable def fragment0330086Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '7', '0', '8', '3', '0', '3', '/', '9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0330086_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0330086Field003Chars00 ++ tail)) fragment0330086Acc00300 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0330086Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_003"
  err.flush

noncomputable def fragment0330086Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0330086Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '7', '0', '3', '1', '7', '7', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '9', '0', '5', '4', '9', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '4', '0', '4', '6', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '5', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0330086Acc00500 : List (String × SourceJson) := (fragment0330086Field004Key00, fragment0330086Field004Value00) :: fragment0330086Acc00400
noncomputable def fragment0330086Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '0', '3', '1', '7', '7', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '9', '0', '5', '4', '9', '/', '1', '3', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '4', '0', '4', '6', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '5', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0330086_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0330086Field004Chars00 ++ tail)) fragment0330086Acc00400 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0330086Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_004"
  err.flush

noncomputable def fragment0330086Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0330086Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '9', '9', '2', '6', '7', '9', '8', '9', '6', '4', '5', '2', '9', '7', '5', '8', '9', '9', '/', '3', '7', '4', '6', '4', '0', '6', '8', '8', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '3', '8', '4', '0', '2', '1', '2', '7', '5', '9', '8', '0', '7', '3', '7', '4', '5', '7', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '0', '6', '7', '7', '2', '5', '7', '5', '6', '4', '9', '8', '0', '7', '2', '9', '/', '7', '1', '3', '6', '0', '1', '3', '1', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '5', '3', '1', '9', '9', '7', '8', '2', '2', '2', '9', '0', '9', '9', '3', '0', '7', '/', '9', '9', '9', '0', '4', '1', '8', '3', '6', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '6', '6', '8', '5', '1', '2', '1', '6', '8', '7', '8', '8', '2', '7', '1', '/', '2', '5', '1', '8', '5', '9', '2', '8', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '2', '4', '4', '6', '3', '3', '7', '0', '6', '9', '4', '2', '8', '6', '1', '1', '/', '2', '4', '9', '7', '6', '0', '4', '5', '9', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '3', '6', '9', '6', '2', '0', '0', '1', '6', '1', '6', '3', '6', '3', '4', '3', '9', '/', '1', '7', '1', '2', '6', '4', '3', '1', '4', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '6', '0', '5', '4', '1', '3', '2', '0', '2', '4', '8', '4', '3', '5', '8', '2', '3', '/', '5', '7', '0', '8', '8', '1', '0', '4', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '5', '4', '6', '4', '9', '0', '6', '6', '5', '3', '1', '2', '3', '3', '5', '4', '7', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '5', '1', '5', '3', '6', '3', '6', '8', '2', '8', '5', '9', '2', '2', '0', '0', '9', '/', '9', '9', '9', '0', '4', '1', '8', '3', '6', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0330086Acc00600 : List (String × SourceJson) := (fragment0330086Field005Key00, fragment0330086Field005Value00) :: fragment0330086Acc00500
noncomputable def fragment0330086Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '2', '6', '7', '9', '8', '9', '6', '4', '5', '2', '9', '7', '5', '8', '9', '9', '/', '3', '7', '4', '6', '4', '0', '6', '8', '8', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '3', '8', '4', '0', '2', '1', '2', '7', '5', '9', '8', '0', '7', '3', '7', '4', '5', '7', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '0', '6', '7', '7', '2', '5', '7', '5', '6', '4', '9', '8', '0', '7', '2', '9', '/', '7', '1', '3', '6', '0', '1', '3', '1', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '5', '3', '1', '9', '9', '7', '8', '2', '2', '2', '9', '0', '9', '9', '3', '0', '7', '/', '9', '9', '9', '0', '4', '1', '8', '3', '6', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '6', '6', '8', '5', '1', '2', '1', '6', '8', '7', '8', '8', '2', '7', '1', '/', '2', '5', '1', '8', '5', '9', '2', '8', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '1', '2', '4', '4', '6', '3', '3', '7', '0', '6', '9', '4', '2', '8', '6', '1', '1', '/', '2', '4', '9', '7', '6', '0', '4', '5', '9', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '3', '6', '9', '6', '2', '0', '0', '1', '6', '1', '6', '3', '6', '3', '4', '3', '9', '/', '1', '7', '1', '2', '6', '4', '3', '1', '4', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '6', '0', '5', '4', '1', '3', '2', '0', '2', '4', '8', '4', '3', '5', '8', '2', '3', '/', '5', '7', '0', '8', '8', '1', '0', '4', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '5', '4', '6', '4', '9', '0', '6', '6', '5', '3', '1', '2', '3', '3', '5', '4', '7', '/', '2', '9', '9', '7', '1', '2', '5', '5', '1', '0', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '5', '1', '5', '3', '6', '3', '6', '8', '2', '8', '5', '9', '2', '2', '0', '0', '9', '/', '9', '9', '9', '0', '4', '1', '8', '3', '6', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0330086_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0330086Field005Chars00 ++ tail)) fragment0330086Acc00500 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment0330086Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_005"
  err.flush

noncomputable def fragment0330086Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0330086Field006Value00 : SourceJson := .str (String.ofList ['2', '1', '5', '1', '9', '4', '3', '5', '1', '0', '8', '8', '7', '8', '7', '1', '2', '6', '4', '6', '6', '1', '2', '8', '3', '7', '1', '5', '5', '2', '3', '8', '4', '7', '6', '6', '6', '2', '5', '4', '5', '8', '5', '8', '0', '4', '0', '8', '8', '3', '8', '5', '9', '3', '7', '5', '/', '3', '0', '9', '8', '0', '9', '1', '1', '4', '7', '4', '8', '8', '1', '2', '8', '0', '3', '6', '3', '0', '9', '5', '3', '0', '6', '4', '8', '9', '2', '3', '4', '9', '1', '7', '1', '2', '0', '3', '4', '3', '6', '7', '5', '3', '6', '1', '2', '0', '0', '5', '4', '0', '1', '9', '6', '7', '3', '4', '7', '6', '8', '5', '9', '3', '5', '5', '4', '9', '4', '4'])
noncomputable def fragment0330086Acc00700 : List (String × SourceJson) := (fragment0330086Field006Key00, fragment0330086Field006Value00) :: fragment0330086Acc00600
noncomputable def fragment0330086Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '5', '1', '9', '4', '3', '5', '1', '0', '8', '8', '7', '8', '7', '1', '2', '6', '4', '6', '6', '1', '2', '8', '3', '7', '1', '5', '5', '2', '3', '8', '4', '7', '6', '6', '6', '2', '5', '4', '5', '8', '5', '8', '0', '4', '0', '8', '8', '3', '8', '5', '9', '3', '7', '5', '/', '3', '0', '9', '8', '0', '9', '1', '1', '4', '7', '4', '8', '8', '1', '2', '8', '0', '3', '6', '3', '0', '9', '5', '3', '0', '6', '4', '8', '9', '2', '3', '4', '9', '1', '7', '1', '2', '0', '3', '4', '3', '6', '7', '5', '3', '6', '1', '2', '0', '0', '5', '4', '0', '1', '9', '6', '7', '3', '4', '7', '6', '8', '5', '9', '3', '5', '5', '4', '9', '4', '4', '"', ',']

theorem object_fragment0330086_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment0330086Field006Chars00 ++ tail)) fragment0330086Acc00600 =
      SourceJson.object (fuel + 361) (SourceJson.white tail) fragment0330086Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_006"
  err.flush

noncomputable def fragment0330086Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0330086Field007Value00 : SourceJson := .str (String.ofList ['5', '5', '0', '1', '3', '2', '4', '2', '0', '1', '9', '4', '8', '2', '7', '6', '5', '2', '4', '1', '3', '0', '9', '2', '8', '8', '9', '5', '6', '8', '6', '6', '4', '5', '0', '3', '9', '2', '9', '8', '0', '0', '7', '6', '9', '9', '1', '8', '2', '0', '4', '4', '0', '1', '8', '0', '7', '5', '2', '9', '2', '8', '0', '4', '3', '4', '2', '8', '8', '2', '8', '6', '0', '6', '7', '3', '4', '7', '4', '1', '4', '4', '2', '7', '9', '7', '6', '4', '9', '4', '4', '0', '8', '8', '7', '7', '9', '9', '7', '0', '1', '9', '0', '3', '3', '7', '2', '8', '2', '5', '7', '3', '2', '5', '9', '2', '5', '5', '0', '7', '5', '3', '3', '2', '2', '9', '2', '6', '9', '4', '5', '6', '5', '6', '0', '2', '2', '4', '6', '9', '4', '5', '9', '0', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '8', '2', '1', '9', '4', '9', '9', '5', '2', '8', '4', '2', '0', '2', '9', '1', '9', '1', '7', '9', '3', '4', '8', '3', '7', '8', '1', '4', '3', '0', '9', '5', '3', '5', '3', '6', '2', '2', '3', '4', '8', '5', '2', '4', '5', '9', '6', '1', '9', '3', '0', '7', '4', '1', '1', '7', '9', '8', '9', '2', '5', '7', '0', '3', '6', '2', '1', '1', '4', '0', '8', '5', '5', '8', '8', '2', '3', '6', '5', '9', '3', '8', '4', '2', '8', '0', '2', '2', '9', '8', '5', '8', '1', '8', '2', '8', '1', '2', '3', '6', '4', '3', '6', '7', '8', '9', '8', '5', '2', '8', '0', '5', '4', '1', '5', '3', '9', '5', '5', '9', '8', '5', '2', '3', '7', '9', '4', '0', '3', '0', '4', '1', '8', '4', '3', '1', '1', '9', '1', '2', '8', '6', '2', '7', '1', '7', '8', '8', '5', '6', '6', '7', '0', '5', '4', '1', '3', '2', '3', '9', '1', '7', '2', '8', '4', '1', '3', '9', '2', '3', '0', '6', '8', '6', '3', '3', '6', '2', '1', '1', '2', '4', '0', '1'])
noncomputable def fragment0330086Acc00800 : List (String × SourceJson) := (fragment0330086Field007Key00, fragment0330086Field007Value00) :: fragment0330086Acc00700
noncomputable def fragment0330086Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '5', '0', '1', '3', '2', '4', '2', '0', '1', '9', '4', '8', '2', '7', '6', '5', '2', '4', '1', '3', '0', '9', '2', '8', '8', '9', '5', '6', '8', '6', '6', '4', '5', '0', '3', '9', '2', '9', '8', '0', '0', '7', '6', '9', '9', '1', '8', '2', '0', '4', '4', '0', '1', '8', '0', '7', '5', '2', '9', '2', '8', '0', '4', '3', '4', '2', '8', '8', '2', '8', '6', '0', '6', '7', '3', '4', '7', '4', '1', '4', '4', '2', '7', '9', '7', '6', '4', '9', '4', '4', '0', '8', '8', '7', '7', '9', '9', '7', '0', '1', '9', '0', '3', '3', '7', '2', '8', '2', '5', '7', '3', '2', '5', '9', '2', '5', '5', '0', '7', '5', '3', '3', '2', '2', '9', '2', '6', '9', '4', '5', '6', '5', '6', '0', '2', '2', '4', '6', '9', '4', '5', '9', '0', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '8', '2', '1', '9', '4', '9', '9', '5', '2', '8', '4', '2', '0', '2', '9', '1', '9', '1', '7', '9', '3', '4', '8', '3', '7', '8', '1', '4', '3', '0', '9', '5', '3', '5', '3', '6', '2', '2', '3', '4', '8', '5', '2', '4', '5', '9', '6', '1', '9', '3', '0', '7', '4', '1', '1', '7', '9', '8', '9', '2', '5', '7', '0', '3', '6', '2', '1', '1', '4', '0', '8', '5', '5', '8', '8', '2', '3', '6', '5', '9', '3', '8', '4', '2', '8', '0', '2', '2', '9', '8', '5', '8', '1', '8', '2', '8', '1', '2', '3', '6', '4', '3', '6', '7', '8', '9', '8', '5', '2', '8', '0', '5', '4', '1', '5', '3', '9', '5', '5', '9', '8', '5', '2', '3', '7', '9', '4', '0', '3', '0', '4', '1', '8', '4', '3', '1', '1', '9', '1', '2', '8', '6', '2', '7', '1', '7', '8', '8', '5', '6', '6', '7', '0', '5', '4', '1', '3', '2', '3', '9', '1', '7', '2', '8', '4', '1', '3', '9', '2', '3', '0', '6', '8', '6', '3', '3', '6', '2', '1', '1', '2', '4', '0', '1', '"', ',']

theorem object_fragment0330086_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 361) (SourceJson.white (fragment0330086Field007Chars00 ++ tail)) fragment0330086Acc00700 =
      SourceJson.object (fuel + 360) (SourceJson.white tail) fragment0330086Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_007"
  err.flush

noncomputable def fragment0330086Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0330086Field008Value00 : SourceJson := .str (String.ofList ['5', '5', '0', '3', '2', '1', '2', '2', '0', '6', '6', '6', '3', '9'])
noncomputable def fragment0330086Acc00900 : List (String × SourceJson) := (fragment0330086Field008Key00, fragment0330086Field008Value00) :: fragment0330086Acc00800
noncomputable def fragment0330086Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '0', '3', '2', '1', '2', '2', '0', '6', '6', '6', '3', '9', '"', ',']

theorem object_fragment0330086_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 360) (SourceJson.white (fragment0330086Field008Chars00 ++ tail)) fragment0330086Acc00800 =
      SourceJson.object (fuel + 359) (SourceJson.white tail) fragment0330086Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_008"
  err.flush

noncomputable def fragment0330086Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0330086Field009Value00 : SourceJson := .str (String.ofList ['3', '1', '5', '3', '3', '8', '8', '6', '9', '9', '8', '7', '7', '2', '8'])
noncomputable def fragment0330086Acc01000 : List (String × SourceJson) := (fragment0330086Field009Key00, fragment0330086Field009Value00) :: fragment0330086Acc00900
noncomputable def fragment0330086Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '5', '3', '3', '8', '8', '6', '9', '9', '8', '7', '7', '2', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0330086_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 359) (SourceJson.white (fragment0330086Field009Chars00 ++ tail)) fragment0330086Acc00900 =
      .ok (.obj (fragment0330086Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330086_object_field_009"
  err.flush

noncomputable def fragment0330086Chars : List Char := '{' :: (fragment0330086Field000Chars00 ++ fragment0330086Field001Chars00 ++ fragment0330086Field002Chars00 ++ fragment0330086Field003Chars00 ++ fragment0330086Field004Chars00 ++ fragment0330086Field005Chars00 ++ fragment0330086Field006Chars00 ++ fragment0330086Field007Chars00 ++ fragment0330086Field008Chars00 ++ fragment0330086Field009Chars00)
noncomputable def fragment0330086Value : SourceJson := .obj (fragment0330086Acc01000.reverse)

theorem value_fragment0330086 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 369) (fragment0330086Chars ++ tail) =
      .ok (fragment0330086Value, tail) := by
  have hinput : fragment0330086Chars ++ tail = '{' :: (fragment0330086Field000Chars00 ++ (fragment0330086Field001Chars00 ++ (fragment0330086Field002Chars00 ++ (fragment0330086Field003Chars00 ++ (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0330086Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 369) (fragment0330086Chars ++ tail) =
        SourceJson.value (fuel + 369) ('{' :: (fragment0330086Field000Chars00 ++ (fragment0330086Field001Chars00 ++ (fragment0330086Field002Chars00 ++ (fragment0330086Field003Chars00 ++ (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 369)) hinput
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0330086Field000Chars00 ++ (fragment0330086Field001Chars00 ++ (fragment0330086Field002Chars00 ++ (fragment0330086Field003Chars00 ++ (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))))))))))) fragment0330086Acc00000 := by rfl
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0330086Field001Chars00 ++ (fragment0330086Field002Chars00 ++ (fragment0330086Field003Chars00 ++ (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail))))))))))) fragment0330086Acc00100 := object_fragment0330086_field_000 fuel (fragment0330086Field001Chars00 ++ (fragment0330086Field002Chars00 ++ (fragment0330086Field003Chars00 ++ (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0330086Field002Chars00 ++ (fragment0330086Field003Chars00 ++ (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))))))))) fragment0330086Acc00200 := object_fragment0330086_field_001 fuel (fragment0330086Field002Chars00 ++ (fragment0330086Field003Chars00 ++ (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0330086Field003Chars00 ++ (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail))))))))) fragment0330086Acc00300 := object_fragment0330086_field_002 fuel (fragment0330086Field003Chars00 ++ (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))))))) fragment0330086Acc00400 := object_fragment0330086_field_003 fuel (fragment0330086Field004Chars00 ++ (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail))))))) fragment0330086Acc00500 := object_fragment0330086_field_004 fuel (fragment0330086Field005Chars00 ++ (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))))) fragment0330086Acc00600 := object_fragment0330086_field_005 fuel (fragment0330086Field006Chars00 ++ (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 361) (SourceJson.white (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail))))) fragment0330086Acc00700 := object_fragment0330086_field_006 fuel (fragment0330086Field007Chars00 ++ (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 360) (SourceJson.white (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))) fragment0330086Acc00800 := object_fragment0330086_field_007 fuel (fragment0330086Field008Chars00 ++ (fragment0330086Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 359) (SourceJson.white (fragment0330086Field009Chars00 ++ (tail))) fragment0330086Acc00900 := object_fragment0330086_field_008 fuel (fragment0330086Field009Chars00 ++ (tail))
    _ = .ok (fragment0330086Value, tail) := object_fragment0330086_field_009 fuel (tail)

noncomputable def fragment0331985Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0331985Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0331985Field000Value00 : SourceJson := .number (String.ofList ['6', '2'])
noncomputable def fragment0331985Acc00100 : List (String × SourceJson) := (fragment0331985Field000Key00, fragment0331985Field000Value00) :: fragment0331985Acc00000
noncomputable def fragment0331985Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '2', ',']

theorem object_fragment0331985_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0331985Field000Chars00 ++ tail)) fragment0331985Acc00000 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0331985Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_000"
  err.flush

noncomputable def fragment0331985Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0331985Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0331985Acc00200 : List (String × SourceJson) := (fragment0331985Field001Key00, fragment0331985Field001Value00) :: fragment0331985Acc00100
noncomputable def fragment0331985Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0331985_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0331985Field001Chars00 ++ tail)) fragment0331985Acc00100 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0331985Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_001"
  err.flush

noncomputable def fragment0331985Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0331985Field002Value00 : SourceJson := .str (String.ofList ['3', '0', '0', '6', '6', '4', '4', '8', '9', '8', '1', '6', '9', '5', '6', '7', '9', '4', '8', '4', '9', '6', '5', '0', '1', '2', '3', '8', '8', '4', '8', '9', '2', '5', '2', '9', '/', '2', '3', '1', '0', '2', '2', '2', '6', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0331985Acc00300 : List (String × SourceJson) := (fragment0331985Field002Key00, fragment0331985Field002Value00) :: fragment0331985Acc00200
noncomputable def fragment0331985Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '0', '0', '6', '6', '4', '4', '8', '9', '8', '1', '6', '9', '5', '6', '7', '9', '4', '8', '4', '9', '6', '5', '0', '1', '2', '3', '8', '8', '4', '8', '9', '2', '5', '2', '9', '/', '2', '3', '1', '0', '2', '2', '2', '6', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0331985_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0331985Field002Chars00 ++ tail)) fragment0331985Acc00200 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0331985Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_002"
  err.flush

noncomputable def fragment0331985Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0331985Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0331985Acc00400 : List (String × SourceJson) := (fragment0331985Field003Key00, fragment0331985Field003Value00) :: fragment0331985Acc00300
noncomputable def fragment0331985Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0331985_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0331985Field003Chars00 ++ tail)) fragment0331985Acc00300 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0331985Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_003"
  err.flush

noncomputable def fragment0331985Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0331985Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '3', '7', '3', '/', '2', '0', '8', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0331985Acc00500 : List (String × SourceJson) := (fragment0331985Field004Key00, fragment0331985Field004Value00) :: fragment0331985Acc00400
noncomputable def fragment0331985Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '3', '7', '3', '/', '2', '0', '8', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0331985_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0331985Field004Chars00 ++ tail)) fragment0331985Acc00400 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0331985Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_004"
  err.flush

noncomputable def fragment0331985Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0331985Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '9', '8', '8', '6', '3', '3', '8', '3', '2', '7', '1', '0', '7', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '2', '5', '4', '1', '3', '7', '3', '3', '6', '8', '6', '7', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '2', '2', '9', '7', '2', '9', '0', '6', '7', '9', '/', '1', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '7', '9', '7', '3', '6', '8', '1', '8', '9', '4', '7', '/', '1', '2', '1', '2', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '9', '0', '4', '7', '4', '5', '5', '9', '0', '1', '/', '3', '0', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '3', '9', '5', '5', '2', '7', '9', '8', '5', '3', '1', '/', '1', '8', '1', '9', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '4', '5', '2', '2', '1', '4', '1', '4', '2', '9', '/', '2', '0', '7', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '8', '3', '1', '3', '7', '7', '7', '2', '5', '5', '9', '/', '2', '0', '7', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '9', '5', '2', '7', '0', '6', '8', '8', '9', '7', '7', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '9', '5', '2', '2', '2', '1', '7', '5', '0', '5', '7', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0331985Acc00600 : List (String × SourceJson) := (fragment0331985Field005Key00, fragment0331985Field005Value00) :: fragment0331985Acc00500
noncomputable def fragment0331985Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '8', '8', '6', '3', '3', '8', '3', '2', '7', '1', '0', '7', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '2', '5', '4', '1', '3', '7', '3', '3', '6', '8', '6', '7', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '2', '2', '9', '7', '2', '9', '0', '6', '7', '9', '/', '1', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '7', '9', '7', '3', '6', '8', '1', '8', '9', '4', '7', '/', '1', '2', '1', '2', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '0', '4', '7', '4', '5', '5', '9', '0', '1', '/', '3', '0', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '3', '9', '5', '5', '2', '7', '9', '8', '5', '3', '1', '/', '1', '8', '1', '9', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '1', '4', '5', '2', '2', '1', '4', '1', '4', '2', '9', '/', '2', '0', '7', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '8', '3', '1', '3', '7', '7', '7', '2', '5', '5', '9', '/', '2', '0', '7', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '9', '5', '2', '7', '0', '6', '8', '8', '9', '7', '7', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '9', '5', '2', '2', '2', '1', '7', '5', '0', '5', '7', '/', '3', '6', '3', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0331985_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0331985Field005Chars00 ++ tail)) fragment0331985Acc00500 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0331985Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_005"
  err.flush

noncomputable def fragment0331985Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0331985Field006Value00 : SourceJson := .str (String.ofList ['1', '6', '2', '2', '8', '7', '6', '4', '7', '9', '6', '5', '2', '0', '1', '9', '2', '4', '2', '5', '4', '4', '9', '1', '8', '5', '1', '6', '4', '7', '3', '6', '0', '7', '5', '3', '6', '0', '1', '6', '9', '2', '5', '0', '0', '/', '1', '9', '4', '0', '9', '9', '2', '5', '5', '6', '8', '9', '9', '7', '1', '3', '5', '6', '6', '1', '1', '0', '5', '3', '1', '5', '1', '5', '9', '3', '1', '4', '6', '1', '6', '1', '4', '2', '1', '2', '6', '8', '4', '8', '6', '8', '1', '8', '1', '3', '2', '5', '1', '9', '5', '6', '7', '1', '6', '9'])
noncomputable def fragment0331985Acc00700 : List (String × SourceJson) := (fragment0331985Field006Key00, fragment0331985Field006Value00) :: fragment0331985Acc00600
noncomputable def fragment0331985Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '2', '2', '8', '7', '6', '4', '7', '9', '6', '5', '2', '0', '1', '9', '2', '4', '2', '5', '4', '4', '9', '1', '8', '5', '1', '6', '4', '7', '3', '6', '0', '7', '5', '3', '6', '0', '1', '6', '9', '2', '5', '0', '0', '/', '1', '9', '4', '0', '9', '9', '2', '5', '5', '6', '8', '9', '9', '7', '1', '3', '5', '6', '6', '1', '1', '0', '5', '3', '1', '5', '1', '5', '9', '3', '1', '4', '6', '1', '6', '1', '4', '2', '1', '2', '6', '8', '4', '8', '6', '8', '1', '8', '1', '3', '2', '5', '1', '9', '5', '6', '7', '1', '6', '9', '"', ',']

theorem object_fragment0331985_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0331985Field006Chars00 ++ tail)) fragment0331985Acc00600 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0331985Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_006"
  err.flush

noncomputable def fragment0331985Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0331985Field007Value00 : SourceJson := .str (String.ofList ['2', '9', '8', '7', '6', '4', '7', '3', '0', '3', '0', '3', '9', '1', '8', '0', '9', '3', '1', '3', '4', '6', '9', '7', '9', '6', '6', '1', '7', '5', '6', '7', '5', '0', '4', '6', '5', '4', '5', '3', '2', '7', '2', '4', '3', '0', '7', '5', '4', '2', '8', '3', '5', '8', '4', '6', '1', '7', '3', '5', '1', '2', '2', '2', '6', '3', '6', '4', '1', '3', '9', '2', '6', '2', '0', '9', '5', '0', '6', '3', '0', '6', '8', '9', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '1', '1', '9', '4', '8', '8', '9', '7', '2', '5', '8', '1', '0', '7', '4', '7', '6', '8', '9', '8', '1', '7', '0', '8', '2', '1', '1', '6', '5', '2', '9', '2', '4', '0', '0', '0', '7', '0', '9', '7', '5', '7', '8', '5', '4', '8', '7', '5', '9', '3', '7', '2', '4', '4', '6', '6', '6', '6', '1', '6', '2', '3', '3', '7', '9', '6', '2', '3', '9', '3', '8', '4', '0', '7', '1', '6', '1', '7', '4', '4', '3', '3', '7', '7', '5', '3', '9', '8', '0', '1', '7', '2', '7', '1', '2', '0', '2', '9', '2', '6', '6', '0', '5', '5', '4', '1', '3', '1', '7', '6', '3', '7', '6', '7', '0', '7', '2', '1', '8', '5', '3', '0', '4', '7', '7', '5', '3'])
noncomputable def fragment0331985Acc00800 : List (String × SourceJson) := (fragment0331985Field007Key00, fragment0331985Field007Value00) :: fragment0331985Acc00700
noncomputable def fragment0331985Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '9', '8', '7', '6', '4', '7', '3', '0', '3', '0', '3', '9', '1', '8', '0', '9', '3', '1', '3', '4', '6', '9', '7', '9', '6', '6', '1', '7', '5', '6', '7', '5', '0', '4', '6', '5', '4', '5', '3', '2', '7', '2', '4', '3', '0', '7', '5', '4', '2', '8', '3', '5', '8', '4', '6', '1', '7', '3', '5', '1', '2', '2', '2', '6', '3', '6', '4', '1', '3', '9', '2', '6', '2', '0', '9', '5', '0', '6', '3', '0', '6', '8', '9', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '1', '1', '9', '4', '8', '8', '9', '7', '2', '5', '8', '1', '0', '7', '4', '7', '6', '8', '9', '8', '1', '7', '0', '8', '2', '1', '1', '6', '5', '2', '9', '2', '4', '0', '0', '0', '7', '0', '9', '7', '5', '7', '8', '5', '4', '8', '7', '5', '9', '3', '7', '2', '4', '4', '6', '6', '6', '6', '1', '6', '2', '3', '3', '7', '9', '6', '2', '3', '9', '3', '8', '4', '0', '7', '1', '6', '1', '7', '4', '4', '3', '3', '7', '7', '5', '3', '9', '8', '0', '1', '7', '2', '7', '1', '2', '0', '2', '9', '2', '6', '6', '0', '5', '5', '4', '1', '3', '1', '7', '6', '3', '7', '6', '7', '0', '7', '2', '1', '8', '5', '3', '0', '4', '7', '7', '5', '3', '"', ',']

theorem object_fragment0331985_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0331985Field007Chars00 ++ tail)) fragment0331985Acc00700 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0331985Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_007"
  err.flush

noncomputable def fragment0331985Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0331985Field008Value00 : SourceJson := .str (String.ofList ['6', '6', '2', '4', '3', '1', '8', '1', '1', '0', '5', '1', '4', '5'])
noncomputable def fragment0331985Acc00900 : List (String × SourceJson) := (fragment0331985Field008Key00, fragment0331985Field008Value00) :: fragment0331985Acc00800
noncomputable def fragment0331985Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '2', '4', '3', '1', '8', '1', '1', '0', '5', '1', '4', '5', '"', ',']

theorem object_fragment0331985_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0331985Field008Chars00 ++ tail)) fragment0331985Acc00800 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0331985Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_008"
  err.flush

noncomputable def fragment0331985Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0331985Field009Value00 : SourceJson := .str (String.ofList ['4', '6', '2', '3', '6', '2', '1', '7', '5', '8', '5', '0', '4', '3', '9'])
noncomputable def fragment0331985Acc01000 : List (String × SourceJson) := (fragment0331985Field009Key00, fragment0331985Field009Value00) :: fragment0331985Acc00900
noncomputable def fragment0331985Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '2', '3', '6', '2', '1', '7', '5', '8', '5', '0', '4', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0331985_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0331985Field009Chars00 ++ tail)) fragment0331985Acc00900 =
      .ok (.obj (fragment0331985Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0331985_object_field_009"
  err.flush

noncomputable def fragment0331985Chars : List Char := '{' :: (fragment0331985Field000Chars00 ++ fragment0331985Field001Chars00 ++ fragment0331985Field002Chars00 ++ fragment0331985Field003Chars00 ++ fragment0331985Field004Chars00 ++ fragment0331985Field005Chars00 ++ fragment0331985Field006Chars00 ++ fragment0331985Field007Chars00 ++ fragment0331985Field008Chars00 ++ fragment0331985Field009Chars00)
noncomputable def fragment0331985Value : SourceJson := .obj (fragment0331985Acc01000.reverse)

theorem value_fragment0331985 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 254) (fragment0331985Chars ++ tail) =
      .ok (fragment0331985Value, tail) := by
  have hinput : fragment0331985Chars ++ tail = '{' :: (fragment0331985Field000Chars00 ++ (fragment0331985Field001Chars00 ++ (fragment0331985Field002Chars00 ++ (fragment0331985Field003Chars00 ++ (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0331985Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 254) (fragment0331985Chars ++ tail) =
        SourceJson.value (fuel + 254) ('{' :: (fragment0331985Field000Chars00 ++ (fragment0331985Field001Chars00 ++ (fragment0331985Field002Chars00 ++ (fragment0331985Field003Chars00 ++ (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 254)) hinput
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0331985Field000Chars00 ++ (fragment0331985Field001Chars00 ++ (fragment0331985Field002Chars00 ++ (fragment0331985Field003Chars00 ++ (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))))))))))) fragment0331985Acc00000 := by rfl
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0331985Field001Chars00 ++ (fragment0331985Field002Chars00 ++ (fragment0331985Field003Chars00 ++ (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail))))))))))) fragment0331985Acc00100 := object_fragment0331985_field_000 fuel (fragment0331985Field001Chars00 ++ (fragment0331985Field002Chars00 ++ (fragment0331985Field003Chars00 ++ (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0331985Field002Chars00 ++ (fragment0331985Field003Chars00 ++ (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))))))))) fragment0331985Acc00200 := object_fragment0331985_field_001 fuel (fragment0331985Field002Chars00 ++ (fragment0331985Field003Chars00 ++ (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0331985Field003Chars00 ++ (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail))))))))) fragment0331985Acc00300 := object_fragment0331985_field_002 fuel (fragment0331985Field003Chars00 ++ (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))))))) fragment0331985Acc00400 := object_fragment0331985_field_003 fuel (fragment0331985Field004Chars00 ++ (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail))))))) fragment0331985Acc00500 := object_fragment0331985_field_004 fuel (fragment0331985Field005Chars00 ++ (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))))) fragment0331985Acc00600 := object_fragment0331985_field_005 fuel (fragment0331985Field006Chars00 ++ (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail))))) fragment0331985Acc00700 := object_fragment0331985_field_006 fuel (fragment0331985Field007Chars00 ++ (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))) fragment0331985Acc00800 := object_fragment0331985_field_007 fuel (fragment0331985Field008Chars00 ++ (fragment0331985Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0331985Field009Chars00 ++ (tail))) fragment0331985Acc00900 := object_fragment0331985_field_008 fuel (fragment0331985Field009Chars00 ++ (tail))
    _ = .ok (fragment0331985Value, tail) := object_fragment0331985_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0061_before_reader"
  err.flush

noncomputable def chunk0061LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0061SuffixChars00 : List Char := [',']
noncomputable def chunk0061Chars00 : List Char := chunk0061LeadChars00 ++ fragment0330086Chars ++ chunk0061SuffixChars00
noncomputable def chunk0061Push00 (acc : List SourceJson) : List SourceJson := fragment0330086Value :: acc

noncomputable def chunk0061AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0061_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 543)
      (SourceJson.white (chunk0061LeadChars00 ++ (fragment0330086Chars ++ rest))) acc =
      (SourceJson.value (fuel + 542) (fragment0330086Chars ++ rest)).bind
        (chunk0061AfterValue00 (fuel + 542) acc) := by rfl

theorem array_chunk0061 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 543) (SourceJson.white (chunk0061Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 542) (SourceJson.white tail) (chunk0061Push00 acc) := by
  have hinput : chunk0061Chars00 ++ tail = chunk0061LeadChars00 ++ (fragment0330086Chars ++ (chunk0061SuffixChars00 ++ tail)) := by
    simp only [chunk0061Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 543) (SourceJson.white (chunk0061Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 543)
          (SourceJson.white (chunk0061LeadChars00 ++ (fragment0330086Chars ++ (chunk0061SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 543) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 542) (fragment0330086Chars ++ (chunk0061SuffixChars00 ++ tail))).bind
        (chunk0061AfterValue00 (fuel + 542) acc) := array_chunk0061_head fuel (chunk0061SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0330086Value, chunk0061SuffixChars00 ++ tail)).bind
        (chunk0061AfterValue00 (fuel + 542) acc) :=
      congrArg (fun result => result.bind (chunk0061AfterValue00 (fuel + 542) acc))
        (value_fragment0330086 (fuel + 173) (chunk0061SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 542) (SourceJson.white tail) (chunk0061Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0061_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0062_before_reader"
  err.flush

noncomputable def chunk0062LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0062SuffixChars00 : List Char := [',']
noncomputable def chunk0062Chars00 : List Char := chunk0062LeadChars00 ++ fragment0331985Chars ++ chunk0062SuffixChars00
noncomputable def chunk0062Push00 (acc : List SourceJson) : List SourceJson := fragment0331985Value :: acc

noncomputable def chunk0062AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0062_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 542)
      (SourceJson.white (chunk0062LeadChars00 ++ (fragment0331985Chars ++ rest))) acc =
      (SourceJson.value (fuel + 541) (fragment0331985Chars ++ rest)).bind
        (chunk0062AfterValue00 (fuel + 541) acc) := by rfl

theorem array_chunk0062 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 542) (SourceJson.white (chunk0062Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 541) (SourceJson.white tail) (chunk0062Push00 acc) := by
  have hinput : chunk0062Chars00 ++ tail = chunk0062LeadChars00 ++ (fragment0331985Chars ++ (chunk0062SuffixChars00 ++ tail)) := by
    simp only [chunk0062Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 542) (SourceJson.white (chunk0062Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 542)
          (SourceJson.white (chunk0062LeadChars00 ++ (fragment0331985Chars ++ (chunk0062SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 542) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 541) (fragment0331985Chars ++ (chunk0062SuffixChars00 ++ tail))).bind
        (chunk0062AfterValue00 (fuel + 541) acc) := array_chunk0062_head fuel (chunk0062SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0331985Value, chunk0062SuffixChars00 ++ tail)).bind
        (chunk0062AfterValue00 (fuel + 541) acc) :=
      congrArg (fun result => result.bind (chunk0062AfterValue00 (fuel + 541) acc))
        (value_fragment0331985 (fuel + 287) (chunk0062SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 541) (SourceJson.white tail) (chunk0062Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0062_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0061Chars00 ++ chunk0062Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0062Push00 (chunk0061Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 543) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 541) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0061Chars00 ++ (chunk0062Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 543) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 543) (SourceJson.white (chunk0061Chars00 ++ (chunk0062Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 543) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 542) (SourceJson.white (chunk0062Chars00 ++ (tail))) (chunk0061Push00 (acc)) := array_chunk0061 fuel (chunk0062Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 541) (SourceJson.white tail) (blockPush acc) := array_chunk0062 fuel (tail) (chunk0061Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 330080).take 3511 = blockChars := by rfl

theorem block_original_split : sourceRest 330080 = blockChars ++ sourceRest 333591 := by
  calc
    sourceRest 330080 = (sourceRest 330080).take 3511 ++ (sourceRest 330080).drop 3511 :=
      (List.take_append_drop 3511 (sourceRest 330080)).symm
    _ = blockChars ++ (sourceRest 330080).drop 3511 :=
      congrArg (fun part => part ++ (sourceRest 330080).drop 3511) block_original_prefix
    _ = blockChars ++ sourceRest 333591 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 330080 3511)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 543) (SourceJson.white (sourceRest 330080)) acc =
      SourceJson.array (fuel + 541) (SourceJson.white (sourceRest 333591)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 543) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 333591) acc)

#print axioms object_fragment0330086_field_000
#print axioms object_fragment0330086_field_001
#print axioms object_fragment0330086_field_002
#print axioms object_fragment0330086_field_003
#print axioms object_fragment0330086_field_004
#print axioms object_fragment0330086_field_005
#print axioms object_fragment0330086_field_006
#print axioms object_fragment0330086_field_007
#print axioms object_fragment0330086_field_008
#print axioms object_fragment0330086_field_009
#print axioms value_fragment0330086
#print axioms object_fragment0331985_field_000
#print axioms object_fragment0331985_field_001
#print axioms object_fragment0331985_field_002
#print axioms object_fragment0331985_field_003
#print axioms object_fragment0331985_field_004
#print axioms object_fragment0331985_field_005
#print axioms object_fragment0331985_field_006
#print axioms object_fragment0331985_field_007
#print axioms object_fragment0331985_field_008
#print axioms object_fragment0331985_field_009
#print axioms value_fragment0331985
#print axioms array_chunk0061_head
#print axioms array_chunk0061
#print axioms array_chunk0062_head
#print axioms array_chunk0062
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock031

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
