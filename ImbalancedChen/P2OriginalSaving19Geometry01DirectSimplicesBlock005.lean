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

namespace SimplicesBlock005

noncomputable def fragment0243143Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0243143Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0243143Field000Value00 : SourceJson := .number (String.ofList ['1', '0'])
noncomputable def fragment0243143Acc00100 : List (String × SourceJson) := (fragment0243143Field000Key00, fragment0243143Field000Value00) :: fragment0243143Acc00000
noncomputable def fragment0243143Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', ',']

theorem object_fragment0243143_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment0243143Field000Chars00 ++ tail)) fragment0243143Acc00000 =
      SourceJson.object (fuel + 368) (SourceJson.white tail) fragment0243143Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_000"
  err.flush

noncomputable def fragment0243143Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0243143Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '2']), .number (String.ofList ['4']), .number (String.ofList ['2'])]
noncomputable def fragment0243143Acc00200 : List (String × SourceJson) := (fragment0243143Field001Key00, fragment0243143Field001Value00) :: fragment0243143Acc00100
noncomputable def fragment0243143Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0243143_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0243143Field001Chars00 ++ tail)) fragment0243143Acc00100 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment0243143Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_001"
  err.flush

noncomputable def fragment0243143Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0243143Field002Value00 : SourceJson := .str (String.ofList ['4', '0', '2', '3', '1', '9', '1', '2', '8', '8', '3', '6', '9', '0', '0', '2', '7', '9', '7', '6', '5', '6', '4', '6', '5', '7', '8', '4', '3', '8', '7', '7', '4', '4', '4', '1', '9', '3', '7', '7', '7', '5', '3', '7', '1', '9', '9', '1', '/', '8', '5', '9', '6', '2', '3', '4', '6', '5', '2', '6', '9', '8', '5', '4', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0243143Acc00300 : List (String × SourceJson) := (fragment0243143Field002Key00, fragment0243143Field002Value00) :: fragment0243143Acc00200
noncomputable def fragment0243143Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '0', '2', '3', '1', '9', '1', '2', '8', '8', '3', '6', '9', '0', '0', '2', '7', '9', '7', '6', '5', '6', '4', '6', '5', '7', '8', '4', '3', '8', '7', '7', '4', '4', '4', '1', '9', '3', '7', '7', '7', '5', '3', '7', '1', '9', '9', '1', '/', '8', '5', '9', '6', '2', '3', '4', '6', '5', '2', '6', '9', '8', '5', '4', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0243143_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0243143Field002Chars00 ++ tail)) fragment0243143Acc00200 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0243143Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_002"
  err.flush

noncomputable def fragment0243143Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0243143Field003Value00 : SourceJson := .str (String.ofList ['5', '9', '1', '6', '2', '9', '/', '5', '1', '7', '4', '4', '0', '0', '0', '0'])
noncomputable def fragment0243143Acc00400 : List (String × SourceJson) := (fragment0243143Field003Key00, fragment0243143Field003Value00) :: fragment0243143Acc00300
noncomputable def fragment0243143Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '9', '1', '6', '2', '9', '/', '5', '1', '7', '4', '4', '0', '0', '0', '0', '"', ',']

theorem object_fragment0243143_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0243143Field003Chars00 ++ tail)) fragment0243143Acc00300 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0243143Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_003"
  err.flush

noncomputable def fragment0243143Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0243143Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '2', '1', '8', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '2', '7', '8', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0243143Acc00500 : List (String × SourceJson) := (fragment0243143Field004Key00, fragment0243143Field004Value00) :: fragment0243143Acc00400
noncomputable def fragment0243143Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '8', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '2', '7', '8', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0243143_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0243143Field004Chars00 ++ tail)) fragment0243143Acc00400 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0243143Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_004"
  err.flush

noncomputable def fragment0243143Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0243143Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '5', '3', '8', '0', '6', '8', '1', '3', '9', '9', '0', '2', '0', '9', '8', '2', '3', '8', '9', '/', '1', '8', '6', '5', '8', '2', '4', '8', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '4', '5', '8', '2', '0', '4', '7', '6', '3', '3', '7', '3', '0', '0', '8', '3', '/', '1', '2', '4', '3', '8', '8', '3', '2', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '2', '9', '6', '6', '8', '1', '0', '8', '5', '7', '4', '7', '1', '5', '8', '4', '1', '/', '3', '9', '9', '8', '1', '9', '6', '1', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '2', '8', '7', '4', '4', '8', '2', '9', '9', '8', '4', '8', '6', '8', '2', '8', '2', '1', '/', '1', '1', '1', '9', '4', '9', '4', '9', '1', '9', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '7', '7', '7', '3', '0', '6', '7', '6', '0', '8', '3', '7', '9', '5', '2', '9', '/', '1', '5', '9', '9', '2', '7', '8', '4', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '2', '8', '7', '9', '0', '1', '9', '6', '0', '6', '7', '2', '5', '0', '7', '4', '9', '/', '5', '5', '9', '7', '4', '7', '4', '5', '9', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '9', '8', '5', '9', '5', '9', '4', '6', '6', '6', '7', '6', '4', '0', '1', '/', '6', '5', '2', '7', '6', '6', '7', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '4', '4', '2', '3', '9', '9', '8', '2', '4', '2', '5', '6', '4', '5', '1', '/', '6', '5', '2', '7', '6', '6', '7', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '9', '7', '4', '4', '9', '9', '8', '0', '7', '2', '1', '1', '8', '6', '5', '7', '1', '7', '/', '5', '5', '9', '7', '4', '7', '4', '5', '9', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '7', '1', '6', '8', '4', '9', '3', '9', '0', '8', '7', '8', '2', '1', '8', '7', '/', '3', '7', '3', '1', '6', '4', '9', '7', '3', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0243143Acc00600 : List (String × SourceJson) := (fragment0243143Field005Key00, fragment0243143Field005Value00) :: fragment0243143Acc00500
noncomputable def fragment0243143Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '3', '8', '0', '6', '8', '1', '3', '9', '9', '0', '2', '0', '9', '8', '2', '3', '8', '9', '/', '1', '8', '6', '5', '8', '2', '4', '8', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '4', '5', '8', '2', '0', '4', '7', '6', '3', '3', '7', '3', '0', '0', '8', '3', '/', '1', '2', '4', '3', '8', '8', '3', '2', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '2', '9', '6', '6', '8', '1', '0', '8', '5', '7', '4', '7', '1', '5', '8', '4', '1', '/', '3', '9', '9', '8', '1', '9', '6', '1', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '8', '7', '4', '4', '8', '2', '9', '9', '8', '4', '8', '6', '8', '2', '8', '2', '1', '/', '1', '1', '1', '9', '4', '9', '4', '9', '1', '9', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '7', '7', '7', '3', '0', '6', '7', '6', '0', '8', '3', '7', '9', '5', '2', '9', '/', '1', '5', '9', '9', '2', '7', '8', '4', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '2', '8', '7', '9', '0', '1', '9', '6', '0', '6', '7', '2', '5', '0', '7', '4', '9', '/', '5', '5', '9', '7', '4', '7', '4', '5', '9', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '9', '8', '5', '9', '5', '9', '4', '6', '6', '6', '7', '6', '4', '0', '1', '/', '6', '5', '2', '7', '6', '6', '7', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '4', '4', '2', '3', '9', '9', '8', '2', '4', '2', '5', '6', '4', '5', '1', '/', '6', '5', '2', '7', '6', '6', '7', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '7', '4', '4', '9', '9', '8', '0', '7', '2', '1', '1', '8', '6', '5', '7', '1', '7', '/', '5', '5', '9', '7', '4', '7', '4', '5', '9', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '7', '1', '6', '8', '4', '9', '3', '9', '0', '8', '7', '8', '2', '1', '8', '7', '/', '3', '7', '3', '1', '6', '4', '9', '7', '3', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0243143_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0243143Field005Chars00 ++ tail)) fragment0243143Acc00500 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0243143Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_005"
  err.flush

noncomputable def fragment0243143Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0243143Field006Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '5', '3', '0', '7', '7', '2', '7', '4', '9', '4', '4', '4', '1', '7', '6', '6', '6', '8', '2', '8', '9', '9', '1', '0', '0', '5', '4', '1', '0', '2', '1', '1', '6', '7', '6', '5', '1', '3', '8', '3', '7', '9', '7', '5', '5', '5', '0', '0', '6', '8', '2', '8', '1', '2', '5', '/', '1', '6', '8', '3', '7', '8', '7', '3', '5', '9', '2', '9', '5', '5', '4', '2', '6', '3', '1', '3', '0', '5', '3', '7', '1', '4', '5', '9', '3', '6', '2', '4', '3', '1', '9', '2', '8', '8', '6', '2', '3', '2', '2', '7', '8', '7', '3', '1', '5', '2', '5', '0', '4', '6', '1', '2', '7', '0', '7', '8', '9', '3', '9', '7', '0', '4', '6', '0', '4'])
noncomputable def fragment0243143Acc00700 : List (String × SourceJson) := (fragment0243143Field006Key00, fragment0243143Field006Value00) :: fragment0243143Acc00600
noncomputable def fragment0243143Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '5', '5', '3', '0', '7', '7', '2', '7', '4', '9', '4', '4', '4', '1', '7', '6', '6', '6', '8', '2', '8', '9', '9', '1', '0', '0', '5', '4', '1', '0', '2', '1', '1', '6', '7', '6', '5', '1', '3', '8', '3', '7', '9', '7', '5', '5', '5', '0', '0', '6', '8', '2', '8', '1', '2', '5', '/', '1', '6', '8', '3', '7', '8', '7', '3', '5', '9', '2', '9', '5', '5', '4', '2', '6', '3', '1', '3', '0', '5', '3', '7', '1', '4', '5', '9', '3', '6', '2', '4', '3', '1', '9', '2', '8', '8', '6', '2', '3', '2', '2', '7', '8', '7', '3', '1', '5', '2', '5', '0', '4', '6', '1', '2', '7', '0', '7', '8', '9', '3', '9', '7', '0', '4', '6', '0', '4', '"', ',']

theorem object_fragment0243143_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0243143Field006Chars00 ++ tail)) fragment0243143Acc00600 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment0243143Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_006"
  err.flush

noncomputable def fragment0243143Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0243143Field007Value00 : SourceJson := .str (String.ofList ['1', '7', '7', '1', '6', '3', '3', '2', '0', '0', '4', '4', '7', '8', '4', '7', '0', '3', '2', '6', '6', '2', '8', '5', '7', '0', '4', '8', '1', '5', '4', '1', '2', '1', '0', '1', '4', '3', '3', '0', '1', '7', '4', '5', '7', '0', '6', '2', '6', '8', '2', '3', '1', '6', '3', '0', '6', '9', '2', '0', '9', '2', '1', '9', '6', '6', '0', '1', '7', '4', '7', '3', '1', '2', '8', '6', '5', '5', '0', '0', '8', '9', '4', '8', '0', '0', '0', '1', '2', '8', '0', '8', '9', '8', '5', '1', '5', '4', '0', '9', '5', '0', '0', '7', '1', '7', '9', '2', '3', '6', '1', '6', '9', '6', '5', '3', '8', '5', '1', '8', '2', '8', '6', '0', '6', '0', '9', '6', '9', '6', '5', '3', '1', '8', '2', '1', '5', '4', '2', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '7', '5', '0', '2', '9', '4', '8', '7', '1', '3', '4', '2', '5', '2', '9', '1', '4', '6', '6', '8', '1', '3', '8', '3', '7', '2', '9', '4', '4', '5', '1', '2', '4', '8', '8', '8', '5', '5', '1', '4', '1', '8', '6', '2', '2', '9', '5', '2', '4', '0', '8', '5', '4', '2', '9', '7', '4', '1', '8', '0', '9', '3', '1', '8', '8', '3', '7', '1', '3', '0', '0', '5', '5', '4', '0', '2', '8', '0', '6', '9', '4', '9', '7', '8', '0', '2', '2', '9', '7', '5', '7', '6', '3', '8', '0', '7', '9', '7', '3', '3', '7', '9', '2', '9', '8', '5', '4', '4', '4', '6', '7', '0', '6', '7', '2', '8', '7', '3', '2', '0', '5', '4', '7', '2', '1', '0', '2', '4', '7', '2', '5', '2', '7', '3', '4', '3', '8', '4', '1', '0', '9', '8', '2', '0', '8', '1', '1', '6', '7', '6', '7', '5', '8', '8', '6', '4', '2', '9', '7', '9', '6', '3', '5', '5', '8', '0', '5', '1', '6', '7', '1', '1', '5', '3', '3', '0', '5', '8', '4', '9', '6', '3'])
noncomputable def fragment0243143Acc00800 : List (String × SourceJson) := (fragment0243143Field007Key00, fragment0243143Field007Value00) :: fragment0243143Acc00700
noncomputable def fragment0243143Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '7', '1', '6', '3', '3', '2', '0', '0', '4', '4', '7', '8', '4', '7', '0', '3', '2', '6', '6', '2', '8', '5', '7', '0', '4', '8', '1', '5', '4', '1', '2', '1', '0', '1', '4', '3', '3', '0', '1', '7', '4', '5', '7', '0', '6', '2', '6', '8', '2', '3', '1', '6', '3', '0', '6', '9', '2', '0', '9', '2', '1', '9', '6', '6', '0', '1', '7', '4', '7', '3', '1', '2', '8', '6', '5', '5', '0', '0', '8', '9', '4', '8', '0', '0', '0', '1', '2', '8', '0', '8', '9', '8', '5', '1', '5', '4', '0', '9', '5', '0', '0', '7', '1', '7', '9', '2', '3', '6', '1', '6', '9', '6', '5', '3', '8', '5', '1', '8', '2', '8', '6', '0', '6', '0', '9', '6', '9', '6', '5', '3', '1', '8', '2', '1', '5', '4', '2', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '7', '5', '0', '2', '9', '4', '8', '7', '1', '3', '4', '2', '5', '2', '9', '1', '4', '6', '6', '8', '1', '3', '8', '3', '7', '2', '9', '4', '4', '5', '1', '2', '4', '8', '8', '8', '5', '5', '1', '4', '1', '8', '6', '2', '2', '9', '5', '2', '4', '0', '8', '5', '4', '2', '9', '7', '4', '1', '8', '0', '9', '3', '1', '8', '8', '3', '7', '1', '3', '0', '0', '5', '5', '4', '0', '2', '8', '0', '6', '9', '4', '9', '7', '8', '0', '2', '2', '9', '7', '5', '7', '6', '3', '8', '0', '7', '9', '7', '3', '3', '7', '9', '2', '9', '8', '5', '4', '4', '4', '6', '7', '0', '6', '7', '2', '8', '7', '3', '2', '0', '5', '4', '7', '2', '1', '0', '2', '4', '7', '2', '5', '2', '7', '3', '4', '3', '8', '4', '1', '0', '9', '8', '2', '0', '8', '1', '1', '6', '7', '6', '7', '5', '8', '8', '6', '4', '2', '9', '7', '9', '6', '3', '5', '5', '8', '0', '5', '1', '6', '7', '1', '1', '5', '3', '3', '0', '5', '8', '4', '9', '6', '3', '"', ',']

theorem object_fragment0243143_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment0243143Field007Chars00 ++ tail)) fragment0243143Acc00700 =
      SourceJson.object (fuel + 361) (SourceJson.white tail) fragment0243143Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_007"
  err.flush

noncomputable def fragment0243143Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0243143Field008Value00 : SourceJson := .str (String.ofList ['6', '8', '4', '7', '7', '3', '8', '6', '1', '1', '7', '4', '6', '8', '9', '8', '3', '7'])
noncomputable def fragment0243143Acc00900 : List (String × SourceJson) := (fragment0243143Field008Key00, fragment0243143Field008Value00) :: fragment0243143Acc00800
noncomputable def fragment0243143Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '8', '4', '7', '7', '3', '8', '6', '1', '1', '7', '4', '6', '8', '9', '8', '3', '7', '"', ',']

theorem object_fragment0243143_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 361) (SourceJson.white (fragment0243143Field008Chars00 ++ tail)) fragment0243143Acc00800 =
      SourceJson.object (fuel + 360) (SourceJson.white tail) fragment0243143Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_008"
  err.flush

noncomputable def fragment0243143Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0243143Field009Value00 : SourceJson := .str (String.ofList ['3', '7', '1', '8', '2', '0', '2', '5', '6', '2', '3', '6', '7', '3', '3', '5', '3', '9', '0'])
noncomputable def fragment0243143Acc01000 : List (String × SourceJson) := (fragment0243143Field009Key00, fragment0243143Field009Value00) :: fragment0243143Acc00900
noncomputable def fragment0243143Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '1', '8', '2', '0', '2', '5', '6', '2', '3', '6', '7', '3', '3', '5', '3', '9', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0243143_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 360) (SourceJson.white (fragment0243143Field009Chars00 ++ tail)) fragment0243143Acc00900 =
      .ok (.obj (fragment0243143Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0243143_object_field_009"
  err.flush

noncomputable def fragment0243143Chars : List Char := '{' :: (fragment0243143Field000Chars00 ++ fragment0243143Field001Chars00 ++ fragment0243143Field002Chars00 ++ fragment0243143Field003Chars00 ++ fragment0243143Field004Chars00 ++ fragment0243143Field005Chars00 ++ fragment0243143Field006Chars00 ++ fragment0243143Field007Chars00 ++ fragment0243143Field008Chars00 ++ fragment0243143Field009Chars00)
noncomputable def fragment0243143Value : SourceJson := .obj (fragment0243143Acc01000.reverse)

theorem value_fragment0243143 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 370) (fragment0243143Chars ++ tail) =
      .ok (fragment0243143Value, tail) := by
  have hinput : fragment0243143Chars ++ tail = '{' :: (fragment0243143Field000Chars00 ++ (fragment0243143Field001Chars00 ++ (fragment0243143Field002Chars00 ++ (fragment0243143Field003Chars00 ++ (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0243143Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 370) (fragment0243143Chars ++ tail) =
        SourceJson.value (fuel + 370) ('{' :: (fragment0243143Field000Chars00 ++ (fragment0243143Field001Chars00 ++ (fragment0243143Field002Chars00 ++ (fragment0243143Field003Chars00 ++ (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 370)) hinput
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment0243143Field000Chars00 ++ (fragment0243143Field001Chars00 ++ (fragment0243143Field002Chars00 ++ (fragment0243143Field003Chars00 ++ (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))))))))))) fragment0243143Acc00000 := by rfl
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0243143Field001Chars00 ++ (fragment0243143Field002Chars00 ++ (fragment0243143Field003Chars00 ++ (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail))))))))))) fragment0243143Acc00100 := object_fragment0243143_field_000 fuel (fragment0243143Field001Chars00 ++ (fragment0243143Field002Chars00 ++ (fragment0243143Field003Chars00 ++ (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0243143Field002Chars00 ++ (fragment0243143Field003Chars00 ++ (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))))))))) fragment0243143Acc00200 := object_fragment0243143_field_001 fuel (fragment0243143Field002Chars00 ++ (fragment0243143Field003Chars00 ++ (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0243143Field003Chars00 ++ (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail))))))))) fragment0243143Acc00300 := object_fragment0243143_field_002 fuel (fragment0243143Field003Chars00 ++ (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))))))) fragment0243143Acc00400 := object_fragment0243143_field_003 fuel (fragment0243143Field004Chars00 ++ (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail))))))) fragment0243143Acc00500 := object_fragment0243143_field_004 fuel (fragment0243143Field005Chars00 ++ (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))))) fragment0243143Acc00600 := object_fragment0243143_field_005 fuel (fragment0243143Field006Chars00 ++ (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail))))) fragment0243143Acc00700 := object_fragment0243143_field_006 fuel (fragment0243143Field007Chars00 ++ (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 361) (SourceJson.white (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))) fragment0243143Acc00800 := object_fragment0243143_field_007 fuel (fragment0243143Field008Chars00 ++ (fragment0243143Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 360) (SourceJson.white (fragment0243143Field009Chars00 ++ (tail))) fragment0243143Acc00900 := object_fragment0243143_field_008 fuel (fragment0243143Field009Chars00 ++ (tail))
    _ = .ok (fragment0243143Value, tail) := object_fragment0243143_field_009 fuel (tail)

noncomputable def fragment0245048Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0245048Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0245048Field000Value00 : SourceJson := .number (String.ofList ['1', '1'])
noncomputable def fragment0245048Acc00100 : List (String × SourceJson) := (fragment0245048Field000Key00, fragment0245048Field000Value00) :: fragment0245048Acc00000
noncomputable def fragment0245048Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', ',']

theorem object_fragment0245048_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0245048Field000Chars00 ++ tail)) fragment0245048Acc00000 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0245048Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_000"
  err.flush

noncomputable def fragment0245048Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0245048Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0245048Acc00200 : List (String × SourceJson) := (fragment0245048Field001Key00, fragment0245048Field001Value00) :: fragment0245048Acc00100
noncomputable def fragment0245048Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0245048_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0245048Field001Chars00 ++ tail)) fragment0245048Acc00100 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0245048Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_001"
  err.flush

noncomputable def fragment0245048Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0245048Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '3', '4', '3', '2', '6', '2', '2', '2', '9', '3', '9', '2', '5', '8', '5', '3', '2', '1', '5', '6', '9', '5', '6', '1', '6', '2', '7', '7', '9', '8', '4', '4', '0', '2', '4', '4', '1', '8', '6', '9', '5', '4', '7', '8', '8', '6', '1', '/', '9', '8', '9', '0', '5', '5', '4', '0', '7', '4', '8', '3', '7', '8', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0245048Acc00300 : List (String × SourceJson) := (fragment0245048Field002Key00, fragment0245048Field002Value00) :: fragment0245048Acc00200
noncomputable def fragment0245048Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '3', '4', '3', '2', '6', '2', '2', '2', '9', '3', '9', '2', '5', '8', '5', '3', '2', '1', '5', '6', '9', '5', '6', '1', '6', '2', '7', '7', '9', '8', '4', '4', '0', '2', '4', '4', '1', '8', '6', '9', '5', '4', '7', '8', '8', '6', '1', '/', '9', '8', '9', '0', '5', '5', '4', '0', '7', '4', '8', '3', '7', '8', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0245048_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0245048Field002Chars00 ++ tail)) fragment0245048Acc00200 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0245048Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_002"
  err.flush

noncomputable def fragment0245048Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0245048Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0245048Acc00400 : List (String × SourceJson) := (fragment0245048Field003Key00, fragment0245048Field003Value00) :: fragment0245048Acc00300
noncomputable def fragment0245048Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0245048_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0245048Field003Chars00 ++ tail)) fragment0245048Acc00300 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0245048Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_003"
  err.flush

noncomputable def fragment0245048Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0245048Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0245048Acc00500 : List (String × SourceJson) := (fragment0245048Field004Key00, fragment0245048Field004Value00) :: fragment0245048Acc00400
noncomputable def fragment0245048Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0245048_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0245048Field004Chars00 ++ tail)) fragment0245048Acc00400 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0245048Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_004"
  err.flush

noncomputable def fragment0245048Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0245048Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '4', '0', '0', '2', '8', '0', '4', '4', '0', '3', '3', '4', '7', '/', '1', '6', '6', '2', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '7', '7', '7', '5', '5', '6', '8', '2', '2', '2', '7', '/', '1', '6', '6', '2', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '9', '8', '8', '4', '9', '0', '0', '6', '9', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '4', '5', '3', '4', '4', '5', '8', '4', '2', '9', '9', '/', '5', '5', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '4', '4', '6', '4', '9', '3', '0', '2', '2', '0', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '9', '2', '5', '9', '5', '0', '7', '9', '6', '1', '/', '2', '4', '9', '4', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '0', '0', '3', '5', '6', '3', '1', '6', '3', '3', '/', '4', '0', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '5', '5', '4', '3', '4', '1', '2', '0', '0', '3', '/', '4', '0', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '5', '9', '0', '4', '2', '0', '3', '3', '0', '8', '3', '/', '4', '9', '8', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '2', '8', '1', '7', '9', '8', '4', '3', '7', '8', '1', '9', '/', '4', '9', '8', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0245048Acc00600 : List (String × SourceJson) := (fragment0245048Field005Key00, fragment0245048Field005Value00) :: fragment0245048Acc00500
noncomputable def fragment0245048Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '0', '2', '8', '0', '4', '4', '0', '3', '3', '4', '7', '/', '1', '6', '6', '2', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '7', '7', '7', '5', '5', '6', '8', '2', '2', '2', '7', '/', '1', '6', '6', '2', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '1', '9', '8', '8', '4', '9', '0', '0', '6', '9', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '4', '5', '3', '4', '4', '5', '8', '4', '2', '9', '9', '/', '5', '5', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '4', '6', '4', '9', '3', '0', '2', '2', '0', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '9', '2', '5', '9', '5', '0', '7', '9', '6', '1', '/', '2', '4', '9', '4', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '0', '0', '3', '5', '6', '3', '1', '6', '3', '3', '/', '4', '0', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '5', '5', '4', '3', '4', '1', '2', '0', '0', '3', '/', '4', '0', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '5', '9', '0', '4', '2', '0', '3', '3', '0', '8', '3', '/', '4', '9', '8', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '8', '1', '7', '9', '8', '4', '3', '7', '8', '1', '9', '/', '4', '9', '8', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0245048_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0245048Field005Chars00 ++ tail)) fragment0245048Acc00500 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0245048Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_005"
  err.flush

noncomputable def fragment0245048Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0245048Field006Value00 : SourceJson := .str (String.ofList ['7', '9', '0', '9', '9', '5', '8', '0', '0', '6', '9', '0', '5', '4', '4', '7', '6', '8', '8', '5', '8', '4', '7', '2', '0', '8', '1', '4', '6', '6', '3', '8', '1', '3', '2', '9', '4', '4', '0', '6', '4', '3', '3', '3', '6', '3', '0', '3', '6', '4', '7', '9', '1', '3', '0', '0', '0', '0', '/', '7', '5', '5', '4', '3', '3', '7', '4', '5', '7', '5', '0', '4', '8', '7', '1', '1', '2', '0', '9', '1', '7', '9', '8', '4', '2', '0', '9', '1', '5', '0', '4', '2', '3', '0', '8', '2', '1', '7', '2', '0', '8', '6', '2', '8', '0', '6', '0', '6', '4', '7', '7', '8', '5', '1', '1', '2', '6', '0', '7', '3', '5', '0', '5', '5', '2', '5', '2', '3'])
noncomputable def fragment0245048Acc00700 : List (String × SourceJson) := (fragment0245048Field006Key00, fragment0245048Field006Value00) :: fragment0245048Acc00600
noncomputable def fragment0245048Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '9', '0', '9', '9', '5', '8', '0', '0', '6', '9', '0', '5', '4', '4', '7', '6', '8', '8', '5', '8', '4', '7', '2', '0', '8', '1', '4', '6', '6', '3', '8', '1', '3', '2', '9', '4', '4', '0', '6', '4', '3', '3', '3', '6', '3', '0', '3', '6', '4', '7', '9', '1', '3', '0', '0', '0', '0', '/', '7', '5', '5', '4', '3', '3', '7', '4', '5', '7', '5', '0', '4', '8', '7', '1', '1', '2', '0', '9', '1', '7', '9', '8', '4', '2', '0', '9', '1', '5', '0', '4', '2', '3', '0', '8', '2', '1', '7', '2', '0', '8', '6', '2', '8', '0', '6', '0', '6', '4', '7', '7', '8', '5', '1', '1', '2', '6', '0', '7', '3', '5', '0', '5', '5', '2', '5', '2', '3', '"', ',']

theorem object_fragment0245048_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0245048Field006Chars00 ++ tail)) fragment0245048Acc00600 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0245048Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_006"
  err.flush

noncomputable def fragment0245048Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0245048Field007Value00 : SourceJson := .str (String.ofList ['2', '2', '3', '5', '6', '2', '1', '0', '8', '6', '6', '7', '8', '1', '5', '7', '0', '7', '7', '3', '0', '1', '8', '8', '9', '9', '9', '3', '2', '3', '3', '9', '0', '1', '0', '5', '5', '8', '9', '7', '3', '1', '5', '0', '2', '3', '6', '1', '8', '6', '7', '8', '0', '1', '5', '8', '8', '8', '7', '2', '7', '6', '6', '4', '6', '9', '0', '1', '5', '0', '4', '7', '8', '6', '2', '9', '8', '6', '8', '7', '7', '9', '3', '7', '1', '0', '6', '6', '3', '4', '6', '7', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '3', '9', '9', '2', '0', '6', '7', '5', '6', '9', '8', '4', '4', '2', '2', '9', '6', '0', '3', '9', '2', '0', '0', '4', '4', '5', '1', '4', '9', '4', '8', '4', '0', '1', '7', '1', '7', '7', '1', '8', '0', '1', '4', '8', '4', '1', '6', '8', '3', '1', '5', '4', '7', '1', '7', '6', '5', '9', '5', '4', '7', '6', '1', '9', '8', '5', '6', '7', '3', '3', '6', '8', '3', '0', '0', '3', '7', '2', '7', '0', '4', '0', '6', '5', '6', '5', '2', '4', '0', '7', '1', '7', '1', '7', '4', '6', '6', '9', '2', '1', '4', '8', '6', '6', '1', '1', '5', '9', '8', '0', '5', '3', '6', '2', '4', '7', '3', '5', '2', '1', '9', '6', '6', '3'])
noncomputable def fragment0245048Acc00800 : List (String × SourceJson) := (fragment0245048Field007Key00, fragment0245048Field007Value00) :: fragment0245048Acc00700
noncomputable def fragment0245048Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '3', '5', '6', '2', '1', '0', '8', '6', '6', '7', '8', '1', '5', '7', '0', '7', '7', '3', '0', '1', '8', '8', '9', '9', '9', '3', '2', '3', '3', '9', '0', '1', '0', '5', '5', '8', '9', '7', '3', '1', '5', '0', '2', '3', '6', '1', '8', '6', '7', '8', '0', '1', '5', '8', '8', '8', '7', '2', '7', '6', '6', '4', '6', '9', '0', '1', '5', '0', '4', '7', '8', '6', '2', '9', '8', '6', '8', '7', '7', '9', '3', '7', '1', '0', '6', '6', '3', '4', '6', '7', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '3', '9', '9', '2', '0', '6', '7', '5', '6', '9', '8', '4', '4', '2', '2', '9', '6', '0', '3', '9', '2', '0', '0', '4', '4', '5', '1', '4', '9', '4', '8', '4', '0', '1', '7', '1', '7', '7', '1', '8', '0', '1', '4', '8', '4', '1', '6', '8', '3', '1', '5', '4', '7', '1', '7', '6', '5', '9', '5', '4', '7', '6', '1', '9', '8', '5', '6', '7', '3', '3', '6', '8', '3', '0', '0', '3', '7', '2', '7', '0', '4', '0', '6', '5', '6', '5', '2', '4', '0', '7', '1', '7', '1', '7', '4', '6', '6', '9', '2', '1', '4', '8', '6', '6', '1', '1', '5', '9', '8', '0', '5', '3', '6', '2', '4', '7', '3', '5', '2', '1', '9', '6', '6', '3', '"', ',']

theorem object_fragment0245048_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0245048Field007Chars00 ++ tail)) fragment0245048Acc00700 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0245048Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_007"
  err.flush

noncomputable def fragment0245048Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0245048Field008Value00 : SourceJson := .str (String.ofList ['8', '2', '9', '5', '7', '8', '2', '9', '4', '5', '5', '9', '1', '3', '8', '9', '0', '1'])
noncomputable def fragment0245048Acc00900 : List (String × SourceJson) := (fragment0245048Field008Key00, fragment0245048Field008Value00) :: fragment0245048Acc00800
noncomputable def fragment0245048Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '2', '9', '5', '7', '8', '2', '9', '4', '5', '5', '9', '1', '3', '8', '9', '0', '1', '"', ',']

theorem object_fragment0245048_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0245048Field008Chars00 ++ tail)) fragment0245048Acc00800 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0245048Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_008"
  err.flush

noncomputable def fragment0245048Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0245048Field009Value00 : SourceJson := .str (String.ofList ['5', '7', '0', '6', '3', '3', '3', '8', '7', '3', '2', '7', '9', '7', '1', '0', '7', '2', '8'])
noncomputable def fragment0245048Acc01000 : List (String × SourceJson) := (fragment0245048Field009Key00, fragment0245048Field009Value00) :: fragment0245048Acc00900
noncomputable def fragment0245048Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '7', '0', '6', '3', '3', '3', '8', '7', '3', '2', '7', '9', '7', '1', '0', '7', '2', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0245048_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0245048Field009Chars00 ++ tail)) fragment0245048Acc00900 =
      .ok (.obj (fragment0245048Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0245048_object_field_009"
  err.flush

noncomputable def fragment0245048Chars : List Char := '{' :: (fragment0245048Field000Chars00 ++ fragment0245048Field001Chars00 ++ fragment0245048Field002Chars00 ++ fragment0245048Field003Chars00 ++ fragment0245048Field004Chars00 ++ fragment0245048Field005Chars00 ++ fragment0245048Field006Chars00 ++ fragment0245048Field007Chars00 ++ fragment0245048Field008Chars00 ++ fragment0245048Field009Chars00)
noncomputable def fragment0245048Value : SourceJson := .obj (fragment0245048Acc01000.reverse)

theorem value_fragment0245048 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 256) (fragment0245048Chars ++ tail) =
      .ok (fragment0245048Value, tail) := by
  have hinput : fragment0245048Chars ++ tail = '{' :: (fragment0245048Field000Chars00 ++ (fragment0245048Field001Chars00 ++ (fragment0245048Field002Chars00 ++ (fragment0245048Field003Chars00 ++ (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0245048Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 256) (fragment0245048Chars ++ tail) =
        SourceJson.value (fuel + 256) ('{' :: (fragment0245048Field000Chars00 ++ (fragment0245048Field001Chars00 ++ (fragment0245048Field002Chars00 ++ (fragment0245048Field003Chars00 ++ (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 256)) hinput
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0245048Field000Chars00 ++ (fragment0245048Field001Chars00 ++ (fragment0245048Field002Chars00 ++ (fragment0245048Field003Chars00 ++ (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))))))))))) fragment0245048Acc00000 := by rfl
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0245048Field001Chars00 ++ (fragment0245048Field002Chars00 ++ (fragment0245048Field003Chars00 ++ (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail))))))))))) fragment0245048Acc00100 := object_fragment0245048_field_000 fuel (fragment0245048Field001Chars00 ++ (fragment0245048Field002Chars00 ++ (fragment0245048Field003Chars00 ++ (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0245048Field002Chars00 ++ (fragment0245048Field003Chars00 ++ (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))))))))) fragment0245048Acc00200 := object_fragment0245048_field_001 fuel (fragment0245048Field002Chars00 ++ (fragment0245048Field003Chars00 ++ (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0245048Field003Chars00 ++ (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail))))))))) fragment0245048Acc00300 := object_fragment0245048_field_002 fuel (fragment0245048Field003Chars00 ++ (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))))))) fragment0245048Acc00400 := object_fragment0245048_field_003 fuel (fragment0245048Field004Chars00 ++ (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail))))))) fragment0245048Acc00500 := object_fragment0245048_field_004 fuel (fragment0245048Field005Chars00 ++ (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))))) fragment0245048Acc00600 := object_fragment0245048_field_005 fuel (fragment0245048Field006Chars00 ++ (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail))))) fragment0245048Acc00700 := object_fragment0245048_field_006 fuel (fragment0245048Field007Chars00 ++ (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))) fragment0245048Acc00800 := object_fragment0245048_field_007 fuel (fragment0245048Field008Chars00 ++ (fragment0245048Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0245048Field009Chars00 ++ (tail))) fragment0245048Acc00900 := object_fragment0245048_field_008 fuel (fragment0245048Field009Chars00 ++ (tail))
    _ = .ok (fragment0245048Value, tail) := object_fragment0245048_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_before_reader"
  err.flush

noncomputable def chunk0010LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0010SuffixChars00 : List Char := [',']
noncomputable def chunk0010Chars00 : List Char := chunk0010LeadChars00 ++ fragment0243143Chars ++ chunk0010SuffixChars00
noncomputable def chunk0010Push00 (acc : List SourceJson) : List SourceJson := fragment0243143Value :: acc

noncomputable def chunk0010AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0010_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 594)
      (SourceJson.white (chunk0010LeadChars00 ++ (fragment0243143Chars ++ rest))) acc =
      (SourceJson.value (fuel + 593) (fragment0243143Chars ++ rest)).bind
        (chunk0010AfterValue00 (fuel + 593) acc) := by rfl

theorem array_chunk0010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 594) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 593) (SourceJson.white tail) (chunk0010Push00 acc) := by
  have hinput : chunk0010Chars00 ++ tail = chunk0010LeadChars00 ++ (fragment0243143Chars ++ (chunk0010SuffixChars00 ++ tail)) := by
    simp only [chunk0010Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 594) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 594)
          (SourceJson.white (chunk0010LeadChars00 ++ (fragment0243143Chars ++ (chunk0010SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 594) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 593) (fragment0243143Chars ++ (chunk0010SuffixChars00 ++ tail))).bind
        (chunk0010AfterValue00 (fuel + 593) acc) := array_chunk0010_head fuel (chunk0010SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0243143Value, chunk0010SuffixChars00 ++ tail)).bind
        (chunk0010AfterValue00 (fuel + 593) acc) :=
      congrArg (fun result => result.bind (chunk0010AfterValue00 (fuel + 593) acc))
        (value_fragment0243143 (fuel + 223) (chunk0010SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 593) (SourceJson.white tail) (chunk0010Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_before_reader"
  err.flush

noncomputable def chunk0011LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0011SuffixChars00 : List Char := [',']
noncomputable def chunk0011Chars00 : List Char := chunk0011LeadChars00 ++ fragment0245048Chars ++ chunk0011SuffixChars00
noncomputable def chunk0011Push00 (acc : List SourceJson) : List SourceJson := fragment0245048Value :: acc

noncomputable def chunk0011AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0011_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 593)
      (SourceJson.white (chunk0011LeadChars00 ++ (fragment0245048Chars ++ rest))) acc =
      (SourceJson.value (fuel + 592) (fragment0245048Chars ++ rest)).bind
        (chunk0011AfterValue00 (fuel + 592) acc) := by rfl

theorem array_chunk0011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 593) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 592) (SourceJson.white tail) (chunk0011Push00 acc) := by
  have hinput : chunk0011Chars00 ++ tail = chunk0011LeadChars00 ++ (fragment0245048Chars ++ (chunk0011SuffixChars00 ++ tail)) := by
    simp only [chunk0011Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 593) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 593)
          (SourceJson.white (chunk0011LeadChars00 ++ (fragment0245048Chars ++ (chunk0011SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 593) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 592) (fragment0245048Chars ++ (chunk0011SuffixChars00 ++ tail))).bind
        (chunk0011AfterValue00 (fuel + 592) acc) := array_chunk0011_head fuel (chunk0011SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0245048Value, chunk0011SuffixChars00 ++ tail)).bind
        (chunk0011AfterValue00 (fuel + 592) acc) :=
      congrArg (fun result => result.bind (chunk0011AfterValue00 (fuel + 592) acc))
        (value_fragment0245048 (fuel + 336) (chunk0011SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 592) (SourceJson.white tail) (chunk0011Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0010Chars00 ++ chunk0011Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0011Push00 (chunk0010Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 594) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 592) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0010Chars00 ++ (chunk0011Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 594) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 594) (SourceJson.white (chunk0010Chars00 ++ (chunk0011Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 594) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 593) (SourceJson.white (chunk0011Chars00 ++ (tail))) (chunk0010Push00 (acc)) := array_chunk0010 fuel (chunk0011Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 592) (SourceJson.white tail) (blockPush acc) := array_chunk0011 fuel (tail) (chunk0010Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 243137).take 3580 = blockChars := by rfl

theorem block_original_split : sourceRest 243137 = blockChars ++ sourceRest 246717 := by
  calc
    sourceRest 243137 = (sourceRest 243137).take 3580 ++ (sourceRest 243137).drop 3580 :=
      (List.take_append_drop 3580 (sourceRest 243137)).symm
    _ = blockChars ++ (sourceRest 243137).drop 3580 :=
      congrArg (fun part => part ++ (sourceRest 243137).drop 3580) block_original_prefix
    _ = blockChars ++ sourceRest 246717 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 243137 3580)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 594) (SourceJson.white (sourceRest 243137)) acc =
      SourceJson.array (fuel + 592) (SourceJson.white (sourceRest 246717)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 594) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 246717) acc)

#print axioms object_fragment0243143_field_000
#print axioms object_fragment0243143_field_001
#print axioms object_fragment0243143_field_002
#print axioms object_fragment0243143_field_003
#print axioms object_fragment0243143_field_004
#print axioms object_fragment0243143_field_005
#print axioms object_fragment0243143_field_006
#print axioms object_fragment0243143_field_007
#print axioms object_fragment0243143_field_008
#print axioms object_fragment0243143_field_009
#print axioms value_fragment0243143
#print axioms object_fragment0245048_field_000
#print axioms object_fragment0245048_field_001
#print axioms object_fragment0245048_field_002
#print axioms object_fragment0245048_field_003
#print axioms object_fragment0245048_field_004
#print axioms object_fragment0245048_field_005
#print axioms object_fragment0245048_field_006
#print axioms object_fragment0245048_field_007
#print axioms object_fragment0245048_field_008
#print axioms object_fragment0245048_field_009
#print axioms value_fragment0245048
#print axioms array_chunk0010_head
#print axioms array_chunk0010
#print axioms array_chunk0011_head
#print axioms array_chunk0011
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock005

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
