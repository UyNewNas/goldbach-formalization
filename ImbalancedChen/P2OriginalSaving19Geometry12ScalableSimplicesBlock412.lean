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

namespace SimplicesBlock412

noncomputable def fragment7962645Acc00000 : List (String × SourceJson) := []

noncomputable def fragment7962645Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment7962645Field000Value00 : SourceJson := .number (String.ofList ['3', '2', '9', '6'])
noncomputable def fragment7962645Acc00100 : List (String × SourceJson) := (fragment7962645Field000Key00, fragment7962645Field000Value00) :: fragment7962645Acc00000
noncomputable def fragment7962645Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '2', '9', '6', ',']

theorem object_fragment7962645_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 371) (SourceJson.white (fragment7962645Field000Chars00 ++ tail)) fragment7962645Acc00000 =
      SourceJson.object (fuel + 370) (SourceJson.white tail) fragment7962645Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_000"
  err.flush

noncomputable def fragment7962645Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment7962645Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '3']), .number (String.ofList ['1', '1', '4']), .number (String.ofList ['1', '1', '3']), .number (String.ofList ['9', '9']), .number (String.ofList ['6', '2']), .number (String.ofList ['5', '7']), .number (String.ofList ['5', '2']), .number (String.ofList ['4', '0'])]
noncomputable def fragment7962645Acc00200 : List (String × SourceJson) := (fragment7962645Field001Key00, fragment7962645Field001Value00) :: fragment7962645Acc00100
noncomputable def fragment7962645Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7962645_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 370) (SourceJson.white (fragment7962645Field001Chars00 ++ tail)) fragment7962645Acc00100 =
      SourceJson.object (fuel + 369) (SourceJson.white tail) fragment7962645Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_001"
  err.flush

noncomputable def fragment7962645Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment7962645Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '8', '9', '9', '7', '8', '1', '6', '9', '4', '2', '3', '6', '9', '8', '8', '7', '7', '1', '0', '0', '5', '2', '5', '5', '9', '8', '0', '7', '7', '2', '5', '9', '3', '8', '2', '8', '9', '/', '3', '9', '7', '4', '4', '3', '8', '0', '7', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7962645Acc00300 : List (String × SourceJson) := (fragment7962645Field002Key00, fragment7962645Field002Value00) :: fragment7962645Acc00200
noncomputable def fragment7962645Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '8', '9', '9', '7', '8', '1', '6', '9', '4', '2', '3', '6', '9', '8', '8', '7', '7', '1', '0', '0', '5', '2', '5', '5', '9', '8', '0', '7', '7', '2', '5', '9', '3', '8', '2', '8', '9', '/', '3', '9', '7', '4', '4', '3', '8', '0', '7', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7962645_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment7962645Field002Chars00 ++ tail)) fragment7962645Acc00200 =
      SourceJson.object (fuel + 368) (SourceJson.white tail) fragment7962645Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_002"
  err.flush

noncomputable def fragment7962645Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment7962645Field003Value00 : SourceJson := .str (String.ofList ['1', '5', '1', '9', '2', '4', '1', '/', '1', '3', '2', '9', '7', '5', '0', '0', '0', '0'])
noncomputable def fragment7962645Acc00400 : List (String × SourceJson) := (fragment7962645Field003Key00, fragment7962645Field003Value00) :: fragment7962645Acc00300
noncomputable def fragment7962645Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '5', '1', '9', '2', '4', '1', '/', '1', '3', '2', '9', '7', '5', '0', '0', '0', '0', '"', ',']

theorem object_fragment7962645_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment7962645Field003Chars00 ++ tail)) fragment7962645Acc00300 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment7962645Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_003"
  err.flush

noncomputable def fragment7962645Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment7962645Field004Value00 : SourceJson := .arr [.str (String.ofList ['6', '2', '1', '0', '8', '7', '/', '1', '1', '8', '7', '5', '0', '0', '0']), .str (String.ofList ['6', '2', '1', '0', '8', '7', '/', '1', '1', '8', '7', '5', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '0', '1', '4', '3', '/', '4', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '7', '4', '8', '9', '/', '1', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '7', '4', '8', '9', '/', '1', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '/', '3', '3', '6']), .str (String.ofList ['1', '1', '/', '3', '3', '6'])]
noncomputable def fragment7962645Acc00500 : List (String × SourceJson) := (fragment7962645Field004Key00, fragment7962645Field004Value00) :: fragment7962645Acc00400
noncomputable def fragment7962645Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '1', '0', '8', '7', '/', '1', '1', '8', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '1', '0', '8', '7', '/', '1', '1', '8', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '0', '1', '4', '3', '/', '4', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '7', '4', '8', '9', '/', '1', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '7', '4', '8', '9', '/', '1', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7962645_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment7962645Field004Chars00 ++ tail)) fragment7962645Acc00400 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment7962645Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_004"
  err.flush

noncomputable def fragment7962645Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment7962645Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '3', '7', '7', '3', '3', '8', '4', '1', '8', '4', '8', '7', '0', '8', '1', '2', '7', '0', '7', '/', '9', '1', '3', '5', '3', '9', '2', '8', '7', '4', '7', '0', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '8', '2', '4', '8', '3', '4', '3', '4', '0', '4', '0', '7', '0', '0', '0', '1', '7', '/', '9', '1', '3', '5', '3', '9', '2', '8', '7', '4', '7', '0', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '2', '2', '1', '7', '3', '8', '4', '1', '8', '3', '6', '7', '9', '8', '7', '9', '1', '/', '1', '3', '5', '3', '3', '9', '1', '5', '3', '6', '9', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '9', '5', '4', '9', '6', '2', '6', '6', '0', '2', '8', '2', '0', '5', '5', '2', '8', '9', '/', '1', '2', '1', '8', '0', '5', '2', '3', '8', '3', '2', '9', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '3', '4', '4', '4', '6', '0', '3', '4', '5', '6', '8', '9', '4', '7', '4', '6', '2', '9', '/', '1', '2', '1', '8', '0', '5', '2', '3', '8', '3', '2', '9', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '6', '2', '9', '4', '5', '8', '8', '0', '7', '0', '7', '9', '7', '5', '1', '3', '1', '/', '1', '3', '5', '3', '3', '9', '1', '5', '3', '6', '9', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '8', '4', '0', '2', '3', '6', '0', '6', '1', '7', '3', '7', '4', '2', '5', '4', '5', '1', '/', '1', '2', '1', '8', '0', '5', '2', '3', '8', '3', '2', '9', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '0', '2', '8', '2', '5', '7', '2', '2', '1', '2', '6', '6', '9', '4', '0', '3', '7', '/', '1', '5', '2', '2', '5', '6', '5', '4', '7', '9', '1', '1', '8', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '2', '9', '2', '6', '0', '9', '6', '7', '8', '7', '4', '4', '2', '5', '5', '3', '3', '/', '1', '8', '2', '7', '0', '7', '8', '5', '7', '4', '9', '4', '1', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '0', '4', '6', '3', '6', '0', '1', '8', '8', '0', '2', '0', '8', '9', '1', '9', '/', '1', '2', '1', '8', '0', '5', '2', '3', '8', '3', '2', '9', '4', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7962645Acc00600 : List (String × SourceJson) := (fragment7962645Field005Key00, fragment7962645Field005Value00) :: fragment7962645Acc00500
noncomputable def fragment7962645Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '7', '3', '3', '8', '4', '1', '8', '4', '8', '7', '0', '8', '1', '2', '7', '0', '7', '/', '9', '1', '3', '5', '3', '9', '2', '8', '7', '4', '7', '0', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '8', '2', '4', '8', '3', '4', '3', '4', '0', '4', '0', '7', '0', '0', '0', '1', '7', '/', '9', '1', '3', '5', '3', '9', '2', '8', '7', '4', '7', '0', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '2', '2', '1', '7', '3', '8', '4', '1', '8', '3', '6', '7', '9', '8', '7', '9', '1', '/', '1', '3', '5', '3', '3', '9', '1', '5', '3', '6', '9', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '9', '5', '4', '9', '6', '2', '6', '6', '0', '2', '8', '2', '0', '5', '5', '2', '8', '9', '/', '1', '2', '1', '8', '0', '5', '2', '3', '8', '3', '2', '9', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '3', '4', '4', '4', '6', '0', '3', '4', '5', '6', '8', '9', '4', '7', '4', '6', '2', '9', '/', '1', '2', '1', '8', '0', '5', '2', '3', '8', '3', '2', '9', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '6', '2', '9', '4', '5', '8', '8', '0', '7', '0', '7', '9', '7', '5', '1', '3', '1', '/', '1', '3', '5', '3', '3', '9', '1', '5', '3', '6', '9', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '8', '4', '0', '2', '3', '6', '0', '6', '1', '7', '3', '7', '4', '2', '5', '4', '5', '1', '/', '1', '2', '1', '8', '0', '5', '2', '3', '8', '3', '2', '9', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '0', '2', '8', '2', '5', '7', '2', '2', '1', '2', '6', '6', '9', '4', '0', '3', '7', '/', '1', '5', '2', '2', '5', '6', '5', '4', '7', '9', '1', '1', '8', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '2', '9', '2', '6', '0', '9', '6', '7', '8', '7', '4', '4', '2', '5', '5', '3', '3', '/', '1', '8', '2', '7', '0', '7', '8', '5', '7', '4', '9', '4', '1', '9', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '0', '0', '4', '6', '3', '6', '0', '1', '8', '8', '0', '2', '0', '8', '9', '1', '9', '/', '1', '2', '1', '8', '0', '5', '2', '3', '8', '3', '2', '9', '4', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7962645_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment7962645Field005Chars00 ++ tail)) fragment7962645Acc00500 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment7962645Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_005"
  err.flush

noncomputable def fragment7962645Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7962645Field006Value00 : SourceJson := .str (String.ofList ['7', '0', '7', '4', '8', '3', '3', '6', '8', '3', '9', '7', '7', '2', '8', '1', '2', '3', '7', '7', '3', '9', '7', '3', '7', '3', '9', '2', '6', '3', '6', '0', '6', '1', '9', '7', '5', '8', '5', '7', '4', '8', '3', '2', '2', '8', '9', '/', '7', '4', '8', '7', '6', '3', '3', '7', '1', '9', '1', '9', '5', '7', '1', '4', '0', '9', '7', '1', '5', '8', '6', '6', '4', '3', '3', '6', '1', '5', '9', '2', '1', '5', '6', '5', '8', '4', '0', '3', '0', '7', '9', '9', '0', '4', '8', '7', '8', '7', '9', '5', '6', '4', '5', '3', '1', '2', '5', '0', '0'])
noncomputable def fragment7962645Acc00700 : List (String × SourceJson) := (fragment7962645Field006Key00, fragment7962645Field006Value00) :: fragment7962645Acc00600
noncomputable def fragment7962645Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '0', '7', '4', '8', '3', '3', '6', '8', '3', '9', '7', '7', '2', '8', '1', '2', '3', '7', '7', '3', '9', '7', '3', '7', '3', '9', '2', '6', '3', '6', '0', '6', '1', '9', '7', '5', '8', '5', '7', '4', '8', '3', '2', '2', '8', '9', '/', '7', '4', '8', '7', '6', '3', '3', '7', '1', '9', '1', '9', '5', '7', '1', '4', '0', '9', '7', '1', '5', '8', '6', '6', '4', '3', '3', '6', '1', '5', '9', '2', '1', '5', '6', '5', '8', '4', '0', '3', '0', '7', '9', '9', '0', '4', '8', '7', '8', '7', '9', '5', '6', '4', '5', '3', '1', '2', '5', '0', '0', '"', ',']

theorem object_fragment7962645_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment7962645Field006Chars00 ++ tail)) fragment7962645Acc00600 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment7962645Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_006"
  err.flush

noncomputable def fragment7962645Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7962645Field007Value00 : SourceJson := .str (String.ofList ['6', '5', '0', '1', '1', '1', '9', '2', '3', '3', '8', '0', '5', '3', '7', '9', '7', '8', '8', '8', '2', '5', '9', '7', '0', '7', '7', '1', '2', '5', '3', '8', '5', '5', '5', '0', '6', '7', '1', '6', '8', '5', '9', '3', '9', '6', '4', '0', '3', '5', '2', '4', '2', '5', '7', '8', '2', '6', '7', '3', '7', '1', '4', '2', '2', '0', '2', '0', '7', '6', '1', '7', '3', '7', '4', '2', '5', '8', '7', '2', '4', '4', '9', '4', '2', '5', '4', '8', '7', '8', '8', '7', '7', '8', '8', '3', '7', '2', '6', '2', '2', '3', '5', '7', '9', '2', '0', '2', '5', '5', '7', '5', '5', '7', '3', '4', '1', '1', '9', '9', '6', '4', '3', '3', '5', '1', '4', '0', '9', '8', '7', '7', '8', '9', '1', '6', '1', '9', '7', '2', '5', '9', '4', '4', '7', '1', '1', '3', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '1', '9', '9', '6', '4', '0', '3', '3', '0', '7', '4', '6', '3', '6', '5', '7', '5', '6', '6', '8', '4', '5', '5', '6', '8', '1', '0', '5', '7', '0', '0', '6', '4', '1', '3', '0', '4', '4', '8', '6', '5', '8', '1', '7', '8', '2', '9', '4', '6', '8', '3', '2', '7', '3', '1', '1', '6', '3', '3', '4', '2', '0', '2', '8', '4', '1', '8', '9', '7', '0', '0', '9', '2', '5', '7', '5', '4', '2', '0', '0', '9', '6', '0', '2', '8', '3', '7', '0', '1', '7', '8', '9', '1', '4', '4', '1', '3', '5', '9', '5', '2', '6', '7', '5', '8', '6', '0', '8', '4', '2', '1', '5', '5', '5', '4', '6', '8', '0', '1', '0', '8', '9', '0', '0', '6', '3', '7', '6', '9', '2', '2', '3', '3', '3', '0', '8', '3', '5', '1', '4', '4', '9', '6', '7', '4', '0', '6', '4', '8', '6', '5', '8', '6', '8', '5', '9', '7', '8', '2', '9', '5', '6', '9', '7', '7', '2', '3', '1', '1', '1', '1', '7', '2', '7', '8', '5', '5', '1', '2', '7', '9', '6', '4', '4', '7'])
noncomputable def fragment7962645Acc00800 : List (String × SourceJson) := (fragment7962645Field007Key00, fragment7962645Field007Value00) :: fragment7962645Acc00700
noncomputable def fragment7962645Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '5', '0', '1', '1', '1', '9', '2', '3', '3', '8', '0', '5', '3', '7', '9', '7', '8', '8', '8', '2', '5', '9', '7', '0', '7', '7', '1', '2', '5', '3', '8', '5', '5', '5', '0', '6', '7', '1', '6', '8', '5', '9', '3', '9', '6', '4', '0', '3', '5', '2', '4', '2', '5', '7', '8', '2', '6', '7', '3', '7', '1', '4', '2', '2', '0', '2', '0', '7', '6', '1', '7', '3', '7', '4', '2', '5', '8', '7', '2', '4', '4', '9', '4', '2', '5', '4', '8', '7', '8', '8', '7', '7', '8', '8', '3', '7', '2', '6', '2', '2', '3', '5', '7', '9', '2', '0', '2', '5', '5', '7', '5', '5', '7', '3', '4', '1', '1', '9', '9', '6', '4', '3', '3', '5', '1', '4', '0', '9', '8', '7', '7', '8', '9', '1', '6', '1', '9', '7', '2', '5', '9', '4', '4', '7', '1', '1', '3', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '1', '9', '9', '6', '4', '0', '3', '3', '0', '7', '4', '6', '3', '6', '5', '7', '5', '6', '6', '8', '4', '5', '5', '6', '8', '1', '0', '5', '7', '0', '0', '6', '4', '1', '3', '0', '4', '4', '8', '6', '5', '8', '1', '7', '8', '2', '9', '4', '6', '8', '3', '2', '7', '3', '1', '1', '6', '3', '3', '4', '2', '0', '2', '8', '4', '1', '8', '9', '7', '0', '0', '9', '2', '5', '7', '5', '4', '2', '0', '0', '9', '6', '0', '2', '8', '3', '7', '0', '1', '7', '8', '9', '1', '4', '4', '1', '3', '5', '9', '5', '2', '6', '7', '5', '8', '6', '0', '8', '4', '2', '1', '5', '5', '5', '4', '6', '8', '0', '1', '0', '8', '9', '0', '0', '6', '3', '7', '6', '9', '2', '2', '3', '3', '3', '0', '8', '3', '5', '1', '4', '4', '9', '6', '7', '4', '0', '6', '4', '8', '6', '5', '8', '6', '8', '5', '9', '7', '8', '2', '9', '5', '6', '9', '7', '7', '2', '3', '1', '1', '1', '1', '7', '2', '7', '8', '5', '5', '1', '2', '7', '9', '6', '4', '4', '7', '"', ',']

theorem object_fragment7962645_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment7962645Field007Chars00 ++ tail)) fragment7962645Acc00700 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment7962645Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_007"
  err.flush

noncomputable def fragment7962645Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7962645Field008Value00 : SourceJson := .str (String.ofList ['7', '4', '8', '6', '0', '2', '4', '2', '0', '8', '6', '7', '0', '1', '9'])
noncomputable def fragment7962645Acc00900 : List (String × SourceJson) := (fragment7962645Field008Key00, fragment7962645Field008Value00) :: fragment7962645Acc00800
noncomputable def fragment7962645Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '4', '8', '6', '0', '2', '4', '2', '0', '8', '6', '7', '0', '1', '9', '"', ',']

theorem object_fragment7962645_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment7962645Field008Chars00 ++ tail)) fragment7962645Acc00800 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment7962645Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_008"
  err.flush

noncomputable def fragment7962645Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7962645Field009Value00 : SourceJson := .str (String.ofList ['4', '2', '2', '2', '0', '2', '3', '9', '0', '5', '7', '5', '7', '4', '7', '8'])
noncomputable def fragment7962645Acc01000 : List (String × SourceJson) := (fragment7962645Field009Key00, fragment7962645Field009Value00) :: fragment7962645Acc00900
noncomputable def fragment7962645Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '2', '2', '0', '2', '3', '9', '0', '5', '7', '5', '7', '4', '7', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment7962645_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment7962645Field009Chars00 ++ tail)) fragment7962645Acc00900 =
      .ok (.obj (fragment7962645Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7962645_object_field_009"
  err.flush

noncomputable def fragment7962645Chars : List Char := '{' :: (fragment7962645Field000Chars00 ++ fragment7962645Field001Chars00 ++ fragment7962645Field002Chars00 ++ fragment7962645Field003Chars00 ++ fragment7962645Field004Chars00 ++ fragment7962645Field005Chars00 ++ fragment7962645Field006Chars00 ++ fragment7962645Field007Chars00 ++ fragment7962645Field008Chars00 ++ fragment7962645Field009Chars00)
noncomputable def fragment7962645Value : SourceJson := .obj (fragment7962645Acc01000.reverse)

theorem value_fragment7962645 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 372) (fragment7962645Chars ++ tail) =
      .ok (fragment7962645Value, tail) := by
  have hinput : fragment7962645Chars ++ tail = '{' :: (fragment7962645Field000Chars00 ++ (fragment7962645Field001Chars00 ++ (fragment7962645Field002Chars00 ++ (fragment7962645Field003Chars00 ++ (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment7962645Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 372) (fragment7962645Chars ++ tail) =
        SourceJson.value (fuel + 372) ('{' :: (fragment7962645Field000Chars00 ++ (fragment7962645Field001Chars00 ++ (fragment7962645Field002Chars00 ++ (fragment7962645Field003Chars00 ++ (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 372)) hinput
    _ = SourceJson.object (fuel + 371) (SourceJson.white (fragment7962645Field000Chars00 ++ (fragment7962645Field001Chars00 ++ (fragment7962645Field002Chars00 ++ (fragment7962645Field003Chars00 ++ (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))))))))))) fragment7962645Acc00000 := by rfl
    _ = SourceJson.object (fuel + 370) (SourceJson.white (fragment7962645Field001Chars00 ++ (fragment7962645Field002Chars00 ++ (fragment7962645Field003Chars00 ++ (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail))))))))))) fragment7962645Acc00100 := object_fragment7962645_field_000 fuel (fragment7962645Field001Chars00 ++ (fragment7962645Field002Chars00 ++ (fragment7962645Field003Chars00 ++ (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment7962645Field002Chars00 ++ (fragment7962645Field003Chars00 ++ (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))))))))) fragment7962645Acc00200 := object_fragment7962645_field_001 fuel (fragment7962645Field002Chars00 ++ (fragment7962645Field003Chars00 ++ (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment7962645Field003Chars00 ++ (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail))))))))) fragment7962645Acc00300 := object_fragment7962645_field_002 fuel (fragment7962645Field003Chars00 ++ (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))))))) fragment7962645Acc00400 := object_fragment7962645_field_003 fuel (fragment7962645Field004Chars00 ++ (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail))))))) fragment7962645Acc00500 := object_fragment7962645_field_004 fuel (fragment7962645Field005Chars00 ++ (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))))) fragment7962645Acc00600 := object_fragment7962645_field_005 fuel (fragment7962645Field006Chars00 ++ (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail))))) fragment7962645Acc00700 := object_fragment7962645_field_006 fuel (fragment7962645Field007Chars00 ++ (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))) fragment7962645Acc00800 := object_fragment7962645_field_007 fuel (fragment7962645Field008Chars00 ++ (fragment7962645Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment7962645Field009Chars00 ++ (tail))) fragment7962645Acc00900 := object_fragment7962645_field_008 fuel (fragment7962645Field009Chars00 ++ (tail))
    _ = .ok (fragment7962645Value, tail) := object_fragment7962645_field_009 fuel (tail)

noncomputable def fragment7964513Acc00000 : List (String × SourceJson) := []

noncomputable def fragment7964513Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment7964513Field000Value00 : SourceJson := .number (String.ofList ['3', '2', '9', '7'])
noncomputable def fragment7964513Acc00100 : List (String × SourceJson) := (fragment7964513Field000Key00, fragment7964513Field000Value00) :: fragment7964513Acc00000
noncomputable def fragment7964513Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '2', '9', '7', ',']

theorem object_fragment7964513_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment7964513Field000Chars00 ++ tail)) fragment7964513Acc00000 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment7964513Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_000"
  err.flush

noncomputable def fragment7964513Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment7964513Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '3']), .number (String.ofList ['1', '1', '4']), .number (String.ofList ['1', '1', '3']), .number (String.ofList ['9', '9']), .number (String.ofList ['6', '2']), .number (String.ofList ['6', '0']), .number (String.ofList ['4', '9']), .number (String.ofList ['4', '0'])]
noncomputable def fragment7964513Acc00200 : List (String × SourceJson) := (fragment7964513Field001Key00, fragment7964513Field001Value00) :: fragment7964513Acc00100
noncomputable def fragment7964513Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7964513_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment7964513Field001Chars00 ++ tail)) fragment7964513Acc00100 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment7964513Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_001"
  err.flush

noncomputable def fragment7964513Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment7964513Field002Value00 : SourceJson := .str (String.ofList ['5', '2', '0', '7', '3', '6', '6', '8', '6', '4', '6', '8', '9', '0', '8', '0', '9', '8', '4', '6', '5', '5', '1', '1', '5', '2', '9', '8', '2', '7', '9', '9', '5', '5', '6', '3', '2', '7', '1', '/', '3', '2', '8', '9', '6', '8', '1', '2', '0', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7964513Acc00300 : List (String × SourceJson) := (fragment7964513Field002Key00, fragment7964513Field002Value00) :: fragment7964513Acc00200
noncomputable def fragment7964513Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '2', '0', '7', '3', '6', '6', '8', '6', '4', '6', '8', '9', '0', '8', '0', '9', '8', '4', '6', '5', '5', '1', '1', '5', '2', '9', '8', '2', '7', '9', '9', '5', '5', '6', '3', '2', '7', '1', '/', '3', '2', '8', '9', '6', '8', '1', '2', '0', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7964513_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment7964513Field002Chars00 ++ tail)) fragment7964513Acc00200 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment7964513Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_002"
  err.flush

noncomputable def fragment7964513Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment7964513Field003Value00 : SourceJson := .str (String.ofList ['7', '8', '1', '1', '/', '1', '3', '5', '0', '0', '0', '0', '0'])
noncomputable def fragment7964513Acc00400 : List (String × SourceJson) := (fragment7964513Field003Key00, fragment7964513Field003Value00) :: fragment7964513Acc00300
noncomputable def fragment7964513Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '7', '8', '1', '1', '/', '1', '3', '5', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7964513_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment7964513Field003Chars00 ++ tail)) fragment7964513Acc00300 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment7964513Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_003"
  err.flush

noncomputable def fragment7964513Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment7964513Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '2', '5', '4', '/', '1', '7', '1', '8', '7', '5']), .str (String.ofList ['1', '0', '2', '5', '4', '/', '1', '7', '1', '8', '7', '5']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '0', '1', '4', '3', '/', '4', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0']), .str (String.ofList ['2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0']), .str (String.ofList ['1', '1', '/', '3', '3', '6']), .str (String.ofList ['1', '1', '/', '3', '3', '6'])]
noncomputable def fragment7964513Acc00500 : List (String × SourceJson) := (fragment7964513Field004Key00, fragment7964513Field004Value00) :: fragment7964513Acc00400
noncomputable def fragment7964513Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '5', '4', '/', '1', '7', '1', '8', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '5', '4', '/', '1', '7', '1', '8', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '0', '1', '4', '3', '/', '4', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7964513_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment7964513Field004Chars00 ++ tail)) fragment7964513Acc00400 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment7964513Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_004"
  err.flush

noncomputable def fragment7964513Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment7964513Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '3', '7', '6', '9', '4', '3', '2', '1', '9', '6', '9', '/', '8', '3', '9', '3', '9', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '3', '2', '1', '8', '1', '7', '7', '0', '5', '7', '/', '4', '1', '9', '6', '9', '8', '1', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '9', '1', '8', '8', '6', '0', '1', '9', '1', '3', '/', '4', '9', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '7', '0', '3', '1', '4', '8', '3', '5', '7', '6', '7', '/', '4', '4', '7', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '1', '7', '0', '9', '4', '3', '5', '7', '3', '8', '7', '/', '4', '4', '7', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '2', '2', '0', '5', '7', '5', '0', '2', '3', '/', '4', '5', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '7', '7', '9', '8', '2', '4', '8', '2', '2', '3', '/', '4', '4', '7', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '6', '0', '9', '4', '0', '3', '0', '0', '2', '9', '/', '2', '2', '3', '8', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '4', '4', '7', '0', '7', '2', '3', '8', '3', '/', '6', '7', '1', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '5', '7', '2', '0', '4', '5', '9', '9', '3', '/', '4', '4', '7', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7964513Acc00600 : List (String × SourceJson) := (fragment7964513Field005Key00, fragment7964513Field005Value00) :: fragment7964513Acc00500
noncomputable def fragment7964513Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '6', '9', '4', '3', '2', '1', '9', '6', '9', '/', '8', '3', '9', '3', '9', '6', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '2', '1', '8', '1', '7', '7', '0', '5', '7', '/', '4', '1', '9', '6', '9', '8', '1', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '9', '1', '8', '8', '6', '0', '1', '9', '1', '3', '/', '4', '9', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '7', '0', '3', '1', '4', '8', '3', '5', '7', '6', '7', '/', '4', '4', '7', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '1', '7', '0', '9', '4', '3', '5', '7', '3', '8', '7', '/', '4', '4', '7', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '2', '2', '0', '5', '7', '5', '0', '2', '3', '/', '4', '5', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '7', '7', '9', '8', '2', '4', '8', '2', '2', '3', '/', '4', '4', '7', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '6', '0', '9', '4', '0', '3', '0', '0', '2', '9', '/', '2', '2', '3', '8', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '1', '4', '4', '7', '0', '7', '2', '3', '8', '3', '/', '6', '7', '1', '5', '1', '7', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '5', '7', '2', '0', '4', '5', '9', '9', '3', '/', '4', '4', '7', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7964513_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment7964513Field005Chars00 ++ tail)) fragment7964513Acc00500 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment7964513Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_005"
  err.flush

noncomputable def fragment7964513Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7964513Field006Value00 : SourceJson := .str (String.ofList ['1', '4', '6', '8', '3', '5', '8', '2', '0', '7', '1', '4', '1', '1', '1', '9', '4', '5', '7', '7', '1', '8', '1', '9', '3', '9', '1', '1', '9', '7', '4', '6', '1', '6', '8', '7', '7', '4', '4', '0', '2', '3', '0', '9', '4', '1', '/', '8', '1', '5', '9', '5', '0', '4', '1', '6', '5', '0', '6', '3', '3', '7', '8', '2', '2', '9', '3', '4', '0', '3', '0', '6', '0', '1', '0', '9', '1', '9', '6', '1', '6', '3', '4', '8', '8', '4', '4', '3', '2', '7', '5', '3', '3', '6', '0', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7964513Acc00700 : List (String × SourceJson) := (fragment7964513Field006Key00, fragment7964513Field006Value00) :: fragment7964513Acc00600
noncomputable def fragment7964513Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '6', '8', '3', '5', '8', '2', '0', '7', '1', '4', '1', '1', '1', '9', '4', '5', '7', '7', '1', '8', '1', '9', '3', '9', '1', '1', '9', '7', '4', '6', '1', '6', '8', '7', '7', '4', '4', '0', '2', '3', '0', '9', '4', '1', '/', '8', '1', '5', '9', '5', '0', '4', '1', '6', '5', '0', '6', '3', '3', '7', '8', '2', '2', '9', '3', '4', '0', '3', '0', '6', '0', '1', '0', '9', '1', '9', '6', '1', '6', '3', '4', '8', '8', '4', '4', '3', '2', '7', '5', '3', '3', '6', '0', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7964513_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment7964513Field006Chars00 ++ tail)) fragment7964513Acc00600 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment7964513Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_006"
  err.flush

noncomputable def fragment7964513Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7964513Field007Value00 : SourceJson := .str (String.ofList ['1', '2', '3', '5', '1', '7', '4', '9', '1', '0', '0', '3', '7', '5', '6', '8', '0', '8', '2', '5', '8', '1', '9', '0', '2', '7', '3', '6', '3', '7', '8', '6', '5', '7', '3', '4', '8', '1', '9', '4', '8', '2', '7', '3', '3', '6', '7', '8', '0', '8', '3', '4', '6', '8', '8', '5', '8', '4', '6', '8', '8', '2', '2', '6', '9', '0', '9', '8', '8', '7', '5', '1', '7', '4', '5', '6', '3', '4', '2', '6', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '9', '4', '1', '6', '2', '4', '1', '9', '8', '5', '9', '4', '7', '1', '6', '2', '1', '4', '8', '1', '3', '3', '9', '3', '5', '6', '4', '5', '2', '3', '2', '4', '3', '0', '1', '6', '5', '5', '5', '1', '5', '5', '7', '8', '1', '5', '1', '9', '0', '6', '4', '8', '8', '6', '4', '9', '9', '6', '8', '6', '0', '8', '2', '9', '4', '6', '2', '3', '8', '0', '1', '0', '2', '7', '9', '5', '8', '8', '4', '1', '0', '9', '1', '9', '8', '1', '5', '9', '5', '5', '9', '0', '9', '7', '6', '9', '7', '1', '7', '8', '3', '1', '3', '7', '7', '5', '4', '8', '8', '5', '7', '8', '1'])
noncomputable def fragment7964513Acc00800 : List (String × SourceJson) := (fragment7964513Field007Key00, fragment7964513Field007Value00) :: fragment7964513Acc00700
noncomputable def fragment7964513Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '3', '5', '1', '7', '4', '9', '1', '0', '0', '3', '7', '5', '6', '8', '0', '8', '2', '5', '8', '1', '9', '0', '2', '7', '3', '6', '3', '7', '8', '6', '5', '7', '3', '4', '8', '1', '9', '4', '8', '2', '7', '3', '3', '6', '7', '8', '0', '8', '3', '4', '6', '8', '8', '5', '8', '4', '6', '8', '8', '2', '2', '6', '9', '0', '9', '8', '8', '7', '5', '1', '7', '4', '5', '6', '3', '4', '2', '6', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '9', '4', '1', '6', '2', '4', '1', '9', '8', '5', '9', '4', '7', '1', '6', '2', '1', '4', '8', '1', '3', '3', '9', '3', '5', '6', '4', '5', '2', '3', '2', '4', '3', '0', '1', '6', '5', '5', '5', '1', '5', '5', '7', '8', '1', '5', '1', '9', '0', '6', '4', '8', '8', '6', '4', '9', '9', '6', '8', '6', '0', '8', '2', '9', '4', '6', '2', '3', '8', '0', '1', '0', '2', '7', '9', '5', '8', '8', '4', '1', '0', '9', '1', '9', '8', '1', '5', '9', '5', '5', '9', '0', '9', '7', '6', '9', '7', '1', '7', '8', '3', '1', '3', '7', '7', '5', '4', '8', '8', '5', '7', '8', '1', '"', ',']

theorem object_fragment7964513_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment7964513Field007Chars00 ++ tail)) fragment7964513Acc00700 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment7964513Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_007"
  err.flush

noncomputable def fragment7964513Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7964513Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '2', '5', '7', '6', '4', '6', '0', '9', '1', '1', '2', '4', '5', '5'])
noncomputable def fragment7964513Acc00900 : List (String × SourceJson) := (fragment7964513Field008Key00, fragment7964513Field008Value00) :: fragment7964513Acc00800
noncomputable def fragment7964513Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '2', '5', '7', '6', '4', '6', '0', '9', '1', '1', '2', '4', '5', '5', '"', ',']

theorem object_fragment7964513_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment7964513Field008Chars00 ++ tail)) fragment7964513Acc00800 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment7964513Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_008"
  err.flush

noncomputable def fragment7964513Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7964513Field009Value00 : SourceJson := .str (String.ofList ['9', '8', '4', '3', '5', '2', '6', '2', '2', '3', '7', '9', '6', '6', '3', '3'])
noncomputable def fragment7964513Acc01000 : List (String × SourceJson) := (fragment7964513Field009Key00, fragment7964513Field009Value00) :: fragment7964513Acc00900
noncomputable def fragment7964513Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '4', '3', '5', '2', '6', '2', '2', '3', '7', '9', '6', '6', '3', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment7964513_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment7964513Field009Chars00 ++ tail)) fragment7964513Acc00900 =
      .ok (.obj (fragment7964513Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7964513_object_field_009"
  err.flush

noncomputable def fragment7964513Chars : List Char := '{' :: (fragment7964513Field000Chars00 ++ fragment7964513Field001Chars00 ++ fragment7964513Field002Chars00 ++ fragment7964513Field003Chars00 ++ fragment7964513Field004Chars00 ++ fragment7964513Field005Chars00 ++ fragment7964513Field006Chars00 ++ fragment7964513Field007Chars00 ++ fragment7964513Field008Chars00 ++ fragment7964513Field009Chars00)
noncomputable def fragment7964513Value : SourceJson := .obj (fragment7964513Acc01000.reverse)

theorem value_fragment7964513 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 228) (fragment7964513Chars ++ tail) =
      .ok (fragment7964513Value, tail) := by
  have hinput : fragment7964513Chars ++ tail = '{' :: (fragment7964513Field000Chars00 ++ (fragment7964513Field001Chars00 ++ (fragment7964513Field002Chars00 ++ (fragment7964513Field003Chars00 ++ (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment7964513Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 228) (fragment7964513Chars ++ tail) =
        SourceJson.value (fuel + 228) ('{' :: (fragment7964513Field000Chars00 ++ (fragment7964513Field001Chars00 ++ (fragment7964513Field002Chars00 ++ (fragment7964513Field003Chars00 ++ (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 228)) hinput
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment7964513Field000Chars00 ++ (fragment7964513Field001Chars00 ++ (fragment7964513Field002Chars00 ++ (fragment7964513Field003Chars00 ++ (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))))))))))) fragment7964513Acc00000 := by rfl
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment7964513Field001Chars00 ++ (fragment7964513Field002Chars00 ++ (fragment7964513Field003Chars00 ++ (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail))))))))))) fragment7964513Acc00100 := object_fragment7964513_field_000 fuel (fragment7964513Field001Chars00 ++ (fragment7964513Field002Chars00 ++ (fragment7964513Field003Chars00 ++ (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment7964513Field002Chars00 ++ (fragment7964513Field003Chars00 ++ (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))))))))) fragment7964513Acc00200 := object_fragment7964513_field_001 fuel (fragment7964513Field002Chars00 ++ (fragment7964513Field003Chars00 ++ (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment7964513Field003Chars00 ++ (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail))))))))) fragment7964513Acc00300 := object_fragment7964513_field_002 fuel (fragment7964513Field003Chars00 ++ (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))))))) fragment7964513Acc00400 := object_fragment7964513_field_003 fuel (fragment7964513Field004Chars00 ++ (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail))))))) fragment7964513Acc00500 := object_fragment7964513_field_004 fuel (fragment7964513Field005Chars00 ++ (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))))) fragment7964513Acc00600 := object_fragment7964513_field_005 fuel (fragment7964513Field006Chars00 ++ (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail))))) fragment7964513Acc00700 := object_fragment7964513_field_006 fuel (fragment7964513Field007Chars00 ++ (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))) fragment7964513Acc00800 := object_fragment7964513_field_007 fuel (fragment7964513Field008Chars00 ++ (fragment7964513Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment7964513Field009Chars00 ++ (tail))) fragment7964513Acc00900 := object_fragment7964513_field_008 fuel (fragment7964513Field009Chars00 ++ (tail))
    _ = .ok (fragment7964513Value, tail) := object_fragment7964513_field_009 fuel (tail)

noncomputable def fragment7966065Acc00000 : List (String × SourceJson) := []

noncomputable def fragment7966065Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment7966065Field000Value00 : SourceJson := .number (String.ofList ['3', '2', '9', '8'])
noncomputable def fragment7966065Acc00100 : List (String × SourceJson) := (fragment7966065Field000Key00, fragment7966065Field000Value00) :: fragment7966065Acc00000
noncomputable def fragment7966065Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '2', '9', '8', ',']

theorem object_fragment7966065_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment7966065Field000Chars00 ++ tail)) fragment7966065Acc00000 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment7966065Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_000"
  err.flush

noncomputable def fragment7966065Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment7966065Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '3']), .number (String.ofList ['1', '1', '4']), .number (String.ofList ['1', '1', '3']), .number (String.ofList ['9', '9']), .number (String.ofList ['6', '2']), .number (String.ofList ['6', '0']), .number (String.ofList ['5', '2']), .number (String.ofList ['4', '0'])]
noncomputable def fragment7966065Acc00200 : List (String × SourceJson) := (fragment7966065Field001Key00, fragment7966065Field001Value00) :: fragment7966065Acc00100
noncomputable def fragment7966065Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7966065_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment7966065Field001Chars00 ++ tail)) fragment7966065Acc00100 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment7966065Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_001"
  err.flush

noncomputable def fragment7966065Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment7966065Field002Value00 : SourceJson := .str (String.ofList ['6', '0', '9', '5', '4', '0', '7', '7', '9', '3', '3', '6', '8', '1', '6', '4', '2', '1', '0', '0', '9', '2', '0', '9', '7', '5', '4', '6', '7', '8', '4', '0', '1', '6', '7', '7', '7', '6', '1', '1', '/', '7', '6', '2', '6', '0', '7', '9', '1', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7966065Acc00300 : List (String × SourceJson) := (fragment7966065Field002Key00, fragment7966065Field002Value00) :: fragment7966065Acc00200
noncomputable def fragment7966065Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '0', '9', '5', '4', '0', '7', '7', '9', '3', '3', '6', '8', '1', '6', '4', '2', '1', '0', '0', '9', '2', '0', '9', '7', '5', '4', '6', '7', '8', '4', '0', '1', '6', '7', '7', '7', '6', '1', '1', '/', '7', '6', '2', '6', '0', '7', '9', '1', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7966065_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment7966065Field002Chars00 ++ tail)) fragment7966065Acc00200 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment7966065Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_002"
  err.flush

noncomputable def fragment7966065Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment7966065Field003Value00 : SourceJson := .str (String.ofList ['7', '8', '1', '1', '/', '1', '3', '5', '0', '0', '0', '0', '0'])
noncomputable def fragment7966065Acc00400 : List (String × SourceJson) := (fragment7966065Field003Key00, fragment7966065Field003Value00) :: fragment7966065Acc00300
noncomputable def fragment7966065Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '7', '8', '1', '1', '/', '1', '3', '5', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7966065_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment7966065Field003Chars00 ++ tail)) fragment7966065Acc00300 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment7966065Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_003"
  err.flush

noncomputable def fragment7966065Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment7966065Field004Value00 : SourceJson := .arr [.str (String.ofList ['9', '3', '7', '4', '3', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '7', '4', '3', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '0', '1', '4', '3', '/', '4', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '7', '4', '8', '9', '/', '1', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '7', '4', '8', '9', '/', '1', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '/', '3', '3', '6']), .str (String.ofList ['1', '1', '/', '3', '3', '6'])]
noncomputable def fragment7966065Acc00500 : List (String × SourceJson) := (fragment7966065Field004Key00, fragment7966065Field004Value00) :: fragment7966065Acc00400
noncomputable def fragment7966065Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '7', '4', '3', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '7', '4', '3', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '0', '1', '4', '3', '/', '4', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '7', '4', '8', '9', '/', '1', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '7', '4', '8', '9', '/', '1', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7966065_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment7966065Field004Chars00 ++ tail)) fragment7966065Acc00400 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment7966065Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_004"
  err.flush

noncomputable def fragment7966065Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment7966065Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '9', '7', '3', '6', '3', '0', '5', '7', '9', '1', '/', '3', '0', '5', '2', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '9', '1', '5', '2', '2', '6', '5', '7', '1', '/', '3', '0', '5', '2', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '5', '7', '2', '1', '1', '0', '8', '8', '3', '/', '4', '5', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '7', '2', '4', '9', '9', '9', '0', '8', '7', '7', '/', '4', '0', '6', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '5', '1', '3', '9', '0', '3', '8', '2', '9', '7', '/', '4', '0', '6', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '1', '9', '9', '6', '5', '1', '4', '6', '3', '/', '4', '5', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '2', '6', '9', '0', '1', '0', '0', '5', '0', '3', '/', '4', '0', '6', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '6', '5', '8', '8', '7', '4', '0', '6', '1', '/', '5', '0', '8', '7', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '0', '6', '6', '4', '0', '6', '2', '1', '/', '6', '1', '0', '4', '7', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '4', '1', '4', '8', '3', '/', '6', '5', '1', '1', '6', '8', '0', '0', '0'])]
noncomputable def fragment7966065Acc00600 : List (String × SourceJson) := (fragment7966065Field005Key00, fragment7966065Field005Value00) :: fragment7966065Acc00500
noncomputable def fragment7966065Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '7', '3', '6', '3', '0', '5', '7', '9', '1', '/', '3', '0', '5', '2', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '9', '1', '5', '2', '2', '6', '5', '7', '1', '/', '3', '0', '5', '2', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '5', '7', '2', '1', '1', '0', '8', '8', '3', '/', '4', '5', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '7', '2', '4', '9', '9', '9', '0', '8', '7', '7', '/', '4', '0', '6', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '5', '1', '3', '9', '0', '3', '8', '2', '9', '7', '/', '4', '0', '6', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '1', '9', '9', '6', '5', '1', '4', '6', '3', '/', '4', '5', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '6', '9', '0', '1', '0', '0', '5', '0', '3', '/', '4', '0', '6', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '6', '5', '8', '8', '7', '4', '0', '6', '1', '/', '5', '0', '8', '7', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '0', '6', '6', '4', '0', '6', '2', '1', '/', '6', '1', '0', '4', '7', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '4', '1', '4', '8', '3', '/', '6', '5', '1', '1', '6', '8', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7966065_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment7966065Field005Chars00 ++ tail)) fragment7966065Acc00500 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment7966065Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_005"
  err.flush

noncomputable def fragment7966065Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7966065Field006Value00 : SourceJson := .str (String.ofList ['3', '3', '3', '2', '7', '8', '6', '1', '1', '9', '1', '7', '9', '9', '1', '1', '1', '4', '5', '1', '5', '2', '0', '5', '6', '1', '7', '5', '6', '5', '5', '0', '9', '6', '8', '5', '3', '4', '9', '4', '3', '6', '6', '4', '7', '/', '2', '9', '6', '6', '8', '0', '3', '1', '3', '6', '1', '6', '2', '8', '5', '2', '4', '3', '0', '4', '1', '3', '8', '5', '1', '5', '7', '6', '1', '0', '3', '9', '5', '3', '1', '6', '0', '3', '2', '0', '8', '3', '3', '9', '5', '7', '0', '2', '0', '2', '7', '3', '4', '3', '7', '5', '0', '0', '0'])
noncomputable def fragment7966065Acc00700 : List (String × SourceJson) := (fragment7966065Field006Key00, fragment7966065Field006Value00) :: fragment7966065Acc00600
noncomputable def fragment7966065Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '3', '2', '7', '8', '6', '1', '1', '9', '1', '7', '9', '9', '1', '1', '1', '4', '5', '1', '5', '2', '0', '5', '6', '1', '7', '5', '6', '5', '5', '0', '9', '6', '8', '5', '3', '4', '9', '4', '3', '6', '6', '4', '7', '/', '2', '9', '6', '6', '8', '0', '3', '1', '3', '6', '1', '6', '2', '8', '5', '2', '4', '3', '0', '4', '1', '3', '8', '5', '1', '5', '7', '6', '1', '0', '3', '9', '5', '3', '1', '6', '0', '3', '2', '0', '8', '3', '3', '9', '5', '7', '0', '2', '0', '2', '7', '3', '4', '3', '7', '5', '0', '0', '0', '"', ',']

theorem object_fragment7966065_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment7966065Field006Chars00 ++ tail)) fragment7966065Acc00600 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment7966065Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_006"
  err.flush

noncomputable def fragment7966065Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7966065Field007Value00 : SourceJson := .str (String.ofList ['3', '0', '0', '5', '0', '8', '5', '1', '3', '6', '7', '2', '4', '4', '9', '5', '1', '0', '3', '5', '4', '4', '9', '1', '0', '6', '6', '3', '8', '7', '0', '0', '3', '2', '6', '2', '0', '7', '3', '6', '0', '0', '2', '5', '3', '4', '0', '6', '1', '0', '1', '2', '4', '5', '3', '5', '1', '0', '0', '5', '3', '3', '7', '0', '7', '2', '9', '4', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '3', '4', '9', '9', '1', '5', '3', '7', '6', '5', '5', '5', '8', '4', '8', '6', '4', '6', '2', '1', '7', '3', '0', '5', '7', '8', '6', '5', '1', '5', '8', '4', '5', '9', '6', '1', '7', '1', '8', '5', '9', '0', '9', '9', '5', '1', '8', '1', '9', '7', '1', '9', '0', '6', '7', '9', '2', '3', '7', '6', '5', '0', '6', '1', '3', '2', '5', '3', '7', '2', '6', '5', '3', '3', '7', '3', '2', '7', '5', '1', '8', '6', '1', '1', '5', '0', '7', '2', '3', '9', '7', '8', '9', '8', '4', '7', '1', '7', '0', '7'])
noncomputable def fragment7966065Acc00800 : List (String × SourceJson) := (fragment7966065Field007Key00, fragment7966065Field007Value00) :: fragment7966065Acc00700
noncomputable def fragment7966065Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '0', '5', '0', '8', '5', '1', '3', '6', '7', '2', '4', '4', '9', '5', '1', '0', '3', '5', '4', '4', '9', '1', '0', '6', '6', '3', '8', '7', '0', '0', '3', '2', '6', '2', '0', '7', '3', '6', '0', '0', '2', '5', '3', '4', '0', '6', '1', '0', '1', '2', '4', '5', '3', '5', '1', '0', '0', '5', '3', '3', '7', '0', '7', '2', '9', '4', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '3', '4', '9', '9', '1', '5', '3', '7', '6', '5', '5', '5', '8', '4', '8', '6', '4', '6', '2', '1', '7', '3', '0', '5', '7', '8', '6', '5', '1', '5', '8', '4', '5', '9', '6', '1', '7', '1', '8', '5', '9', '0', '9', '9', '5', '1', '8', '1', '9', '7', '1', '9', '0', '6', '7', '9', '2', '3', '7', '6', '5', '0', '6', '1', '3', '2', '5', '3', '7', '2', '6', '5', '3', '3', '7', '3', '2', '7', '5', '1', '8', '6', '1', '1', '5', '0', '7', '2', '3', '9', '7', '8', '9', '8', '4', '7', '1', '7', '0', '7', '"', ',']

theorem object_fragment7966065_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment7966065Field007Chars00 ++ tail)) fragment7966065Acc00700 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment7966065Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_007"
  err.flush

noncomputable def fragment7966065Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7966065Field008Value00 : SourceJson := .str (String.ofList ['8', '9', '0', '0', '1', '6', '9', '9', '1', '8', '8', '2', '9', '9', '7'])
noncomputable def fragment7966065Acc00900 : List (String × SourceJson) := (fragment7966065Field008Key00, fragment7966065Field008Value00) :: fragment7966065Acc00800
noncomputable def fragment7966065Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '9', '0', '0', '1', '6', '9', '9', '1', '8', '8', '2', '9', '9', '7', '"', ',']

theorem object_fragment7966065_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment7966065Field008Chars00 ++ tail)) fragment7966065Acc00800 =
      SourceJson.object (fuel + 193) (SourceJson.white tail) fragment7966065Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_008"
  err.flush

noncomputable def fragment7966065Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7966065Field009Value00 : SourceJson := .str (String.ofList ['5', '1', '3', '6', '7', '3', '8', '0', '4', '2', '5', '0', '4', '2', '8', '1'])
noncomputable def fragment7966065Acc01000 : List (String × SourceJson) := (fragment7966065Field009Key00, fragment7966065Field009Value00) :: fragment7966065Acc00900
noncomputable def fragment7966065Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '1', '3', '6', '7', '3', '8', '0', '4', '2', '5', '0', '4', '2', '8', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment7966065_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment7966065Field009Chars00 ++ tail)) fragment7966065Acc00900 =
      .ok (.obj (fragment7966065Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7966065_object_field_009"
  err.flush

noncomputable def fragment7966065Chars : List Char := '{' :: (fragment7966065Field000Chars00 ++ fragment7966065Field001Chars00 ++ fragment7966065Field002Chars00 ++ fragment7966065Field003Chars00 ++ fragment7966065Field004Chars00 ++ fragment7966065Field005Chars00 ++ fragment7966065Field006Chars00 ++ fragment7966065Field007Chars00 ++ fragment7966065Field008Chars00 ++ fragment7966065Field009Chars00)
noncomputable def fragment7966065Value : SourceJson := .obj (fragment7966065Acc01000.reverse)

theorem value_fragment7966065 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 203) (fragment7966065Chars ++ tail) =
      .ok (fragment7966065Value, tail) := by
  have hinput : fragment7966065Chars ++ tail = '{' :: (fragment7966065Field000Chars00 ++ (fragment7966065Field001Chars00 ++ (fragment7966065Field002Chars00 ++ (fragment7966065Field003Chars00 ++ (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment7966065Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 203) (fragment7966065Chars ++ tail) =
        SourceJson.value (fuel + 203) ('{' :: (fragment7966065Field000Chars00 ++ (fragment7966065Field001Chars00 ++ (fragment7966065Field002Chars00 ++ (fragment7966065Field003Chars00 ++ (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 203)) hinput
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment7966065Field000Chars00 ++ (fragment7966065Field001Chars00 ++ (fragment7966065Field002Chars00 ++ (fragment7966065Field003Chars00 ++ (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))))))))))) fragment7966065Acc00000 := by rfl
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment7966065Field001Chars00 ++ (fragment7966065Field002Chars00 ++ (fragment7966065Field003Chars00 ++ (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail))))))))))) fragment7966065Acc00100 := object_fragment7966065_field_000 fuel (fragment7966065Field001Chars00 ++ (fragment7966065Field002Chars00 ++ (fragment7966065Field003Chars00 ++ (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment7966065Field002Chars00 ++ (fragment7966065Field003Chars00 ++ (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))))))))) fragment7966065Acc00200 := object_fragment7966065_field_001 fuel (fragment7966065Field002Chars00 ++ (fragment7966065Field003Chars00 ++ (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment7966065Field003Chars00 ++ (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail))))))))) fragment7966065Acc00300 := object_fragment7966065_field_002 fuel (fragment7966065Field003Chars00 ++ (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))))))) fragment7966065Acc00400 := object_fragment7966065_field_003 fuel (fragment7966065Field004Chars00 ++ (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail))))))) fragment7966065Acc00500 := object_fragment7966065_field_004 fuel (fragment7966065Field005Chars00 ++ (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))))) fragment7966065Acc00600 := object_fragment7966065_field_005 fuel (fragment7966065Field006Chars00 ++ (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail))))) fragment7966065Acc00700 := object_fragment7966065_field_006 fuel (fragment7966065Field007Chars00 ++ (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))) fragment7966065Acc00800 := object_fragment7966065_field_007 fuel (fragment7966065Field008Chars00 ++ (fragment7966065Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment7966065Field009Chars00 ++ (tail))) fragment7966065Acc00900 := object_fragment7966065_field_008 fuel (fragment7966065Field009Chars00 ++ (tail))
    _ = .ok (fragment7966065Value, tail) := object_fragment7966065_field_009 fuel (tail)

noncomputable def fragment7967576Acc00000 : List (String × SourceJson) := []

noncomputable def fragment7967576Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment7967576Field000Value00 : SourceJson := .number (String.ofList ['3', '2', '9', '9'])
noncomputable def fragment7967576Acc00100 : List (String × SourceJson) := (fragment7967576Field000Key00, fragment7967576Field000Value00) :: fragment7967576Acc00000
noncomputable def fragment7967576Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '2', '9', '9', ',']

theorem object_fragment7967576_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 390) (SourceJson.white (fragment7967576Field000Chars00 ++ tail)) fragment7967576Acc00000 =
      SourceJson.object (fuel + 389) (SourceJson.white tail) fragment7967576Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_000"
  err.flush

noncomputable def fragment7967576Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment7967576Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '3']), .number (String.ofList ['1', '1', '4']), .number (String.ofList ['1', '1', '3']), .number (String.ofList ['9', '9']), .number (String.ofList ['8', '0']), .number (String.ofList ['4', '9']), .number (String.ofList ['8']), .number (String.ofList ['3'])]
noncomputable def fragment7967576Acc00200 : List (String × SourceJson) := (fragment7967576Field001Key00, fragment7967576Field001Value00) :: fragment7967576Acc00100
noncomputable def fragment7967576Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7967576_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 389) (SourceJson.white (fragment7967576Field001Chars00 ++ tail)) fragment7967576Acc00100 =
      SourceJson.object (fuel + 388) (SourceJson.white tail) fragment7967576Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_001"
  err.flush

noncomputable def fragment7967576Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment7967576Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '7', '1', '8', '0', '7', '8', '1', '9', '8', '0', '8', '8', '8', '4', '6', '6', '3', '8', '2', '2', '2', '9', '7', '2', '8', '8', '6', '1', '4', '1', '0', '5', '3', '3', '8', '7', '7', '4', '6', '3', '/', '2', '8', '4', '9', '4', '0', '8', '0', '7', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7967576Acc00300 : List (String × SourceJson) := (fragment7967576Field002Key00, fragment7967576Field002Value00) :: fragment7967576Acc00200
noncomputable def fragment7967576Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '7', '1', '8', '0', '7', '8', '1', '9', '8', '0', '8', '8', '8', '4', '6', '6', '3', '8', '2', '2', '2', '9', '7', '2', '8', '8', '6', '1', '4', '1', '0', '5', '3', '3', '8', '7', '7', '4', '6', '3', '/', '2', '8', '4', '9', '4', '0', '8', '0', '7', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7967576_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 388) (SourceJson.white (fragment7967576Field002Chars00 ++ tail)) fragment7967576Acc00200 =
      SourceJson.object (fuel + 387) (SourceJson.white tail) fragment7967576Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_002"
  err.flush

noncomputable def fragment7967576Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment7967576Field003Value00 : SourceJson := .str (String.ofList ['2', '3', '4', '9', '5', '0', '6', '9', '/', '2', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7967576Acc00400 : List (String × SourceJson) := (fragment7967576Field003Key00, fragment7967576Field003Value00) :: fragment7967576Acc00300
noncomputable def fragment7967576Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '3', '4', '9', '5', '0', '6', '9', '/', '2', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7967576_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 387) (SourceJson.white (fragment7967576Field003Chars00 ++ tail)) fragment7967576Acc00300 =
      SourceJson.object (fuel + 386) (SourceJson.white tail) fragment7967576Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_003"
  err.flush

noncomputable def fragment7967576Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment7967576Field004Value00 : SourceJson := .arr [.str (String.ofList ['4', '2', '6', '5', '6', '5', '7', '/', '7', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '8', '4', '2', '7', '/', '1', '7', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '7', '0', '4', '0', '7', '/', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '3', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '0', '9', '9', '1', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '4', '4', '0', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '4', '4', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7967576Acc00500 : List (String × SourceJson) := (fragment7967576Field004Key00, fragment7967576Field004Value00) :: fragment7967576Acc00400
noncomputable def fragment7967576Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '5', '6', '5', '7', '/', '7', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '8', '4', '2', '7', '/', '1', '7', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '0', '4', '0', '7', '/', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '3', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '0', '9', '9', '1', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '4', '4', '0', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '4', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7967576_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 386) (SourceJson.white (fragment7967576Field004Chars00 ++ tail)) fragment7967576Acc00400 =
      SourceJson.object (fuel + 385) (SourceJson.white tail) fragment7967576Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_004"
  err.flush

noncomputable def fragment7967576Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment7967576Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '0', '2', '3', '4', '0', '8', '9', '9', '7', '9', '7', '8', '3', '9', '4', '3', '6', '2', '9', '/', '2', '4', '6', '1', '9', '5', '8', '2', '7', '6', '3', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '8', '2', '3', '5', '2', '8', '9', '2', '8', '8', '6', '7', '1', '2', '3', '1', '6', '7', '7', '/', '8', '0', '0', '1', '3', '6', '4', '3', '9', '8', '0', '4', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '6', '8', '7', '5', '8', '6', '7', '6', '5', '9', '8', '9', '6', '3', '5', '2', '3', '/', '2', '8', '0', '7', '4', '9', '6', '2', '8', '0', '0', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '0', '9', '6', '8', '9', '3', '1', '2', '6', '0', '7', '4', '3', '3', '5', '8', '1', '9', '9', '/', '5', '3', '3', '4', '2', '4', '2', '9', '3', '2', '0', '3', '2', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '3', '0', '6', '0', '2', '7', '5', '3', '0', '6', '7', '9', '6', '3', '6', '5', '1', '/', '2', '8', '0', '7', '4', '9', '6', '2', '8', '0', '0', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '9', '5', '0', '8', '9', '9', '6', '3', '2', '8', '7', '8', '8', '1', '6', '6', '9', '/', '2', '5', '5', '2', '2', '6', '9', '3', '4', '5', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '2', '5', '2', '7', '0', '7', '9', '1', '4', '5', '6', '9', '7', '2', '4', '3', '3', '/', '1', '8', '7', '1', '6', '6', '4', '1', '8', '6', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '1', '2', '5', '4', '3', '6', '3', '0', '7', '2', '4', '1', '6', '9', '4', '1', '3', '/', '7', '0', '1', '8', '7', '4', '0', '7', '0', '0', '0', '4', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '2', '2', '9', '1', '4', '6', '2', '8', '2', '6', '2', '5', '2', '6', '5', '6', '7', '/', '8', '0', '0', '1', '3', '6', '4', '3', '9', '8', '0', '4', '8', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '2', '3', '1', '6', '5', '4', '1', '4', '6', '4', '4', '3', '7', '1', '1', '0', '1', '/', '3', '5', '5', '6', '1', '6', '1', '9', '5', '4', '6', '8', '8', '2', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7967576Acc00600 : List (String × SourceJson) := (fragment7967576Field005Key00, fragment7967576Field005Value00) :: fragment7967576Acc00500
noncomputable def fragment7967576Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '2', '3', '4', '0', '8', '9', '9', '7', '9', '7', '8', '3', '9', '4', '3', '6', '2', '9', '/', '2', '4', '6', '1', '9', '5', '8', '2', '7', '6', '3', '2', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '8', '2', '3', '5', '2', '8', '9', '2', '8', '8', '6', '7', '1', '2', '3', '1', '6', '7', '7', '/', '8', '0', '0', '1', '3', '6', '4', '3', '9', '8', '0', '4', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '6', '8', '7', '5', '8', '6', '7', '6', '5', '9', '8', '9', '6', '3', '5', '2', '3', '/', '2', '8', '0', '7', '4', '9', '6', '2', '8', '0', '0', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '0', '9', '6', '8', '9', '3', '1', '2', '6', '0', '7', '4', '3', '3', '5', '8', '1', '9', '9', '/', '5', '3', '3', '4', '2', '4', '2', '9', '3', '2', '0', '3', '2', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '7', '3', '0', '6', '0', '2', '7', '5', '3', '0', '6', '7', '9', '6', '3', '6', '5', '1', '/', '2', '8', '0', '7', '4', '9', '6', '2', '8', '0', '0', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '9', '5', '0', '8', '9', '9', '6', '3', '2', '8', '7', '8', '8', '1', '6', '6', '9', '/', '2', '5', '5', '2', '2', '6', '9', '3', '4', '5', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '2', '5', '2', '7', '0', '7', '9', '1', '4', '5', '6', '9', '7', '2', '4', '3', '3', '/', '1', '8', '7', '1', '6', '6', '4', '1', '8', '6', '6', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '1', '2', '5', '4', '3', '6', '3', '0', '7', '2', '4', '1', '6', '9', '4', '1', '3', '/', '7', '0', '1', '8', '7', '4', '0', '7', '0', '0', '0', '4', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '2', '2', '9', '1', '4', '6', '2', '8', '2', '6', '2', '5', '2', '6', '5', '6', '7', '/', '8', '0', '0', '1', '3', '6', '4', '3', '9', '8', '0', '4', '8', '4', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '2', '3', '1', '6', '5', '4', '1', '4', '6', '4', '4', '3', '7', '1', '1', '0', '1', '/', '3', '5', '5', '6', '1', '6', '1', '9', '5', '4', '6', '8', '8', '2', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7967576_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 385) (SourceJson.white (fragment7967576Field005Chars00 ++ tail)) fragment7967576Acc00500 =
      SourceJson.object (fuel + 384) (SourceJson.white tail) fragment7967576Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_005"
  err.flush

noncomputable def fragment7967576Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7967576Field006Value00 : SourceJson := .str (String.ofList ['7', '7', '3', '6', '8', '5', '9', '7', '3', '7', '8', '1', '2', '3', '2', '0', '3', '0', '7', '9', '5', '2', '9', '5', '3', '8', '6', '9', '6', '3', '7', '6', '9', '1', '9', '5', '5', '3', '6', '2', '1', '5', '/', '7', '4', '2', '2', '4', '3', '2', '9', '2', '2', '8', '3', '8', '9', '9', '1', '7', '5', '2', '6', '8', '1', '3', '3', '3', '6', '1', '3', '9', '7', '7', '5', '3', '4', '3', '9', '0', '8', '7', '6', '7', '1', '2', '9', '7', '4', '2', '5', '9', '0', '1', '5', '5', '5', '8'])
noncomputable def fragment7967576Acc00700 : List (String × SourceJson) := (fragment7967576Field006Key00, fragment7967576Field006Value00) :: fragment7967576Acc00600
noncomputable def fragment7967576Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '7', '3', '6', '8', '5', '9', '7', '3', '7', '8', '1', '2', '3', '2', '0', '3', '0', '7', '9', '5', '2', '9', '5', '3', '8', '6', '9', '6', '3', '7', '6', '9', '1', '9', '5', '5', '3', '6', '2', '1', '5', '/', '7', '4', '2', '2', '4', '3', '2', '9', '2', '2', '8', '3', '8', '9', '9', '1', '7', '5', '2', '6', '8', '1', '3', '3', '3', '6', '1', '3', '9', '7', '7', '5', '3', '4', '3', '9', '0', '8', '7', '6', '7', '1', '2', '9', '7', '4', '2', '5', '9', '0', '1', '5', '5', '5', '8', '"', ',']

theorem object_fragment7967576_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 384) (SourceJson.white (fragment7967576Field006Chars00 ++ tail)) fragment7967576Acc00600 =
      SourceJson.object (fuel + 383) (SourceJson.white tail) fragment7967576Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_006"
  err.flush

noncomputable def fragment7967576Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7967576Field007Value00 : SourceJson := .str (String.ofList ['9', '7', '9', '1', '0', '1', '3', '5', '3', '3', '6', '8', '0', '0', '6', '2', '2', '2', '1', '3', '0', '3', '2', '0', '4', '6', '1', '8', '8', '5', '2', '6', '7', '8', '8', '8', '7', '4', '8', '0', '3', '3', '6', '9', '7', '3', '8', '8', '6', '4', '8', '2', '5', '2', '2', '3', '4', '6', '7', '8', '0', '2', '9', '0', '8', '6', '9', '3', '2', '3', '7', '7', '3', '3', '6', '2', '3', '6', '7', '8', '0', '5', '9', '5', '7', '9', '8', '0', '2', '3', '2', '5', '5', '3', '2', '5', '0', '9', '4', '2', '6', '5', '2', '1', '8', '7', '2', '8', '5', '5', '6', '3', '5', '2', '1', '4', '3', '4', '7', '2', '9', '8', '7', '2', '7', '5', '7', '3', '8', '6', '7', '4', '9', '9', '2', '4', '0', '7', '1', '3', '6', '4', '6', '5', '2', '3', '2', '7', '8', '7', '1', '9', '7', '7', '0', '6', '0', '8', '6', '9', '2', '6', '7', '1', '6', '9', '0', '6', '7', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '1', '8', '8', '2', '9', '1', '3', '6', '6', '2', '6', '4', '3', '6', '6', '6', '9', '6', '3', '7', '9', '8', '3', '0', '3', '2', '2', '8', '0', '6', '6', '0', '1', '2', '6', '8', '9', '3', '4', '8', '0', '9', '5', '0', '0', '8', '7', '5', '3', '1', '2', '0', '8', '3', '4', '7', '2', '3', '9', '6', '2', '1', '8', '1', '2', '8', '3', '0', '8', '1', '9', '6', '3', '1', '5', '6', '8', '2', '9', '9', '6', '5', '6', '7', '0', '2', '4', '8', '2', '9', '6', '8', '0', '7', '1', '2', '4', '0', '0', '2', '4', '7', '9', '9', '2', '2', '5', '5', '6', '4', '7', '2', '4', '7', '5', '2', '0', '3', '0', '8', '3', '7', '9', '6', '7', '3', '6', '8', '8', '2', '5', '7', '2', '4', '3', '3', '8', '8', '1', '4', '2', '4', '4', '1', '9', '6', '2', '5', '3', '9', '4', '6', '4', '5', '8', '9', '1', '8', '6', '3', '1', '8', '0', '0', '4', '3', '9', '3', '6', '6', '1', '8', '7', '7', '3', '3', '0', '5', '8', '3', '4', '3', '0', '0', '8', '1', '2', '4', '1', '1', '5', '7', '7', '9'])
noncomputable def fragment7967576Acc00800 : List (String × SourceJson) := (fragment7967576Field007Key00, fragment7967576Field007Value00) :: fragment7967576Acc00700
noncomputable def fragment7967576Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '7', '9', '1', '0', '1', '3', '5', '3', '3', '6', '8', '0', '0', '6', '2', '2', '2', '1', '3', '0', '3', '2', '0', '4', '6', '1', '8', '8', '5', '2', '6', '7', '8', '8', '8', '7', '4', '8', '0', '3', '3', '6', '9', '7', '3', '8', '8', '6', '4', '8', '2', '5', '2', '2', '3', '4', '6', '7', '8', '0', '2', '9', '0', '8', '6', '9', '3', '2', '3', '7', '7', '3', '3', '6', '2', '3', '6', '7', '8', '0', '5', '9', '5', '7', '9', '8', '0', '2', '3', '2', '5', '5', '3', '2', '5', '0', '9', '4', '2', '6', '5', '2', '1', '8', '7', '2', '8', '5', '5', '6', '3', '5', '2', '1', '4', '3', '4', '7', '2', '9', '8', '7', '2', '7', '5', '7', '3', '8', '6', '7', '4', '9', '9', '2', '4', '0', '7', '1', '3', '6', '4', '6', '5', '2', '3', '2', '7', '8', '7', '1', '9', '7', '7', '0', '6', '0', '8', '6', '9', '2', '6', '7', '1', '6', '9', '0', '6', '7', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '1', '8', '8', '2', '9', '1', '3', '6', '6', '2', '6', '4', '3', '6', '6', '6', '9', '6', '3', '7', '9', '8', '3', '0', '3', '2', '2', '8', '0', '6', '6', '0', '1', '2', '6', '8', '9', '3', '4', '8', '0', '9', '5', '0', '0', '8', '7', '5', '3', '1', '2', '0', '8', '3', '4', '7', '2', '3', '9', '6', '2', '1', '8', '1', '2', '8', '3', '0', '8', '1', '9', '6', '3', '1', '5', '6', '8', '2', '9', '9', '6', '5', '6', '7', '0', '2', '4', '8', '2', '9', '6', '8', '0', '7', '1', '2', '4', '0', '0', '2', '4', '7', '9', '9', '2', '2', '5', '5', '6', '4', '7', '2', '4', '7', '5', '2', '0', '3', '0', '8', '3', '7', '9', '6', '7', '3', '6', '8', '8', '2', '5', '7', '2', '4', '3', '3', '8', '8', '1', '4', '2', '4', '4', '1', '9', '6', '2', '5', '3', '9', '4', '6', '4', '5', '8', '9', '1', '8', '6', '3', '1', '8', '0', '0', '4', '3', '9', '3', '6', '6', '1', '8', '7', '7', '3', '3', '0', '5', '8', '3', '4', '3', '0', '0', '8', '1', '2', '4', '1', '1', '5', '7', '7', '9', '"', ',']

theorem object_fragment7967576_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 383) (SourceJson.white (fragment7967576Field007Chars00 ++ tail)) fragment7967576Acc00700 =
      SourceJson.object (fuel + 382) (SourceJson.white tail) fragment7967576Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_007"
  err.flush

noncomputable def fragment7967576Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7967576Field008Value00 : SourceJson := .str (String.ofList ['8', '2', '5', '8', '4', '4', '0', '1', '5', '0', '6', '8', '5', '8', '8', '3'])
noncomputable def fragment7967576Acc00900 : List (String × SourceJson) := (fragment7967576Field008Key00, fragment7967576Field008Value00) :: fragment7967576Acc00800
noncomputable def fragment7967576Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '2', '5', '8', '4', '4', '0', '1', '5', '0', '6', '8', '5', '8', '8', '3', '"', ',']

theorem object_fragment7967576_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 382) (SourceJson.white (fragment7967576Field008Chars00 ++ tail)) fragment7967576Acc00800 =
      SourceJson.object (fuel + 381) (SourceJson.white tail) fragment7967576Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_008"
  err.flush

noncomputable def fragment7967576Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7967576Field009Value00 : SourceJson := .str (String.ofList ['4', '7', '9', '1', '8', '8', '3', '1', '8', '1', '9', '5', '4', '1', '9', '7', '1'])
noncomputable def fragment7967576Acc01000 : List (String × SourceJson) := (fragment7967576Field009Key00, fragment7967576Field009Value00) :: fragment7967576Acc00900
noncomputable def fragment7967576Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '7', '9', '1', '8', '8', '3', '1', '8', '1', '9', '5', '4', '1', '9', '7', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment7967576_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 381) (SourceJson.white (fragment7967576Field009Chars00 ++ tail)) fragment7967576Acc00900 =
      .ok (.obj (fragment7967576Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7967576_object_field_009"
  err.flush

noncomputable def fragment7967576Chars : List Char := '{' :: (fragment7967576Field000Chars00 ++ fragment7967576Field001Chars00 ++ fragment7967576Field002Chars00 ++ fragment7967576Field003Chars00 ++ fragment7967576Field004Chars00 ++ fragment7967576Field005Chars00 ++ fragment7967576Field006Chars00 ++ fragment7967576Field007Chars00 ++ fragment7967576Field008Chars00 ++ fragment7967576Field009Chars00)
noncomputable def fragment7967576Value : SourceJson := .obj (fragment7967576Acc01000.reverse)

theorem value_fragment7967576 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 391) (fragment7967576Chars ++ tail) =
      .ok (fragment7967576Value, tail) := by
  have hinput : fragment7967576Chars ++ tail = '{' :: (fragment7967576Field000Chars00 ++ (fragment7967576Field001Chars00 ++ (fragment7967576Field002Chars00 ++ (fragment7967576Field003Chars00 ++ (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment7967576Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 391) (fragment7967576Chars ++ tail) =
        SourceJson.value (fuel + 391) ('{' :: (fragment7967576Field000Chars00 ++ (fragment7967576Field001Chars00 ++ (fragment7967576Field002Chars00 ++ (fragment7967576Field003Chars00 ++ (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 391)) hinput
    _ = SourceJson.object (fuel + 390) (SourceJson.white (fragment7967576Field000Chars00 ++ (fragment7967576Field001Chars00 ++ (fragment7967576Field002Chars00 ++ (fragment7967576Field003Chars00 ++ (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))))))))))) fragment7967576Acc00000 := by rfl
    _ = SourceJson.object (fuel + 389) (SourceJson.white (fragment7967576Field001Chars00 ++ (fragment7967576Field002Chars00 ++ (fragment7967576Field003Chars00 ++ (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail))))))))))) fragment7967576Acc00100 := object_fragment7967576_field_000 fuel (fragment7967576Field001Chars00 ++ (fragment7967576Field002Chars00 ++ (fragment7967576Field003Chars00 ++ (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 388) (SourceJson.white (fragment7967576Field002Chars00 ++ (fragment7967576Field003Chars00 ++ (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))))))))) fragment7967576Acc00200 := object_fragment7967576_field_001 fuel (fragment7967576Field002Chars00 ++ (fragment7967576Field003Chars00 ++ (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 387) (SourceJson.white (fragment7967576Field003Chars00 ++ (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail))))))))) fragment7967576Acc00300 := object_fragment7967576_field_002 fuel (fragment7967576Field003Chars00 ++ (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 386) (SourceJson.white (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))))))) fragment7967576Acc00400 := object_fragment7967576_field_003 fuel (fragment7967576Field004Chars00 ++ (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 385) (SourceJson.white (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail))))))) fragment7967576Acc00500 := object_fragment7967576_field_004 fuel (fragment7967576Field005Chars00 ++ (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 384) (SourceJson.white (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))))) fragment7967576Acc00600 := object_fragment7967576_field_005 fuel (fragment7967576Field006Chars00 ++ (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 383) (SourceJson.white (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail))))) fragment7967576Acc00700 := object_fragment7967576_field_006 fuel (fragment7967576Field007Chars00 ++ (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 382) (SourceJson.white (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))) fragment7967576Acc00800 := object_fragment7967576_field_007 fuel (fragment7967576Field008Chars00 ++ (fragment7967576Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 381) (SourceJson.white (fragment7967576Field009Chars00 ++ (tail))) fragment7967576Acc00900 := object_fragment7967576_field_008 fuel (fragment7967576Field009Chars00 ++ (tail))
    _ = .ok (fragment7967576Value, tail) := object_fragment7967576_field_009 fuel (tail)

noncomputable def fragment7969477Acc00000 : List (String × SourceJson) := []

noncomputable def fragment7969477Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment7969477Field000Value00 : SourceJson := .number (String.ofList ['3', '3', '0', '0'])
noncomputable def fragment7969477Acc00100 : List (String × SourceJson) := (fragment7969477Field000Key00, fragment7969477Field000Value00) :: fragment7969477Acc00000
noncomputable def fragment7969477Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '3', '0', '0', ',']

theorem object_fragment7969477_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment7969477Field000Chars00 ++ tail)) fragment7969477Acc00000 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment7969477Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_000"
  err.flush

noncomputable def fragment7969477Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment7969477Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '3']), .number (String.ofList ['1', '1', '4']), .number (String.ofList ['1', '1', '3']), .number (String.ofList ['9', '9']), .number (String.ofList ['8', '0']), .number (String.ofList ['4', '9']), .number (String.ofList ['4', '0']), .number (String.ofList ['3'])]
noncomputable def fragment7969477Acc00200 : List (String × SourceJson) := (fragment7969477Field001Key00, fragment7969477Field001Value00) :: fragment7969477Acc00100
noncomputable def fragment7969477Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7969477_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment7969477Field001Chars00 ++ tail)) fragment7969477Acc00100 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment7969477Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_001"
  err.flush

noncomputable def fragment7969477Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment7969477Field002Value00 : SourceJson := .str (String.ofList ['5', '0', '5', '4', '9', '9', '4', '2', '1', '8', '9', '3', '6', '8', '4', '1', '4', '2', '5', '6', '3', '8', '8', '6', '4', '0', '3', '6', '4', '9', '3', '7', '4', '4', '1', '1', '7', '3', '5', '0', '2', '7', '/', '2', '2', '5', '5', '7', '8', '1', '3', '9', '4', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7969477Acc00300 : List (String × SourceJson) := (fragment7969477Field002Key00, fragment7969477Field002Value00) :: fragment7969477Acc00200
noncomputable def fragment7969477Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '0', '5', '4', '9', '9', '4', '2', '1', '8', '9', '3', '6', '8', '4', '1', '4', '2', '5', '6', '3', '8', '8', '6', '4', '0', '3', '6', '4', '9', '3', '7', '4', '4', '1', '1', '7', '3', '5', '0', '2', '7', '/', '2', '2', '5', '5', '7', '8', '1', '3', '9', '4', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7969477_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment7969477Field002Chars00 ++ tail)) fragment7969477Acc00200 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment7969477Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_002"
  err.flush

noncomputable def fragment7969477Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment7969477Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '6', '0', '9', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7969477Acc00400 : List (String × SourceJson) := (fragment7969477Field003Key00, fragment7969477Field003Value00) :: fragment7969477Acc00300
noncomputable def fragment7969477Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '6', '0', '9', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7969477_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment7969477Field003Chars00 ++ tail)) fragment7969477Acc00300 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment7969477Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_003"
  err.flush

noncomputable def fragment7969477Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment7969477Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '2', '5', '4', '/', '1', '7', '1', '8', '7', '5']), .str (String.ofList ['1', '0', '2', '5', '4', '/', '1', '7', '1', '8', '7', '5']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '7', '0', '4', '0', '7', '/', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0']), .str (String.ofList ['2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0']), .str (String.ofList ['1', '4', '8', '4', '4', '0', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '4', '4', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7969477Acc00500 : List (String × SourceJson) := (fragment7969477Field004Key00, fragment7969477Field004Value00) :: fragment7969477Acc00400
noncomputable def fragment7969477Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '5', '4', '/', '1', '7', '1', '8', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '5', '4', '/', '1', '7', '1', '8', '7', '5', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '0', '4', '0', '7', '/', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '4', '4', '0', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '4', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7969477_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment7969477Field004Chars00 ++ tail)) fragment7969477Acc00400 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment7969477Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_004"
  err.flush

noncomputable def fragment7969477Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment7969477Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '3', '0', '6', '5', '5', '2', '1', '9', '0', '5', '9', '/', '1', '9', '1', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '1', '1', '6', '7', '6', '6', '0', '5', '5', '7', '/', '4', '7', '9', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '0', '2', '0', '6', '9', '3', '6', '3', '4', '1', '/', '6', '3', '9', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '5', '7', '1', '6', '8', '4', '1', '7', '1', '3', '/', '6', '3', '9', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '5', '2', '5', '6', '7', '7', '3', '3', '7', '3', '/', '6', '3', '9', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '7', '5', '3', '0', '3', '6', '4', '3', '/', '1', '1', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '1', '6', '1', '1', '2', '4', '8', '3', '9', '/', '8', '5', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '1', '3', '0', '5', '6', '4', '9', '4', '7', '9', '/', '2', '5', '5', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '6', '2', '1', '1', '2', '3', '7', '7', '/', '1', '1', '9', '9', '1', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '4', '1', '0', '8', '3', '4', '7', '9', '/', '1', '0', '6', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7969477Acc00600 : List (String × SourceJson) := (fragment7969477Field005Key00, fragment7969477Field005Value00) :: fragment7969477Acc00500
noncomputable def fragment7969477Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '0', '6', '5', '5', '2', '1', '9', '0', '5', '9', '/', '1', '9', '1', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '1', '6', '7', '6', '6', '0', '5', '5', '7', '/', '4', '7', '9', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '0', '2', '0', '6', '9', '3', '6', '3', '4', '1', '/', '6', '3', '9', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '5', '7', '1', '6', '8', '4', '1', '7', '1', '3', '/', '6', '3', '9', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '5', '2', '5', '6', '7', '7', '3', '3', '7', '3', '/', '6', '3', '9', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '7', '5', '3', '0', '3', '6', '4', '3', '/', '1', '1', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '1', '6', '1', '1', '2', '4', '8', '3', '9', '/', '8', '5', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '3', '0', '5', '6', '4', '9', '4', '7', '9', '/', '2', '5', '5', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '6', '2', '1', '1', '2', '3', '7', '7', '/', '1', '1', '9', '9', '1', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '4', '1', '0', '8', '3', '4', '7', '9', '/', '1', '0', '6', '5', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7969477_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment7969477Field005Chars00 ++ tail)) fragment7969477Acc00500 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment7969477Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_005"
  err.flush

noncomputable def fragment7969477Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7969477Field006Value00 : SourceJson := .str (String.ofList ['2', '0', '3', '9', '9', '8', '2', '0', '1', '6', '9', '8', '9', '6', '1', '0', '2', '8', '5', '4', '1', '8', '5', '3', '3', '8', '4', '9', '1', '8', '5', '3', '3', '1', '0', '0', '6', '1', '3', '9', '9', '5', '/', '9', '0', '1', '0', '3', '9', '5', '2', '9', '5', '2', '9', '8', '7', '1', '5', '2', '0', '8', '6', '1', '8', '8', '5', '1', '0', '3', '3', '8', '1', '1', '5', '8', '2', '8', '1', '2', '7', '0', '3', '6', '4', '7', '0', '4', '6', '8', '4', '6', '9', '0', '6', '3', '6', '8'])
noncomputable def fragment7969477Acc00700 : List (String × SourceJson) := (fragment7969477Field006Key00, fragment7969477Field006Value00) :: fragment7969477Acc00600
noncomputable def fragment7969477Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '0', '3', '9', '9', '8', '2', '0', '1', '6', '9', '8', '9', '6', '1', '0', '2', '8', '5', '4', '1', '8', '5', '3', '3', '8', '4', '9', '1', '8', '5', '3', '3', '1', '0', '0', '6', '1', '3', '9', '9', '5', '/', '9', '0', '1', '0', '3', '9', '5', '2', '9', '5', '2', '9', '8', '7', '1', '5', '2', '0', '8', '6', '1', '8', '8', '5', '1', '0', '3', '3', '8', '1', '1', '5', '8', '2', '8', '1', '2', '7', '0', '3', '6', '4', '7', '0', '4', '6', '8', '4', '6', '9', '0', '6', '3', '6', '8', '"', ',']

theorem object_fragment7969477_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment7969477Field006Chars00 ++ tail)) fragment7969477Acc00600 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment7969477Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_006"
  err.flush

noncomputable def fragment7969477Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7969477Field007Value00 : SourceJson := .str (String.ofList ['8', '6', '4', '0', '6', '0', '7', '8', '4', '1', '7', '9', '0', '2', '1', '3', '3', '4', '0', '0', '4', '0', '6', '7', '4', '8', '3', '4', '0', '2', '2', '8', '5', '4', '5', '7', '0', '3', '9', '5', '9', '8', '6', '3', '7', '5', '5', '9', '4', '1', '9', '7', '4', '3', '9', '4', '6', '2', '8', '2', '4', '4', '3', '1', '4', '6', '1', '9', '7', '5', '9', '8', '9', '0', '0', '5', '7', '9', '6', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '2', '9', '8', '7', '9', '1', '4', '8', '4', '3', '2', '9', '1', '2', '6', '2', '1', '4', '5', '3', '0', '3', '8', '0', '4', '0', '0', '3', '3', '1', '7', '3', '5', '1', '2', '0', '3', '2', '2', '7', '5', '0', '2', '8', '5', '5', '6', '4', '5', '2', '7', '6', '4', '3', '2', '9', '6', '4', '1', '4', '9', '0', '0', '6', '7', '7', '4', '2', '3', '3', '5', '4', '0', '8', '2', '1', '3', '5', '6', '0', '4', '4', '6', '1', '1', '7', '2', '9', '7', '4', '4', '3', '9', '7', '4', '2', '7', '6', '6', '9', '9', '3', '0', '2', '4', '0', '2', '4', '6', '7'])
noncomputable def fragment7969477Acc00800 : List (String × SourceJson) := (fragment7969477Field007Key00, fragment7969477Field007Value00) :: fragment7969477Acc00700
noncomputable def fragment7969477Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '6', '4', '0', '6', '0', '7', '8', '4', '1', '7', '9', '0', '2', '1', '3', '3', '4', '0', '0', '4', '0', '6', '7', '4', '8', '3', '4', '0', '2', '2', '8', '5', '4', '5', '7', '0', '3', '9', '5', '9', '8', '6', '3', '7', '5', '5', '9', '4', '1', '9', '7', '4', '3', '9', '4', '6', '2', '8', '2', '4', '4', '3', '1', '4', '6', '1', '9', '7', '5', '9', '8', '9', '0', '0', '5', '7', '9', '6', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '2', '9', '8', '7', '9', '1', '4', '8', '4', '3', '2', '9', '1', '2', '6', '2', '1', '4', '5', '3', '0', '3', '8', '0', '4', '0', '0', '3', '3', '1', '7', '3', '5', '1', '2', '0', '3', '2', '2', '7', '5', '0', '2', '8', '5', '5', '6', '4', '5', '2', '7', '6', '4', '3', '2', '9', '6', '4', '1', '4', '9', '0', '0', '6', '7', '7', '4', '2', '3', '3', '5', '4', '0', '8', '2', '1', '3', '5', '6', '0', '4', '4', '6', '1', '1', '7', '2', '9', '7', '4', '4', '3', '9', '7', '4', '2', '7', '6', '6', '9', '9', '3', '0', '2', '4', '0', '2', '4', '6', '7', '"', ',']

theorem object_fragment7969477_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment7969477Field007Chars00 ++ tail)) fragment7969477Acc00700 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment7969477Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_007"
  err.flush

noncomputable def fragment7969477Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7969477Field008Value00 : SourceJson := .str (String.ofList ['1', '7', '9', '3', '7', '5', '0', '6', '7', '8', '7', '5', '8', '3', '3', '2'])
noncomputable def fragment7969477Acc00900 : List (String × SourceJson) := (fragment7969477Field008Key00, fragment7969477Field008Value00) :: fragment7969477Acc00800
noncomputable def fragment7969477Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '9', '3', '7', '5', '0', '6', '7', '8', '7', '5', '8', '3', '3', '2', '"', ',']

theorem object_fragment7969477_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment7969477Field008Chars00 ++ tail)) fragment7969477Acc00800 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment7969477Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_008"
  err.flush

noncomputable def fragment7969477Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7969477Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '6', '8', '4', '2', '5', '8', '5', '6', '2', '0', '6', '8', '4', '7'])
noncomputable def fragment7969477Acc01000 : List (String × SourceJson) := (fragment7969477Field009Key00, fragment7969477Field009Value00) :: fragment7969477Acc00900
noncomputable def fragment7969477Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '8', '6', '8', '4', '2', '5', '8', '5', '6', '2', '0', '6', '8', '4', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment7969477_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment7969477Field009Chars00 ++ tail)) fragment7969477Acc00900 =
      .ok (.obj (fragment7969477Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7969477_object_field_009"
  err.flush

noncomputable def fragment7969477Chars : List Char := '{' :: (fragment7969477Field000Chars00 ++ fragment7969477Field001Chars00 ++ fragment7969477Field002Chars00 ++ fragment7969477Field003Chars00 ++ fragment7969477Field004Chars00 ++ fragment7969477Field005Chars00 ++ fragment7969477Field006Chars00 ++ fragment7969477Field007Chars00 ++ fragment7969477Field008Chars00 ++ fragment7969477Field009Chars00)
noncomputable def fragment7969477Value : SourceJson := .obj (fragment7969477Acc01000.reverse)

theorem value_fragment7969477 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 221) (fragment7969477Chars ++ tail) =
      .ok (fragment7969477Value, tail) := by
  have hinput : fragment7969477Chars ++ tail = '{' :: (fragment7969477Field000Chars00 ++ (fragment7969477Field001Chars00 ++ (fragment7969477Field002Chars00 ++ (fragment7969477Field003Chars00 ++ (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment7969477Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 221) (fragment7969477Chars ++ tail) =
        SourceJson.value (fuel + 221) ('{' :: (fragment7969477Field000Chars00 ++ (fragment7969477Field001Chars00 ++ (fragment7969477Field002Chars00 ++ (fragment7969477Field003Chars00 ++ (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 221)) hinput
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment7969477Field000Chars00 ++ (fragment7969477Field001Chars00 ++ (fragment7969477Field002Chars00 ++ (fragment7969477Field003Chars00 ++ (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))))))))))) fragment7969477Acc00000 := by rfl
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment7969477Field001Chars00 ++ (fragment7969477Field002Chars00 ++ (fragment7969477Field003Chars00 ++ (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail))))))))))) fragment7969477Acc00100 := object_fragment7969477_field_000 fuel (fragment7969477Field001Chars00 ++ (fragment7969477Field002Chars00 ++ (fragment7969477Field003Chars00 ++ (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment7969477Field002Chars00 ++ (fragment7969477Field003Chars00 ++ (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))))))))) fragment7969477Acc00200 := object_fragment7969477_field_001 fuel (fragment7969477Field002Chars00 ++ (fragment7969477Field003Chars00 ++ (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment7969477Field003Chars00 ++ (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail))))))))) fragment7969477Acc00300 := object_fragment7969477_field_002 fuel (fragment7969477Field003Chars00 ++ (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))))))) fragment7969477Acc00400 := object_fragment7969477_field_003 fuel (fragment7969477Field004Chars00 ++ (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail))))))) fragment7969477Acc00500 := object_fragment7969477_field_004 fuel (fragment7969477Field005Chars00 ++ (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))))) fragment7969477Acc00600 := object_fragment7969477_field_005 fuel (fragment7969477Field006Chars00 ++ (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail))))) fragment7969477Acc00700 := object_fragment7969477_field_006 fuel (fragment7969477Field007Chars00 ++ (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))) fragment7969477Acc00800 := object_fragment7969477_field_007 fuel (fragment7969477Field008Chars00 ++ (fragment7969477Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment7969477Field009Chars00 ++ (tail))) fragment7969477Acc00900 := object_fragment7969477_field_008 fuel (fragment7969477Field009Chars00 ++ (tail))
    _ = .ok (fragment7969477Value, tail) := object_fragment7969477_field_009 fuel (tail)

noncomputable def fragment7971030Acc00000 : List (String × SourceJson) := []

noncomputable def fragment7971030Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment7971030Field000Value00 : SourceJson := .number (String.ofList ['3', '3', '0', '1'])
noncomputable def fragment7971030Acc00100 : List (String × SourceJson) := (fragment7971030Field000Key00, fragment7971030Field000Value00) :: fragment7971030Acc00000
noncomputable def fragment7971030Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '3', '0', '1', ',']

theorem object_fragment7971030_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment7971030Field000Chars00 ++ tail)) fragment7971030Acc00000 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment7971030Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_000"
  err.flush

noncomputable def fragment7971030Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment7971030Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '3']), .number (String.ofList ['1', '1', '4']), .number (String.ofList ['1', '1', '3']), .number (String.ofList ['9', '9']), .number (String.ofList ['8', '0']), .number (String.ofList ['7', '1']), .number (String.ofList ['4', '0']), .number (String.ofList ['3'])]
noncomputable def fragment7971030Acc00200 : List (String × SourceJson) := (fragment7971030Field001Key00, fragment7971030Field001Value00) :: fragment7971030Acc00100
noncomputable def fragment7971030Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7971030_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment7971030Field001Chars00 ++ tail)) fragment7971030Acc00100 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment7971030Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_001"
  err.flush

noncomputable def fragment7971030Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment7971030Field002Value00 : SourceJson := .str (String.ofList ['2', '2', '7', '3', '2', '0', '4', '4', '4', '3', '9', '4', '4', '5', '6', '2', '9', '2', '9', '9', '0', '4', '1', '1', '7', '5', '2', '4', '8', '3', '4', '2', '2', '3', '6', '6', '7', '7', '9', '1', '7', '3', '3', '/', '1', '1', '2', '9', '0', '9', '6', '9', '9', '7', '6', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7971030Acc00300 : List (String × SourceJson) := (fragment7971030Field002Key00, fragment7971030Field002Value00) :: fragment7971030Acc00200
noncomputable def fragment7971030Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '2', '7', '3', '2', '0', '4', '4', '4', '3', '9', '4', '4', '5', '6', '2', '9', '2', '9', '9', '0', '4', '1', '1', '7', '5', '2', '4', '8', '3', '4', '2', '2', '3', '6', '6', '7', '7', '9', '1', '7', '3', '3', '/', '1', '1', '2', '9', '0', '9', '6', '9', '9', '7', '6', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7971030_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment7971030Field002Chars00 ++ tail)) fragment7971030Acc00200 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment7971030Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_002"
  err.flush

noncomputable def fragment7971030Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment7971030Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '6', '0', '9', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7971030Acc00400 : List (String × SourceJson) := (fragment7971030Field003Key00, fragment7971030Field003Value00) :: fragment7971030Acc00300
noncomputable def fragment7971030Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '6', '0', '9', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7971030_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment7971030Field003Chars00 ++ tail)) fragment7971030Acc00300 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment7971030Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_003"
  err.flush

noncomputable def fragment7971030Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment7971030Field004Value00 : SourceJson := .arr [.str (String.ofList ['6', '5', '6', '2', '7', '/', '1', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '6', '2', '7', '/', '1', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '7', '0', '4', '0', '7', '/', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0']), .str (String.ofList ['2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0']), .str (String.ofList ['1', '4', '8', '4', '4', '0', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '4', '4', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7971030Acc00500 : List (String × SourceJson) := (fragment7971030Field004Key00, fragment7971030Field004Value00) :: fragment7971030Acc00400
noncomputable def fragment7971030Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '6', '2', '7', '/', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '6', '2', '7', '/', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '0', '4', '0', '7', '/', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '7', '0', '2', '9', '/', '2', '9', '6', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '4', '4', '0', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '4', '4', '0', '3', '/', '1', '8', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7971030_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment7971030Field004Chars00 ++ tail)) fragment7971030Acc00400 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment7971030Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_004"
  err.flush

noncomputable def fragment7971030Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment7971030Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '3', '8', '6', '8', '5', '0', '8', '5', '8', '2', '3', '/', '5', '6', '6', '8', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '1', '3', '0', '4', '0', '2', '5', '2', '1', '9', '/', '2', '2', '6', '7', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '9', '2', '4', '9', '6', '9', '0', '6', '1', '3', '/', '7', '5', '5', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '1', '1', '2', '9', '5', '7', '4', '0', '9', '/', '2', '9', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '8', '1', '9', '3', '1', '7', '9', '3', '9', '/', '2', '9', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '2', '0', '4', '7', '1', '6', '9', '7', '9', '/', '1', '5', '1', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '2', '4', '3', '0', '9', '6', '8', '2', '1', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '0', '2', '4', '6', '5', '2', '4', '5', '0', '9', '/', '3', '0', '2', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '9', '5', '0', '2', '5', '4', '7', '0', '2', '1', '/', '2', '2', '6', '7', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '7', '9', '0', '1', '2', '2', '9', '9', '9', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7971030Acc00600 : List (String × SourceJson) := (fragment7971030Field005Key00, fragment7971030Field005Value00) :: fragment7971030Acc00500
noncomputable def fragment7971030Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '8', '6', '8', '5', '0', '8', '5', '8', '2', '3', '/', '5', '6', '6', '8', '6', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '1', '3', '0', '4', '0', '2', '5', '2', '1', '9', '/', '2', '2', '6', '7', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '9', '2', '4', '9', '6', '9', '0', '6', '1', '3', '/', '7', '5', '5', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '1', '2', '9', '5', '7', '4', '0', '9', '/', '2', '9', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '1', '9', '3', '1', '7', '9', '3', '9', '/', '2', '9', '0', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '2', '0', '4', '7', '1', '6', '9', '7', '9', '/', '1', '5', '1', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '2', '4', '3', '0', '9', '6', '8', '2', '1', '/', '1', '0', '0', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '2', '4', '6', '5', '2', '4', '5', '0', '9', '/', '3', '0', '2', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '5', '0', '2', '5', '4', '7', '0', '2', '1', '/', '2', '2', '6', '7', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '7', '9', '0', '1', '2', '2', '9', '9', '9', '/', '2', '5', '1', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7971030_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment7971030Field005Chars00 ++ tail)) fragment7971030Acc00500 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment7971030Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_005"
  err.flush

noncomputable def fragment7971030Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7971030Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '3', '4', '7', '3', '8', '4', '7', '2', '7', '8', '2', '3', '0', '2', '7', '8', '4', '1', '5', '4', '6', '0', '0', '7', '7', '3', '9', '9', '5', '9', '5', '9', '4', '3', '1', '5', '1', '3', '2', '1', '/', '7', '5', '7', '9', '6', '5', '5', '8', '9', '8', '4', '5', '0', '8', '4', '6', '7', '0', '5', '5', '2', '8', '2', '8', '2', '9', '0', '7', '6', '5', '0', '9', '8', '5', '2', '5', '9', '3', '6', '0', '7', '5', '4', '9', '0', '5', '9', '6', '2', '7', '9', '8', '0', '8', '0'])
noncomputable def fragment7971030Acc00700 : List (String × SourceJson) := (fragment7971030Field006Key00, fragment7971030Field006Value00) :: fragment7971030Acc00600
noncomputable def fragment7971030Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '3', '4', '7', '3', '8', '4', '7', '2', '7', '8', '2', '3', '0', '2', '7', '8', '4', '1', '5', '4', '6', '0', '0', '7', '7', '3', '9', '9', '5', '9', '5', '9', '4', '3', '1', '5', '1', '3', '2', '1', '/', '7', '5', '7', '9', '6', '5', '5', '8', '9', '8', '4', '5', '0', '8', '4', '6', '7', '0', '5', '5', '2', '8', '2', '8', '2', '9', '0', '7', '6', '5', '0', '9', '8', '5', '2', '5', '9', '3', '6', '0', '7', '5', '4', '9', '0', '5', '9', '6', '2', '7', '9', '8', '0', '8', '0', '"', ',']

theorem object_fragment7971030_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment7971030Field006Chars00 ++ tail)) fragment7971030Acc00600 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment7971030Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_006"
  err.flush

noncomputable def fragment7971030Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7971030Field007Value00 : SourceJson := .str (String.ofList ['4', '9', '4', '1', '4', '9', '5', '0', '0', '7', '0', '8', '1', '3', '2', '8', '5', '1', '3', '9', '8', '3', '0', '4', '2', '3', '5', '7', '5', '1', '7', '1', '8', '2', '7', '4', '7', '7', '6', '4', '8', '1', '9', '4', '1', '6', '9', '7', '7', '2', '6', '3', '3', '5', '3', '9', '6', '6', '9', '6', '5', '8', '4', '0', '7', '0', '3', '0', '5', '3', '5', '8', '3', '5', '8', '7', '0', '0', '8', '1', '0', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '6', '0', '5', '4', '9', '1', '9', '6', '0', '6', '2', '4', '1', '8', '4', '2', '6', '0', '2', '3', '6', '8', '5', '8', '5', '3', '0', '3', '2', '7', '8', '1', '1', '2', '4', '1', '9', '7', '5', '0', '2', '0', '2', '5', '1', '8', '5', '3', '1', '6', '2', '1', '4', '2', '7', '9', '2', '3', '6', '7', '9', '1', '8', '7', '8', '4', '7', '6', '1', '9', '2', '1', '4', '6', '7', '4', '1', '0', '2', '3', '7', '3', '1', '8', '9', '3', '1', '5', '2', '4', '0', '3', '5', '2', '9', '5', '0', '7', '0', '7', '1', '1', '2', '1', '2', '6', '4', '0', '5', '3', '3'])
noncomputable def fragment7971030Acc00800 : List (String × SourceJson) := (fragment7971030Field007Key00, fragment7971030Field007Value00) :: fragment7971030Acc00700
noncomputable def fragment7971030Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '9', '4', '1', '4', '9', '5', '0', '0', '7', '0', '8', '1', '3', '2', '8', '5', '1', '3', '9', '8', '3', '0', '4', '2', '3', '5', '7', '5', '1', '7', '1', '8', '2', '7', '4', '7', '7', '6', '4', '8', '1', '9', '4', '1', '6', '9', '7', '7', '2', '6', '3', '3', '5', '3', '9', '6', '6', '9', '6', '5', '8', '4', '0', '7', '0', '3', '0', '5', '3', '5', '8', '3', '5', '8', '7', '0', '0', '8', '1', '0', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '6', '0', '5', '4', '9', '1', '9', '6', '0', '6', '2', '4', '1', '8', '4', '2', '6', '0', '2', '3', '6', '8', '5', '8', '5', '3', '0', '3', '2', '7', '8', '1', '1', '2', '4', '1', '9', '7', '5', '0', '2', '0', '2', '5', '1', '8', '5', '3', '1', '6', '2', '1', '4', '2', '7', '9', '2', '3', '6', '7', '9', '1', '8', '7', '8', '4', '7', '6', '1', '9', '2', '1', '4', '6', '7', '4', '1', '0', '2', '3', '7', '3', '1', '8', '9', '3', '1', '5', '2', '4', '0', '3', '5', '2', '9', '5', '0', '7', '0', '7', '1', '1', '2', '1', '2', '6', '4', '0', '5', '3', '3', '"', ',']

theorem object_fragment7971030_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment7971030Field007Chars00 ++ tail)) fragment7971030Acc00700 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment7971030Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_007"
  err.flush

noncomputable def fragment7971030Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7971030Field008Value00 : SourceJson := .str (String.ofList ['1', '9', '1', '7', '8', '0', '4', '1', '8', '3', '2', '0', '1', '4', '9', '8'])
noncomputable def fragment7971030Acc00900 : List (String × SourceJson) := (fragment7971030Field008Key00, fragment7971030Field008Value00) :: fragment7971030Acc00800
noncomputable def fragment7971030Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '1', '7', '8', '0', '4', '1', '8', '3', '2', '0', '1', '4', '9', '8', '"', ',']

theorem object_fragment7971030_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment7971030Field008Chars00 ++ tail)) fragment7971030Acc00800 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment7971030Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_008"
  err.flush

noncomputable def fragment7971030Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7971030Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '4', '1', '0', '8', '6', '1', '5', '2', '7', '7', '3', '6', '4', '6', '6'])
noncomputable def fragment7971030Acc01000 : List (String × SourceJson) := (fragment7971030Field009Key00, fragment7971030Field009Value00) :: fragment7971030Acc00900
noncomputable def fragment7971030Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '4', '1', '0', '8', '6', '1', '5', '2', '7', '7', '3', '6', '4', '6', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment7971030_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment7971030Field009Chars00 ++ tail)) fragment7971030Acc00900 =
      .ok (.obj (fragment7971030Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7971030_object_field_009"
  err.flush

noncomputable def fragment7971030Chars : List Char := '{' :: (fragment7971030Field000Chars00 ++ fragment7971030Field001Chars00 ++ fragment7971030Field002Chars00 ++ fragment7971030Field003Chars00 ++ fragment7971030Field004Chars00 ++ fragment7971030Field005Chars00 ++ fragment7971030Field006Chars00 ++ fragment7971030Field007Chars00 ++ fragment7971030Field008Chars00 ++ fragment7971030Field009Chars00)
noncomputable def fragment7971030Value : SourceJson := .obj (fragment7971030Acc01000.reverse)

theorem value_fragment7971030 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 225) (fragment7971030Chars ++ tail) =
      .ok (fragment7971030Value, tail) := by
  have hinput : fragment7971030Chars ++ tail = '{' :: (fragment7971030Field000Chars00 ++ (fragment7971030Field001Chars00 ++ (fragment7971030Field002Chars00 ++ (fragment7971030Field003Chars00 ++ (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment7971030Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 225) (fragment7971030Chars ++ tail) =
        SourceJson.value (fuel + 225) ('{' :: (fragment7971030Field000Chars00 ++ (fragment7971030Field001Chars00 ++ (fragment7971030Field002Chars00 ++ (fragment7971030Field003Chars00 ++ (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 225)) hinput
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment7971030Field000Chars00 ++ (fragment7971030Field001Chars00 ++ (fragment7971030Field002Chars00 ++ (fragment7971030Field003Chars00 ++ (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))))))))))) fragment7971030Acc00000 := by rfl
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment7971030Field001Chars00 ++ (fragment7971030Field002Chars00 ++ (fragment7971030Field003Chars00 ++ (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail))))))))))) fragment7971030Acc00100 := object_fragment7971030_field_000 fuel (fragment7971030Field001Chars00 ++ (fragment7971030Field002Chars00 ++ (fragment7971030Field003Chars00 ++ (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment7971030Field002Chars00 ++ (fragment7971030Field003Chars00 ++ (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))))))))) fragment7971030Acc00200 := object_fragment7971030_field_001 fuel (fragment7971030Field002Chars00 ++ (fragment7971030Field003Chars00 ++ (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment7971030Field003Chars00 ++ (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail))))))))) fragment7971030Acc00300 := object_fragment7971030_field_002 fuel (fragment7971030Field003Chars00 ++ (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))))))) fragment7971030Acc00400 := object_fragment7971030_field_003 fuel (fragment7971030Field004Chars00 ++ (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail))))))) fragment7971030Acc00500 := object_fragment7971030_field_004 fuel (fragment7971030Field005Chars00 ++ (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))))) fragment7971030Acc00600 := object_fragment7971030_field_005 fuel (fragment7971030Field006Chars00 ++ (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail))))) fragment7971030Acc00700 := object_fragment7971030_field_006 fuel (fragment7971030Field007Chars00 ++ (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))) fragment7971030Acc00800 := object_fragment7971030_field_007 fuel (fragment7971030Field008Chars00 ++ (fragment7971030Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment7971030Field009Chars00 ++ (tail))) fragment7971030Acc00900 := object_fragment7971030_field_008 fuel (fragment7971030Field009Chars00 ++ (tail))
    _ = .ok (fragment7971030Value, tail) := object_fragment7971030_field_009 fuel (tail)

noncomputable def fragment7972593Acc00000 : List (String × SourceJson) := []

noncomputable def fragment7972593Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment7972593Field000Value00 : SourceJson := .number (String.ofList ['3', '3', '0', '2'])
noncomputable def fragment7972593Acc00100 : List (String × SourceJson) := (fragment7972593Field000Key00, fragment7972593Field000Value00) :: fragment7972593Acc00000
noncomputable def fragment7972593Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '3', '0', '2', ',']

theorem object_fragment7972593_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 480) (SourceJson.white (fragment7972593Field000Chars00 ++ tail)) fragment7972593Acc00000 =
      SourceJson.object (fuel + 479) (SourceJson.white tail) fragment7972593Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_000"
  err.flush

noncomputable def fragment7972593Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment7972593Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '3']), .number (String.ofList ['1', '1', '4']), .number (String.ofList ['1', '1', '3']), .number (String.ofList ['9', '9']), .number (String.ofList ['9', '1']), .number (String.ofList ['6', '2']), .number (String.ofList ['4', '4']), .number (String.ofList ['4', '1'])]
noncomputable def fragment7972593Acc00200 : List (String × SourceJson) := (fragment7972593Field001Key00, fragment7972593Field001Value00) :: fragment7972593Acc00100
noncomputable def fragment7972593Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7972593_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 479) (SourceJson.white (fragment7972593Field001Chars00 ++ tail)) fragment7972593Acc00100 =
      SourceJson.object (fuel + 478) (SourceJson.white tail) fragment7972593Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_001"
  err.flush

noncomputable def fragment7972593Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment7972593Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '2', '2', '6', '4', '3', '4', '9', '3', '2', '9', '7', '9', '9', '8', '1', '6', '4', '5', '9', '1', '9', '4', '5', '7', '8', '4', '4', '9', '5', '5', '1', '9', '3', '2', '7', '/', '3', '1', '3', '4', '4', '5', '0', '4', '6', '8', '7', '8', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7972593Acc00300 : List (String × SourceJson) := (fragment7972593Field002Key00, fragment7972593Field002Value00) :: fragment7972593Acc00200
noncomputable def fragment7972593Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '2', '2', '6', '4', '3', '4', '9', '3', '2', '9', '7', '9', '9', '8', '1', '6', '4', '5', '9', '1', '9', '4', '5', '7', '8', '4', '4', '9', '5', '5', '1', '9', '3', '2', '7', '/', '3', '1', '3', '4', '4', '5', '0', '4', '6', '8', '7', '8', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7972593_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 478) (SourceJson.white (fragment7972593Field002Chars00 ++ tail)) fragment7972593Acc00200 =
      SourceJson.object (fuel + 477) (SourceJson.white tail) fragment7972593Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_002"
  err.flush

noncomputable def fragment7972593Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment7972593Field003Value00 : SourceJson := .str (String.ofList ['1', '6', '8', '1', '0', '8', '9', '9', '2', '6', '9', '/', '6', '8', '4', '3', '4', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7972593Acc00400 : List (String × SourceJson) := (fragment7972593Field003Key00, fragment7972593Field003Value00) :: fragment7972593Acc00300
noncomputable def fragment7972593Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '6', '8', '1', '0', '8', '9', '9', '2', '6', '9', '/', '6', '8', '4', '3', '4', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7972593_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 477) (SourceJson.white (fragment7972593Field003Chars00 ++ tail)) fragment7972593Acc00300 =
      SourceJson.object (fuel + 476) (SourceJson.white tail) fragment7972593Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_003"
  err.flush

noncomputable def fragment7972593Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment7972593Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '9', '5', '3', '0', '7', '3', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '9', '3', '2', '9', '/', '4', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '9', '9', '9', '8', '9', '/', '4', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '3', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '7', '1', '7', '4', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '/', '1', '4', '7', '2']), .str (String.ofList ['4', '9', '/', '1', '4', '7', '2'])]
noncomputable def fragment7972593Acc00500 : List (String × SourceJson) := (fragment7972593Field004Key00, fragment7972593Field004Value00) :: fragment7972593Acc00400
noncomputable def fragment7972593Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '3', '0', '7', '3', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '5', '9', '3', '2', '9', '/', '4', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '9', '9', '9', '8', '9', '/', '4', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '3', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '7', '1', '7', '4', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '/', '1', '4', '7', '2', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '/', '1', '4', '7', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7972593_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment7972593Field004Chars00 ++ tail)) fragment7972593Acc00400 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment7972593Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_004"
  err.flush

noncomputable def fragment7972593Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment7972593Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '5', '1', '4', '1', '8', '3', '0', '0', '7', '2', '3', '3', '3', '3', '5', '5', '2', '8', '2', '7', '5', '1', '6', '7', '/', '1', '3', '6', '9', '0', '2', '4', '1', '2', '6', '8', '7', '7', '9', '7', '3', '7', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '9', '8', '0', '7', '3', '5', '0', '5', '4', '8', '3', '9', '3', '0', '9', '6', '4', '0', '4', '0', '3', '2', '9', '/', '1', '3', '6', '9', '0', '2', '4', '1', '2', '6', '8', '7', '7', '9', '7', '3', '7', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '2', '5', '5', '4', '4', '8', '2', '4', '3', '8', '0', '7', '6', '8', '3', '3', '8', '6', '7', '1', '/', '7', '9', '2', '2', '5', '9', '3', '3', '2', '6', '8', '4', '0', '1', '2', '5', '9', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '1', '8', '5', '6', '0', '1', '4', '6', '1', '5', '6', '7', '5', '8', '8', '4', '2', '2', '1', '9', '9', '/', '2', '4', '0', '1', '7', '9', '6', '7', '1', '3', '8', '2', '1', '0', '0', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '2', '7', '4', '7', '0', '4', '9', '6', '9', '3', '7', '3', '5', '5', '7', '3', '2', '1', '2', '0', '4', '4', '1', '/', '4', '5', '6', '3', '4', '1', '3', '7', '5', '6', '2', '5', '9', '9', '1', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '7', '3', '4', '0', '3', '7', '7', '2', '1', '7', '4', '6', '8', '6', '8', '2', '4', '5', '8', '7', '9', '7', '/', '2', '5', '3', '5', '2', '2', '9', '8', '6', '4', '5', '8', '8', '8', '4', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '0', '0', '0', '2', '4', '3', '2', '3', '0', '5', '5', '6', '0', '3', '3', '7', '6', '1', '2', '6', '0', '9', '7', '/', '9', '1', '2', '6', '8', '2', '7', '5', '1', '2', '5', '1', '9', '8', '2', '5', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '4', '3', '9', '4', '2', '3', '7', '9', '9', '6', '3', '2', '2', '1', '3', '2', '4', '3', '8', '5', '4', '0', '7', '/', '9', '1', '2', '6', '8', '2', '7', '5', '1', '2', '5', '1', '9', '8', '2', '5', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '5', '1', '4', '0', '4', '6', '2', '0', '3', '3', '1', '8', '7', '5', '8', '9', '8', '0', '9', '0', '7', '7', '9', '/', '1', '3', '6', '9', '0', '2', '4', '1', '2', '6', '8', '7', '7', '9', '7', '3', '7', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '7', '6', '0', '5', '6', '5', '8', '1', '8', '2', '3', '9', '3', '8', '7', '1', '8', '1', '3', '6', '2', '3', '/', '4', '5', '6', '3', '4', '1', '3', '7', '5', '6', '2', '5', '9', '9', '1', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7972593Acc00600 : List (String × SourceJson) := (fragment7972593Field005Key00, fragment7972593Field005Value00) :: fragment7972593Acc00500
noncomputable def fragment7972593Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '1', '4', '1', '8', '3', '0', '0', '7', '2', '3', '3', '3', '3', '5', '5', '2', '8', '2', '7', '5', '1', '6', '7', '/', '1', '3', '6', '9', '0', '2', '4', '1', '2', '6', '8', '7', '7', '9', '7', '3', '7', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '9', '8', '0', '7', '3', '5', '0', '5', '4', '8', '3', '9', '3', '0', '9', '6', '4', '0', '4', '0', '3', '2', '9', '/', '1', '3', '6', '9', '0', '2', '4', '1', '2', '6', '8', '7', '7', '9', '7', '3', '7', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '2', '5', '5', '4', '4', '8', '2', '4', '3', '8', '0', '7', '6', '8', '3', '3', '8', '6', '7', '1', '/', '7', '9', '2', '2', '5', '9', '3', '3', '2', '6', '8', '4', '0', '1', '2', '5', '9', '3', '7', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '1', '8', '5', '6', '0', '1', '4', '6', '1', '5', '6', '7', '5', '8', '8', '4', '2', '2', '1', '9', '9', '/', '2', '4', '0', '1', '7', '9', '6', '7', '1', '3', '8', '2', '1', '0', '0', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '7', '4', '7', '0', '4', '9', '6', '9', '3', '7', '3', '5', '5', '7', '3', '2', '1', '2', '0', '4', '4', '1', '/', '4', '5', '6', '3', '4', '1', '3', '7', '5', '6', '2', '5', '9', '9', '1', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '7', '3', '4', '0', '3', '7', '7', '2', '1', '7', '4', '6', '8', '6', '8', '2', '4', '5', '8', '7', '9', '7', '/', '2', '5', '3', '5', '2', '2', '9', '8', '6', '4', '5', '8', '8', '8', '4', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '0', '0', '0', '2', '4', '3', '2', '3', '0', '5', '5', '6', '0', '3', '3', '7', '6', '1', '2', '6', '0', '9', '7', '/', '9', '1', '2', '6', '8', '2', '7', '5', '1', '2', '5', '1', '9', '8', '2', '5', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '4', '3', '9', '4', '2', '3', '7', '9', '9', '6', '3', '2', '2', '1', '3', '2', '4', '3', '8', '5', '4', '0', '7', '/', '9', '1', '2', '6', '8', '2', '7', '5', '1', '2', '5', '1', '9', '8', '2', '5', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '1', '4', '0', '4', '6', '2', '0', '3', '3', '1', '8', '7', '5', '8', '9', '8', '0', '9', '0', '7', '7', '9', '/', '1', '3', '6', '9', '0', '2', '4', '1', '2', '6', '8', '7', '7', '9', '7', '3', '7', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '7', '6', '0', '5', '6', '5', '8', '1', '8', '2', '3', '9', '3', '8', '7', '1', '8', '1', '3', '6', '2', '3', '/', '4', '5', '6', '3', '4', '1', '3', '7', '5', '6', '2', '5', '9', '9', '1', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7972593_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment7972593Field005Chars00 ++ tail)) fragment7972593Acc00500 =
      SourceJson.object (fuel + 474) (SourceJson.white tail) fragment7972593Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_005"
  err.flush

noncomputable def fragment7972593Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7972593Field006Value00 : SourceJson := .str (String.ofList ['3', '5', '2', '9', '0', '9', '7', '1', '4', '9', '5', '6', '3', '3', '7', '8', '8', '7', '5', '4', '2', '2', '8', '8', '8', '1', '2', '9', '4', '0', '0', '9', '0', '4', '2', '8', '1', '0', '6', '3', '9', '3', '9', '4', '0', '2', '7', '9', '2', '8', '/', '9', '0', '2', '2', '7', '1', '1', '7', '9', '2', '6', '3', '1', '3', '3', '2', '8', '8', '0', '0', '0', '7', '4', '7', '8', '4', '1', '0', '8', '5', '3', '4', '7', '4', '1', '0', '0', '8', '8', '3', '6', '7', '2', '5', '9', '8', '8', '8', '3', '1', '3', '9', '2', '7', '9', '9', '2', '2', '2', '1', '8', '7', '5'])
noncomputable def fragment7972593Acc00700 : List (String × SourceJson) := (fragment7972593Field006Key00, fragment7972593Field006Value00) :: fragment7972593Acc00600
noncomputable def fragment7972593Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '5', '2', '9', '0', '9', '7', '1', '4', '9', '5', '6', '3', '3', '7', '8', '8', '7', '5', '4', '2', '2', '8', '8', '8', '1', '2', '9', '4', '0', '0', '9', '0', '4', '2', '8', '1', '0', '6', '3', '9', '3', '9', '4', '0', '2', '7', '9', '2', '8', '/', '9', '0', '2', '2', '7', '1', '1', '7', '9', '2', '6', '3', '1', '3', '3', '2', '8', '8', '0', '0', '0', '7', '4', '7', '8', '4', '1', '0', '8', '5', '3', '4', '7', '4', '1', '0', '0', '8', '8', '3', '6', '7', '2', '5', '9', '8', '8', '8', '3', '1', '3', '9', '2', '7', '9', '9', '2', '2', '2', '1', '8', '7', '5', '"', ',']

theorem object_fragment7972593_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 474) (SourceJson.white (fragment7972593Field006Chars00 ++ tail)) fragment7972593Acc00600 =
      SourceJson.object (fuel + 473) (SourceJson.white tail) fragment7972593Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_006"
  err.flush

noncomputable def fragment7972593Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7972593Field007Value00 : SourceJson := .str (String.ofList ['2', '5', '1', '8', '8', '9', '7', '9', '8', '0', '9', '0', '9', '5', '8', '5', '9', '5', '3', '6', '8', '9', '0', '9', '6', '6', '5', '6', '4', '0', '6', '9', '1', '2', '9', '9', '9', '6', '8', '5', '1', '4', '5', '8', '4', '6', '6', '0', '6', '3', '9', '1', '2', '1', '9', '4', '6', '9', '5', '9', '5', '6', '0', '7', '7', '1', '5', '9', '3', '8', '0', '8', '8', '1', '7', '7', '9', '9', '6', '1', '9', '0', '4', '7', '4', '6', '3', '1', '1', '7', '4', '2', '8', '5', '9', '4', '1', '8', '2', '0', '4', '6', '2', '8', '0', '7', '3', '2', '7', '1', '6', '6', '4', '4', '1', '9', '2', '6', '4', '1', '7', '3', '4', '1', '9', '3', '4', '0', '2', '6', '5', '1', '9', '0', '4', '7', '4', '1', '8', '5', '7', '0', '3', '7', '4', '0', '5', '5', '4', '0', '2', '5', '7', '7', '9', '4', '2', '3', '9', '0', '9', '7', '1', '4', '7', '6', '8', '6', '8', '4', '0', '1', '5', '0', '4', '9', '0', '3', '3', '4', '8', '9', '6', '0', '4', '3', '3', '9', '6', '0', '7', '6', '1', '6', '6', '1', '9', '0', '3', '6', '8', '3', '4', '9', '6', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '5', '8', '6', '7', '8', '3', '3', '7', '8', '1', '7', '4', '6', '9', '1', '7', '3', '8', '4', '7', '6', '1', '6', '9', '0', '8', '4', '7', '9', '4', '5', '2', '5', '0', '1', '4', '2', '8', '7', '0', '4', '1', '6', '0', '3', '1', '7', '6', '8', '0', '3', '0', '4', '3', '5', '5', '5', '5', '9', '7', '8', '6', '6', '9', '6', '2', '1', '3', '6', '9', '8', '7', '7', '9', '2', '9', '7', '2', '8', '8', '8', '4', '4', '6', '8', '0', '4', '4', '0', '5', '1', '1', '3', '5', '5', '3', '8', '4', '6', '6', '2', '9', '9', '8', '1', '5', '7', '2', '1', '5', '1', '1', '9', '9', '0', '4', '0', '0', '4', '7', '1', '8', '2', '3', '1', '2', '8', '0', '0', '3', '6', '1', '1', '4', '6', '3', '6', '8', '4', '3', '0', '9', '4', '6', '0', '0', '5', '4', '1', '3', '4', '9', '3', '9', '0', '7', '1', '1', '7', '6', '9', '4', '4', '1', '4', '9', '8', '4', '7', '1', '0', '5', '6', '4', '2', '4', '3', '2', '2', '3', '0', '2', '9', '4', '9', '6', '9', '9', '1', '0', '6', '4', '8', '5', '1', '1', '3', '8', '7', '6', '5', '1', '2', '6', '5', '9', '9', '4', '2', '0', '8', '5', '4', '8', '7', '0', '6', '9', '6', '2', '6', '4', '7', '1', '1', '3', '1', '2', '0', '4', '4', '4', '2', '2', '0', '5', '3', '3', '9'])
noncomputable def fragment7972593Acc00800 : List (String × SourceJson) := (fragment7972593Field007Key00, fragment7972593Field007Value00) :: fragment7972593Acc00700
noncomputable def fragment7972593Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '5', '1', '8', '8', '9', '7', '9', '8', '0', '9', '0', '9', '5', '8', '5', '9', '5', '3', '6', '8', '9', '0', '9', '6', '6', '5', '6', '4', '0', '6', '9', '1', '2', '9', '9', '9', '6', '8', '5', '1', '4', '5', '8', '4', '6', '6', '0', '6', '3', '9', '1', '2', '1', '9', '4', '6', '9', '5', '9', '5', '6', '0', '7', '7', '1', '5', '9', '3', '8', '0', '8', '8', '1', '7', '7', '9', '9', '6', '1', '9', '0', '4', '7', '4', '6', '3', '1', '1', '7', '4', '2', '8', '5', '9', '4', '1', '8', '2', '0', '4', '6', '2', '8', '0', '7', '3', '2', '7', '1', '6', '6', '4', '4', '1', '9', '2', '6', '4', '1', '7', '3', '4', '1', '9', '3', '4', '0', '2', '6', '5', '1', '9', '0', '4', '7', '4', '1', '8', '5', '7', '0', '3', '7', '4', '0', '5', '5', '4', '0', '2', '5', '7', '7', '9', '4', '2', '3', '9', '0', '9', '7', '1', '4', '7', '6', '8', '6', '8', '4', '0', '1', '5', '0', '4', '9', '0', '3', '3', '4', '8', '9', '6', '0', '4', '3', '3', '9', '6', '0', '7', '6', '1', '6', '6', '1', '9', '0', '3', '6', '8', '3', '4', '9', '6', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '5', '8', '6', '7', '8', '3', '3', '7', '8', '1', '7', '4', '6', '9', '1', '7', '3', '8', '4', '7', '6', '1', '6', '9', '0', '8', '4', '7', '9', '4', '5', '2', '5', '0', '1', '4', '2', '8', '7', '0', '4', '1', '6', '0', '3', '1', '7', '6', '8', '0', '3', '0', '4', '3', '5', '5', '5', '5', '9', '7', '8', '6', '6', '9', '6', '2', '1', '3', '6', '9', '8', '7', '7', '9', '2', '9', '7', '2', '8', '8', '8', '4', '4', '6', '8', '0', '4', '4', '0', '5', '1', '1', '3', '5', '5', '3', '8', '4', '6', '6', '2', '9', '9', '8', '1', '5', '7', '2', '1', '5', '1', '1', '9', '9', '0', '4', '0', '0', '4', '7', '1', '8', '2', '3', '1', '2', '8', '0', '0', '3', '6', '1', '1', '4', '6', '3', '6', '8', '4', '3', '0', '9', '4', '6', '0', '0', '5', '4', '1', '3', '4', '9', '3', '9', '0', '7', '1', '1', '7', '6', '9', '4', '4', '1', '4', '9', '8', '4', '7', '1', '0', '5', '6', '4', '2', '4', '3', '2', '2', '3', '0', '2', '9', '4', '9', '6', '9', '9', '1', '0', '6', '4', '8', '5', '1', '1', '3', '8', '7', '6', '5', '1', '2', '6', '5', '9', '9', '4', '2', '0', '8', '5', '4', '8', '7', '0', '6', '9', '6', '2', '6', '4', '7', '1', '1', '3', '1', '2', '0', '4', '4', '4', '2', '2', '0', '5', '3', '3', '9', '"', ',']

theorem object_fragment7972593_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 473) (SourceJson.white (fragment7972593Field007Chars00 ++ tail)) fragment7972593Acc00700 =
      SourceJson.object (fuel + 472) (SourceJson.white tail) fragment7972593Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_007"
  err.flush

noncomputable def fragment7972593Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7972593Field008Value00 : SourceJson := .str (String.ofList ['3', '0', '9', '8', '8', '8', '9', '6', '5', '6', '6', '8', '3', '7', '1', '7'])
noncomputable def fragment7972593Acc00900 : List (String × SourceJson) := (fragment7972593Field008Key00, fragment7972593Field008Value00) :: fragment7972593Acc00800
noncomputable def fragment7972593Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '9', '8', '8', '8', '9', '6', '5', '6', '6', '8', '3', '7', '1', '7', '"', ',']

theorem object_fragment7972593_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment7972593Field008Chars00 ++ tail)) fragment7972593Acc00800 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment7972593Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_008"
  err.flush

noncomputable def fragment7972593Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7972593Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '1', '8', '8', '8', '9', '3', '9', '4', '6', '2', '4', '8', '0', '9', '7'])
noncomputable def fragment7972593Acc01000 : List (String × SourceJson) := (fragment7972593Field009Key00, fragment7972593Field009Value00) :: fragment7972593Acc00900
noncomputable def fragment7972593Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '1', '8', '8', '8', '9', '3', '9', '4', '6', '2', '4', '8', '0', '9', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment7972593_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment7972593Field009Chars00 ++ tail)) fragment7972593Acc00900 =
      .ok (.obj (fragment7972593Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7972593_object_field_009"
  err.flush

noncomputable def fragment7972593Chars : List Char := '{' :: (fragment7972593Field000Chars00 ++ fragment7972593Field001Chars00 ++ fragment7972593Field002Chars00 ++ fragment7972593Field003Chars00 ++ fragment7972593Field004Chars00 ++ fragment7972593Field005Chars00 ++ fragment7972593Field006Chars00 ++ fragment7972593Field007Chars00 ++ fragment7972593Field008Chars00 ++ fragment7972593Field009Chars00)
noncomputable def fragment7972593Value : SourceJson := .obj (fragment7972593Acc01000.reverse)

theorem value_fragment7972593 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 481) (fragment7972593Chars ++ tail) =
      .ok (fragment7972593Value, tail) := by
  have hinput : fragment7972593Chars ++ tail = '{' :: (fragment7972593Field000Chars00 ++ (fragment7972593Field001Chars00 ++ (fragment7972593Field002Chars00 ++ (fragment7972593Field003Chars00 ++ (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment7972593Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 481) (fragment7972593Chars ++ tail) =
        SourceJson.value (fuel + 481) ('{' :: (fragment7972593Field000Chars00 ++ (fragment7972593Field001Chars00 ++ (fragment7972593Field002Chars00 ++ (fragment7972593Field003Chars00 ++ (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 481)) hinput
    _ = SourceJson.object (fuel + 480) (SourceJson.white (fragment7972593Field000Chars00 ++ (fragment7972593Field001Chars00 ++ (fragment7972593Field002Chars00 ++ (fragment7972593Field003Chars00 ++ (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))))))))))) fragment7972593Acc00000 := by rfl
    _ = SourceJson.object (fuel + 479) (SourceJson.white (fragment7972593Field001Chars00 ++ (fragment7972593Field002Chars00 ++ (fragment7972593Field003Chars00 ++ (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail))))))))))) fragment7972593Acc00100 := object_fragment7972593_field_000 fuel (fragment7972593Field001Chars00 ++ (fragment7972593Field002Chars00 ++ (fragment7972593Field003Chars00 ++ (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 478) (SourceJson.white (fragment7972593Field002Chars00 ++ (fragment7972593Field003Chars00 ++ (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))))))))) fragment7972593Acc00200 := object_fragment7972593_field_001 fuel (fragment7972593Field002Chars00 ++ (fragment7972593Field003Chars00 ++ (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 477) (SourceJson.white (fragment7972593Field003Chars00 ++ (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail))))))))) fragment7972593Acc00300 := object_fragment7972593_field_002 fuel (fragment7972593Field003Chars00 ++ (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))))))) fragment7972593Acc00400 := object_fragment7972593_field_003 fuel (fragment7972593Field004Chars00 ++ (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail))))))) fragment7972593Acc00500 := object_fragment7972593_field_004 fuel (fragment7972593Field005Chars00 ++ (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 474) (SourceJson.white (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))))) fragment7972593Acc00600 := object_fragment7972593_field_005 fuel (fragment7972593Field006Chars00 ++ (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 473) (SourceJson.white (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail))))) fragment7972593Acc00700 := object_fragment7972593_field_006 fuel (fragment7972593Field007Chars00 ++ (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))) fragment7972593Acc00800 := object_fragment7972593_field_007 fuel (fragment7972593Field008Chars00 ++ (fragment7972593Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment7972593Field009Chars00 ++ (tail))) fragment7972593Acc00900 := object_fragment7972593_field_008 fuel (fragment7972593Field009Chars00 ++ (tail))
    _ = .ok (fragment7972593Value, tail) := object_fragment7972593_field_009 fuel (tail)

noncomputable def fragment7974678Acc00000 : List (String × SourceJson) := []

noncomputable def fragment7974678Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment7974678Field000Value00 : SourceJson := .number (String.ofList ['3', '3', '0', '3'])
noncomputable def fragment7974678Acc00100 : List (String × SourceJson) := (fragment7974678Field000Key00, fragment7974678Field000Value00) :: fragment7974678Acc00000
noncomputable def fragment7974678Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '3', '0', '3', ',']

theorem object_fragment7974678_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 504) (SourceJson.white (fragment7974678Field000Chars00 ++ tail)) fragment7974678Acc00000 =
      SourceJson.object (fuel + 503) (SourceJson.white tail) fragment7974678Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_000"
  err.flush

noncomputable def fragment7974678Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment7974678Field001Value00 : SourceJson := .arr [.number (String.ofList ['1', '3', '9']), .number (String.ofList ['1', '3', '3']), .number (String.ofList ['1', '1', '4']), .number (String.ofList ['1', '1', '3']), .number (String.ofList ['9', '9']), .number (String.ofList ['9', '1']), .number (String.ofList ['6', '2']), .number (String.ofList ['5', '7']), .number (String.ofList ['4', '1'])]
noncomputable def fragment7974678Acc00200 : List (String × SourceJson) := (fragment7974678Field001Key00, fragment7974678Field001Value00) :: fragment7974678Acc00100
noncomputable def fragment7974678Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7974678_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 503) (SourceJson.white (fragment7974678Field001Chars00 ++ tail)) fragment7974678Acc00100 =
      SourceJson.object (fuel + 502) (SourceJson.white tail) fragment7974678Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_001"
  err.flush

noncomputable def fragment7974678Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment7974678Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '1', '7', '9', '2', '5', '5', '4', '2', '6', '5', '4', '0', '4', '0', '2', '9', '0', '4', '0', '6', '8', '1', '4', '0', '7', '3', '7', '8', '5', '3', '1', '0', '7', '6', '1', '8', '8', '1', '/', '1', '3', '0', '0', '9', '1', '9', '3', '8', '4', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7974678Acc00300 : List (String × SourceJson) := (fragment7974678Field002Key00, fragment7974678Field002Value00) :: fragment7974678Acc00200
noncomputable def fragment7974678Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '1', '7', '9', '2', '5', '5', '4', '2', '6', '5', '4', '0', '4', '0', '2', '9', '0', '4', '0', '6', '8', '1', '4', '0', '7', '3', '7', '8', '5', '3', '1', '0', '7', '6', '1', '8', '8', '1', '/', '1', '3', '0', '0', '9', '1', '9', '3', '8', '4', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7974678_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 502) (SourceJson.white (fragment7974678Field002Chars00 ++ tail)) fragment7974678Acc00200 =
      SourceJson.object (fuel + 501) (SourceJson.white tail) fragment7974678Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_002"
  err.flush

noncomputable def fragment7974678Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment7974678Field003Value00 : SourceJson := .str (String.ofList ['1', '3', '0', '5', '9', '2', '3', '0', '2', '0', '6', '1', '/', '5', '8', '6', '1', '5', '3', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment7974678Acc00400 : List (String × SourceJson) := (fragment7974678Field003Key00, fragment7974678Field003Value00) :: fragment7974678Acc00300
noncomputable def fragment7974678Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '3', '0', '5', '9', '2', '3', '0', '2', '0', '6', '1', '/', '5', '8', '6', '1', '5', '3', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment7974678_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 501) (SourceJson.white (fragment7974678Field003Chars00 ++ tail)) fragment7974678Acc00300 =
      SourceJson.object (fuel + 500) (SourceJson.white tail) fragment7974678Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_003"
  err.flush

noncomputable def fragment7974678Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment7974678Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '9', '5', '3', '0', '7', '3', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '3', '0', '7', '3', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '9', '9', '9', '8', '9', '/', '4', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '3', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '1', '8', '7', '1', '7', '/', '9', '8', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '/', '3', '3', '6']), .str (String.ofList ['1', '1', '/', '3', '3', '6'])]
noncomputable def fragment7974678Acc00500 : List (String × SourceJson) := (fragment7974678Field004Key00, fragment7974678Field004Value00) :: fragment7974678Acc00400
noncomputable def fragment7974678Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '3', '0', '7', '3', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '3', '0', '7', '3', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '1', '/', '1', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '4', '3', '7', '1', '/', '2', '7', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '9', '9', '9', '8', '9', '/', '4', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '3', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '1', '8', '7', '1', '7', '/', '9', '8', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '3', '6', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '/', '3', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7974678_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 500) (SourceJson.white (fragment7974678Field004Chars00 ++ tail)) fragment7974678Acc00400 =
      SourceJson.object (fuel + 499) (SourceJson.white tail) fragment7974678Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_004"
  err.flush

noncomputable def fragment7974678Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment7974678Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '2', '6', '0', '9', '1', '8', '9', '7', '1', '9', '7', '8', '0', '7', '9', '1', '7', '4', '3', '4', '8', '9', '2', '5', '1', '/', '1', '3', '0', '1', '3', '0', '1', '9', '5', '9', '7', '6', '4', '6', '5', '0', '6', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '9', '0', '6', '7', '5', '6', '3', '9', '7', '6', '6', '2', '2', '0', '0', '1', '8', '1', '2', '2', '7', '3', '5', '7', '/', '1', '3', '0', '1', '3', '0', '1', '9', '5', '9', '7', '6', '4', '6', '5', '0', '6', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '4', '3', '6', '8', '4', '1', '9', '7', '2', '6', '1', '3', '5', '8', '8', '6', '3', '2', '1', '1', '2', '9', '7', '/', '4', '8', '1', '9', '6', '3', '6', '8', '8', '8', '0', '1', '7', '2', '2', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '1', '2', '7', '9', '8', '5', '4', '1', '9', '8', '5', '6', '6', '7', '0', '7', '1', '9', '5', '7', '1', '1', '/', '1', '1', '4', '1', '4', '9', '2', '9', '4', '7', '1', '6', '1', '9', '7', '4', '2', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '5', '9', '3', '0', '9', '2', '8', '6', '4', '8', '4', '6', '4', '0', '8', '7', '9', '9', '6', '7', '9', '7', '9', '9', '/', '2', '1', '6', '8', '8', '3', '6', '5', '9', '9', '6', '0', '7', '7', '5', '1', '1', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '5', '1', '2', '2', '3', '4', '0', '6', '8', '3', '6', '6', '5', '2', '0', '7', '7', '9', '8', '3', '6', '6', '7', '/', '4', '8', '1', '9', '6', '3', '6', '8', '8', '8', '0', '1', '7', '2', '2', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '3', '6', '0', '3', '1', '0', '2', '6', '8', '3', '9', '9', '8', '3', '1', '4', '9', '4', '9', '6', '7', '9', '3', '/', '4', '3', '3', '7', '6', '7', '3', '1', '9', '9', '2', '1', '5', '5', '0', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '7', '9', '7', '3', '9', '9', '8', '6', '8', '2', '1', '9', '6', '4', '2', '2', '5', '3', '2', '5', '5', '7', '7', '/', '1', '0', '8', '4', '4', '1', '8', '2', '9', '9', '8', '0', '3', '8', '7', '5', '5', '7', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '2', '5', '9', '7', '9', '8', '1', '1', '0', '0', '2', '0', '3', '9', '7', '4', '1', '6', '3', '4', '0', '2', '0', '7', '/', '1', '3', '0', '1', '3', '0', '1', '9', '5', '9', '7', '6', '4', '6', '5', '0', '6', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '8', '3', '7', '6', '8', '6', '3', '5', '7', '0', '0', '8', '1', '0', '2', '8', '7', '7', '5', '0', '4', '5', '9', '/', '4', '3', '3', '7', '6', '7', '3', '1', '9', '9', '2', '1', '5', '5', '0', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment7974678Acc00600 : List (String × SourceJson) := (fragment7974678Field005Key00, fragment7974678Field005Value00) :: fragment7974678Acc00500
noncomputable def fragment7974678Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '6', '0', '9', '1', '8', '9', '7', '1', '9', '7', '8', '0', '7', '9', '1', '7', '4', '3', '4', '8', '9', '2', '5', '1', '/', '1', '3', '0', '1', '3', '0', '1', '9', '5', '9', '7', '6', '4', '6', '5', '0', '6', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '9', '0', '6', '7', '5', '6', '3', '9', '7', '6', '6', '2', '2', '0', '0', '1', '8', '1', '2', '2', '7', '3', '5', '7', '/', '1', '3', '0', '1', '3', '0', '1', '9', '5', '9', '7', '6', '4', '6', '5', '0', '6', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '4', '3', '6', '8', '4', '1', '9', '7', '2', '6', '1', '3', '5', '8', '8', '6', '3', '2', '1', '1', '2', '9', '7', '/', '4', '8', '1', '9', '6', '3', '6', '8', '8', '8', '0', '1', '7', '2', '2', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '1', '2', '7', '9', '8', '5', '4', '1', '9', '8', '5', '6', '6', '7', '0', '7', '1', '9', '5', '7', '1', '1', '/', '1', '1', '4', '1', '4', '9', '2', '9', '4', '7', '1', '6', '1', '9', '7', '4', '2', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '9', '3', '0', '9', '2', '8', '6', '4', '8', '4', '6', '4', '0', '8', '7', '9', '9', '6', '7', '9', '7', '9', '9', '/', '2', '1', '6', '8', '8', '3', '6', '5', '9', '9', '6', '0', '7', '7', '5', '1', '1', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '5', '1', '2', '2', '3', '4', '0', '6', '8', '3', '6', '6', '5', '2', '0', '7', '7', '9', '8', '3', '6', '6', '7', '/', '4', '8', '1', '9', '6', '3', '6', '8', '8', '8', '0', '1', '7', '2', '2', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '3', '6', '0', '3', '1', '0', '2', '6', '8', '3', '9', '9', '8', '3', '1', '4', '9', '4', '9', '6', '7', '9', '3', '/', '4', '3', '3', '7', '6', '7', '3', '1', '9', '9', '2', '1', '5', '5', '0', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '7', '9', '7', '3', '9', '9', '8', '6', '8', '2', '1', '9', '6', '4', '2', '2', '5', '3', '2', '5', '5', '7', '7', '/', '1', '0', '8', '4', '4', '1', '8', '2', '9', '9', '8', '0', '3', '8', '7', '5', '5', '7', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '2', '5', '9', '7', '9', '8', '1', '1', '0', '0', '2', '0', '3', '9', '7', '4', '1', '6', '3', '4', '0', '2', '0', '7', '/', '1', '3', '0', '1', '3', '0', '1', '9', '5', '9', '7', '6', '4', '6', '5', '0', '6', '9', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '8', '3', '7', '6', '8', '6', '3', '5', '7', '0', '0', '8', '1', '0', '2', '8', '7', '7', '5', '0', '4', '5', '9', '/', '4', '3', '3', '7', '6', '7', '3', '1', '9', '9', '2', '1', '5', '5', '0', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment7974678_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 499) (SourceJson.white (fragment7974678Field005Chars00 ++ tail)) fragment7974678Acc00500 =
      SourceJson.object (fuel + 498) (SourceJson.white tail) fragment7974678Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_005"
  err.flush

noncomputable def fragment7974678Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7974678Field006Value00 : SourceJson := .str (String.ofList ['7', '9', '3', '0', '4', '3', '5', '6', '7', '6', '8', '5', '0', '4', '0', '3', '0', '0', '5', '2', '2', '8', '9', '2', '2', '1', '5', '4', '1', '0', '6', '6', '1', '8', '8', '8', '1', '7', '2', '2', '8', '5', '4', '5', '7', '5', '2', '5', '2', '2', '4', '/', '5', '7', '5', '2', '4', '9', '5', '3', '6', '7', '6', '6', '8', '2', '6', '6', '1', '2', '4', '5', '1', '2', '7', '3', '2', '8', '7', '1', '8', '3', '4', '1', '4', '2', '3', '6', '4', '2', '1', '4', '1', '2', '1', '0', '6', '5', '0', '1', '0', '0', '6', '3', '7', '8', '5', '3', '2', '7', '1', '4', '8', '4', '3', '7', '5'])
noncomputable def fragment7974678Acc00700 : List (String × SourceJson) := (fragment7974678Field006Key00, fragment7974678Field006Value00) :: fragment7974678Acc00600
noncomputable def fragment7974678Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '9', '3', '0', '4', '3', '5', '6', '7', '6', '8', '5', '0', '4', '0', '3', '0', '0', '5', '2', '2', '8', '9', '2', '2', '1', '5', '4', '1', '0', '6', '6', '1', '8', '8', '8', '1', '7', '2', '2', '8', '5', '4', '5', '7', '5', '2', '5', '2', '2', '4', '/', '5', '7', '5', '2', '4', '9', '5', '3', '6', '7', '6', '6', '8', '2', '6', '6', '1', '2', '4', '5', '1', '2', '7', '3', '2', '8', '7', '1', '8', '3', '4', '1', '4', '2', '3', '6', '4', '2', '1', '4', '1', '2', '1', '0', '6', '5', '0', '1', '0', '0', '6', '3', '7', '8', '5', '3', '2', '7', '1', '4', '8', '4', '3', '7', '5', '"', ',']

theorem object_fragment7974678_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 498) (SourceJson.white (fragment7974678Field006Chars00 ++ tail)) fragment7974678Acc00600 =
      SourceJson.object (fuel + 497) (SourceJson.white tail) fragment7974678Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_006"
  err.flush

noncomputable def fragment7974678Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment7974678Field007Value00 : SourceJson := .str (String.ofList ['1', '4', '9', '1', '0', '4', '0', '5', '9', '9', '8', '2', '3', '3', '8', '8', '8', '1', '0', '8', '4', '6', '8', '9', '3', '6', '5', '8', '0', '6', '9', '3', '9', '4', '0', '1', '0', '7', '5', '8', '3', '7', '8', '5', '3', '7', '2', '8', '5', '6', '3', '8', '3', '2', '6', '0', '5', '5', '1', '9', '6', '3', '3', '6', '5', '7', '8', '3', '6', '1', '4', '8', '1', '1', '0', '8', '2', '2', '2', '5', '9', '3', '3', '6', '8', '5', '1', '3', '1', '1', '5', '6', '4', '9', '6', '2', '1', '1', '2', '7', '5', '5', '8', '6', '2', '4', '8', '6', '4', '7', '7', '6', '6', '6', '9', '9', '0', '4', '5', '0', '6', '5', '4', '7', '9', '7', '1', '1', '2', '1', '3', '8', '9', '3', '9', '6', '8', '8', '8', '0', '9', '9', '6', '5', '7', '7', '3', '7', '6', '6', '5', '2', '1', '7', '1', '3', '0', '2', '5', '2', '9', '0', '8', '7', '1', '5', '5', '3', '9', '1', '5', '0', '8', '2', '2', '3', '6', '2', '3', '5', '3', '3', '2', '8', '6', '5', '1', '6', '4', '0', '6', '6', '9', '1', '0', '6', '1', '3', '1', '2', '8', '3', '8', '5', '1', '6', '9', '2', '3', '4', '7', '7', '6', '0', '8', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '6', '8', '8', '4', '0', '0', '5', '9', '6', '2', '0', '7', '4', '4', '6', '2', '0', '6', '8', '1', '4', '9', '0', '9', '9', '7', '7', '5', '1', '3', '0', '6', '3', '6', '2', '3', '9', '5', '9', '6', '3', '5', '6', '8', '8', '3', '7', '1', '3', '0', '9', '2', '3', '7', '8', '7', '8', '3', '4', '4', '5', '9', '6', '1', '6', '8', '1', '3', '2', '0', '5', '4', '7', '8', '6', '4', '7', '1', '9', '9', '7', '2', '4', '4', '6', '0', '0', '6', '5', '4', '9', '0', '5', '3', '4', '7', '0', '5', '4', '0', '1', '0', '9', '2', '9', '6', '9', '5', '9', '4', '6', '6', '7', '5', '6', '1', '7', '9', '3', '3', '7', '0', '4', '2', '6', '2', '7', '9', '3', '9', '6', '3', '8', '0', '0', '2', '7', '0', '1', '7', '7', '3', '0', '2', '6', '7', '8', '9', '3', '4', '7', '9', '1', '9', '0', '4', '0', '5', '4', '9', '4', '6', '4', '6', '1', '6', '1', '0', '4', '7', '2', '1', '0', '3', '9', '3', '8', '7', '0', '4', '5', '3', '6', '3', '4', '1', '9', '4', '5', '2', '9', '3', '5', '4', '2', '7', '9', '5', '4', '3', '0', '1', '0', '3', '6', '3', '9', '4', '3', '7', '2', '4', '3', '1', '2', '8', '4', '7', '6', '7', '1', '5', '4', '3', '1', '5', '6', '0', '5', '5', '4', '5', '4', '3', '8', '2', '3', '3', '0', '5', '3', '3', '0', '8', '9', '8', '5', '5', '8', '8', '9'])
noncomputable def fragment7974678Acc00800 : List (String × SourceJson) := (fragment7974678Field007Key00, fragment7974678Field007Value00) :: fragment7974678Acc00700
noncomputable def fragment7974678Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '9', '1', '0', '4', '0', '5', '9', '9', '8', '2', '3', '3', '8', '8', '8', '1', '0', '8', '4', '6', '8', '9', '3', '6', '5', '8', '0', '6', '9', '3', '9', '4', '0', '1', '0', '7', '5', '8', '3', '7', '8', '5', '3', '7', '2', '8', '5', '6', '3', '8', '3', '2', '6', '0', '5', '5', '1', '9', '6', '3', '3', '6', '5', '7', '8', '3', '6', '1', '4', '8', '1', '1', '0', '8', '2', '2', '2', '5', '9', '3', '3', '6', '8', '5', '1', '3', '1', '1', '5', '6', '4', '9', '6', '2', '1', '1', '2', '7', '5', '5', '8', '6', '2', '4', '8', '6', '4', '7', '7', '6', '6', '6', '9', '9', '0', '4', '5', '0', '6', '5', '4', '7', '9', '7', '1', '1', '2', '1', '3', '8', '9', '3', '9', '6', '8', '8', '8', '0', '9', '9', '6', '5', '7', '7', '3', '7', '6', '6', '5', '2', '1', '7', '1', '3', '0', '2', '5', '2', '9', '0', '8', '7', '1', '5', '5', '3', '9', '1', '5', '0', '8', '2', '2', '3', '6', '2', '3', '5', '3', '3', '2', '8', '6', '5', '1', '6', '4', '0', '6', '6', '9', '1', '0', '6', '1', '3', '1', '2', '8', '3', '8', '5', '1', '6', '9', '2', '3', '4', '7', '7', '6', '0', '8', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '6', '8', '8', '4', '0', '0', '5', '9', '6', '2', '0', '7', '4', '4', '6', '2', '0', '6', '8', '1', '4', '9', '0', '9', '9', '7', '7', '5', '1', '3', '0', '6', '3', '6', '2', '3', '9', '5', '9', '6', '3', '5', '6', '8', '8', '3', '7', '1', '3', '0', '9', '2', '3', '7', '8', '7', '8', '3', '4', '4', '5', '9', '6', '1', '6', '8', '1', '3', '2', '0', '5', '4', '7', '8', '6', '4', '7', '1', '9', '9', '7', '2', '4', '4', '6', '0', '0', '6', '5', '4', '9', '0', '5', '3', '4', '7', '0', '5', '4', '0', '1', '0', '9', '2', '9', '6', '9', '5', '9', '4', '6', '6', '7', '5', '6', '1', '7', '9', '3', '3', '7', '0', '4', '2', '6', '2', '7', '9', '3', '9', '6', '3', '8', '0', '0', '2', '7', '0', '1', '7', '7', '3', '0', '2', '6', '7', '8', '9', '3', '4', '7', '9', '1', '9', '0', '4', '0', '5', '4', '9', '4', '6', '4', '6', '1', '6', '1', '0', '4', '7', '2', '1', '0', '3', '9', '3', '8', '7', '0', '4', '5', '3', '6', '3', '4', '1', '9', '4', '5', '2', '9', '3', '5', '4', '2', '7', '9', '5', '4', '3', '0', '1', '0', '3', '6', '3', '9', '4', '3', '7', '2', '4', '3', '1', '2', '8', '4', '7', '6', '7', '1', '5', '4', '3', '1', '5', '6', '0', '5', '5', '4', '5', '4', '3', '8', '2', '3', '3', '0', '5', '3', '3', '0', '8', '9', '8', '5', '5', '8', '8', '9', '"', ',']

theorem object_fragment7974678_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 497) (SourceJson.white (fragment7974678Field007Chars00 ++ tail)) fragment7974678Acc00700 =
      SourceJson.object (fuel + 496) (SourceJson.white tail) fragment7974678Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_007"
  err.flush

noncomputable def fragment7974678Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7974678Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '9', '2', '2', '4', '5', '7', '2', '3', '7', '3', '5', '5', '5', '2'])
noncomputable def fragment7974678Acc00900 : List (String × SourceJson) := (fragment7974678Field008Key00, fragment7974678Field008Value00) :: fragment7974678Acc00800
noncomputable def fragment7974678Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '9', '2', '2', '4', '5', '7', '2', '3', '7', '3', '5', '5', '5', '2', '"', ',']

theorem object_fragment7974678_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 496) (SourceJson.white (fragment7974678Field008Chars00 ++ tail)) fragment7974678Acc00800 =
      SourceJson.object (fuel + 495) (SourceJson.white tail) fragment7974678Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_008"
  err.flush

noncomputable def fragment7974678Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment7974678Field009Value00 : SourceJson := .str (String.ofList ['3', '5', '0', '6', '6', '1', '9', '6', '3', '3', '6', '8', '6', '9', '9', '2'])
noncomputable def fragment7974678Acc01000 : List (String × SourceJson) := (fragment7974678Field009Key00, fragment7974678Field009Value00) :: fragment7974678Acc00900
noncomputable def fragment7974678Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '5', '0', '6', '6', '1', '9', '6', '3', '3', '6', '8', '6', '9', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment7974678_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 495) (SourceJson.white (fragment7974678Field009Chars00 ++ tail)) fragment7974678Acc00900 =
      .ok (.obj (fragment7974678Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment7974678_object_field_009"
  err.flush

noncomputable def fragment7974678Chars : List Char := '{' :: (fragment7974678Field000Chars00 ++ fragment7974678Field001Chars00 ++ fragment7974678Field002Chars00 ++ fragment7974678Field003Chars00 ++ fragment7974678Field004Chars00 ++ fragment7974678Field005Chars00 ++ fragment7974678Field006Chars00 ++ fragment7974678Field007Chars00 ++ fragment7974678Field008Chars00 ++ fragment7974678Field009Chars00)
noncomputable def fragment7974678Value : SourceJson := .obj (fragment7974678Acc01000.reverse)

theorem value_fragment7974678 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 505) (fragment7974678Chars ++ tail) =
      .ok (fragment7974678Value, tail) := by
  have hinput : fragment7974678Chars ++ tail = '{' :: (fragment7974678Field000Chars00 ++ (fragment7974678Field001Chars00 ++ (fragment7974678Field002Chars00 ++ (fragment7974678Field003Chars00 ++ (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment7974678Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 505) (fragment7974678Chars ++ tail) =
        SourceJson.value (fuel + 505) ('{' :: (fragment7974678Field000Chars00 ++ (fragment7974678Field001Chars00 ++ (fragment7974678Field002Chars00 ++ (fragment7974678Field003Chars00 ++ (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 505)) hinput
    _ = SourceJson.object (fuel + 504) (SourceJson.white (fragment7974678Field000Chars00 ++ (fragment7974678Field001Chars00 ++ (fragment7974678Field002Chars00 ++ (fragment7974678Field003Chars00 ++ (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))))))))))) fragment7974678Acc00000 := by rfl
    _ = SourceJson.object (fuel + 503) (SourceJson.white (fragment7974678Field001Chars00 ++ (fragment7974678Field002Chars00 ++ (fragment7974678Field003Chars00 ++ (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail))))))))))) fragment7974678Acc00100 := object_fragment7974678_field_000 fuel (fragment7974678Field001Chars00 ++ (fragment7974678Field002Chars00 ++ (fragment7974678Field003Chars00 ++ (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 502) (SourceJson.white (fragment7974678Field002Chars00 ++ (fragment7974678Field003Chars00 ++ (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))))))))) fragment7974678Acc00200 := object_fragment7974678_field_001 fuel (fragment7974678Field002Chars00 ++ (fragment7974678Field003Chars00 ++ (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 501) (SourceJson.white (fragment7974678Field003Chars00 ++ (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail))))))))) fragment7974678Acc00300 := object_fragment7974678_field_002 fuel (fragment7974678Field003Chars00 ++ (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 500) (SourceJson.white (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))))))) fragment7974678Acc00400 := object_fragment7974678_field_003 fuel (fragment7974678Field004Chars00 ++ (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 499) (SourceJson.white (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail))))))) fragment7974678Acc00500 := object_fragment7974678_field_004 fuel (fragment7974678Field005Chars00 ++ (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 498) (SourceJson.white (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))))) fragment7974678Acc00600 := object_fragment7974678_field_005 fuel (fragment7974678Field006Chars00 ++ (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 497) (SourceJson.white (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail))))) fragment7974678Acc00700 := object_fragment7974678_field_006 fuel (fragment7974678Field007Chars00 ++ (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 496) (SourceJson.white (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))) fragment7974678Acc00800 := object_fragment7974678_field_007 fuel (fragment7974678Field008Chars00 ++ (fragment7974678Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 495) (SourceJson.white (fragment7974678Field009Chars00 ++ (tail))) fragment7974678Acc00900 := object_fragment7974678_field_008 fuel (fragment7974678Field009Chars00 ++ (tail))
    _ = .ok (fragment7974678Value, tail) := object_fragment7974678_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3296_before_reader"
  err.flush

noncomputable def chunk3296LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk3296SuffixChars00 : List Char := [',']
noncomputable def chunk3296Chars00 : List Char := chunk3296LeadChars00 ++ fragment7962645Chars ++ chunk3296SuffixChars00
noncomputable def chunk3296Push00 (acc : List SourceJson) : List SourceJson := fragment7962645Value :: acc

noncomputable def chunk3296AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk3296_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3896)
      (SourceJson.white (chunk3296LeadChars00 ++ (fragment7962645Chars ++ rest))) acc =
      (SourceJson.value (fuel + 3895) (fragment7962645Chars ++ rest)).bind
        (chunk3296AfterValue00 (fuel + 3895) acc) := by rfl

theorem array_chunk3296 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3896) (SourceJson.white (chunk3296Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 3895) (SourceJson.white tail) (chunk3296Push00 acc) := by
  have hinput : chunk3296Chars00 ++ tail = chunk3296LeadChars00 ++ (fragment7962645Chars ++ (chunk3296SuffixChars00 ++ tail)) := by
    simp only [chunk3296Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 3896) (SourceJson.white (chunk3296Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 3896)
          (SourceJson.white (chunk3296LeadChars00 ++ (fragment7962645Chars ++ (chunk3296SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 3896) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 3895) (fragment7962645Chars ++ (chunk3296SuffixChars00 ++ tail))).bind
        (chunk3296AfterValue00 (fuel + 3895) acc) := array_chunk3296_head fuel (chunk3296SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment7962645Value, chunk3296SuffixChars00 ++ tail)).bind
        (chunk3296AfterValue00 (fuel + 3895) acc) :=
      congrArg (fun result => result.bind (chunk3296AfterValue00 (fuel + 3895) acc))
        (value_fragment7962645 (fuel + 3523) (chunk3296SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 3895) (SourceJson.white tail) (chunk3296Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3296_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3297_before_reader"
  err.flush

noncomputable def chunk3297LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk3297SuffixChars00 : List Char := [',']
noncomputable def chunk3297Chars00 : List Char := chunk3297LeadChars00 ++ fragment7964513Chars ++ chunk3297SuffixChars00
noncomputable def chunk3297Push00 (acc : List SourceJson) : List SourceJson := fragment7964513Value :: acc

noncomputable def chunk3297AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk3297_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3895)
      (SourceJson.white (chunk3297LeadChars00 ++ (fragment7964513Chars ++ rest))) acc =
      (SourceJson.value (fuel + 3894) (fragment7964513Chars ++ rest)).bind
        (chunk3297AfterValue00 (fuel + 3894) acc) := by rfl

theorem array_chunk3297 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3895) (SourceJson.white (chunk3297Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 3894) (SourceJson.white tail) (chunk3297Push00 acc) := by
  have hinput : chunk3297Chars00 ++ tail = chunk3297LeadChars00 ++ (fragment7964513Chars ++ (chunk3297SuffixChars00 ++ tail)) := by
    simp only [chunk3297Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 3895) (SourceJson.white (chunk3297Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 3895)
          (SourceJson.white (chunk3297LeadChars00 ++ (fragment7964513Chars ++ (chunk3297SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 3895) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 3894) (fragment7964513Chars ++ (chunk3297SuffixChars00 ++ tail))).bind
        (chunk3297AfterValue00 (fuel + 3894) acc) := array_chunk3297_head fuel (chunk3297SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment7964513Value, chunk3297SuffixChars00 ++ tail)).bind
        (chunk3297AfterValue00 (fuel + 3894) acc) :=
      congrArg (fun result => result.bind (chunk3297AfterValue00 (fuel + 3894) acc))
        (value_fragment7964513 (fuel + 3666) (chunk3297SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 3894) (SourceJson.white tail) (chunk3297Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3297_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3298_before_reader"
  err.flush

noncomputable def chunk3298LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk3298SuffixChars00 : List Char := [',']
noncomputable def chunk3298Chars00 : List Char := chunk3298LeadChars00 ++ fragment7966065Chars ++ chunk3298SuffixChars00
noncomputable def chunk3298Push00 (acc : List SourceJson) : List SourceJson := fragment7966065Value :: acc

noncomputable def chunk3298AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk3298_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3894)
      (SourceJson.white (chunk3298LeadChars00 ++ (fragment7966065Chars ++ rest))) acc =
      (SourceJson.value (fuel + 3893) (fragment7966065Chars ++ rest)).bind
        (chunk3298AfterValue00 (fuel + 3893) acc) := by rfl

theorem array_chunk3298 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3894) (SourceJson.white (chunk3298Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 3893) (SourceJson.white tail) (chunk3298Push00 acc) := by
  have hinput : chunk3298Chars00 ++ tail = chunk3298LeadChars00 ++ (fragment7966065Chars ++ (chunk3298SuffixChars00 ++ tail)) := by
    simp only [chunk3298Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 3894) (SourceJson.white (chunk3298Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 3894)
          (SourceJson.white (chunk3298LeadChars00 ++ (fragment7966065Chars ++ (chunk3298SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 3894) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 3893) (fragment7966065Chars ++ (chunk3298SuffixChars00 ++ tail))).bind
        (chunk3298AfterValue00 (fuel + 3893) acc) := array_chunk3298_head fuel (chunk3298SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment7966065Value, chunk3298SuffixChars00 ++ tail)).bind
        (chunk3298AfterValue00 (fuel + 3893) acc) :=
      congrArg (fun result => result.bind (chunk3298AfterValue00 (fuel + 3893) acc))
        (value_fragment7966065 (fuel + 3690) (chunk3298SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 3893) (SourceJson.white tail) (chunk3298Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3298_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3299_before_reader"
  err.flush

noncomputable def chunk3299LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk3299SuffixChars00 : List Char := [',']
noncomputable def chunk3299Chars00 : List Char := chunk3299LeadChars00 ++ fragment7967576Chars ++ chunk3299SuffixChars00
noncomputable def chunk3299Push00 (acc : List SourceJson) : List SourceJson := fragment7967576Value :: acc

noncomputable def chunk3299AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk3299_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3893)
      (SourceJson.white (chunk3299LeadChars00 ++ (fragment7967576Chars ++ rest))) acc =
      (SourceJson.value (fuel + 3892) (fragment7967576Chars ++ rest)).bind
        (chunk3299AfterValue00 (fuel + 3892) acc) := by rfl

theorem array_chunk3299 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3893) (SourceJson.white (chunk3299Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 3892) (SourceJson.white tail) (chunk3299Push00 acc) := by
  have hinput : chunk3299Chars00 ++ tail = chunk3299LeadChars00 ++ (fragment7967576Chars ++ (chunk3299SuffixChars00 ++ tail)) := by
    simp only [chunk3299Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 3893) (SourceJson.white (chunk3299Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 3893)
          (SourceJson.white (chunk3299LeadChars00 ++ (fragment7967576Chars ++ (chunk3299SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 3893) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 3892) (fragment7967576Chars ++ (chunk3299SuffixChars00 ++ tail))).bind
        (chunk3299AfterValue00 (fuel + 3892) acc) := array_chunk3299_head fuel (chunk3299SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment7967576Value, chunk3299SuffixChars00 ++ tail)).bind
        (chunk3299AfterValue00 (fuel + 3892) acc) :=
      congrArg (fun result => result.bind (chunk3299AfterValue00 (fuel + 3892) acc))
        (value_fragment7967576 (fuel + 3501) (chunk3299SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 3892) (SourceJson.white tail) (chunk3299Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3299_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3300_before_reader"
  err.flush

noncomputable def chunk3300LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk3300SuffixChars00 : List Char := [',']
noncomputable def chunk3300Chars00 : List Char := chunk3300LeadChars00 ++ fragment7969477Chars ++ chunk3300SuffixChars00
noncomputable def chunk3300Push00 (acc : List SourceJson) : List SourceJson := fragment7969477Value :: acc

noncomputable def chunk3300AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk3300_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3892)
      (SourceJson.white (chunk3300LeadChars00 ++ (fragment7969477Chars ++ rest))) acc =
      (SourceJson.value (fuel + 3891) (fragment7969477Chars ++ rest)).bind
        (chunk3300AfterValue00 (fuel + 3891) acc) := by rfl

theorem array_chunk3300 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3892) (SourceJson.white (chunk3300Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 3891) (SourceJson.white tail) (chunk3300Push00 acc) := by
  have hinput : chunk3300Chars00 ++ tail = chunk3300LeadChars00 ++ (fragment7969477Chars ++ (chunk3300SuffixChars00 ++ tail)) := by
    simp only [chunk3300Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 3892) (SourceJson.white (chunk3300Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 3892)
          (SourceJson.white (chunk3300LeadChars00 ++ (fragment7969477Chars ++ (chunk3300SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 3892) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 3891) (fragment7969477Chars ++ (chunk3300SuffixChars00 ++ tail))).bind
        (chunk3300AfterValue00 (fuel + 3891) acc) := array_chunk3300_head fuel (chunk3300SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment7969477Value, chunk3300SuffixChars00 ++ tail)).bind
        (chunk3300AfterValue00 (fuel + 3891) acc) :=
      congrArg (fun result => result.bind (chunk3300AfterValue00 (fuel + 3891) acc))
        (value_fragment7969477 (fuel + 3670) (chunk3300SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 3891) (SourceJson.white tail) (chunk3300Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3300_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3301_before_reader"
  err.flush

noncomputable def chunk3301LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk3301SuffixChars00 : List Char := [',']
noncomputable def chunk3301Chars00 : List Char := chunk3301LeadChars00 ++ fragment7971030Chars ++ chunk3301SuffixChars00
noncomputable def chunk3301Push00 (acc : List SourceJson) : List SourceJson := fragment7971030Value :: acc

noncomputable def chunk3301AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk3301_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3891)
      (SourceJson.white (chunk3301LeadChars00 ++ (fragment7971030Chars ++ rest))) acc =
      (SourceJson.value (fuel + 3890) (fragment7971030Chars ++ rest)).bind
        (chunk3301AfterValue00 (fuel + 3890) acc) := by rfl

theorem array_chunk3301 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3891) (SourceJson.white (chunk3301Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 3890) (SourceJson.white tail) (chunk3301Push00 acc) := by
  have hinput : chunk3301Chars00 ++ tail = chunk3301LeadChars00 ++ (fragment7971030Chars ++ (chunk3301SuffixChars00 ++ tail)) := by
    simp only [chunk3301Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 3891) (SourceJson.white (chunk3301Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 3891)
          (SourceJson.white (chunk3301LeadChars00 ++ (fragment7971030Chars ++ (chunk3301SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 3891) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 3890) (fragment7971030Chars ++ (chunk3301SuffixChars00 ++ tail))).bind
        (chunk3301AfterValue00 (fuel + 3890) acc) := array_chunk3301_head fuel (chunk3301SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment7971030Value, chunk3301SuffixChars00 ++ tail)).bind
        (chunk3301AfterValue00 (fuel + 3890) acc) :=
      congrArg (fun result => result.bind (chunk3301AfterValue00 (fuel + 3890) acc))
        (value_fragment7971030 (fuel + 3665) (chunk3301SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 3890) (SourceJson.white tail) (chunk3301Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3301_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3302_before_reader"
  err.flush

noncomputable def chunk3302LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk3302SuffixChars00 : List Char := [',']
noncomputable def chunk3302Chars00 : List Char := chunk3302LeadChars00 ++ fragment7972593Chars ++ chunk3302SuffixChars00
noncomputable def chunk3302Push00 (acc : List SourceJson) : List SourceJson := fragment7972593Value :: acc

noncomputable def chunk3302AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk3302_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3890)
      (SourceJson.white (chunk3302LeadChars00 ++ (fragment7972593Chars ++ rest))) acc =
      (SourceJson.value (fuel + 3889) (fragment7972593Chars ++ rest)).bind
        (chunk3302AfterValue00 (fuel + 3889) acc) := by rfl

theorem array_chunk3302 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3890) (SourceJson.white (chunk3302Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 3889) (SourceJson.white tail) (chunk3302Push00 acc) := by
  have hinput : chunk3302Chars00 ++ tail = chunk3302LeadChars00 ++ (fragment7972593Chars ++ (chunk3302SuffixChars00 ++ tail)) := by
    simp only [chunk3302Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 3890) (SourceJson.white (chunk3302Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 3890)
          (SourceJson.white (chunk3302LeadChars00 ++ (fragment7972593Chars ++ (chunk3302SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 3890) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 3889) (fragment7972593Chars ++ (chunk3302SuffixChars00 ++ tail))).bind
        (chunk3302AfterValue00 (fuel + 3889) acc) := array_chunk3302_head fuel (chunk3302SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment7972593Value, chunk3302SuffixChars00 ++ tail)).bind
        (chunk3302AfterValue00 (fuel + 3889) acc) :=
      congrArg (fun result => result.bind (chunk3302AfterValue00 (fuel + 3889) acc))
        (value_fragment7972593 (fuel + 3408) (chunk3302SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 3889) (SourceJson.white tail) (chunk3302Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3302_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3303_before_reader"
  err.flush

noncomputable def chunk3303LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk3303SuffixChars00 : List Char := [',']
noncomputable def chunk3303Chars00 : List Char := chunk3303LeadChars00 ++ fragment7974678Chars ++ chunk3303SuffixChars00
noncomputable def chunk3303Push00 (acc : List SourceJson) : List SourceJson := fragment7974678Value :: acc

noncomputable def chunk3303AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk3303_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3889)
      (SourceJson.white (chunk3303LeadChars00 ++ (fragment7974678Chars ++ rest))) acc =
      (SourceJson.value (fuel + 3888) (fragment7974678Chars ++ rest)).bind
        (chunk3303AfterValue00 (fuel + 3888) acc) := by rfl

theorem array_chunk3303 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3889) (SourceJson.white (chunk3303Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 3888) (SourceJson.white tail) (chunk3303Push00 acc) := by
  have hinput : chunk3303Chars00 ++ tail = chunk3303LeadChars00 ++ (fragment7974678Chars ++ (chunk3303SuffixChars00 ++ tail)) := by
    simp only [chunk3303Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 3889) (SourceJson.white (chunk3303Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 3889)
          (SourceJson.white (chunk3303LeadChars00 ++ (fragment7974678Chars ++ (chunk3303SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 3889) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 3888) (fragment7974678Chars ++ (chunk3303SuffixChars00 ++ tail))).bind
        (chunk3303AfterValue00 (fuel + 3888) acc) := array_chunk3303_head fuel (chunk3303SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment7974678Value, chunk3303SuffixChars00 ++ tail)).bind
        (chunk3303AfterValue00 (fuel + 3888) acc) :=
      congrArg (fun result => result.bind (chunk3303AfterValue00 (fuel + 3888) acc))
        (value_fragment7974678 (fuel + 3383) (chunk3303SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 3888) (SourceJson.white tail) (chunk3303Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk3303_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk3296Chars00 ++ chunk3297Chars00 ++ chunk3298Chars00 ++ chunk3299Chars00 ++ chunk3300Chars00 ++ chunk3301Chars00 ++ chunk3302Chars00 ++ chunk3303Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk3303Push00 (chunk3302Push00 (chunk3301Push00 (chunk3300Push00 (chunk3299Push00 (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 3896) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 3888) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk3296Chars00 ++ (chunk3297Chars00 ++ (chunk3298Chars00 ++ (chunk3299Chars00 ++ (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 3896) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 3896) (SourceJson.white (chunk3296Chars00 ++ (chunk3297Chars00 ++ (chunk3298Chars00 ++ (chunk3299Chars00 ++ (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 3896) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 3895) (SourceJson.white (chunk3297Chars00 ++ (chunk3298Chars00 ++ (chunk3299Chars00 ++ (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail))))))))) (chunk3296Push00 (acc)) := array_chunk3296 fuel (chunk3297Chars00 ++ (chunk3298Chars00 ++ (chunk3299Chars00 ++ (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 3894) (SourceJson.white (chunk3298Chars00 ++ (chunk3299Chars00 ++ (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail)))))))) (chunk3297Push00 (chunk3296Push00 (acc))) := array_chunk3297 fuel (chunk3298Chars00 ++ (chunk3299Chars00 ++ (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail))))))) (chunk3296Push00 (acc))
    _ = SourceJson.array (fuel + 3893) (SourceJson.white (chunk3299Chars00 ++ (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail))))))) (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc)))) := array_chunk3298 fuel (chunk3299Chars00 ++ (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail)))))) (chunk3297Push00 (chunk3296Push00 (acc)))
    _ = SourceJson.array (fuel + 3892) (SourceJson.white (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail)))))) (chunk3299Push00 (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc))))) := array_chunk3299 fuel (chunk3300Chars00 ++ (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail))))) (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc))))
    _ = SourceJson.array (fuel + 3891) (SourceJson.white (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail))))) (chunk3300Push00 (chunk3299Push00 (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc)))))) := array_chunk3300 fuel (chunk3301Chars00 ++ (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail)))) (chunk3299Push00 (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc)))))
    _ = SourceJson.array (fuel + 3890) (SourceJson.white (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail)))) (chunk3301Push00 (chunk3300Push00 (chunk3299Push00 (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc))))))) := array_chunk3301 fuel (chunk3302Chars00 ++ (chunk3303Chars00 ++ (tail))) (chunk3300Push00 (chunk3299Push00 (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc))))))
    _ = SourceJson.array (fuel + 3889) (SourceJson.white (chunk3303Chars00 ++ (tail))) (chunk3302Push00 (chunk3301Push00 (chunk3300Push00 (chunk3299Push00 (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc)))))))) := array_chunk3302 fuel (chunk3303Chars00 ++ (tail)) (chunk3301Push00 (chunk3300Push00 (chunk3299Push00 (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc)))))))
    _ = SourceJson.array (fuel + 3888) (SourceJson.white tail) (blockPush acc) := array_chunk3303 fuel (tail) (chunk3302Push00 (chunk3301Push00 (chunk3300Push00 (chunk3299Push00 (chunk3298Push00 (chunk3297Push00 (chunk3296Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 7962639).take 14173 = blockChars := by rfl

theorem block_original_split : sourceRest 7962639 = blockChars ++ sourceRest 7976812 := by
  calc
    sourceRest 7962639 = (sourceRest 7962639).take 14173 ++ (sourceRest 7962639).drop 14173 :=
      (List.take_append_drop 14173 (sourceRest 7962639)).symm
    _ = blockChars ++ (sourceRest 7962639).drop 14173 :=
      congrArg (fun part => part ++ (sourceRest 7962639).drop 14173) block_original_prefix
    _ = blockChars ++ sourceRest 7976812 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 7962639 14173)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 3896) (SourceJson.white (sourceRest 7962639)) acc =
      SourceJson.array (fuel + 3888) (SourceJson.white (sourceRest 7976812)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 3896) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 7976812) acc)

#print axioms object_fragment7962645_field_000
#print axioms object_fragment7962645_field_001
#print axioms object_fragment7962645_field_002
#print axioms object_fragment7962645_field_003
#print axioms object_fragment7962645_field_004
#print axioms object_fragment7962645_field_005
#print axioms object_fragment7962645_field_006
#print axioms object_fragment7962645_field_007
#print axioms object_fragment7962645_field_008
#print axioms object_fragment7962645_field_009
#print axioms value_fragment7962645
#print axioms object_fragment7964513_field_000
#print axioms object_fragment7964513_field_001
#print axioms object_fragment7964513_field_002
#print axioms object_fragment7964513_field_003
#print axioms object_fragment7964513_field_004
#print axioms object_fragment7964513_field_005
#print axioms object_fragment7964513_field_006
#print axioms object_fragment7964513_field_007
#print axioms object_fragment7964513_field_008
#print axioms object_fragment7964513_field_009
#print axioms value_fragment7964513
#print axioms object_fragment7966065_field_000
#print axioms object_fragment7966065_field_001
#print axioms object_fragment7966065_field_002
#print axioms object_fragment7966065_field_003
#print axioms object_fragment7966065_field_004
#print axioms object_fragment7966065_field_005
#print axioms object_fragment7966065_field_006
#print axioms object_fragment7966065_field_007
#print axioms object_fragment7966065_field_008
#print axioms object_fragment7966065_field_009
#print axioms value_fragment7966065
#print axioms object_fragment7967576_field_000
#print axioms object_fragment7967576_field_001
#print axioms object_fragment7967576_field_002
#print axioms object_fragment7967576_field_003
#print axioms object_fragment7967576_field_004
#print axioms object_fragment7967576_field_005
#print axioms object_fragment7967576_field_006
#print axioms object_fragment7967576_field_007
#print axioms object_fragment7967576_field_008
#print axioms object_fragment7967576_field_009
#print axioms value_fragment7967576
#print axioms object_fragment7969477_field_000
#print axioms object_fragment7969477_field_001
#print axioms object_fragment7969477_field_002
#print axioms object_fragment7969477_field_003
#print axioms object_fragment7969477_field_004
#print axioms object_fragment7969477_field_005
#print axioms object_fragment7969477_field_006
#print axioms object_fragment7969477_field_007
#print axioms object_fragment7969477_field_008
#print axioms object_fragment7969477_field_009
#print axioms value_fragment7969477
#print axioms object_fragment7971030_field_000
#print axioms object_fragment7971030_field_001
#print axioms object_fragment7971030_field_002
#print axioms object_fragment7971030_field_003
#print axioms object_fragment7971030_field_004
#print axioms object_fragment7971030_field_005
#print axioms object_fragment7971030_field_006
#print axioms object_fragment7971030_field_007
#print axioms object_fragment7971030_field_008
#print axioms object_fragment7971030_field_009
#print axioms value_fragment7971030
#print axioms object_fragment7972593_field_000
#print axioms object_fragment7972593_field_001
#print axioms object_fragment7972593_field_002
#print axioms object_fragment7972593_field_003
#print axioms object_fragment7972593_field_004
#print axioms object_fragment7972593_field_005
#print axioms object_fragment7972593_field_006
#print axioms object_fragment7972593_field_007
#print axioms object_fragment7972593_field_008
#print axioms object_fragment7972593_field_009
#print axioms value_fragment7972593
#print axioms object_fragment7974678_field_000
#print axioms object_fragment7974678_field_001
#print axioms object_fragment7974678_field_002
#print axioms object_fragment7974678_field_003
#print axioms object_fragment7974678_field_004
#print axioms object_fragment7974678_field_005
#print axioms object_fragment7974678_field_006
#print axioms object_fragment7974678_field_007
#print axioms object_fragment7974678_field_008
#print axioms object_fragment7974678_field_009
#print axioms value_fragment7974678
#print axioms array_chunk3296_head
#print axioms array_chunk3296
#print axioms array_chunk3297_head
#print axioms array_chunk3297
#print axioms array_chunk3298_head
#print axioms array_chunk3298
#print axioms array_chunk3299_head
#print axioms array_chunk3299
#print axioms array_chunk3300_head
#print axioms array_chunk3300
#print axioms array_chunk3301_head
#print axioms array_chunk3301
#print axioms array_chunk3302_head
#print axioms array_chunk3302
#print axioms array_chunk3303_head
#print axioms array_chunk3303
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock412

end ImbalancedChen.P2OriginalSaving19Geometry12ScalableParsing
