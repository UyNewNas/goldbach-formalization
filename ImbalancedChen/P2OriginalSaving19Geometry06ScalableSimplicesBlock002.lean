import ImbalancedChen.P2OriginalSaving19Geometry06ScalableInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock002

noncomputable def fragment0155531Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0155531Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0155531Field000Value00 : SourceJson := .number (String.ofList ['1', '6'])
noncomputable def fragment0155531Acc00100 : List (String × SourceJson) := (fragment0155531Field000Key00, fragment0155531Field000Value00) :: fragment0155531Acc00000
noncomputable def fragment0155531Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '6', ',']

theorem object_fragment0155531_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0155531Field000Chars00 ++ tail)) fragment0155531Acc00000 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0155531Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_000"
  err.flush

noncomputable def fragment0155531Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0155531Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0155531Acc00200 : List (String × SourceJson) := (fragment0155531Field001Key00, fragment0155531Field001Value00) :: fragment0155531Acc00100
noncomputable def fragment0155531Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0155531_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0155531Field001Chars00 ++ tail)) fragment0155531Acc00100 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0155531Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_001"
  err.flush

noncomputable def fragment0155531Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0155531Field002Value00 : SourceJson := .str (String.ofList ['6', '1', '4', '4', '4', '2', '5', '9', '9', '2', '9', '8', '3', '2', '9', '5', '0', '2', '0', '2', '5', '2', '3', '5', '2', '0', '9', '0', '0', '6', '7', '3', '0', '9', '6', '9', '8', '1', '8', '4', '2', '1', '7', '5', '5', '4', '3', '9', '/', '3', '3', '7', '4', '9', '9', '5', '3', '6', '5', '4', '6', '5', '2', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0155531Acc00300 : List (String × SourceJson) := (fragment0155531Field002Key00, fragment0155531Field002Value00) :: fragment0155531Acc00200
noncomputable def fragment0155531Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '1', '4', '4', '4', '2', '5', '9', '9', '2', '9', '8', '3', '2', '9', '5', '0', '2', '0', '2', '5', '2', '3', '5', '2', '0', '9', '0', '0', '6', '7', '3', '0', '9', '6', '9', '8', '1', '8', '4', '2', '1', '7', '5', '5', '4', '3', '9', '/', '3', '3', '7', '4', '9', '9', '5', '3', '6', '5', '4', '6', '5', '2', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0155531_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0155531Field002Chars00 ++ tail)) fragment0155531Acc00200 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0155531Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_002"
  err.flush

noncomputable def fragment0155531Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0155531Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0155531Acc00400 : List (String × SourceJson) := (fragment0155531Field003Key00, fragment0155531Field003Value00) :: fragment0155531Acc00300
noncomputable def fragment0155531Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0155531_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0155531Field003Chars00 ++ tail)) fragment0155531Acc00300 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0155531Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_003"
  err.flush

noncomputable def fragment0155531Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0155531Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0155531Acc00500 : List (String × SourceJson) := (fragment0155531Field004Key00, fragment0155531Field004Value00) :: fragment0155531Acc00400
noncomputable def fragment0155531Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0155531_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0155531Field004Chars00 ++ tail)) fragment0155531Acc00400 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0155531Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_004"
  err.flush

noncomputable def fragment0155531Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0155531Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '6', '8', '5', '4', '1', '4', '0', '9', '5', '3', '3', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '3', '0', '7', '1', '8', '5', '2', '3', '3', '7', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '7', '6', '2', '7', '8', '7', '8', '8', '7', '8', '7', '7', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '0', '8', '2', '9', '6', '3', '1', '7', '4', '2', '3', '/', '5', '1', '2', '5', '9', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '2', '0', '5', '6', '5', '5', '4', '1', '6', '5', '9', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '8', '1', '2', '9', '9', '5', '0', '1', '4', '0', '9', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '5', '3', '8', '9', '3', '6', '6', '2', '0', '3', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '9', '0', '2', '1', '0', '0', '2', '7', '3', '3', '1', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '2', '6', '8', '0', '8', '6', '2', '6', '6', '1', '1', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '2', '5', '3', '9', '8', '8', '0', '3', '7', '1', '/', '5', '5', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0155531Acc00600 : List (String × SourceJson) := (fragment0155531Field005Key00, fragment0155531Field005Value00) :: fragment0155531Acc00500
noncomputable def fragment0155531Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '8', '5', '4', '1', '4', '0', '9', '5', '3', '3', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '3', '0', '7', '1', '8', '5', '2', '3', '3', '7', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '7', '6', '2', '7', '8', '7', '8', '8', '7', '8', '7', '7', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '0', '8', '2', '9', '6', '3', '1', '7', '4', '2', '3', '/', '5', '1', '2', '5', '9', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '2', '0', '5', '6', '5', '5', '4', '1', '6', '5', '9', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '8', '1', '2', '9', '9', '5', '0', '1', '4', '0', '9', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '5', '3', '8', '9', '3', '6', '6', '2', '0', '3', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '9', '0', '2', '1', '0', '0', '2', '7', '3', '3', '1', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '2', '6', '8', '0', '8', '6', '2', '6', '6', '1', '1', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '2', '5', '3', '9', '8', '8', '0', '3', '7', '1', '/', '5', '5', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0155531_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0155531Field005Chars00 ++ tail)) fragment0155531Acc00500 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0155531Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_005"
  err.flush

noncomputable def fragment0155531Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0155531Field006Value00 : SourceJson := .str (String.ofList ['2', '8', '4', '6', '4', '3', '1', '1', '7', '7', '7', '1', '5', '9', '2', '2', '7', '2', '6', '9', '2', '5', '2', '3', '1', '5', '8', '4', '5', '2', '5', '8', '1', '3', '6', '2', '5', '0', '6', '4', '1', '9', '5', '8', '3', '4', '0', '8', '2', '0', '0', '8', '0', '0', '/', '2', '0', '9', '7', '9', '7', '6', '6', '5', '4', '3', '0', '9', '2', '5', '1', '2', '8', '1', '7', '4', '6', '1', '6', '4', '3', '9', '4', '1', '8', '1', '8', '3', '2', '5', '2', '8', '0', '3', '2', '8', '6', '4', '4', '6', '7', '2', '4', '4', '8', '8', '1', '4', '8', '6', '0', '7', '3', '1', '3', '5', '9', '7', '4', '2', '3'])
noncomputable def fragment0155531Acc00700 : List (String × SourceJson) := (fragment0155531Field006Key00, fragment0155531Field006Value00) :: fragment0155531Acc00600
noncomputable def fragment0155531Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '8', '4', '6', '4', '3', '1', '1', '7', '7', '7', '1', '5', '9', '2', '2', '7', '2', '6', '9', '2', '5', '2', '3', '1', '5', '8', '4', '5', '2', '5', '8', '1', '3', '6', '2', '5', '0', '6', '4', '1', '9', '5', '8', '3', '4', '0', '8', '2', '0', '0', '8', '0', '0', '/', '2', '0', '9', '7', '9', '7', '6', '6', '5', '4', '3', '0', '9', '2', '5', '1', '2', '8', '1', '7', '4', '6', '1', '6', '4', '3', '9', '4', '1', '8', '1', '8', '3', '2', '5', '2', '8', '0', '3', '2', '8', '6', '4', '4', '6', '7', '2', '4', '4', '8', '8', '1', '4', '8', '6', '0', '7', '3', '1', '3', '5', '9', '7', '4', '2', '3', '"', ',']

theorem object_fragment0155531_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0155531Field006Chars00 ++ tail)) fragment0155531Acc00600 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0155531Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_006"
  err.flush

noncomputable def fragment0155531Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0155531Field007Value00 : SourceJson := .str (String.ofList ['4', '2', '3', '2', '4', '4', '0', '8', '8', '2', '0', '8', '2', '6', '7', '0', '2', '2', '8', '6', '5', '1', '0', '4', '0', '1', '7', '5', '6', '1', '0', '9', '3', '7', '2', '4', '8', '1', '3', '8', '7', '9', '3', '3', '5', '4', '2', '4', '5', '8', '1', '2', '0', '1', '5', '2', '4', '5', '0', '8', '9', '4', '8', '9', '9', '5', '5', '0', '3', '3', '3', '5', '1', '4', '7', '7', '2', '1', '1', '1', '1', '2', '7', '4', '5', '0', '3', '4', '7', '3', '9', '0', '5', '0', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '8', '8', '9', '4', '6', '6', '1', '4', '9', '5', '4', '2', '1', '9', '7', '6', '5', '3', '7', '7', '9', '6', '5', '2', '8', '1', '6', '9', '2', '3', '0', '0', '5', '6', '7', '8', '3', '9', '3', '5', '2', '8', '2', '8', '9', '4', '7', '1', '7', '4', '1', '0', '2', '6', '1', '9', '1', '8', '2', '1', '6', '1', '4', '7', '0', '0', '4', '5', '7', '3', '9', '5', '7', '5', '4', '3', '6', '0', '7', '4', '0', '2', '8', '9', '8', '7', '2', '3', '4', '9', '7', '6', '0', '7', '3', '5', '5', '6', '8', '1', '5', '7', '4', '2', '2', '2', '2', '1', '6', '9', '4', '8', '6', '6', '0', '1', '7', '8', '1', '8', '6', '6', '3', '4', '6', '9', '9'])
noncomputable def fragment0155531Acc00800 : List (String × SourceJson) := (fragment0155531Field007Key00, fragment0155531Field007Value00) :: fragment0155531Acc00700
noncomputable def fragment0155531Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '2', '3', '2', '4', '4', '0', '8', '8', '2', '0', '8', '2', '6', '7', '0', '2', '2', '8', '6', '5', '1', '0', '4', '0', '1', '7', '5', '6', '1', '0', '9', '3', '7', '2', '4', '8', '1', '3', '8', '7', '9', '3', '3', '5', '4', '2', '4', '5', '8', '1', '2', '0', '1', '5', '2', '4', '5', '0', '8', '9', '4', '8', '9', '9', '5', '5', '0', '3', '3', '3', '5', '1', '4', '7', '7', '2', '1', '1', '1', '1', '2', '7', '4', '5', '0', '3', '4', '7', '3', '9', '0', '5', '0', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '8', '8', '9', '4', '6', '6', '1', '4', '9', '5', '4', '2', '1', '9', '7', '6', '5', '3', '7', '7', '9', '6', '5', '2', '8', '1', '6', '9', '2', '3', '0', '0', '5', '6', '7', '8', '3', '9', '3', '5', '2', '8', '2', '8', '9', '4', '7', '1', '7', '4', '1', '0', '2', '6', '1', '9', '1', '8', '2', '1', '6', '1', '4', '7', '0', '0', '4', '5', '7', '3', '9', '5', '7', '5', '4', '3', '6', '0', '7', '4', '0', '2', '8', '9', '8', '7', '2', '3', '4', '9', '7', '6', '0', '7', '3', '5', '5', '6', '8', '1', '5', '7', '4', '2', '2', '2', '2', '1', '6', '9', '4', '8', '6', '6', '0', '1', '7', '8', '1', '8', '6', '6', '3', '4', '6', '9', '9', '"', ',']

theorem object_fragment0155531_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0155531Field007Chars00 ++ tail)) fragment0155531Acc00700 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0155531Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_007"
  err.flush

noncomputable def fragment0155531Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0155531Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '4', '9', '2', '8', '6', '0', '5', '4', '7', '5', '8', '1', '5', '0', '5'])
noncomputable def fragment0155531Acc00900 : List (String × SourceJson) := (fragment0155531Field008Key00, fragment0155531Field008Value00) :: fragment0155531Acc00800
noncomputable def fragment0155531Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '4', '9', '2', '8', '6', '0', '5', '4', '7', '5', '8', '1', '5', '0', '5', '"', ',']

theorem object_fragment0155531_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0155531Field008Chars00 ++ tail)) fragment0155531Acc00800 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0155531Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_008"
  err.flush

noncomputable def fragment0155531Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0155531Field009Value00 : SourceJson := .str (String.ofList ['4', '8', '6', '7', '2', '6', '4', '1', '2', '1', '1', '8', '2', '2', '2', '7', '5', '9'])
noncomputable def fragment0155531Acc01000 : List (String × SourceJson) := (fragment0155531Field009Key00, fragment0155531Field009Value00) :: fragment0155531Acc00900
noncomputable def fragment0155531Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '8', '6', '7', '2', '6', '4', '1', '2', '1', '1', '8', '2', '2', '2', '7', '5', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0155531_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0155531Field009Chars00 ++ tail)) fragment0155531Acc00900 =
      .ok (.obj (fragment0155531Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0155531_object_field_009"
  err.flush

noncomputable def fragment0155531Chars : List Char := '{' :: (fragment0155531Field000Chars00 ++ fragment0155531Field001Chars00 ++ fragment0155531Field002Chars00 ++ fragment0155531Field003Chars00 ++ fragment0155531Field004Chars00 ++ fragment0155531Field005Chars00 ++ fragment0155531Field006Chars00 ++ fragment0155531Field007Chars00 ++ fragment0155531Field008Chars00 ++ fragment0155531Field009Chars00)
noncomputable def fragment0155531Value : SourceJson := .obj (fragment0155531Acc01000.reverse)

theorem value_fragment0155531 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 257) (fragment0155531Chars ++ tail) =
      .ok (fragment0155531Value, tail) := by
  have hinput : fragment0155531Chars ++ tail = '{' :: (fragment0155531Field000Chars00 ++ (fragment0155531Field001Chars00 ++ (fragment0155531Field002Chars00 ++ (fragment0155531Field003Chars00 ++ (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0155531Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 257) (fragment0155531Chars ++ tail) =
        SourceJson.value (fuel + 257) ('{' :: (fragment0155531Field000Chars00 ++ (fragment0155531Field001Chars00 ++ (fragment0155531Field002Chars00 ++ (fragment0155531Field003Chars00 ++ (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 257)) hinput
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0155531Field000Chars00 ++ (fragment0155531Field001Chars00 ++ (fragment0155531Field002Chars00 ++ (fragment0155531Field003Chars00 ++ (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))))))))))) fragment0155531Acc00000 := by rfl
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0155531Field001Chars00 ++ (fragment0155531Field002Chars00 ++ (fragment0155531Field003Chars00 ++ (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail))))))))))) fragment0155531Acc00100 := object_fragment0155531_field_000 fuel (fragment0155531Field001Chars00 ++ (fragment0155531Field002Chars00 ++ (fragment0155531Field003Chars00 ++ (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0155531Field002Chars00 ++ (fragment0155531Field003Chars00 ++ (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))))))))) fragment0155531Acc00200 := object_fragment0155531_field_001 fuel (fragment0155531Field002Chars00 ++ (fragment0155531Field003Chars00 ++ (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0155531Field003Chars00 ++ (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail))))))))) fragment0155531Acc00300 := object_fragment0155531_field_002 fuel (fragment0155531Field003Chars00 ++ (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))))))) fragment0155531Acc00400 := object_fragment0155531_field_003 fuel (fragment0155531Field004Chars00 ++ (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail))))))) fragment0155531Acc00500 := object_fragment0155531_field_004 fuel (fragment0155531Field005Chars00 ++ (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))))) fragment0155531Acc00600 := object_fragment0155531_field_005 fuel (fragment0155531Field006Chars00 ++ (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail))))) fragment0155531Acc00700 := object_fragment0155531_field_006 fuel (fragment0155531Field007Chars00 ++ (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))) fragment0155531Acc00800 := object_fragment0155531_field_007 fuel (fragment0155531Field008Chars00 ++ (fragment0155531Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0155531Field009Chars00 ++ (tail))) fragment0155531Acc00900 := object_fragment0155531_field_008 fuel (fragment0155531Field009Chars00 ++ (tail))
    _ = .ok (fragment0155531Value, tail) := object_fragment0155531_field_009 fuel (tail)

noncomputable def fragment0157200Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0157200Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0157200Field000Value00 : SourceJson := .number (String.ofList ['1', '7'])
noncomputable def fragment0157200Acc00100 : List (String × SourceJson) := (fragment0157200Field000Key00, fragment0157200Field000Value00) :: fragment0157200Acc00000
noncomputable def fragment0157200Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '7', ',']

theorem object_fragment0157200_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0157200Field000Chars00 ++ tail)) fragment0157200Acc00000 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0157200Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_000"
  err.flush

noncomputable def fragment0157200Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0157200Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7'])]
noncomputable def fragment0157200Acc00200 : List (String × SourceJson) := (fragment0157200Field001Key00, fragment0157200Field001Value00) :: fragment0157200Acc00100
noncomputable def fragment0157200Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0157200_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0157200Field001Chars00 ++ tail)) fragment0157200Acc00100 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0157200Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_001"
  err.flush

noncomputable def fragment0157200Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0157200Field002Value00 : SourceJson := .str (String.ofList ['3', '8', '6', '6', '7', '6', '2', '5', '7', '2', '2', '7', '1', '0', '7', '7', '9', '5', '7', '6', '5', '7', '3', '1', '3', '3', '0', '4', '7', '4', '7', '6', '2', '7', '4', '9', '9', '6', '7', '/', '3', '5', '7', '8', '4', '5', '2', '7', '7', '0', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0157200Acc00300 : List (String × SourceJson) := (fragment0157200Field002Key00, fragment0157200Field002Value00) :: fragment0157200Acc00200
noncomputable def fragment0157200Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '8', '6', '6', '7', '6', '2', '5', '7', '2', '2', '7', '1', '0', '7', '7', '9', '5', '7', '6', '5', '7', '3', '1', '3', '3', '0', '4', '7', '4', '7', '6', '2', '7', '4', '9', '9', '6', '7', '/', '3', '5', '7', '8', '4', '5', '2', '7', '7', '0', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0157200_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0157200Field002Chars00 ++ tail)) fragment0157200Acc00200 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0157200Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_002"
  err.flush

noncomputable def fragment0157200Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0157200Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0157200Acc00400 : List (String × SourceJson) := (fragment0157200Field003Key00, fragment0157200Field003Value00) :: fragment0157200Acc00300
noncomputable def fragment0157200Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0157200_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0157200Field003Chars00 ++ tail)) fragment0157200Acc00300 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0157200Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_003"
  err.flush

noncomputable def fragment0157200Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0157200Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0157200Acc00500 : List (String × SourceJson) := (fragment0157200Field004Key00, fragment0157200Field004Value00) :: fragment0157200Acc00400
noncomputable def fragment0157200Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0157200_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0157200Field004Chars00 ++ tail)) fragment0157200Acc00400 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0157200Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_004"
  err.flush

noncomputable def fragment0157200Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0157200Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '7', '0', '4', '8', '6', '2', '9', '8', '7', '7', '6', '9', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '2', '7', '9', '4', '3', '7', '1', '1', '2', '3', '9', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '9', '9', '2', '5', '3', '2', '7', '3', '5', '1', '7', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '4', '6', '1', '9', '0', '9', '0', '3', '0', '5', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '5', '8', '1', '5', '3', '7', '2', '2', '0', '7', '/', '4', '1', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '4', '8', '0', '3', '5', '8', '0', '2', '9', '6', '3', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '9', '8', '7', '5', '4', '9', '9', '9', '/', '6', '6', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '6', '4', '7', '7', '1', '5', '8', '3', '1', '/', '9', '2', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '9', '6', '5', '9', '7', '6', '8', '0', '4', '7', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '1', '9', '2', '1', '9', '7', '4', '4', '1', '/', '2', '0', '6', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0157200Acc00600 : List (String × SourceJson) := (fragment0157200Field005Key00, fragment0157200Field005Value00) :: fragment0157200Acc00500
noncomputable def fragment0157200Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '4', '8', '6', '2', '9', '8', '7', '7', '6', '9', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '7', '9', '4', '3', '7', '1', '1', '2', '3', '9', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '9', '9', '2', '5', '3', '2', '7', '3', '5', '1', '7', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '4', '6', '1', '9', '0', '9', '0', '3', '0', '5', '9', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '5', '8', '1', '5', '3', '7', '2', '2', '0', '7', '/', '4', '1', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '4', '8', '0', '3', '5', '8', '0', '2', '9', '6', '3', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '9', '8', '7', '5', '4', '9', '9', '9', '/', '6', '6', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '6', '4', '7', '7', '1', '5', '8', '3', '1', '/', '9', '2', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '9', '6', '5', '9', '7', '6', '8', '0', '4', '7', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '1', '9', '2', '1', '9', '7', '4', '4', '1', '/', '2', '0', '6', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0157200_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0157200Field005Chars00 ++ tail)) fragment0157200Acc00500 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0157200Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_005"
  err.flush

noncomputable def fragment0157200Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0157200Field006Value00 : SourceJson := .str (String.ofList ['6', '7', '7', '6', '8', '3', '6', '0', '3', '1', '5', '8', '9', '2', '0', '2', '9', '6', '4', '0', '7', '9', '2', '3', '8', '8', '3', '4', '0', '6', '7', '7', '4', '3', '4', '3', '0', '1', '6', '6', '8', '3', '8', '7', '5', '0', '0', '/', '7', '8', '7', '6', '4', '5', '9', '2', '0', '9', '7', '7', '5', '6', '7', '9', '9', '3', '1', '1', '2', '1', '2', '8', '5', '7', '9', '9', '2', '9', '1', '3', '5', '9', '7', '8', '6', '0', '7', '4', '8', '2', '2', '9', '2', '5', '3', '5', '6', '2', '2', '1', '1', '8', '5', '1', '8', '5', '3', '4', '1', '7', '9'])
noncomputable def fragment0157200Acc00700 : List (String × SourceJson) := (fragment0157200Field006Key00, fragment0157200Field006Value00) :: fragment0157200Acc00600
noncomputable def fragment0157200Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '7', '7', '6', '8', '3', '6', '0', '3', '1', '5', '8', '9', '2', '0', '2', '9', '6', '4', '0', '7', '9', '2', '3', '8', '8', '3', '4', '0', '6', '7', '7', '4', '3', '4', '3', '0', '1', '6', '6', '8', '3', '8', '7', '5', '0', '0', '/', '7', '8', '7', '6', '4', '5', '9', '2', '0', '9', '7', '7', '5', '6', '7', '9', '9', '3', '1', '1', '2', '1', '2', '8', '5', '7', '9', '9', '2', '9', '1', '3', '5', '9', '7', '8', '6', '0', '7', '4', '8', '2', '2', '9', '2', '5', '3', '5', '6', '2', '2', '1', '1', '8', '5', '1', '8', '5', '3', '4', '1', '7', '9', '"', ',']

theorem object_fragment0157200_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0157200Field006Chars00 ++ tail)) fragment0157200Acc00600 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0157200Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_006"
  err.flush

noncomputable def fragment0157200Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0157200Field007Value00 : SourceJson := .str (String.ofList ['3', '9', '5', '3', '7', '1', '1', '3', '8', '0', '3', '5', '9', '6', '6', '2', '9', '5', '9', '0', '7', '9', '0', '7', '2', '5', '9', '0', '1', '3', '9', '7', '8', '4', '9', '7', '8', '0', '1', '9', '9', '0', '5', '7', '5', '8', '1', '8', '9', '6', '1', '5', '4', '5', '8', '8', '7', '3', '0', '3', '7', '3', '5', '7', '3', '2', '3', '2', '9', '4', '6', '2', '8', '5', '5', '9', '5', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '7', '3', '1', '1', '4', '2', '9', '5', '3', '4', '7', '9', '9', '8', '5', '4', '9', '3', '0', '1', '5', '1', '2', '1', '0', '7', '6', '6', '2', '7', '4', '0', '3', '6', '9', '6', '2', '9', '0', '2', '8', '0', '6', '3', '9', '0', '4', '7', '6', '3', '6', '1', '6', '6', '5', '4', '6', '5', '8', '8', '0', '2', '5', '4', '2', '9', '3', '0', '8', '8', '2', '6', '4', '7', '5', '6', '7', '3', '5', '0', '3', '1', '8', '6', '1', '2', '9', '8', '1', '5', '4', '7', '4', '4', '8', '1', '7', '2', '6', '0', '1', '0', '8', '1', '0', '5', '1', '5', '4', '5', '6', '1', '9', '5', '4', '3'])
noncomputable def fragment0157200Acc00800 : List (String × SourceJson) := (fragment0157200Field007Key00, fragment0157200Field007Value00) :: fragment0157200Acc00700
noncomputable def fragment0157200Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '9', '5', '3', '7', '1', '1', '3', '8', '0', '3', '5', '9', '6', '6', '2', '9', '5', '9', '0', '7', '9', '0', '7', '2', '5', '9', '0', '1', '3', '9', '7', '8', '4', '9', '7', '8', '0', '1', '9', '9', '0', '5', '7', '5', '8', '1', '8', '9', '6', '1', '5', '4', '5', '8', '8', '7', '3', '0', '3', '7', '3', '5', '7', '3', '2', '3', '2', '9', '4', '6', '2', '8', '5', '5', '9', '5', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '7', '3', '1', '1', '4', '2', '9', '5', '3', '4', '7', '9', '9', '8', '5', '4', '9', '3', '0', '1', '5', '1', '2', '1', '0', '7', '6', '6', '2', '7', '4', '0', '3', '6', '9', '6', '2', '9', '0', '2', '8', '0', '6', '3', '9', '0', '4', '7', '6', '3', '6', '1', '6', '6', '5', '4', '6', '5', '8', '8', '0', '2', '5', '4', '2', '9', '3', '0', '8', '8', '2', '6', '4', '7', '5', '6', '7', '3', '5', '0', '3', '1', '8', '6', '1', '2', '9', '8', '1', '5', '4', '7', '4', '4', '8', '1', '7', '2', '6', '0', '1', '0', '8', '1', '0', '5', '1', '5', '4', '5', '6', '1', '9', '5', '4', '3', '"', ',']

theorem object_fragment0157200_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0157200Field007Chars00 ++ tail)) fragment0157200Acc00700 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0157200Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_007"
  err.flush

noncomputable def fragment0157200Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0157200Field008Value00 : SourceJson := .str (String.ofList ['6', '8', '1', '6', '7', '2', '1', '2', '2', '1', '3', '4', '3'])
noncomputable def fragment0157200Acc00900 : List (String × SourceJson) := (fragment0157200Field008Key00, fragment0157200Field008Value00) :: fragment0157200Acc00800
noncomputable def fragment0157200Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '8', '1', '6', '7', '2', '1', '2', '2', '1', '3', '4', '3', '"', ',']

theorem object_fragment0157200_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0157200Field008Chars00 ++ tail)) fragment0157200Acc00800 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0157200Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_008"
  err.flush

noncomputable def fragment0157200Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0157200Field009Value00 : SourceJson := .str (String.ofList ['2', '6', '7', '0', '2', '0', '2', '6', '3', '0', '8', '9', '2', '9'])
noncomputable def fragment0157200Acc01000 : List (String × SourceJson) := (fragment0157200Field009Key00, fragment0157200Field009Value00) :: fragment0157200Acc00900
noncomputable def fragment0157200Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '6', '7', '0', '2', '0', '2', '6', '3', '0', '8', '9', '2', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0157200_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0157200Field009Chars00 ++ tail)) fragment0157200Acc00900 =
      .ok (.obj (fragment0157200Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157200_object_field_009"
  err.flush

noncomputable def fragment0157200Chars : List Char := '{' :: (fragment0157200Field000Chars00 ++ fragment0157200Field001Chars00 ++ fragment0157200Field002Chars00 ++ fragment0157200Field003Chars00 ++ fragment0157200Field004Chars00 ++ fragment0157200Field005Chars00 ++ fragment0157200Field006Chars00 ++ fragment0157200Field007Chars00 ++ fragment0157200Field008Chars00 ++ fragment0157200Field009Chars00)
noncomputable def fragment0157200Value : SourceJson := .obj (fragment0157200Acc01000.reverse)

theorem value_fragment0157200 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 232) (fragment0157200Chars ++ tail) =
      .ok (fragment0157200Value, tail) := by
  have hinput : fragment0157200Chars ++ tail = '{' :: (fragment0157200Field000Chars00 ++ (fragment0157200Field001Chars00 ++ (fragment0157200Field002Chars00 ++ (fragment0157200Field003Chars00 ++ (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0157200Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 232) (fragment0157200Chars ++ tail) =
        SourceJson.value (fuel + 232) ('{' :: (fragment0157200Field000Chars00 ++ (fragment0157200Field001Chars00 ++ (fragment0157200Field002Chars00 ++ (fragment0157200Field003Chars00 ++ (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 232)) hinput
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0157200Field000Chars00 ++ (fragment0157200Field001Chars00 ++ (fragment0157200Field002Chars00 ++ (fragment0157200Field003Chars00 ++ (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))))))))))) fragment0157200Acc00000 := by rfl
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0157200Field001Chars00 ++ (fragment0157200Field002Chars00 ++ (fragment0157200Field003Chars00 ++ (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail))))))))))) fragment0157200Acc00100 := object_fragment0157200_field_000 fuel (fragment0157200Field001Chars00 ++ (fragment0157200Field002Chars00 ++ (fragment0157200Field003Chars00 ++ (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0157200Field002Chars00 ++ (fragment0157200Field003Chars00 ++ (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))))))))) fragment0157200Acc00200 := object_fragment0157200_field_001 fuel (fragment0157200Field002Chars00 ++ (fragment0157200Field003Chars00 ++ (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0157200Field003Chars00 ++ (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail))))))))) fragment0157200Acc00300 := object_fragment0157200_field_002 fuel (fragment0157200Field003Chars00 ++ (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))))))) fragment0157200Acc00400 := object_fragment0157200_field_003 fuel (fragment0157200Field004Chars00 ++ (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail))))))) fragment0157200Acc00500 := object_fragment0157200_field_004 fuel (fragment0157200Field005Chars00 ++ (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))))) fragment0157200Acc00600 := object_fragment0157200_field_005 fuel (fragment0157200Field006Chars00 ++ (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail))))) fragment0157200Acc00700 := object_fragment0157200_field_006 fuel (fragment0157200Field007Chars00 ++ (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))) fragment0157200Acc00800 := object_fragment0157200_field_007 fuel (fragment0157200Field008Chars00 ++ (fragment0157200Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0157200Field009Chars00 ++ (tail))) fragment0157200Acc00900 := object_fragment0157200_field_008 fuel (fragment0157200Field009Chars00 ++ (tail))
    _ = .ok (fragment0157200Value, tail) := object_fragment0157200_field_009 fuel (tail)

noncomputable def fragment0158782Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0158782Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0158782Field000Value00 : SourceJson := .number (String.ofList ['1', '8'])
noncomputable def fragment0158782Acc00100 : List (String × SourceJson) := (fragment0158782Field000Key00, fragment0158782Field000Value00) :: fragment0158782Acc00000
noncomputable def fragment0158782Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '8', ',']

theorem object_fragment0158782_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0158782Field000Chars00 ++ tail)) fragment0158782Acc00000 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0158782Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_000"
  err.flush

noncomputable def fragment0158782Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0158782Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7'])]
noncomputable def fragment0158782Acc00200 : List (String × SourceJson) := (fragment0158782Field001Key00, fragment0158782Field001Value00) :: fragment0158782Acc00100
noncomputable def fragment0158782Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0158782_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0158782Field001Chars00 ++ tail)) fragment0158782Acc00100 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0158782Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_001"
  err.flush

noncomputable def fragment0158782Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0158782Field002Value00 : SourceJson := .str (String.ofList ['7', '0', '4', '8', '4', '2', '5', '0', '2', '8', '6', '2', '4', '4', '3', '6', '6', '8', '9', '1', '5', '7', '8', '4', '3', '4', '3', '2', '2', '1', '7', '5', '5', '3', '6', '5', '5', '8', '2', '1', '6', '2', '8', '3', '/', '6', '3', '6', '1', '6', '9', '3', '8', '1', '4', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0158782Acc00300 : List (String × SourceJson) := (fragment0158782Field002Key00, fragment0158782Field002Value00) :: fragment0158782Acc00200
noncomputable def fragment0158782Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '0', '4', '8', '4', '2', '5', '0', '2', '8', '6', '2', '4', '4', '3', '6', '6', '8', '9', '1', '5', '7', '8', '4', '3', '4', '3', '2', '2', '1', '7', '5', '5', '3', '6', '5', '5', '8', '2', '1', '6', '2', '8', '3', '/', '6', '3', '6', '1', '6', '9', '3', '8', '1', '4', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0158782_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0158782Field002Chars00 ++ tail)) fragment0158782Acc00200 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0158782Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_002"
  err.flush

noncomputable def fragment0158782Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0158782Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0158782Acc00400 : List (String × SourceJson) := (fragment0158782Field003Key00, fragment0158782Field003Value00) :: fragment0158782Acc00300
noncomputable def fragment0158782Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0158782_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0158782Field003Chars00 ++ tail)) fragment0158782Acc00300 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0158782Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_003"
  err.flush

noncomputable def fragment0158782Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0158782Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0158782Acc00500 : List (String × SourceJson) := (fragment0158782Field004Key00, fragment0158782Field004Value00) :: fragment0158782Acc00400
noncomputable def fragment0158782Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0158782_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0158782Field004Chars00 ++ tail)) fragment0158782Acc00400 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0158782Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_004"
  err.flush

noncomputable def fragment0158782Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0158782Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '3', '7', '4', '0', '4', '6', '8', '9', '9', '0', '7', '/', '1', '4', '8', '5', '7', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '6', '2', '5', '5', '7', '3', '8', '9', '2', '3', '/', '7', '4', '2', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '9', '9', '2', '5', '3', '2', '7', '3', '5', '1', '7', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '2', '8', '9', '4', '9', '2', '4', '7', '1', '9', '/', '9', '2', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '5', '8', '1', '5', '3', '7', '2', '2', '0', '7', '/', '4', '1', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '4', '8', '0', '3', '5', '8', '0', '2', '9', '6', '3', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '9', '8', '7', '5', '4', '9', '9', '9', '/', '6', '6', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '6', '4', '7', '7', '1', '5', '8', '3', '1', '/', '9', '2', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '3', '9', '2', '8', '2', '6', '3', '9', '5', '7', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '5', '6', '3', '4', '1', '7', '5', '6', '9', '/', '4', '1', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0158782Acc00600 : List (String × SourceJson) := (fragment0158782Field005Key00, fragment0158782Field005Value00) :: fragment0158782Acc00500
noncomputable def fragment0158782Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '4', '0', '4', '6', '8', '9', '9', '0', '7', '/', '1', '4', '8', '5', '7', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '6', '2', '5', '5', '7', '3', '8', '9', '2', '3', '/', '7', '4', '2', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '9', '9', '2', '5', '3', '2', '7', '3', '5', '1', '7', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '2', '8', '9', '4', '9', '2', '4', '7', '1', '9', '/', '9', '2', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '5', '8', '1', '5', '3', '7', '2', '2', '0', '7', '/', '4', '1', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '4', '8', '0', '3', '5', '8', '0', '2', '9', '6', '3', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '9', '8', '7', '5', '4', '9', '9', '9', '/', '6', '6', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '6', '4', '7', '7', '1', '5', '8', '3', '1', '/', '9', '2', '8', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '3', '9', '2', '8', '2', '6', '3', '9', '5', '7', '/', '3', '7', '1', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '5', '6', '3', '4', '1', '7', '5', '6', '9', '/', '4', '1', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0158782_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0158782Field005Chars00 ++ tail)) fragment0158782Acc00500 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0158782Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_005"
  err.flush

noncomputable def fragment0158782Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0158782Field006Value00 : SourceJson := .str (String.ofList ['6', '1', '7', '6', '4', '8', '7', '4', '1', '1', '2', '6', '1', '2', '8', '5', '8', '2', '1', '6', '1', '5', '9', '1', '8', '0', '9', '8', '7', '8', '2', '9', '8', '6', '9', '5', '8', '1', '3', '9', '1', '9', '4', '0', '7', '9', '8', '6', '8', '7', '5', '/', '7', '0', '0', '1', '2', '9', '7', '0', '7', '5', '3', '5', '6', '1', '5', '9', '9', '3', '8', '7', '7', '4', '4', '7', '6', '2', '6', '6', '0', '3', '6', '7', '6', '4', '2', '5', '4', '2', '8', '8', '7', '3', '1', '4', '8', '9', '2', '0', '5', '5', '2', '9', '9', '4', '2', '3', '8', '6', '9', '7', '0', '4', '8'])
noncomputable def fragment0158782Acc00700 : List (String × SourceJson) := (fragment0158782Field006Key00, fragment0158782Field006Value00) :: fragment0158782Acc00600
noncomputable def fragment0158782Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '1', '7', '6', '4', '8', '7', '4', '1', '1', '2', '6', '1', '2', '8', '5', '8', '2', '1', '6', '1', '5', '9', '1', '8', '0', '9', '8', '7', '8', '2', '9', '8', '6', '9', '5', '8', '1', '3', '9', '1', '9', '4', '0', '7', '9', '8', '6', '8', '7', '5', '/', '7', '0', '0', '1', '2', '9', '7', '0', '7', '5', '3', '5', '6', '1', '5', '9', '9', '3', '8', '7', '7', '4', '4', '7', '6', '2', '6', '6', '0', '3', '6', '7', '6', '4', '2', '5', '4', '2', '8', '8', '7', '3', '1', '4', '8', '9', '2', '0', '5', '5', '2', '9', '9', '4', '2', '3', '8', '6', '9', '7', '0', '4', '8', '"', ',']

theorem object_fragment0158782_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0158782Field006Chars00 ++ tail)) fragment0158782Acc00600 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0158782Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_006"
  err.flush

noncomputable def fragment0158782Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0158782Field007Value00 : SourceJson := .str (String.ofList ['1', '2', '9', '7', '2', '4', '5', '1', '2', '2', '0', '1', '5', '6', '0', '7', '1', '0', '9', '1', '0', '4', '1', '3', '4', '5', '7', '5', '6', '5', '2', '3', '4', '7', '1', '3', '9', '4', '3', '4', '8', '9', '8', '4', '2', '0', '2', '1', '3', '3', '5', '1', '7', '2', '5', '9', '3', '7', '3', '1', '9', '9', '3', '8', '3', '4', '5', '2', '6', '8', '3', '2', '3', '3', '8', '0', '5', '8', '1', '8', '8', '4', '3', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '8', '7', '4', '9', '3', '0', '1', '0', '3', '6', '3', '0', '9', '0', '7', '9', '5', '2', '0', '6', '2', '8', '3', '2', '7', '9', '9', '4', '0', '7', '9', '7', '2', '8', '7', '1', '7', '1', '4', '5', '0', '4', '4', '2', '0', '2', '5', '4', '6', '9', '1', '3', '2', '9', '2', '9', '6', '1', '3', '0', '7', '3', '4', '4', '6', '2', '0', '9', '0', '1', '5', '1', '5', '3', '4', '7', '4', '1', '7', '6', '4', '9', '6', '6', '1', '5', '8', '8', '3', '1', '0', '1', '9', '1', '8', '9', '2', '8', '8', '6', '1', '3', '3', '9', '3', '6', '2', '7', '2', '2', '1', '9', '6', '7'])
noncomputable def fragment0158782Acc00800 : List (String × SourceJson) := (fragment0158782Field007Key00, fragment0158782Field007Value00) :: fragment0158782Acc00700
noncomputable def fragment0158782Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '9', '7', '2', '4', '5', '1', '2', '2', '0', '1', '5', '6', '0', '7', '1', '0', '9', '1', '0', '4', '1', '3', '4', '5', '7', '5', '6', '5', '2', '3', '4', '7', '1', '3', '9', '4', '3', '4', '8', '9', '8', '4', '2', '0', '2', '1', '3', '3', '5', '1', '7', '2', '5', '9', '3', '7', '3', '1', '9', '9', '3', '8', '3', '4', '5', '2', '6', '8', '3', '2', '3', '3', '8', '0', '5', '8', '1', '8', '8', '4', '3', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '8', '7', '4', '9', '3', '0', '1', '0', '3', '6', '3', '0', '9', '0', '7', '9', '5', '2', '0', '6', '2', '8', '3', '2', '7', '9', '9', '4', '0', '7', '9', '7', '2', '8', '7', '1', '7', '1', '4', '5', '0', '4', '4', '2', '0', '2', '5', '4', '6', '9', '1', '3', '2', '9', '2', '9', '6', '1', '3', '0', '7', '3', '4', '4', '6', '2', '0', '9', '0', '1', '5', '1', '5', '3', '4', '7', '4', '1', '7', '6', '4', '9', '6', '6', '1', '5', '8', '8', '3', '1', '0', '1', '9', '1', '8', '9', '2', '8', '8', '6', '1', '3', '3', '9', '3', '6', '2', '7', '2', '2', '1', '9', '6', '7', '"', ',']

theorem object_fragment0158782_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0158782Field007Chars00 ++ tail)) fragment0158782Acc00700 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0158782Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_007"
  err.flush

noncomputable def fragment0158782Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0158782Field008Value00 : SourceJson := .str (String.ofList ['6', '9', '8', '9', '4', '4', '4', '1', '4', '3', '2', '7', '4', '3', '1', '4', '4'])
noncomputable def fragment0158782Acc00900 : List (String × SourceJson) := (fragment0158782Field008Key00, fragment0158782Field008Value00) :: fragment0158782Acc00800
noncomputable def fragment0158782Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '9', '8', '9', '4', '4', '4', '1', '4', '3', '2', '7', '4', '3', '1', '4', '4', '"', ',']

theorem object_fragment0158782_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0158782Field008Chars00 ++ tail)) fragment0158782Acc00800 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0158782Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_008"
  err.flush

noncomputable def fragment0158782Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0158782Field009Value00 : SourceJson := .str (String.ofList ['2', '7', '8', '7', '2', '1', '4', '7', '0', '2', '7', '5', '4', '6', '2', '4', '8', '8'])
noncomputable def fragment0158782Acc01000 : List (String × SourceJson) := (fragment0158782Field009Key00, fragment0158782Field009Value00) :: fragment0158782Acc00900
noncomputable def fragment0158782Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '8', '7', '2', '1', '4', '7', '0', '2', '7', '5', '4', '6', '2', '4', '8', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0158782_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0158782Field009Chars00 ++ tail)) fragment0158782Acc00900 =
      .ok (.obj (fragment0158782Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0158782_object_field_009"
  err.flush

noncomputable def fragment0158782Chars : List Char := '{' :: (fragment0158782Field000Chars00 ++ fragment0158782Field001Chars00 ++ fragment0158782Field002Chars00 ++ fragment0158782Field003Chars00 ++ fragment0158782Field004Chars00 ++ fragment0158782Field005Chars00 ++ fragment0158782Field006Chars00 ++ fragment0158782Field007Chars00 ++ fragment0158782Field008Chars00 ++ fragment0158782Field009Chars00)
noncomputable def fragment0158782Value : SourceJson := .obj (fragment0158782Acc01000.reverse)

theorem value_fragment0158782 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 233) (fragment0158782Chars ++ tail) =
      .ok (fragment0158782Value, tail) := by
  have hinput : fragment0158782Chars ++ tail = '{' :: (fragment0158782Field000Chars00 ++ (fragment0158782Field001Chars00 ++ (fragment0158782Field002Chars00 ++ (fragment0158782Field003Chars00 ++ (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0158782Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 233) (fragment0158782Chars ++ tail) =
        SourceJson.value (fuel + 233) ('{' :: (fragment0158782Field000Chars00 ++ (fragment0158782Field001Chars00 ++ (fragment0158782Field002Chars00 ++ (fragment0158782Field003Chars00 ++ (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 233)) hinput
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0158782Field000Chars00 ++ (fragment0158782Field001Chars00 ++ (fragment0158782Field002Chars00 ++ (fragment0158782Field003Chars00 ++ (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))))))))))) fragment0158782Acc00000 := by rfl
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0158782Field001Chars00 ++ (fragment0158782Field002Chars00 ++ (fragment0158782Field003Chars00 ++ (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail))))))))))) fragment0158782Acc00100 := object_fragment0158782_field_000 fuel (fragment0158782Field001Chars00 ++ (fragment0158782Field002Chars00 ++ (fragment0158782Field003Chars00 ++ (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0158782Field002Chars00 ++ (fragment0158782Field003Chars00 ++ (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))))))))) fragment0158782Acc00200 := object_fragment0158782_field_001 fuel (fragment0158782Field002Chars00 ++ (fragment0158782Field003Chars00 ++ (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0158782Field003Chars00 ++ (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail))))))))) fragment0158782Acc00300 := object_fragment0158782_field_002 fuel (fragment0158782Field003Chars00 ++ (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))))))) fragment0158782Acc00400 := object_fragment0158782_field_003 fuel (fragment0158782Field004Chars00 ++ (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail))))))) fragment0158782Acc00500 := object_fragment0158782_field_004 fuel (fragment0158782Field005Chars00 ++ (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))))) fragment0158782Acc00600 := object_fragment0158782_field_005 fuel (fragment0158782Field006Chars00 ++ (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail))))) fragment0158782Acc00700 := object_fragment0158782_field_006 fuel (fragment0158782Field007Chars00 ++ (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))) fragment0158782Acc00800 := object_fragment0158782_field_007 fuel (fragment0158782Field008Chars00 ++ (fragment0158782Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0158782Field009Chars00 ++ (tail))) fragment0158782Acc00900 := object_fragment0158782_field_008 fuel (fragment0158782Field009Chars00 ++ (tail))
    _ = .ok (fragment0158782Value, tail) := object_fragment0158782_field_009 fuel (tail)

noncomputable def fragment0160379Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0160379Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0160379Field000Value00 : SourceJson := .number (String.ofList ['1', '9'])
noncomputable def fragment0160379Acc00100 : List (String × SourceJson) := (fragment0160379Field000Key00, fragment0160379Field000Value00) :: fragment0160379Acc00000
noncomputable def fragment0160379Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '9', ',']

theorem object_fragment0160379_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 571) (SourceJson.white (fragment0160379Field000Chars00 ++ tail)) fragment0160379Acc00000 =
      SourceJson.object (fuel + 570) (SourceJson.white tail) fragment0160379Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_000"
  err.flush

noncomputable def fragment0160379Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0160379Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0160379Acc00200 : List (String × SourceJson) := (fragment0160379Field001Key00, fragment0160379Field001Value00) :: fragment0160379Acc00100
noncomputable def fragment0160379Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0160379_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 570) (SourceJson.white (fragment0160379Field001Chars00 ++ tail)) fragment0160379Acc00100 =
      SourceJson.object (fuel + 569) (SourceJson.white tail) fragment0160379Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_001"
  err.flush

noncomputable def fragment0160379Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0160379Field002Value00 : SourceJson := .str (String.ofList ['6', '7', '7', '2', '9', '0', '0', '5', '8', '3', '9', '9', '4', '9', '7', '3', '8', '1', '6', '8', '3', '3', '2', '2', '7', '6', '3', '0', '2', '6', '3', '5', '4', '0', '8', '0', '2', '6', '3', '4', '6', '4', '6', '6', '7', '/', '2', '2', '6', '6', '4', '3', '6', '5', '8', '3', '1', '9', '7', '3', '6', '3', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0160379Acc00300 : List (String × SourceJson) := (fragment0160379Field002Key00, fragment0160379Field002Value00) :: fragment0160379Acc00200
noncomputable def fragment0160379Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '7', '7', '2', '9', '0', '0', '5', '8', '3', '9', '9', '4', '9', '7', '3', '8', '1', '6', '8', '3', '3', '2', '2', '7', '6', '3', '0', '2', '6', '3', '5', '4', '0', '8', '0', '2', '6', '3', '4', '6', '4', '6', '6', '7', '/', '2', '2', '6', '6', '4', '3', '6', '5', '8', '3', '1', '9', '7', '3', '6', '3', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0160379_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 569) (SourceJson.white (fragment0160379Field002Chars00 ++ tail)) fragment0160379Acc00200 =
      SourceJson.object (fuel + 568) (SourceJson.white tail) fragment0160379Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_002"
  err.flush

noncomputable def fragment0160379Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0160379Field003Value00 : SourceJson := .str (String.ofList ['1', '7', '2', '5', '9', '7', '0', '7', '8', '0', '9', '9', '7', '6', '9', '/', '3', '8', '7', '6', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0160379Acc00400 : List (String × SourceJson) := (fragment0160379Field003Key00, fragment0160379Field003Value00) :: fragment0160379Acc00300
noncomputable def fragment0160379Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '7', '2', '5', '9', '7', '0', '7', '8', '0', '9', '9', '7', '6', '9', '/', '3', '8', '7', '6', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0160379_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 568) (SourceJson.white (fragment0160379Field003Chars00 ++ tail)) fragment0160379Acc00300 =
      SourceJson.object (fuel + 567) (SourceJson.white tail) fragment0160379Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_003"
  err.flush

noncomputable def fragment0160379Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0160379Field004Value00 : SourceJson := .arr [.str (String.ofList ['5', '3', '9', '0', '5', '9', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '5', '/', '5', '5', '0', '4']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0160379Acc00500 : List (String × SourceJson) := (fragment0160379Field004Key00, fragment0160379Field004Value00) :: fragment0160379Acc00400
noncomputable def fragment0160379Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '5', '9', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '5', '/', '5', '5', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0160379_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 567) (SourceJson.white (fragment0160379Field004Chars00 ++ tail)) fragment0160379Acc00400 =
      SourceJson.object (fuel + 566) (SourceJson.white tail) fragment0160379Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_004"
  err.flush

noncomputable def fragment0160379Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0160379Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '7', '6', '1', '6', '5', '5', '3', '6', '2', '7', '2', '6', '7', '1', '9', '2', '5', '7', '2', '9', '0', '2', '3', '3', '6', '3', '7', '4', '9', '/', '6', '6', '9', '0', '7', '1', '2', '4', '6', '3', '2', '7', '4', '1', '8', '0', '9', '7', '4', '7', '5', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '2', '3', '6', '2', '1', '2', '4', '9', '5', '5', '6', '5', '5', '0', '1', '0', '1', '9', '4', '3', '2', '9', '1', '0', '3', '1', '9', '/', '5', '9', '7', '3', '8', '5', '0', '4', '1', '3', '6', '3', '7', '6', '6', '1', '5', '8', '4', '6', '0', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '0', '4', '0', '3', '0', '2', '5', '2', '3', '6', '9', '3', '2', '6', '0', '8', '3', '4', '8', '9', '0', '0', '1', '1', '8', '7', '5', '5', '1', '/', '1', '6', '7', '2', '6', '7', '8', '1', '1', '5', '8', '1', '8', '5', '4', '5', '2', '4', '3', '6', '8', '9', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '1', '3', '2', '2', '2', '2', '2', '6', '6', '4', '6', '3', '0', '4', '3', '4', '1', '3', '3', '9', '6', '2', '8', '7', '4', '9', '9', '3', '/', '8', '3', '6', '3', '3', '9', '0', '5', '7', '9', '0', '9', '2', '7', '2', '6', '2', '1', '8', '4', '4', '9', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '2', '7', '8', '7', '5', '1', '9', '7', '8', '0', '9', '0', '2', '8', '2', '5', '4', '3', '9', '3', '1', '6', '6', '1', '1', '5', '9', '7', '/', '2', '7', '8', '7', '7', '9', '6', '8', '5', '9', '6', '9', '7', '5', '7', '5', '4', '0', '6', '1', '4', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '9', '6', '0', '1', '0', '6', '9', '1', '8', '7', '4', '1', '3', '2', '2', '8', '4', '3', '0', '0', '7', '9', '2', '2', '9', '/', '3', '8', '0', '1', '5', '4', '1', '1', '7', '2', '3', '1', '4', '8', '7', '5', '5', '5', '3', '8', '4', '0', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '7', '2', '2', '7', '9', '3', '4', '9', '4', '4', '7', '0', '4', '4', '2', '7', '8', '8', '9', '2', '9', '2', '3', '4', '8', '7', '/', '3', '0', '4', '1', '2', '3', '2', '9', '3', '7', '8', '5', '1', '9', '0', '0', '4', '4', '3', '0', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '5', '6', '4', '1', '3', '9', '1', '1', '8', '4', '2', '3', '0', '7', '4', '1', '6', '0', '0', '4', '6', '3', '6', '5', '8', '7', '/', '1', '5', '2', '0', '6', '1', '6', '4', '6', '8', '9', '2', '5', '9', '5', '0', '2', '2', '1', '5', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '7', '9', '6', '2', '6', '1', '7', '2', '3', '1', '8', '9', '7', '0', '2', '8', '2', '8', '1', '6', '3', '9', '8', '8', '6', '3', '/', '3', '0', '4', '1', '2', '3', '2', '9', '3', '7', '8', '5', '1', '9', '0', '0', '4', '4', '3', '0', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '6', '4', '5', '1', '7', '6', '0', '7', '0', '3', '2', '0', '2', '3', '9', '8', '2', '9', '6', '5', '1', '8', '3', '2', '5', '1', '/', '1', '9', '9', '1', '2', '8', '3', '4', '7', '1', '2', '1', '2', '5', '5', '3', '8', '6', '1', '5', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0160379Acc00600 : List (String × SourceJson) := (fragment0160379Field005Key00, fragment0160379Field005Value00) :: fragment0160379Acc00500
noncomputable def fragment0160379Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '6', '1', '6', '5', '5', '3', '6', '2', '7', '2', '6', '7', '1', '9', '2', '5', '7', '2', '9', '0', '2', '3', '3', '6', '3', '7', '4', '9', '/', '6', '6', '9', '0', '7', '1', '2', '4', '6', '3', '2', '7', '4', '1', '8', '0', '9', '7', '4', '7', '5', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '2', '3', '6', '2', '1', '2', '4', '9', '5', '5', '6', '5', '5', '0', '1', '0', '1', '9', '4', '3', '2', '9', '1', '0', '3', '1', '9', '/', '5', '9', '7', '3', '8', '5', '0', '4', '1', '3', '6', '3', '7', '6', '6', '1', '5', '8', '4', '6', '0', '6', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '4', '0', '3', '0', '2', '5', '2', '3', '6', '9', '3', '2', '6', '0', '8', '3', '4', '8', '9', '0', '0', '1', '1', '8', '7', '5', '5', '1', '/', '1', '6', '7', '2', '6', '7', '8', '1', '1', '5', '8', '1', '8', '5', '4', '5', '2', '4', '3', '6', '8', '9', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '1', '3', '2', '2', '2', '2', '2', '6', '6', '4', '6', '3', '0', '4', '3', '4', '1', '3', '3', '9', '6', '2', '8', '7', '4', '9', '9', '3', '/', '8', '3', '6', '3', '3', '9', '0', '5', '7', '9', '0', '9', '2', '7', '2', '6', '2', '1', '8', '4', '4', '9', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '2', '7', '8', '7', '5', '1', '9', '7', '8', '0', '9', '0', '2', '8', '2', '5', '4', '3', '9', '3', '1', '6', '6', '1', '1', '5', '9', '7', '/', '2', '7', '8', '7', '7', '9', '6', '8', '5', '9', '6', '9', '7', '5', '7', '5', '4', '0', '6', '1', '4', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '9', '6', '0', '1', '0', '6', '9', '1', '8', '7', '4', '1', '3', '2', '2', '8', '4', '3', '0', '0', '7', '9', '2', '2', '9', '/', '3', '8', '0', '1', '5', '4', '1', '1', '7', '2', '3', '1', '4', '8', '7', '5', '5', '5', '3', '8', '4', '0', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '7', '2', '2', '7', '9', '3', '4', '9', '4', '4', '7', '0', '4', '4', '2', '7', '8', '8', '9', '2', '9', '2', '3', '4', '8', '7', '/', '3', '0', '4', '1', '2', '3', '2', '9', '3', '7', '8', '5', '1', '9', '0', '0', '4', '4', '3', '0', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '5', '6', '4', '1', '3', '9', '1', '1', '8', '4', '2', '3', '0', '7', '4', '1', '6', '0', '0', '4', '6', '3', '6', '5', '8', '7', '/', '1', '5', '2', '0', '6', '1', '6', '4', '6', '8', '9', '2', '5', '9', '5', '0', '2', '2', '1', '5', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '7', '9', '6', '2', '6', '1', '7', '2', '3', '1', '8', '9', '7', '0', '2', '8', '2', '8', '1', '6', '3', '9', '8', '8', '6', '3', '/', '3', '0', '4', '1', '2', '3', '2', '9', '3', '7', '8', '5', '1', '9', '0', '0', '4', '4', '3', '0', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '6', '4', '5', '1', '7', '6', '0', '7', '0', '3', '2', '0', '2', '3', '9', '8', '2', '9', '6', '5', '1', '8', '3', '2', '5', '1', '/', '1', '9', '9', '1', '2', '8', '3', '4', '7', '1', '2', '1', '2', '5', '5', '3', '8', '6', '1', '5', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0160379_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 566) (SourceJson.white (fragment0160379Field005Chars00 ++ tail)) fragment0160379Acc00500 =
      SourceJson.object (fuel + 565) (SourceJson.white tail) fragment0160379Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_005"
  err.flush

noncomputable def fragment0160379Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0160379Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '6', '8', '9', '8', '2', '8', '5', '1', '0', '5', '7', '7', '5', '1', '5', '6', '5', '8', '3', '6', '5', '1', '6', '8', '4', '5', '0', '2', '3', '9', '8', '5', '7', '9', '9', '9', '1', '2', '2', '7', '7', '9', '1', '9', '1', '4', '2', '4', '8', '6', '3', '2', '3', '6', '1', '9', '2', '3', '/', '3', '6', '4', '1', '3', '0', '1', '3', '7', '1', '3', '6', '0', '4', '0', '3', '2', '2', '5', '1', '0', '2', '8', '8', '4', '8', '2', '4', '4', '1', '8', '6', '9', '9', '1', '5', '8', '2', '6', '0', '9', '4', '7', '2', '0', '0', '2', '8', '8', '8', '3', '4', '8', '4', '0', '9', '5', '8', '7', '6', '4', '7', '5', '6', '3', '9', '6', '0', '3', '5', '3', '9', '1', '2', '0'])
noncomputable def fragment0160379Acc00700 : List (String × SourceJson) := (fragment0160379Field006Key00, fragment0160379Field006Value00) :: fragment0160379Acc00600
noncomputable def fragment0160379Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '6', '8', '9', '8', '2', '8', '5', '1', '0', '5', '7', '7', '5', '1', '5', '6', '5', '8', '3', '6', '5', '1', '6', '8', '4', '5', '0', '2', '3', '9', '8', '5', '7', '9', '9', '9', '1', '2', '2', '7', '7', '9', '1', '9', '1', '4', '2', '4', '8', '6', '3', '2', '3', '6', '1', '9', '2', '3', '/', '3', '6', '4', '1', '3', '0', '1', '3', '7', '1', '3', '6', '0', '4', '0', '3', '2', '2', '5', '1', '0', '2', '8', '8', '4', '8', '2', '4', '4', '1', '8', '6', '9', '9', '1', '5', '8', '2', '6', '0', '9', '4', '7', '2', '0', '0', '2', '8', '8', '8', '3', '4', '8', '4', '0', '9', '5', '8', '7', '6', '4', '7', '5', '6', '3', '9', '6', '0', '3', '5', '3', '9', '1', '2', '0', '"', ',']

theorem object_fragment0160379_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 565) (SourceJson.white (fragment0160379Field006Chars00 ++ tail)) fragment0160379Acc00600 =
      SourceJson.object (fuel + 564) (SourceJson.white tail) fragment0160379Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_006"
  err.flush

noncomputable def fragment0160379Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0160379Field007Value00 : SourceJson := .str (String.ofList ['8', '8', '3', '2', '4', '2', '7', '2', '5', '7', '6', '6', '3', '5', '4', '4', '8', '4', '3', '3', '1', '8', '2', '4', '9', '8', '8', '5', '6', '1', '4', '8', '1', '0', '1', '6', '4', '9', '3', '6', '0', '5', '3', '6', '5', '1', '5', '5', '5', '9', '5', '1', '8', '1', '1', '2', '7', '0', '4', '5', '5', '0', '6', '4', '3', '9', '2', '5', '9', '5', '9', '2', '1', '1', '5', '1', '6', '5', '4', '7', '3', '6', '2', '7', '5', '6', '9', '8', '3', '9', '0', '7', '2', '9', '8', '7', '1', '2', '2', '4', '2', '6', '8', '7', '5', '7', '3', '3', '7', '7', '2', '2', '6', '1', '2', '2', '7', '8', '8', '1', '2', '0', '5', '6', '7', '5', '4', '6', '5', '2', '6', '8', '4', '3', '5', '3', '5', '7', '9', '1', '8', '6', '8', '4', '1', '6', '4', '2', '7', '4', '5', '3', '2', '1', '1', '0', '4', '6', '6', '4', '9', '3', '3', '4', '1', '3', '1', '3', '9', '4', '3', '3', '2', '9', '5', '4', '1', '2', '7', '8', '3', '8', '4', '6', '4', '5', '9', '8', '4', '2', '8', '9', '2', '9', '9', '2', '4', '9', '8', '9', '1', '8', '2', '2', '4', '3', '1', '6', '4', '4', '9', '0', '2', '0', '8', '9', '3', '0', '8', '8', '4', '4', '8', '5', '4', '8', '2', '2', '6', '5', '2', '9', '1', '0', '6', '1', '1', '0', '1', '0', '1', '0', '6', '9', '1', '5', '9', '4', '9', '7', '2', '8', '4', '1', '0', '3', '3', '5', '2', '0', '5', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '/', '1', '2', '5', '2', '7', '0', '4', '3', '5', '4', '3', '0', '3', '4', '3', '5', '8', '6', '7', '1', '2', '8', '5', '3', '1', '6', '1', '6', '2', '8', '9', '7', '1', '3', '5', '9', '0', '9', '0', '1', '4', '4', '1', '5', '9', '3', '2', '3', '3', '2', '7', '9', '0', '5', '6', '1', '8', '2', '1', '7', '7', '8', '0', '7', '7', '8', '7', '2', '3', '4', '7', '9', '1', '5', '1', '2', '7', '7', '6', '5', '9', '2', '0', '9', '7', '9', '6', '9', '1', '8', '9', '4', '3', '3', '7', '1', '7', '1', '7', '4', '3', '1', '3', '0', '0', '4', '5', '9', '4', '6', '4', '4', '5', '1', '3', '4', '6', '8', '1', '5', '1', '7', '0', '9', '2', '0', '3', '4', '9', '4', '9', '5', '0', '0', '6', '9', '8', '1', '2', '1', '3', '7', '2', '7', '5', '7', '1', '8', '2', '7', '4', '9', '8', '0', '1', '6', '2', '3', '5', '8', '5', '1', '8', '3', '0', '3', '7', '8', '1', '7', '0', '2', '2', '4', '8', '6', '9', '1', '2', '8', '9', '0', '6', '5', '0', '2', '0', '2', '8', '7', '1', '4', '1', '7', '8', '7', '6', '4', '5', '8', '5', '8', '6', '2', '8', '8', '2', '8', '3', '4', '0', '5', '3', '4', '9', '4', '2', '3', '4', '6', '6', '1', '3', '2', '2', '8', '5', '0', '2', '4', '0', '1', '5', '8', '0', '0', '1', '3', '4', '6', '4', '4', '2', '2', '3', '8', '5', '6', '2', '9', '1', '8', '8', '0', '6', '1', '6', '2', '4', '8', '9', '0', '1', '0', '3', '6', '3', '8', '5', '5', '1', '7', '8', '3', '2', '8', '2', '0', '0', '8', '3', '4', '2', '5', '0', '8', '1', '3'])
noncomputable def fragment0160379Acc00800 : List (String × SourceJson) := (fragment0160379Field007Key00, fragment0160379Field007Value00) :: fragment0160379Acc00700
noncomputable def fragment0160379Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '8', '3', '2', '4', '2', '7', '2', '5', '7', '6', '6', '3', '5', '4', '4', '8', '4', '3', '3', '1', '8', '2', '4', '9', '8', '8', '5', '6', '1', '4', '8', '1', '0', '1', '6', '4', '9', '3', '6', '0', '5', '3', '6', '5', '1', '5', '5', '5', '9', '5', '1', '8', '1', '1', '2', '7', '0', '4', '5', '5', '0', '6', '4', '3', '9', '2', '5', '9', '5', '9', '2', '1', '1', '5', '1', '6', '5', '4', '7', '3', '6', '2', '7', '5', '6', '9', '8', '3', '9', '0', '7', '2', '9', '8', '7', '1', '2', '2', '4', '2', '6', '8', '7', '5', '7', '3', '3', '7', '7', '2', '2', '6', '1', '2', '2', '7', '8', '8', '1', '2', '0', '5', '6', '7', '5', '4', '6', '5', '2', '6', '8', '4', '3', '5', '3', '5', '7', '9', '1', '8', '6', '8', '4', '1', '6', '4', '2', '7', '4', '5', '3', '2', '1', '1', '0', '4', '6', '6', '4', '9', '3', '3', '4', '1', '3', '1', '3', '9', '4', '3', '3', '2', '9', '5', '4', '1', '2', '7', '8', '3', '8', '4', '6', '4', '5', '9', '8', '4', '2', '8', '9', '2', '9', '9', '2', '4', '9', '8', '9', '1', '8', '2', '2', '4', '3', '1', '6', '4', '4', '9', '0', '2', '0', '8', '9', '3', '0', '8', '8', '4', '4', '8', '5', '4', '8', '2', '2', '6', '5', '2', '9', '1', '0', '6', '1', '1', '0', '1', '0', '1', '0', '6', '9', '1', '5', '9', '4', '9', '7', '2', '8', '4', '1', '0', '3', '3', '5', '2', '0', '5', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '/', '1', '2', '5', '2', '7', '0', '4', '3', '5', '4', '3', '0', '3', '4', '3', '5', '8', '6', '7', '1', '2', '8', '5', '3', '1', '6', '1', '6', '2', '8', '9', '7', '1', '3', '5', '9', '0', '9', '0', '1', '4', '4', '1', '5', '9', '3', '2', '3', '3', '2', '7', '9', '0', '5', '6', '1', '8', '2', '1', '7', '7', '8', '0', '7', '7', '8', '7', '2', '3', '4', '7', '9', '1', '5', '1', '2', '7', '7', '6', '5', '9', '2', '0', '9', '7', '9', '6', '9', '1', '8', '9', '4', '3', '3', '7', '1', '7', '1', '7', '4', '3', '1', '3', '0', '0', '4', '5', '9', '4', '6', '4', '4', '5', '1', '3', '4', '6', '8', '1', '5', '1', '7', '0', '9', '2', '0', '3', '4', '9', '4', '9', '5', '0', '0', '6', '9', '8', '1', '2', '1', '3', '7', '2', '7', '5', '7', '1', '8', '2', '7', '4', '9', '8', '0', '1', '6', '2', '3', '5', '8', '5', '1', '8', '3', '0', '3', '7', '8', '1', '7', '0', '2', '2', '4', '8', '6', '9', '1', '2', '8', '9', '0', '6', '5', '0', '2', '0', '2', '8', '7', '1', '4', '1', '7', '8', '7', '6', '4', '5', '8', '5', '8', '6', '2', '8', '8', '2', '8', '3', '4', '0', '5', '3', '4', '9', '4', '2', '3', '4', '6', '6', '1', '3', '2', '2', '8', '5', '0', '2', '4', '0', '1', '5', '8', '0', '0', '1', '3', '4', '6', '4', '4', '2', '2', '3', '8', '5', '6', '2', '9', '1', '8', '8', '0', '6', '1', '6', '2', '4', '8', '9', '0', '1', '0', '3', '6', '3', '8', '5', '5', '1', '7', '8', '3', '2', '8', '2', '0', '0', '8', '3', '4', '2', '5', '0', '8', '1', '3', '"', ',']

theorem object_fragment0160379_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 564) (SourceJson.white (fragment0160379Field007Chars00 ++ tail)) fragment0160379Acc00700 =
      SourceJson.object (fuel + 563) (SourceJson.white tail) fragment0160379Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_007"
  err.flush

noncomputable def fragment0160379Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0160379Field008Value00 : SourceJson := .str (String.ofList ['2', '5', '4', '3', '4', '9', '6', '2', '3', '5', '3', '9', '6', '4'])
noncomputable def fragment0160379Acc00900 : List (String × SourceJson) := (fragment0160379Field008Key00, fragment0160379Field008Value00) :: fragment0160379Acc00800
noncomputable def fragment0160379Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '4', '3', '4', '9', '6', '2', '3', '5', '3', '9', '6', '4', '"', ',']

theorem object_fragment0160379_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 563) (SourceJson.white (fragment0160379Field008Chars00 ++ tail)) fragment0160379Acc00800 =
      SourceJson.object (fuel + 562) (SourceJson.white tail) fragment0160379Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_008"
  err.flush

noncomputable def fragment0160379Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0160379Field009Value00 : SourceJson := .str (String.ofList ['5', '5', '8', '6', '1', '3', '0', '3', '5', '6', '7', '8', '8', '7'])
noncomputable def fragment0160379Acc01000 : List (String × SourceJson) := (fragment0160379Field009Key00, fragment0160379Field009Value00) :: fragment0160379Acc00900
noncomputable def fragment0160379Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '8', '6', '1', '3', '0', '3', '5', '6', '7', '8', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0160379_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 562) (SourceJson.white (fragment0160379Field009Chars00 ++ tail)) fragment0160379Acc00900 =
      .ok (.obj (fragment0160379Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0160379_object_field_009"
  err.flush

noncomputable def fragment0160379Chars : List Char := '{' :: (fragment0160379Field000Chars00 ++ fragment0160379Field001Chars00 ++ fragment0160379Field002Chars00 ++ fragment0160379Field003Chars00 ++ fragment0160379Field004Chars00 ++ fragment0160379Field005Chars00 ++ fragment0160379Field006Chars00 ++ fragment0160379Field007Chars00 ++ fragment0160379Field008Chars00 ++ fragment0160379Field009Chars00)
noncomputable def fragment0160379Value : SourceJson := .obj (fragment0160379Acc01000.reverse)

theorem value_fragment0160379 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 572) (fragment0160379Chars ++ tail) =
      .ok (fragment0160379Value, tail) := by
  have hinput : fragment0160379Chars ++ tail = '{' :: (fragment0160379Field000Chars00 ++ (fragment0160379Field001Chars00 ++ (fragment0160379Field002Chars00 ++ (fragment0160379Field003Chars00 ++ (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0160379Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 572) (fragment0160379Chars ++ tail) =
        SourceJson.value (fuel + 572) ('{' :: (fragment0160379Field000Chars00 ++ (fragment0160379Field001Chars00 ++ (fragment0160379Field002Chars00 ++ (fragment0160379Field003Chars00 ++ (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 572)) hinput
    _ = SourceJson.object (fuel + 571) (SourceJson.white (fragment0160379Field000Chars00 ++ (fragment0160379Field001Chars00 ++ (fragment0160379Field002Chars00 ++ (fragment0160379Field003Chars00 ++ (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))))))))))) fragment0160379Acc00000 := by rfl
    _ = SourceJson.object (fuel + 570) (SourceJson.white (fragment0160379Field001Chars00 ++ (fragment0160379Field002Chars00 ++ (fragment0160379Field003Chars00 ++ (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail))))))))))) fragment0160379Acc00100 := object_fragment0160379_field_000 fuel (fragment0160379Field001Chars00 ++ (fragment0160379Field002Chars00 ++ (fragment0160379Field003Chars00 ++ (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 569) (SourceJson.white (fragment0160379Field002Chars00 ++ (fragment0160379Field003Chars00 ++ (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))))))))) fragment0160379Acc00200 := object_fragment0160379_field_001 fuel (fragment0160379Field002Chars00 ++ (fragment0160379Field003Chars00 ++ (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 568) (SourceJson.white (fragment0160379Field003Chars00 ++ (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail))))))))) fragment0160379Acc00300 := object_fragment0160379_field_002 fuel (fragment0160379Field003Chars00 ++ (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 567) (SourceJson.white (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))))))) fragment0160379Acc00400 := object_fragment0160379_field_003 fuel (fragment0160379Field004Chars00 ++ (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 566) (SourceJson.white (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail))))))) fragment0160379Acc00500 := object_fragment0160379_field_004 fuel (fragment0160379Field005Chars00 ++ (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 565) (SourceJson.white (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))))) fragment0160379Acc00600 := object_fragment0160379_field_005 fuel (fragment0160379Field006Chars00 ++ (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 564) (SourceJson.white (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail))))) fragment0160379Acc00700 := object_fragment0160379_field_006 fuel (fragment0160379Field007Chars00 ++ (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 563) (SourceJson.white (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))) fragment0160379Acc00800 := object_fragment0160379_field_007 fuel (fragment0160379Field008Chars00 ++ (fragment0160379Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 562) (SourceJson.white (fragment0160379Field009Chars00 ++ (tail))) fragment0160379Acc00900 := object_fragment0160379_field_008 fuel (fragment0160379Field009Chars00 ++ (tail))
    _ = .ok (fragment0160379Value, tail) := object_fragment0160379_field_009 fuel (tail)

noncomputable def fragment0162686Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0162686Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0162686Field000Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment0162686Acc00100 : List (String × SourceJson) := (fragment0162686Field000Key00, fragment0162686Field000Value00) :: fragment0162686Acc00000
noncomputable def fragment0162686Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '0', ',']

theorem object_fragment0162686_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 487) (SourceJson.white (fragment0162686Field000Chars00 ++ tail)) fragment0162686Acc00000 =
      SourceJson.object (fuel + 486) (SourceJson.white tail) fragment0162686Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_000"
  err.flush

noncomputable def fragment0162686Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0162686Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0162686Acc00200 : List (String × SourceJson) := (fragment0162686Field001Key00, fragment0162686Field001Value00) :: fragment0162686Acc00100
noncomputable def fragment0162686Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0162686_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 486) (SourceJson.white (fragment0162686Field001Chars00 ++ tail)) fragment0162686Acc00100 =
      SourceJson.object (fuel + 485) (SourceJson.white tail) fragment0162686Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_001"
  err.flush

noncomputable def fragment0162686Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0162686Field002Value00 : SourceJson := .str (String.ofList ['5', '1', '9', '9', '1', '8', '6', '2', '1', '8', '7', '9', '2', '7', '3', '7', '5', '6', '4', '2', '3', '8', '8', '3', '2', '7', '3', '4', '1', '6', '9', '1', '8', '9', '1', '8', '7', '1', '5', '6', '5', '4', '0', '0', '3', '/', '1', '3', '4', '6', '3', '9', '7', '9', '7', '0', '2', '1', '6', '2', '5', '5', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0162686Acc00300 : List (String × SourceJson) := (fragment0162686Field002Key00, fragment0162686Field002Value00) :: fragment0162686Acc00200
noncomputable def fragment0162686Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '1', '9', '9', '1', '8', '6', '2', '1', '8', '7', '9', '2', '7', '3', '7', '5', '6', '4', '2', '3', '8', '8', '3', '2', '7', '3', '4', '1', '6', '9', '1', '8', '9', '1', '8', '7', '1', '5', '6', '5', '4', '0', '0', '3', '/', '1', '3', '4', '6', '3', '9', '7', '9', '7', '0', '2', '1', '6', '2', '5', '5', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0162686_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 485) (SourceJson.white (fragment0162686Field002Chars00 ++ tail)) fragment0162686Acc00200 =
      SourceJson.object (fuel + 484) (SourceJson.white tail) fragment0162686Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_002"
  err.flush

noncomputable def fragment0162686Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0162686Field003Value00 : SourceJson := .str (String.ofList ['4', '7', '4', '8', '0', '4', '7', '7', '4', '1', '3', '3', '/', '1', '2', '7', '9', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0162686Acc00400 : List (String × SourceJson) := (fragment0162686Field003Key00, fragment0162686Field003Value00) :: fragment0162686Acc00300
noncomputable def fragment0162686Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '7', '4', '8', '0', '4', '7', '7', '4', '1', '3', '3', '/', '1', '2', '7', '9', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0162686_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 484) (SourceJson.white (fragment0162686Field003Chars00 ++ tail)) fragment0162686Acc00300 =
      SourceJson.object (fuel + 483) (SourceJson.white tail) fragment0162686Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_003"
  err.flush

noncomputable def fragment0162686Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0162686Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0162686Acc00500 : List (String × SourceJson) := (fragment0162686Field004Key00, fragment0162686Field004Value00) :: fragment0162686Acc00400
noncomputable def fragment0162686Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0162686_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 483) (SourceJson.white (fragment0162686Field004Chars00 ++ tail)) fragment0162686Acc00400 =
      SourceJson.object (fuel + 482) (SourceJson.white tail) fragment0162686Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_004"
  err.flush

noncomputable def fragment0162686Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0162686Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '0', '0', '0', '6', '5', '2', '0', '2', '5', '0', '4', '5', '3', '6', '6', '7', '2', '7', '9', '3', '3', '1', '/', '1', '8', '2', '2', '3', '5', '3', '5', '2', '1', '4', '1', '3', '3', '3', '7', '5', '8', '9', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '5', '0', '7', '8', '7', '4', '9', '7', '3', '9', '0', '3', '0', '2', '1', '4', '8', '4', '8', '4', '5', '6', '9', '/', '1', '3', '0', '1', '6', '8', '1', '0', '8', '6', '7', '2', '3', '8', '1', '2', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '8', '4', '7', '5', '2', '2', '2', '0', '2', '7', '4', '6', '8', '9', '5', '3', '7', '1', '7', '3', '0', '3', '1', '8', '3', '/', '1', '8', '2', '2', '3', '5', '3', '5', '2', '1', '4', '1', '3', '3', '3', '7', '5', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '6', '0', '5', '2', '1', '1', '9', '2', '1', '8', '6', '0', '5', '3', '5', '4', '5', '4', '0', '5', '0', '2', '6', '7', '3', '/', '1', '8', '2', '2', '3', '5', '3', '5', '2', '1', '4', '1', '3', '3', '3', '7', '5', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '5', '5', '6', '6', '5', '8', '4', '8', '6', '0', '3', '4', '8', '7', '5', '8', '4', '3', '3', '6', '7', '4', '9', '/', '2', '0', '2', '4', '8', '3', '7', '2', '4', '6', '0', '1', '4', '8', '1', '9', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '2', '6', '2', '4', '3', '9', '0', '6', '5', '7', '7', '0', '1', '9', '0', '6', '1', '5', '4', '2', '8', '7', '/', '6', '6', '2', '6', '7', '4', '0', '0', '7', '7', '8', '6', '6', '6', '8', '2', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '4', '6', '2', '1', '4', '3', '5', '9', '5', '6', '5', '0', '9', '0', '7', '8', '7', '5', '1', '1', '4', '7', '/', '1', '6', '5', '6', '6', '8', '5', '0', '1', '9', '4', '6', '6', '6', '7', '0', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '2', '5', '8', '0', '5', '4', '3', '4', '7', '4', '7', '4', '4', '6', '1', '9', '1', '0', '6', '1', '3', '/', '3', '3', '1', '3', '3', '7', '0', '0', '3', '8', '9', '3', '3', '3', '4', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '8', '4', '7', '8', '3', '5', '5', '2', '9', '7', '7', '7', '6', '2', '8', '7', '2', '9', '0', '1', '8', '7', '/', '1', '6', '5', '6', '6', '8', '5', '0', '1', '9', '4', '6', '6', '6', '7', '0', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '7', '9', '9', '4', '2', '1', '2', '9', '0', '3', '0', '3', '6', '9', '3', '9', '3', '0', '6', '8', '0', '1', '/', '4', '3', '3', '8', '9', '3', '6', '9', '5', '5', '7', '4', '6', '0', '4', '1', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0162686Acc00600 : List (String × SourceJson) := (fragment0162686Field005Key00, fragment0162686Field005Value00) :: fragment0162686Acc00500
noncomputable def fragment0162686Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '0', '0', '6', '5', '2', '0', '2', '5', '0', '4', '5', '3', '6', '6', '7', '2', '7', '9', '3', '3', '1', '/', '1', '8', '2', '2', '3', '5', '3', '5', '2', '1', '4', '1', '3', '3', '3', '7', '5', '8', '9', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '5', '0', '7', '8', '7', '4', '9', '7', '3', '9', '0', '3', '0', '2', '1', '4', '8', '4', '8', '4', '5', '6', '9', '/', '1', '3', '0', '1', '6', '8', '1', '0', '8', '6', '7', '2', '3', '8', '1', '2', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '8', '4', '7', '5', '2', '2', '2', '0', '2', '7', '4', '6', '8', '9', '5', '3', '7', '1', '7', '3', '0', '3', '1', '8', '3', '/', '1', '8', '2', '2', '3', '5', '3', '5', '2', '1', '4', '1', '3', '3', '3', '7', '5', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '0', '5', '2', '1', '1', '9', '2', '1', '8', '6', '0', '5', '3', '5', '4', '5', '4', '0', '5', '0', '2', '6', '7', '3', '/', '1', '8', '2', '2', '3', '5', '3', '5', '2', '1', '4', '1', '3', '3', '3', '7', '5', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '5', '5', '6', '6', '5', '8', '4', '8', '6', '0', '3', '4', '8', '7', '5', '8', '4', '3', '3', '6', '7', '4', '9', '/', '2', '0', '2', '4', '8', '3', '7', '2', '4', '6', '0', '1', '4', '8', '1', '9', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '2', '6', '2', '4', '3', '9', '0', '6', '5', '7', '7', '0', '1', '9', '0', '6', '1', '5', '4', '2', '8', '7', '/', '6', '6', '2', '6', '7', '4', '0', '0', '7', '7', '8', '6', '6', '6', '8', '2', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '4', '6', '2', '1', '4', '3', '5', '9', '5', '6', '5', '0', '9', '0', '7', '8', '7', '5', '1', '1', '4', '7', '/', '1', '6', '5', '6', '6', '8', '5', '0', '1', '9', '4', '6', '6', '6', '7', '0', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '2', '5', '8', '0', '5', '4', '3', '4', '7', '4', '7', '4', '4', '6', '1', '9', '1', '0', '6', '1', '3', '/', '3', '3', '1', '3', '3', '7', '0', '0', '3', '8', '9', '3', '3', '3', '4', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '8', '4', '7', '8', '3', '5', '5', '2', '9', '7', '7', '7', '6', '2', '8', '7', '2', '9', '0', '1', '8', '7', '/', '1', '6', '5', '6', '6', '8', '5', '0', '1', '9', '4', '6', '6', '6', '7', '0', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '7', '9', '9', '4', '2', '1', '2', '9', '0', '3', '0', '3', '6', '9', '3', '9', '3', '0', '6', '8', '0', '1', '/', '4', '3', '3', '8', '9', '3', '6', '9', '5', '5', '7', '4', '6', '0', '4', '1', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0162686_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 482) (SourceJson.white (fragment0162686Field005Chars00 ++ tail)) fragment0162686Acc00500 =
      SourceJson.object (fuel + 481) (SourceJson.white tail) fragment0162686Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_005"
  err.flush

noncomputable def fragment0162686Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0162686Field006Value00 : SourceJson := .str (String.ofList ['3', '2', '4', '8', '1', '5', '5', '8', '3', '9', '8', '5', '4', '3', '3', '1', '6', '8', '3', '0', '6', '4', '6', '8', '8', '8', '8', '7', '3', '8', '7', '8', '5', '3', '5', '5', '7', '1', '2', '5', '7', '9', '8', '4', '9', '1', '3', '9', '2', '0', '0', '4', '0', '0', '5', '2', '5', '0', '0', '0', '/', '1', '2', '8', '1', '2', '9', '2', '7', '8', '2', '7', '3', '0', '6', '6', '8', '0', '0', '5', '2', '3', '1', '7', '6', '7', '4', '9', '7', '3', '7', '1', '7', '6', '5', '7', '3', '4', '9', '8', '5', '4', '9', '1', '4', '8', '1', '7', '4', '3', '0', '6', '6', '4', '4', '1', '1', '9', '9', '3', '0', '3', '9', '2', '8', '1', '1', '1', '6', '2', '3', '0', '8', '5', '5', '7'])
noncomputable def fragment0162686Acc00700 : List (String × SourceJson) := (fragment0162686Field006Key00, fragment0162686Field006Value00) :: fragment0162686Acc00600
noncomputable def fragment0162686Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '2', '4', '8', '1', '5', '5', '8', '3', '9', '8', '5', '4', '3', '3', '1', '6', '8', '3', '0', '6', '4', '6', '8', '8', '8', '8', '7', '3', '8', '7', '8', '5', '3', '5', '5', '7', '1', '2', '5', '7', '9', '8', '4', '9', '1', '3', '9', '2', '0', '0', '4', '0', '0', '5', '2', '5', '0', '0', '0', '/', '1', '2', '8', '1', '2', '9', '2', '7', '8', '2', '7', '3', '0', '6', '6', '8', '0', '0', '5', '2', '3', '1', '7', '6', '7', '4', '9', '7', '3', '7', '1', '7', '6', '5', '7', '3', '4', '9', '8', '5', '4', '9', '1', '4', '8', '1', '7', '4', '3', '0', '6', '6', '4', '4', '1', '1', '9', '9', '3', '0', '3', '9', '2', '8', '1', '1', '1', '6', '2', '3', '0', '8', '5', '5', '7', '"', ',']

theorem object_fragment0162686_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 481) (SourceJson.white (fragment0162686Field006Chars00 ++ tail)) fragment0162686Acc00600 =
      SourceJson.object (fuel + 480) (SourceJson.white tail) fragment0162686Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_006"
  err.flush

noncomputable def fragment0162686Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0162686Field007Value00 : SourceJson := .str (String.ofList ['2', '3', '9', '0', '9', '2', '7', '5', '0', '7', '5', '1', '0', '7', '6', '9', '8', '4', '7', '8', '8', '4', '9', '7', '3', '9', '8', '7', '2', '3', '2', '1', '0', '1', '3', '9', '0', '0', '7', '3', '7', '6', '3', '4', '5', '6', '5', '1', '4', '3', '1', '8', '3', '3', '5', '3', '8', '9', '2', '8', '4', '8', '7', '2', '4', '8', '0', '9', '5', '8', '5', '3', '9', '0', '3', '4', '3', '0', '3', '9', '3', '1', '0', '7', '9', '7', '4', '0', '5', '5', '6', '1', '8', '9', '3', '0', '6', '2', '1', '5', '9', '3', '9', '4', '9', '0', '8', '2', '4', '0', '8', '2', '6', '0', '7', '4', '4', '4', '1', '5', '4', '2', '9', '0', '1', '1', '7', '8', '9', '9', '7', '9', '6', '5', '2', '8', '8', '9', '4', '0', '4', '7', '5', '4', '6', '9', '8', '2', '3', '9', '6', '1', '4', '3', '1', '2', '9', '4', '7', '7', '2', '4', '7', '9', '5', '9', '8', '4', '7', '0', '3', '6', '6', '3', '1', '0', '9', '4', '3', '7', '9', '2', '1', '2', '1', '5', '9', '7', '7', '3', '1', '4', '9', '4', '9', '1', '1', '7', '7', '1', '4', '6', '1', '3', '8', '6', '2', '4', '9', '7', '1', '3', '6', '9', '2', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '0', '4', '1', '3', '5', '2', '7', '5', '5', '5', '7', '0', '9', '1', '5', '8', '7', '4', '7', '4', '4', '1', '6', '6', '0', '0', '1', '0', '6', '6', '3', '1', '8', '1', '9', '7', '8', '7', '5', '3', '0', '1', '7', '5', '2', '8', '6', '0', '0', '3', '0', '2', '2', '3', '5', '2', '9', '1', '7', '1', '9', '7', '3', '4', '5', '6', '3', '4', '0', '0', '3', '1', '2', '5', '6', '7', '3', '7', '9', '0', '3', '5', '2', '7', '2', '5', '3', '9', '2', '4', '6', '7', '9', '5', '5', '5', '3', '8', '7', '3', '9', '1', '0', '1', '7', '5', '0', '9', '5', '2', '7', '1', '8', '0', '9', '6', '9', '8', '4', '3', '3', '8', '5', '9', '8', '5', '7', '9', '4', '1', '2', '3', '4', '8', '9', '1', '6', '5', '2', '8', '0', '0', '0', '1', '8', '0', '0', '0', '7', '3', '6', '4', '1', '8', '2', '7', '3', '9', '2', '7', '3', '3', '9', '7', '0', '1', '3', '8', '5', '4', '6', '4', '6', '7', '6', '9', '2', '1', '0', '8', '4', '7', '4', '2', '9', '6', '5', '8', '2', '4', '8', '3', '4', '9', '4', '0', '4', '8', '2', '7', '5', '8', '5', '6', '3', '3', '2', '6', '2', '4', '2', '2', '4', '8', '6', '7', '3', '2', '6', '0', '0', '9', '5', '7', '2', '3', '5', '1', '7', '1', '5', '5', '2', '2', '5', '0', '4', '4', '9', '8', '6', '9', '1'])
noncomputable def fragment0162686Acc00800 : List (String × SourceJson) := (fragment0162686Field007Key00, fragment0162686Field007Value00) :: fragment0162686Acc00700
noncomputable def fragment0162686Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '3', '9', '0', '9', '2', '7', '5', '0', '7', '5', '1', '0', '7', '6', '9', '8', '4', '7', '8', '8', '4', '9', '7', '3', '9', '8', '7', '2', '3', '2', '1', '0', '1', '3', '9', '0', '0', '7', '3', '7', '6', '3', '4', '5', '6', '5', '1', '4', '3', '1', '8', '3', '3', '5', '3', '8', '9', '2', '8', '4', '8', '7', '2', '4', '8', '0', '9', '5', '8', '5', '3', '9', '0', '3', '4', '3', '0', '3', '9', '3', '1', '0', '7', '9', '7', '4', '0', '5', '5', '6', '1', '8', '9', '3', '0', '6', '2', '1', '5', '9', '3', '9', '4', '9', '0', '8', '2', '4', '0', '8', '2', '6', '0', '7', '4', '4', '4', '1', '5', '4', '2', '9', '0', '1', '1', '7', '8', '9', '9', '7', '9', '6', '5', '2', '8', '8', '9', '4', '0', '4', '7', '5', '4', '6', '9', '8', '2', '3', '9', '6', '1', '4', '3', '1', '2', '9', '4', '7', '7', '2', '4', '7', '9', '5', '9', '8', '4', '7', '0', '3', '6', '6', '3', '1', '0', '9', '4', '3', '7', '9', '2', '1', '2', '1', '5', '9', '7', '7', '3', '1', '4', '9', '4', '9', '1', '1', '7', '7', '1', '4', '6', '1', '3', '8', '6', '2', '4', '9', '7', '1', '3', '6', '9', '2', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '0', '4', '1', '3', '5', '2', '7', '5', '5', '5', '7', '0', '9', '1', '5', '8', '7', '4', '7', '4', '4', '1', '6', '6', '0', '0', '1', '0', '6', '6', '3', '1', '8', '1', '9', '7', '8', '7', '5', '3', '0', '1', '7', '5', '2', '8', '6', '0', '0', '3', '0', '2', '2', '3', '5', '2', '9', '1', '7', '1', '9', '7', '3', '4', '5', '6', '3', '4', '0', '0', '3', '1', '2', '5', '6', '7', '3', '7', '9', '0', '3', '5', '2', '7', '2', '5', '3', '9', '2', '4', '6', '7', '9', '5', '5', '5', '3', '8', '7', '3', '9', '1', '0', '1', '7', '5', '0', '9', '5', '2', '7', '1', '8', '0', '9', '6', '9', '8', '4', '3', '3', '8', '5', '9', '8', '5', '7', '9', '4', '1', '2', '3', '4', '8', '9', '1', '6', '5', '2', '8', '0', '0', '0', '1', '8', '0', '0', '0', '7', '3', '6', '4', '1', '8', '2', '7', '3', '9', '2', '7', '3', '3', '9', '7', '0', '1', '3', '8', '5', '4', '6', '4', '6', '7', '6', '9', '2', '1', '0', '8', '4', '7', '4', '2', '9', '6', '5', '8', '2', '4', '8', '3', '4', '9', '4', '0', '4', '8', '2', '7', '5', '8', '5', '6', '3', '3', '2', '6', '2', '4', '2', '2', '4', '8', '6', '7', '3', '2', '6', '0', '0', '9', '5', '7', '2', '3', '5', '1', '7', '1', '5', '5', '2', '2', '5', '0', '4', '4', '9', '8', '6', '9', '1', '"', ',']

theorem object_fragment0162686_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 480) (SourceJson.white (fragment0162686Field007Chars00 ++ tail)) fragment0162686Acc00700 =
      SourceJson.object (fuel + 479) (SourceJson.white tail) fragment0162686Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_007"
  err.flush

noncomputable def fragment0162686Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0162686Field008Value00 : SourceJson := .str (String.ofList ['2', '0', '0', '8', '4', '8', '2', '5', '4', '3', '7', '2', '5', '7', '6'])
noncomputable def fragment0162686Acc00900 : List (String × SourceJson) := (fragment0162686Field008Key00, fragment0162686Field008Value00) :: fragment0162686Acc00800
noncomputable def fragment0162686Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '0', '8', '4', '8', '2', '5', '4', '3', '7', '2', '5', '7', '6', '"', ',']

theorem object_fragment0162686_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 479) (SourceJson.white (fragment0162686Field008Chars00 ++ tail)) fragment0162686Acc00800 =
      SourceJson.object (fuel + 478) (SourceJson.white tail) fragment0162686Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_008"
  err.flush

noncomputable def fragment0162686Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0162686Field009Value00 : SourceJson := .str (String.ofList ['5', '9', '1', '2', '0', '0', '9', '8', '5', '0', '8', '3', '1', '0', '6'])
noncomputable def fragment0162686Acc01000 : List (String × SourceJson) := (fragment0162686Field009Key00, fragment0162686Field009Value00) :: fragment0162686Acc00900
noncomputable def fragment0162686Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '1', '2', '0', '0', '9', '8', '5', '0', '8', '3', '1', '0', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0162686_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 478) (SourceJson.white (fragment0162686Field009Chars00 ++ tail)) fragment0162686Acc00900 =
      .ok (.obj (fragment0162686Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0162686_object_field_009"
  err.flush

noncomputable def fragment0162686Chars : List Char := '{' :: (fragment0162686Field000Chars00 ++ fragment0162686Field001Chars00 ++ fragment0162686Field002Chars00 ++ fragment0162686Field003Chars00 ++ fragment0162686Field004Chars00 ++ fragment0162686Field005Chars00 ++ fragment0162686Field006Chars00 ++ fragment0162686Field007Chars00 ++ fragment0162686Field008Chars00 ++ fragment0162686Field009Chars00)
noncomputable def fragment0162686Value : SourceJson := .obj (fragment0162686Acc01000.reverse)

theorem value_fragment0162686 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 488) (fragment0162686Chars ++ tail) =
      .ok (fragment0162686Value, tail) := by
  have hinput : fragment0162686Chars ++ tail = '{' :: (fragment0162686Field000Chars00 ++ (fragment0162686Field001Chars00 ++ (fragment0162686Field002Chars00 ++ (fragment0162686Field003Chars00 ++ (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0162686Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 488) (fragment0162686Chars ++ tail) =
        SourceJson.value (fuel + 488) ('{' :: (fragment0162686Field000Chars00 ++ (fragment0162686Field001Chars00 ++ (fragment0162686Field002Chars00 ++ (fragment0162686Field003Chars00 ++ (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 488)) hinput
    _ = SourceJson.object (fuel + 487) (SourceJson.white (fragment0162686Field000Chars00 ++ (fragment0162686Field001Chars00 ++ (fragment0162686Field002Chars00 ++ (fragment0162686Field003Chars00 ++ (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))))))))))) fragment0162686Acc00000 := by rfl
    _ = SourceJson.object (fuel + 486) (SourceJson.white (fragment0162686Field001Chars00 ++ (fragment0162686Field002Chars00 ++ (fragment0162686Field003Chars00 ++ (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail))))))))))) fragment0162686Acc00100 := object_fragment0162686_field_000 fuel (fragment0162686Field001Chars00 ++ (fragment0162686Field002Chars00 ++ (fragment0162686Field003Chars00 ++ (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 485) (SourceJson.white (fragment0162686Field002Chars00 ++ (fragment0162686Field003Chars00 ++ (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))))))))) fragment0162686Acc00200 := object_fragment0162686_field_001 fuel (fragment0162686Field002Chars00 ++ (fragment0162686Field003Chars00 ++ (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 484) (SourceJson.white (fragment0162686Field003Chars00 ++ (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail))))))))) fragment0162686Acc00300 := object_fragment0162686_field_002 fuel (fragment0162686Field003Chars00 ++ (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 483) (SourceJson.white (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))))))) fragment0162686Acc00400 := object_fragment0162686_field_003 fuel (fragment0162686Field004Chars00 ++ (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 482) (SourceJson.white (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail))))))) fragment0162686Acc00500 := object_fragment0162686_field_004 fuel (fragment0162686Field005Chars00 ++ (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 481) (SourceJson.white (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))))) fragment0162686Acc00600 := object_fragment0162686_field_005 fuel (fragment0162686Field006Chars00 ++ (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 480) (SourceJson.white (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail))))) fragment0162686Acc00700 := object_fragment0162686_field_006 fuel (fragment0162686Field007Chars00 ++ (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 479) (SourceJson.white (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))) fragment0162686Acc00800 := object_fragment0162686_field_007 fuel (fragment0162686Field008Chars00 ++ (fragment0162686Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 478) (SourceJson.white (fragment0162686Field009Chars00 ++ (tail))) fragment0162686Acc00900 := object_fragment0162686_field_008 fuel (fragment0162686Field009Chars00 ++ (tail))
    _ = .ok (fragment0162686Value, tail) := object_fragment0162686_field_009 fuel (tail)

noncomputable def fragment0164829Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0164829Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0164829Field000Value00 : SourceJson := .number (String.ofList ['2', '1'])
noncomputable def fragment0164829Acc00100 : List (String × SourceJson) := (fragment0164829Field000Key00, fragment0164829Field000Value00) :: fragment0164829Acc00000
noncomputable def fragment0164829Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '1', ',']

theorem object_fragment0164829_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment0164829Field000Chars00 ++ tail)) fragment0164829Acc00000 =
      SourceJson.object (fuel + 469) (SourceJson.white tail) fragment0164829Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_000"
  err.flush

noncomputable def fragment0164829Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0164829Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0164829Acc00200 : List (String × SourceJson) := (fragment0164829Field001Key00, fragment0164829Field001Value00) :: fragment0164829Acc00100
noncomputable def fragment0164829Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0164829_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 469) (SourceJson.white (fragment0164829Field001Chars00 ++ tail)) fragment0164829Acc00100 =
      SourceJson.object (fuel + 468) (SourceJson.white tail) fragment0164829Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_001"
  err.flush

noncomputable def fragment0164829Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0164829Field002Value00 : SourceJson := .str (String.ofList ['9', '5', '0', '2', '0', '7', '1', '8', '5', '7', '3', '4', '6', '0', '0', '5', '5', '7', '3', '7', '7', '4', '6', '5', '4', '0', '3', '7', '7', '2', '8', '9', '5', '3', '9', '9', '3', '0', '1', '/', '7', '0', '4', '5', '1', '0', '5', '6', '5', '8', '1', '0', '8', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0164829Acc00300 : List (String × SourceJson) := (fragment0164829Field002Key00, fragment0164829Field002Value00) :: fragment0164829Acc00200
noncomputable def fragment0164829Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '5', '0', '2', '0', '7', '1', '8', '5', '7', '3', '4', '6', '0', '0', '5', '5', '7', '3', '7', '7', '4', '6', '5', '4', '0', '3', '7', '7', '2', '8', '9', '5', '3', '9', '9', '3', '0', '1', '/', '7', '0', '4', '5', '1', '0', '5', '6', '5', '8', '1', '0', '8', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0164829_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 468) (SourceJson.white (fragment0164829Field002Chars00 ++ tail)) fragment0164829Acc00200 =
      SourceJson.object (fuel + 467) (SourceJson.white tail) fragment0164829Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_002"
  err.flush

noncomputable def fragment0164829Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0164829Field003Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0164829Acc00400 : List (String × SourceJson) := (fragment0164829Field003Key00, fragment0164829Field003Value00) :: fragment0164829Acc00300
noncomputable def fragment0164829Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0164829_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 467) (SourceJson.white (fragment0164829Field003Chars00 ++ tail)) fragment0164829Acc00300 =
      SourceJson.object (fuel + 466) (SourceJson.white tail) fragment0164829Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_003"
  err.flush

noncomputable def fragment0164829Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0164829Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0164829Acc00500 : List (String × SourceJson) := (fragment0164829Field004Key00, fragment0164829Field004Value00) :: fragment0164829Acc00400
noncomputable def fragment0164829Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0164829_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 466) (SourceJson.white (fragment0164829Field004Chars00 ++ tail)) fragment0164829Acc00400 =
      SourceJson.object (fuel + 465) (SourceJson.white tail) fragment0164829Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_004"
  err.flush

noncomputable def fragment0164829Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0164829Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '7', '6', '9', '5', '8', '6', '8', '2', '7', '1', '2', '6', '2', '5', '1', '9', '4', '6', '9', '8', '2', '0', '7', '7', '/', '8', '7', '0', '4', '0', '8', '6', '0', '8', '5', '5', '9', '1', '6', '0', '4', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '4', '6', '7', '1', '3', '3', '2', '4', '4', '0', '0', '2', '0', '0', '5', '9', '1', '6', '4', '7', '7', '7', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '7', '0', '1', '7', '1', '9', '3', '1', '9', '2', '3', '7', '2', '0', '8', '6', '7', '6', '1', '4', '0', '1', '6', '7', '/', '3', '6', '2', '6', '7', '0', '2', '5', '3', '5', '6', '6', '3', '1', '6', '8', '6', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '0', '0', '5', '6', '1', '6', '5', '2', '1', '6', '0', '2', '0', '3', '9', '9', '2', '2', '8', '0', '5', '7', '3', '1', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '2', '1', '1', '3', '9', '9', '1', '8', '0', '6', '2', '0', '1', '2', '3', '2', '1', '4', '4', '6', '1', '3', '0', '1', '/', '5', '4', '4', '0', '0', '5', '3', '8', '0', '3', '4', '9', '4', '7', '5', '2', '9', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '6', '7', '3', '0', '0', '6', '8', '5', '4', '6', '3', '5', '8', '7', '7', '6', '7', '6', '9', '9', '/', '8', '2', '4', '2', '5', '0', '5', '7', '6', '2', '8', '7', '0', '8', '3', '7', '8', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '3', '0', '1', '6', '0', '4', '6', '4', '4', '9', '4', '0', '7', '1', '4', '8', '4', '3', '7', '5', '3', '/', '3', '9', '5', '6', '4', '0', '2', '7', '6', '6', '1', '7', '8', '0', '0', '2', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '1', '8', '0', '1', '0', '1', '4', '6', '6', '5', '9', '5', '6', '5', '0', '3', '0', '4', '0', '9', '1', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '5', '8', '0', '3', '8', '6', '6', '1', '5', '9', '8', '9', '4', '4', '6', '4', '2', '2', '7', '6', '2', '7', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '0', '6', '7', '0', '7', '2', '7', '8', '5', '2', '7', '1', '6', '3', '1', '0', '6', '1', '2', '9', '9', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0164829Acc00600 : List (String × SourceJson) := (fragment0164829Field005Key00, fragment0164829Field005Value00) :: fragment0164829Acc00500
noncomputable def fragment0164829Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '6', '9', '5', '8', '6', '8', '2', '7', '1', '2', '6', '2', '5', '1', '9', '4', '6', '9', '8', '2', '0', '7', '7', '/', '8', '7', '0', '4', '0', '8', '6', '0', '8', '5', '5', '9', '1', '6', '0', '4', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '6', '7', '1', '3', '3', '2', '4', '4', '0', '0', '2', '0', '0', '5', '9', '1', '6', '4', '7', '7', '7', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '7', '0', '1', '7', '1', '9', '3', '1', '9', '2', '3', '7', '2', '0', '8', '6', '7', '6', '1', '4', '0', '1', '6', '7', '/', '3', '6', '2', '6', '7', '0', '2', '5', '3', '5', '6', '6', '3', '1', '6', '8', '6', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '0', '0', '5', '6', '1', '6', '5', '2', '1', '6', '0', '2', '0', '3', '9', '9', '2', '2', '8', '0', '5', '7', '3', '1', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '2', '1', '1', '3', '9', '9', '1', '8', '0', '6', '2', '0', '1', '2', '3', '2', '1', '4', '4', '6', '1', '3', '0', '1', '/', '5', '4', '4', '0', '0', '5', '3', '8', '0', '3', '4', '9', '4', '7', '5', '2', '9', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '6', '7', '3', '0', '0', '6', '8', '5', '4', '6', '3', '5', '8', '7', '7', '6', '7', '6', '9', '9', '/', '8', '2', '4', '2', '5', '0', '5', '7', '6', '2', '8', '7', '0', '8', '3', '7', '8', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '3', '0', '1', '6', '0', '4', '6', '4', '4', '9', '4', '0', '7', '1', '4', '8', '4', '3', '7', '5', '3', '/', '3', '9', '5', '6', '4', '0', '2', '7', '6', '6', '1', '7', '8', '0', '0', '2', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '1', '1', '8', '0', '1', '0', '1', '4', '6', '6', '5', '9', '5', '6', '5', '0', '3', '0', '4', '0', '9', '1', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '5', '8', '0', '3', '8', '6', '6', '1', '5', '9', '8', '9', '4', '4', '6', '4', '2', '2', '7', '6', '2', '7', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '0', '6', '7', '0', '7', '2', '7', '8', '5', '2', '7', '1', '6', '3', '1', '0', '6', '1', '2', '9', '9', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0164829_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 465) (SourceJson.white (fragment0164829Field005Chars00 ++ tail)) fragment0164829Acc00500 =
      SourceJson.object (fuel + 464) (SourceJson.white tail) fragment0164829Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_005"
  err.flush

noncomputable def fragment0164829Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0164829Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '7', '4', '4', '2', '0', '9', '4', '9', '2', '7', '0', '1', '7', '0', '0', '7', '4', '3', '9', '9', '1', '2', '5', '6', '4', '6', '8', '0', '7', '5', '9', '1', '6', '4', '2', '5', '3', '4', '2', '0', '7', '4', '2', '4', '7', '5', '2', '7', '9', '0', '0', '0', '0', '0', '0', '/', '1', '5', '2', '8', '6', '1', '3', '1', '4', '3', '5', '2', '5', '4', '9', '5', '5', '4', '7', '3', '1', '5', '0', '7', '7', '9', '6', '9', '7', '9', '6', '2', '0', '5', '6', '5', '0', '9', '7', '8', '8', '0', '8', '4', '2', '7', '0', '4', '8', '0', '9', '5', '8', '2', '6', '3', '0', '8', '4', '8', '9', '5', '2', '7', '6', '2', '3', '0', '2', '4', '8', '8', '3', '8', '7', '1'])
noncomputable def fragment0164829Acc00700 : List (String × SourceJson) := (fragment0164829Field006Key00, fragment0164829Field006Value00) :: fragment0164829Acc00600
noncomputable def fragment0164829Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '7', '7', '4', '4', '2', '0', '9', '4', '9', '2', '7', '0', '1', '7', '0', '0', '7', '4', '3', '9', '9', '1', '2', '5', '6', '4', '6', '8', '0', '7', '5', '9', '1', '6', '4', '2', '5', '3', '4', '2', '0', '7', '4', '2', '4', '7', '5', '2', '7', '9', '0', '0', '0', '0', '0', '0', '/', '1', '5', '2', '8', '6', '1', '3', '1', '4', '3', '5', '2', '5', '4', '9', '5', '5', '4', '7', '3', '1', '5', '0', '7', '7', '9', '6', '9', '7', '9', '6', '2', '0', '5', '6', '5', '0', '9', '7', '8', '8', '0', '8', '4', '2', '7', '0', '4', '8', '0', '9', '5', '8', '2', '6', '3', '0', '8', '4', '8', '9', '5', '2', '7', '6', '2', '3', '0', '2', '4', '8', '8', '3', '8', '7', '1', '"', ',']

theorem object_fragment0164829_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 464) (SourceJson.white (fragment0164829Field006Chars00 ++ tail)) fragment0164829Acc00600 =
      SourceJson.object (fuel + 463) (SourceJson.white tail) fragment0164829Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_006"
  err.flush

noncomputable def fragment0164829Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0164829Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '5', '6', '8', '9', '7', '2', '8', '3', '2', '5', '2', '3', '2', '8', '1', '0', '9', '3', '0', '3', '2', '7', '1', '1', '8', '2', '1', '6', '0', '3', '8', '9', '5', '1', '8', '6', '8', '5', '1', '4', '4', '8', '3', '4', '9', '1', '9', '2', '3', '9', '7', '9', '9', '0', '7', '9', '6', '4', '6', '7', '3', '9', '8', '7', '3', '2', '5', '9', '1', '6', '1', '1', '6', '0', '8', '4', '4', '9', '2', '5', '2', '0', '5', '8', '1', '2', '9', '5', '2', '3', '8', '9', '0', '4', '4', '2', '3', '3', '9', '0', '4', '8', '2', '0', '5', '3', '9', '1', '3', '2', '5', '9', '5', '9', '0', '5', '0', '9', '7', '6', '2', '4', '0', '2', '9', '4', '0', '1', '7', '4', '0', '2', '8', '9', '9', '1', '5', '7', '1', '6', '8', '3', '2', '9', '2', '2', '7', '5', '1', '0', '7', '0', '5', '5', '3', '9', '4', '3', '2', '3', '0', '9', '5', '1', '9', '5', '8', '3', '8', '4', '8', '3', '7', '3', '4', '8', '8', '8', '5', '2', '3', '5', '3', '5', '9', '5', '2', '4', '7', '6', '5', '7', '2', '9', '6', '2', '2', '5', '2', '6', '1', '0', '7', '3', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '7', '0', '6', '6', '5', '5', '0', '2', '2', '6', '9', '8', '1', '4', '4', '9', '8', '6', '1', '5', '4', '2', '6', '4', '6', '2', '1', '2', '6', '3', '9', '6', '8', '1', '7', '5', '8', '7', '7', '8', '3', '2', '4', '0', '0', '2', '5', '4', '1', '8', '2', '9', '6', '1', '3', '2', '2', '1', '0', '3', '6', '5', '8', '2', '2', '4', '0', '1', '5', '9', '1', '1', '0', '9', '6', '4', '3', '5', '0', '7', '3', '8', '4', '3', '4', '9', '3', '1', '1', '6', '3', '4', '4', '8', '3', '5', '3', '5', '2', '5', '4', '3', '4', '3', '0', '4', '7', '7', '2', '6', '5', '5', '8', '3', '8', '4', '0', '4', '5', '5', '7', '4', '0', '5', '3', '1', '1', '1', '0', '1', '2', '3', '4', '8', '0', '9', '5', '4', '0', '2', '5', '3', '5', '7', '9', '0', '3', '1', '8', '3', '1', '2', '5', '2', '8', '0', '4', '6', '6', '3', '7', '4', '1', '7', '5', '0', '9', '1', '3', '8', '8', '0', '1', '2', '2', '6', '1', '9', '6', '9', '6', '9', '6', '6', '0', '7', '5', '4', '2', '1', '9', '5', '8', '6', '7', '6', '2', '7', '7', '8', '7', '4', '7', '7', '5', '0', '4', '4', '0', '9', '5', '5', '0', '8', '4', '5', '8', '7', '4', '4', '7', '8', '9', '0', '0', '6', '7', '2', '2', '2', '4', '5', '2', '7', '4', '1'])
noncomputable def fragment0164829Acc00800 : List (String × SourceJson) := (fragment0164829Field007Key00, fragment0164829Field007Value00) :: fragment0164829Acc00700
noncomputable def fragment0164829Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '5', '6', '8', '9', '7', '2', '8', '3', '2', '5', '2', '3', '2', '8', '1', '0', '9', '3', '0', '3', '2', '7', '1', '1', '8', '2', '1', '6', '0', '3', '8', '9', '5', '1', '8', '6', '8', '5', '1', '4', '4', '8', '3', '4', '9', '1', '9', '2', '3', '9', '7', '9', '9', '0', '7', '9', '6', '4', '6', '7', '3', '9', '8', '7', '3', '2', '5', '9', '1', '6', '1', '1', '6', '0', '8', '4', '4', '9', '2', '5', '2', '0', '5', '8', '1', '2', '9', '5', '2', '3', '8', '9', '0', '4', '4', '2', '3', '3', '9', '0', '4', '8', '2', '0', '5', '3', '9', '1', '3', '2', '5', '9', '5', '9', '0', '5', '0', '9', '7', '6', '2', '4', '0', '2', '9', '4', '0', '1', '7', '4', '0', '2', '8', '9', '9', '1', '5', '7', '1', '6', '8', '3', '2', '9', '2', '2', '7', '5', '1', '0', '7', '0', '5', '5', '3', '9', '4', '3', '2', '3', '0', '9', '5', '1', '9', '5', '8', '3', '8', '4', '8', '3', '7', '3', '4', '8', '8', '8', '5', '2', '3', '5', '3', '5', '9', '5', '2', '4', '7', '6', '5', '7', '2', '9', '6', '2', '2', '5', '2', '6', '1', '0', '7', '3', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '7', '0', '6', '6', '5', '5', '0', '2', '2', '6', '9', '8', '1', '4', '4', '9', '8', '6', '1', '5', '4', '2', '6', '4', '6', '2', '1', '2', '6', '3', '9', '6', '8', '1', '7', '5', '8', '7', '7', '8', '3', '2', '4', '0', '0', '2', '5', '4', '1', '8', '2', '9', '6', '1', '3', '2', '2', '1', '0', '3', '6', '5', '8', '2', '2', '4', '0', '1', '5', '9', '1', '1', '0', '9', '6', '4', '3', '5', '0', '7', '3', '8', '4', '3', '4', '9', '3', '1', '1', '6', '3', '4', '4', '8', '3', '5', '3', '5', '2', '5', '4', '3', '4', '3', '0', '4', '7', '7', '2', '6', '5', '5', '8', '3', '8', '4', '0', '4', '5', '5', '7', '4', '0', '5', '3', '1', '1', '1', '0', '1', '2', '3', '4', '8', '0', '9', '5', '4', '0', '2', '5', '3', '5', '7', '9', '0', '3', '1', '8', '3', '1', '2', '5', '2', '8', '0', '4', '6', '6', '3', '7', '4', '1', '7', '5', '0', '9', '1', '3', '8', '8', '0', '1', '2', '2', '6', '1', '9', '6', '9', '6', '9', '6', '6', '0', '7', '5', '4', '2', '1', '9', '5', '8', '6', '7', '6', '2', '7', '7', '8', '7', '4', '7', '7', '5', '0', '4', '4', '0', '9', '5', '5', '0', '8', '4', '5', '8', '7', '4', '4', '7', '8', '9', '0', '0', '6', '7', '2', '2', '2', '4', '5', '2', '7', '4', '1', '"', ',']

theorem object_fragment0164829_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 463) (SourceJson.white (fragment0164829Field007Chars00 ++ tail)) fragment0164829Acc00700 =
      SourceJson.object (fuel + 462) (SourceJson.white tail) fragment0164829Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_007"
  err.flush

noncomputable def fragment0164829Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0164829Field008Value00 : SourceJson := .str (String.ofList ['5', '5', '8', '4', '3', '9', '2', '4', '7', '7', '4'])
noncomputable def fragment0164829Acc00900 : List (String × SourceJson) := (fragment0164829Field008Key00, fragment0164829Field008Value00) :: fragment0164829Acc00800
noncomputable def fragment0164829Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '5', '8', '4', '3', '9', '2', '4', '7', '7', '4', '"', ',']

theorem object_fragment0164829_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 462) (SourceJson.white (fragment0164829Field008Chars00 ++ tail)) fragment0164829Acc00800 =
      SourceJson.object (fuel + 461) (SourceJson.white tail) fragment0164829Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_008"
  err.flush

noncomputable def fragment0164829Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0164829Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '1', '6', '3', '6', '8', '4', '1', '2', '7', '2'])
noncomputable def fragment0164829Acc01000 : List (String × SourceJson) := (fragment0164829Field009Key00, fragment0164829Field009Value00) :: fragment0164829Acc00900
noncomputable def fragment0164829Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '1', '6', '3', '6', '8', '4', '1', '2', '7', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0164829_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 461) (SourceJson.white (fragment0164829Field009Chars00 ++ tail)) fragment0164829Acc00900 =
      .ok (.obj (fragment0164829Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0164829_object_field_009"
  err.flush

noncomputable def fragment0164829Chars : List Char := '{' :: (fragment0164829Field000Chars00 ++ fragment0164829Field001Chars00 ++ fragment0164829Field002Chars00 ++ fragment0164829Field003Chars00 ++ fragment0164829Field004Chars00 ++ fragment0164829Field005Chars00 ++ fragment0164829Field006Chars00 ++ fragment0164829Field007Chars00 ++ fragment0164829Field008Chars00 ++ fragment0164829Field009Chars00)
noncomputable def fragment0164829Value : SourceJson := .obj (fragment0164829Acc01000.reverse)

theorem value_fragment0164829 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 471) (fragment0164829Chars ++ tail) =
      .ok (fragment0164829Value, tail) := by
  have hinput : fragment0164829Chars ++ tail = '{' :: (fragment0164829Field000Chars00 ++ (fragment0164829Field001Chars00 ++ (fragment0164829Field002Chars00 ++ (fragment0164829Field003Chars00 ++ (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0164829Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 471) (fragment0164829Chars ++ tail) =
        SourceJson.value (fuel + 471) ('{' :: (fragment0164829Field000Chars00 ++ (fragment0164829Field001Chars00 ++ (fragment0164829Field002Chars00 ++ (fragment0164829Field003Chars00 ++ (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 471)) hinput
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment0164829Field000Chars00 ++ (fragment0164829Field001Chars00 ++ (fragment0164829Field002Chars00 ++ (fragment0164829Field003Chars00 ++ (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))))))))))) fragment0164829Acc00000 := by rfl
    _ = SourceJson.object (fuel + 469) (SourceJson.white (fragment0164829Field001Chars00 ++ (fragment0164829Field002Chars00 ++ (fragment0164829Field003Chars00 ++ (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail))))))))))) fragment0164829Acc00100 := object_fragment0164829_field_000 fuel (fragment0164829Field001Chars00 ++ (fragment0164829Field002Chars00 ++ (fragment0164829Field003Chars00 ++ (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 468) (SourceJson.white (fragment0164829Field002Chars00 ++ (fragment0164829Field003Chars00 ++ (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))))))))) fragment0164829Acc00200 := object_fragment0164829_field_001 fuel (fragment0164829Field002Chars00 ++ (fragment0164829Field003Chars00 ++ (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 467) (SourceJson.white (fragment0164829Field003Chars00 ++ (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail))))))))) fragment0164829Acc00300 := object_fragment0164829_field_002 fuel (fragment0164829Field003Chars00 ++ (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 466) (SourceJson.white (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))))))) fragment0164829Acc00400 := object_fragment0164829_field_003 fuel (fragment0164829Field004Chars00 ++ (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 465) (SourceJson.white (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail))))))) fragment0164829Acc00500 := object_fragment0164829_field_004 fuel (fragment0164829Field005Chars00 ++ (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 464) (SourceJson.white (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))))) fragment0164829Acc00600 := object_fragment0164829_field_005 fuel (fragment0164829Field006Chars00 ++ (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 463) (SourceJson.white (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail))))) fragment0164829Acc00700 := object_fragment0164829_field_006 fuel (fragment0164829Field007Chars00 ++ (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 462) (SourceJson.white (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))) fragment0164829Acc00800 := object_fragment0164829_field_007 fuel (fragment0164829Field008Chars00 ++ (fragment0164829Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 461) (SourceJson.white (fragment0164829Field009Chars00 ++ (tail))) fragment0164829Acc00900 := object_fragment0164829_field_008 fuel (fragment0164829Field009Chars00 ++ (tail))
    _ = .ok (fragment0164829Value, tail) := object_fragment0164829_field_009 fuel (tail)

noncomputable def fragment0166929Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0166929Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0166929Field000Value00 : SourceJson := .number (String.ofList ['2', '2'])
noncomputable def fragment0166929Acc00100 : List (String × SourceJson) := (fragment0166929Field000Key00, fragment0166929Field000Value00) :: fragment0166929Acc00000
noncomputable def fragment0166929Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '2', ',']

theorem object_fragment0166929_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0166929Field000Chars00 ++ tail)) fragment0166929Acc00000 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0166929Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_000"
  err.flush

noncomputable def fragment0166929Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0166929Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0166929Acc00200 : List (String × SourceJson) := (fragment0166929Field001Key00, fragment0166929Field001Value00) :: fragment0166929Acc00100
noncomputable def fragment0166929Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0166929_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0166929Field001Chars00 ++ tail)) fragment0166929Acc00100 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0166929Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_001"
  err.flush

noncomputable def fragment0166929Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0166929Field002Value00 : SourceJson := .str (String.ofList ['9', '4', '0', '6', '3', '5', '3', '1', '0', '6', '0', '6', '3', '2', '6', '6', '8', '7', '3', '7', '5', '9', '0', '8', '7', '9', '3', '5', '7', '3', '0', '4', '3', '0', '2', '1', '0', '0', '6', '1', '/', '7', '7', '0', '5', '5', '8', '4', '3', '1', '3', '5', '5', '5', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0166929Acc00300 : List (String × SourceJson) := (fragment0166929Field002Key00, fragment0166929Field002Value00) :: fragment0166929Acc00200
noncomputable def fragment0166929Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '4', '0', '6', '3', '5', '3', '1', '0', '6', '0', '6', '3', '2', '6', '6', '8', '7', '3', '7', '5', '9', '0', '8', '7', '9', '3', '5', '7', '3', '0', '4', '3', '0', '2', '1', '0', '0', '6', '1', '/', '7', '7', '0', '5', '5', '8', '4', '3', '1', '3', '5', '5', '5', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0166929_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0166929Field002Chars00 ++ tail)) fragment0166929Acc00200 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0166929Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_002"
  err.flush

noncomputable def fragment0166929Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0166929Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0166929Acc00400 : List (String × SourceJson) := (fragment0166929Field003Key00, fragment0166929Field003Value00) :: fragment0166929Acc00300
noncomputable def fragment0166929Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0166929_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0166929Field003Chars00 ++ tail)) fragment0166929Acc00300 =
      SourceJson.object (fuel + 428) (SourceJson.white tail) fragment0166929Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_003"
  err.flush

noncomputable def fragment0166929Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0166929Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0166929Acc00500 : List (String × SourceJson) := (fragment0166929Field004Key00, fragment0166929Field004Value00) :: fragment0166929Acc00400
noncomputable def fragment0166929Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0166929_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 428) (SourceJson.white (fragment0166929Field004Chars00 ++ tail)) fragment0166929Acc00400 =
      SourceJson.object (fuel + 427) (SourceJson.white tail) fragment0166929Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_004"
  err.flush

noncomputable def fragment0166929Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0166929Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '9', '5', '4', '3', '9', '5', '7', '1', '7', '4', '5', '2', '5', '0', '4', '0', '9', '5', '4', '8', '3', '/', '5', '5', '1', '4', '9', '6', '7', '6', '4', '2', '5', '3', '7', '3', '2', '4', '1', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '5', '5', '5', '6', '2', '8', '1', '8', '8', '4', '2', '2', '9', '1', '2', '0', '5', '4', '3', '/', '1', '4', '6', '5', '7', '7', '2', '1', '3', '0', '9', '0', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '5', '4', '2', '4', '2', '9', '7', '7', '9', '6', '3', '9', '3', '1', '2', '9', '6', '5', '9', '2', '9', '/', '2', '5', '5', '7', '6', '6', '6', '1', '5', '3', '0', '6', '0', '7', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '5', '5', '4', '4', '8', '5', '9', '2', '1', '7', '2', '9', '7', '1', '7', '8', '8', '8', '1', '7', '6', '1', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '9', '8', '7', '1', '0', '2', '2', '1', '4', '5', '1', '4', '7', '5', '9', '9', '4', '7', '9', '2', '8', '7', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '0', '7', '6', '0', '6', '0', '6', '6', '6', '5', '0', '3', '9', '8', '9', '7', '1', '2', '6', '3', '/', '1', '0', '6', '9', '5', '6', '9', '4', '8', '2', '1', '8', '9', '0', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '0', '6', '3', '6', '3', '2', '8', '9', '4', '0', '1', '0', '4', '6', '7', '0', '6', '9', '/', '6', '4', '1', '7', '4', '1', '6', '8', '9', '3', '1', '3', '4', '3', '4', '0', '8', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '2', '9', '9', '6', '6', '3', '7', '0', '0', '2', '8', '8', '7', '7', '8', '3', '0', '0', '5', '1', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '4', '2', '7', '6', '2', '0', '4', '4', '9', '9', '4', '9', '5', '5', '7', '9', '2', '0', '6', '7', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '2', '0', '3', '0', '1', '9', '8', '4', '8', '7', '0', '0', '0', '6', '2', '7', '7', '4', '1', '/', '1', '4', '6', '5', '7', '7', '2', '1', '3', '0', '9', '0', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0166929Acc00600 : List (String × SourceJson) := (fragment0166929Field005Key00, fragment0166929Field005Value00) :: fragment0166929Acc00500
noncomputable def fragment0166929Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '5', '4', '3', '9', '5', '7', '1', '7', '4', '5', '2', '5', '0', '4', '0', '9', '5', '4', '8', '3', '/', '5', '5', '1', '4', '9', '6', '7', '6', '4', '2', '5', '3', '7', '3', '2', '4', '1', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '5', '5', '5', '6', '2', '8', '1', '8', '8', '4', '2', '2', '9', '1', '2', '0', '5', '4', '3', '/', '1', '4', '6', '5', '7', '7', '2', '1', '3', '0', '9', '0', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '4', '2', '4', '2', '9', '7', '7', '9', '6', '3', '9', '3', '1', '2', '9', '6', '5', '9', '2', '9', '/', '2', '5', '5', '7', '6', '6', '6', '1', '5', '3', '0', '6', '0', '7', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '5', '5', '4', '4', '8', '5', '9', '2', '1', '7', '2', '9', '7', '1', '7', '8', '8', '8', '1', '7', '6', '1', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '9', '8', '7', '1', '0', '2', '2', '1', '4', '5', '1', '4', '7', '5', '9', '9', '4', '7', '9', '2', '8', '7', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '0', '7', '6', '0', '6', '0', '6', '6', '6', '5', '0', '3', '9', '8', '9', '7', '1', '2', '6', '3', '/', '1', '0', '6', '9', '5', '6', '9', '4', '8', '2', '1', '8', '9', '0', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '6', '3', '6', '3', '2', '8', '9', '4', '0', '1', '0', '4', '6', '7', '0', '6', '9', '/', '6', '4', '1', '7', '4', '1', '6', '8', '9', '3', '1', '3', '4', '3', '4', '0', '8', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '2', '9', '9', '6', '6', '3', '7', '0', '0', '2', '8', '8', '7', '7', '8', '3', '0', '0', '5', '1', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '4', '2', '7', '6', '2', '0', '4', '4', '9', '9', '4', '9', '5', '5', '7', '9', '2', '0', '6', '7', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '2', '0', '3', '0', '1', '9', '8', '4', '8', '7', '0', '0', '0', '6', '2', '7', '7', '4', '1', '/', '1', '4', '6', '5', '7', '7', '2', '1', '3', '0', '9', '0', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0166929_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 427) (SourceJson.white (fragment0166929Field005Chars00 ++ tail)) fragment0166929Acc00500 =
      SourceJson.object (fuel + 426) (SourceJson.white tail) fragment0166929Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_005"
  err.flush

noncomputable def fragment0166929Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0166929Field006Value00 : SourceJson := .str (String.ofList ['2', '0', '1', '3', '1', '3', '9', '8', '5', '7', '3', '5', '5', '2', '3', '9', '4', '9', '3', '8', '8', '5', '3', '8', '4', '6', '5', '5', '3', '5', '9', '4', '6', '3', '4', '6', '9', '5', '8', '6', '0', '8', '1', '8', '0', '5', '2', '9', '5', '8', '7', '2', '0', '0', '0', '0', '0', '/', '4', '2', '2', '9', '3', '6', '4', '4', '2', '8', '7', '2', '6', '6', '6', '7', '5', '2', '2', '2', '1', '5', '6', '3', '0', '7', '4', '6', '4', '7', '1', '7', '1', '5', '2', '3', '9', '8', '6', '2', '3', '1', '5', '8', '0', '6', '0', '6', '1', '9', '2', '5', '2', '1', '1', '1', '3', '0', '2', '0', '8', '1', '7', '9', '1', '9', '4', '1', '3', '9', '9', '9', '4', '9'])
noncomputable def fragment0166929Acc00700 : List (String × SourceJson) := (fragment0166929Field006Key00, fragment0166929Field006Value00) :: fragment0166929Acc00600
noncomputable def fragment0166929Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '0', '1', '3', '1', '3', '9', '8', '5', '7', '3', '5', '5', '2', '3', '9', '4', '9', '3', '8', '8', '5', '3', '8', '4', '6', '5', '5', '3', '5', '9', '4', '6', '3', '4', '6', '9', '5', '8', '6', '0', '8', '1', '8', '0', '5', '2', '9', '5', '8', '7', '2', '0', '0', '0', '0', '0', '/', '4', '2', '2', '9', '3', '6', '4', '4', '2', '8', '7', '2', '6', '6', '6', '7', '5', '2', '2', '2', '1', '5', '6', '3', '0', '7', '4', '6', '4', '7', '1', '7', '1', '5', '2', '3', '9', '8', '6', '2', '3', '1', '5', '8', '0', '6', '0', '6', '1', '9', '2', '5', '2', '1', '1', '1', '3', '0', '2', '0', '8', '1', '7', '9', '1', '9', '4', '1', '3', '9', '9', '9', '4', '9', '"', ',']

theorem object_fragment0166929_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 426) (SourceJson.white (fragment0166929Field006Chars00 ++ tail)) fragment0166929Acc00600 =
      SourceJson.object (fuel + 425) (SourceJson.white tail) fragment0166929Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_006"
  err.flush

noncomputable def fragment0166929Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0166929Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '3', '1', '6', '7', '6', '6', '1', '5', '7', '0', '4', '3', '8', '8', '8', '7', '8', '2', '5', '8', '7', '3', '5', '5', '3', '5', '7', '9', '0', '6', '6', '6', '0', '5', '8', '4', '7', '4', '4', '5', '3', '2', '0', '4', '4', '3', '1', '9', '9', '1', '6', '8', '4', '6', '2', '9', '6', '7', '2', '5', '8', '4', '5', '7', '2', '1', '3', '4', '0', '2', '1', '4', '2', '0', '7', '5', '1', '3', '1', '2', '1', '0', '0', '8', '2', '0', '1', '8', '4', '0', '7', '3', '9', '4', '9', '2', '6', '6', '6', '4', '1', '4', '5', '1', '9', '4', '9', '2', '9', '5', '6', '0', '3', '6', '9', '1', '1', '6', '3', '8', '4', '8', '7', '5', '3', '1', '6', '1', '3', '6', '5', '9', '0', '2', '0', '3', '0', '0', '5', '6', '0', '9', '8', '6', '6', '9', '2', '1', '2', '3', '3', '1', '2', '0', '8', '7', '1', '4', '6', '0', '7', '4', '8', '1', '8', '8', '5', '8', '1', '6', '7', '8', '5', '0', '2', '1', '9', '9', '0', '1', '6', '5', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '9', '9', '9', '8', '2', '7', '9', '1', '3', '4', '7', '7', '3', '0', '4', '2', '8', '7', '2', '6', '3', '2', '8', '1', '1', '3', '7', '9', '3', '0', '5', '2', '7', '3', '7', '2', '1', '0', '5', '3', '9', '4', '4', '6', '1', '8', '5', '8', '9', '5', '4', '5', '1', '2', '3', '6', '3', '2', '9', '5', '6', '7', '0', '9', '4', '7', '8', '0', '3', '5', '2', '8', '7', '8', '3', '7', '5', '9', '5', '0', '2', '1', '2', '5', '5', '9', '0', '8', '8', '4', '4', '2', '5', '1', '1', '6', '2', '2', '1', '7', '2', '0', '2', '5', '5', '1', '6', '7', '8', '8', '0', '2', '5', '9', '3', '2', '5', '2', '7', '3', '3', '0', '0', '3', '4', '6', '0', '4', '6', '2', '9', '2', '2', '4', '3', '5', '5', '4', '5', '6', '0', '8', '0', '6', '8', '7', '4', '3', '0', '2', '6', '9', '7', '6', '4', '9', '9', '6', '9', '8', '9', '5', '1', '2', '7', '5', '5', '5', '3', '8', '3', '9', '6', '1', '7', '1', '9', '1', '9', '1', '4', '4', '4', '2', '2', '4', '1', '8', '8', '1', '2', '6', '2', '6', '5', '0', '8', '4', '5', '2', '9', '3', '1', '4', '2', '6', '4', '1', '9', '3', '6', '6', '9', '4', '3', '8', '3'])
noncomputable def fragment0166929Acc00800 : List (String × SourceJson) := (fragment0166929Field007Key00, fragment0166929Field007Value00) :: fragment0166929Acc00700
noncomputable def fragment0166929Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '3', '1', '6', '7', '6', '6', '1', '5', '7', '0', '4', '3', '8', '8', '8', '7', '8', '2', '5', '8', '7', '3', '5', '5', '3', '5', '7', '9', '0', '6', '6', '6', '0', '5', '8', '4', '7', '4', '4', '5', '3', '2', '0', '4', '4', '3', '1', '9', '9', '1', '6', '8', '4', '6', '2', '9', '6', '7', '2', '5', '8', '4', '5', '7', '2', '1', '3', '4', '0', '2', '1', '4', '2', '0', '7', '5', '1', '3', '1', '2', '1', '0', '0', '8', '2', '0', '1', '8', '4', '0', '7', '3', '9', '4', '9', '2', '6', '6', '6', '4', '1', '4', '5', '1', '9', '4', '9', '2', '9', '5', '6', '0', '3', '6', '9', '1', '1', '6', '3', '8', '4', '8', '7', '5', '3', '1', '6', '1', '3', '6', '5', '9', '0', '2', '0', '3', '0', '0', '5', '6', '0', '9', '8', '6', '6', '9', '2', '1', '2', '3', '3', '1', '2', '0', '8', '7', '1', '4', '6', '0', '7', '4', '8', '1', '8', '8', '5', '8', '1', '6', '7', '8', '5', '0', '2', '1', '9', '9', '0', '1', '6', '5', '9', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '9', '9', '9', '8', '2', '7', '9', '1', '3', '4', '7', '7', '3', '0', '4', '2', '8', '7', '2', '6', '3', '2', '8', '1', '1', '3', '7', '9', '3', '0', '5', '2', '7', '3', '7', '2', '1', '0', '5', '3', '9', '4', '4', '6', '1', '8', '5', '8', '9', '5', '4', '5', '1', '2', '3', '6', '3', '2', '9', '5', '6', '7', '0', '9', '4', '7', '8', '0', '3', '5', '2', '8', '7', '8', '3', '7', '5', '9', '5', '0', '2', '1', '2', '5', '5', '9', '0', '8', '8', '4', '4', '2', '5', '1', '1', '6', '2', '2', '1', '7', '2', '0', '2', '5', '5', '1', '6', '7', '8', '8', '0', '2', '5', '9', '3', '2', '5', '2', '7', '3', '3', '0', '0', '3', '4', '6', '0', '4', '6', '2', '9', '2', '2', '4', '3', '5', '5', '4', '5', '6', '0', '8', '0', '6', '8', '7', '4', '3', '0', '2', '6', '9', '7', '6', '4', '9', '9', '6', '9', '8', '9', '5', '1', '2', '7', '5', '5', '5', '3', '8', '3', '9', '6', '1', '7', '1', '9', '1', '9', '1', '4', '4', '4', '2', '2', '4', '1', '8', '8', '1', '2', '6', '2', '6', '5', '0', '8', '4', '5', '2', '9', '3', '1', '4', '2', '6', '4', '1', '9', '3', '6', '6', '9', '4', '3', '8', '3', '"', ',']

theorem object_fragment0166929_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 425) (SourceJson.white (fragment0166929Field007Chars00 ++ tail)) fragment0166929Acc00700 =
      SourceJson.object (fuel + 424) (SourceJson.white tail) fragment0166929Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_007"
  err.flush

noncomputable def fragment0166929Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0166929Field008Value00 : SourceJson := .str (String.ofList ['3', '7', '7', '1', '1', '9', '0', '0', '7', '9', '9', '8'])
noncomputable def fragment0166929Acc00900 : List (String × SourceJson) := (fragment0166929Field008Key00, fragment0166929Field008Value00) :: fragment0166929Acc00800
noncomputable def fragment0166929Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '7', '1', '1', '9', '0', '0', '7', '9', '9', '8', '"', ',']

theorem object_fragment0166929_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 424) (SourceJson.white (fragment0166929Field008Chars00 ++ tail)) fragment0166929Acc00800 =
      SourceJson.object (fuel + 423) (SourceJson.white tail) fragment0166929Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_008"
  err.flush

noncomputable def fragment0166929Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0166929Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '7', '3', '0', '4', '9', '4', '9', '8', '0', '3'])
noncomputable def fragment0166929Acc01000 : List (String × SourceJson) := (fragment0166929Field009Key00, fragment0166929Field009Value00) :: fragment0166929Acc00900
noncomputable def fragment0166929Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '7', '3', '0', '4', '9', '4', '9', '8', '0', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0166929_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 423) (SourceJson.white (fragment0166929Field009Chars00 ++ tail)) fragment0166929Acc00900 =
      .ok (.obj (fragment0166929Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0166929_object_field_009"
  err.flush

noncomputable def fragment0166929Chars : List Char := '{' :: (fragment0166929Field000Chars00 ++ fragment0166929Field001Chars00 ++ fragment0166929Field002Chars00 ++ fragment0166929Field003Chars00 ++ fragment0166929Field004Chars00 ++ fragment0166929Field005Chars00 ++ fragment0166929Field006Chars00 ++ fragment0166929Field007Chars00 ++ fragment0166929Field008Chars00 ++ fragment0166929Field009Chars00)
noncomputable def fragment0166929Value : SourceJson := .obj (fragment0166929Acc01000.reverse)

theorem value_fragment0166929 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 433) (fragment0166929Chars ++ tail) =
      .ok (fragment0166929Value, tail) := by
  have hinput : fragment0166929Chars ++ tail = '{' :: (fragment0166929Field000Chars00 ++ (fragment0166929Field001Chars00 ++ (fragment0166929Field002Chars00 ++ (fragment0166929Field003Chars00 ++ (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0166929Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 433) (fragment0166929Chars ++ tail) =
        SourceJson.value (fuel + 433) ('{' :: (fragment0166929Field000Chars00 ++ (fragment0166929Field001Chars00 ++ (fragment0166929Field002Chars00 ++ (fragment0166929Field003Chars00 ++ (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 433)) hinput
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0166929Field000Chars00 ++ (fragment0166929Field001Chars00 ++ (fragment0166929Field002Chars00 ++ (fragment0166929Field003Chars00 ++ (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))))))))))) fragment0166929Acc00000 := by rfl
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0166929Field001Chars00 ++ (fragment0166929Field002Chars00 ++ (fragment0166929Field003Chars00 ++ (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail))))))))))) fragment0166929Acc00100 := object_fragment0166929_field_000 fuel (fragment0166929Field001Chars00 ++ (fragment0166929Field002Chars00 ++ (fragment0166929Field003Chars00 ++ (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0166929Field002Chars00 ++ (fragment0166929Field003Chars00 ++ (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))))))))) fragment0166929Acc00200 := object_fragment0166929_field_001 fuel (fragment0166929Field002Chars00 ++ (fragment0166929Field003Chars00 ++ (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0166929Field003Chars00 ++ (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail))))))))) fragment0166929Acc00300 := object_fragment0166929_field_002 fuel (fragment0166929Field003Chars00 ++ (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 428) (SourceJson.white (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))))))) fragment0166929Acc00400 := object_fragment0166929_field_003 fuel (fragment0166929Field004Chars00 ++ (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 427) (SourceJson.white (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail))))))) fragment0166929Acc00500 := object_fragment0166929_field_004 fuel (fragment0166929Field005Chars00 ++ (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 426) (SourceJson.white (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))))) fragment0166929Acc00600 := object_fragment0166929_field_005 fuel (fragment0166929Field006Chars00 ++ (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 425) (SourceJson.white (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail))))) fragment0166929Acc00700 := object_fragment0166929_field_006 fuel (fragment0166929Field007Chars00 ++ (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 424) (SourceJson.white (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))) fragment0166929Acc00800 := object_fragment0166929_field_007 fuel (fragment0166929Field008Chars00 ++ (fragment0166929Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 423) (SourceJson.white (fragment0166929Field009Chars00 ++ (tail))) fragment0166929Acc00900 := object_fragment0166929_field_008 fuel (fragment0166929Field009Chars00 ++ (tail))
    _ = .ok (fragment0166929Value, tail) := object_fragment0166929_field_009 fuel (tail)

noncomputable def fragment0168948Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0168948Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0168948Field000Value00 : SourceJson := .number (String.ofList ['2', '3'])
noncomputable def fragment0168948Acc00100 : List (String × SourceJson) := (fragment0168948Field000Key00, fragment0168948Field000Value00) :: fragment0168948Acc00000
noncomputable def fragment0168948Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '3', ',']

theorem object_fragment0168948_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 373) (SourceJson.white (fragment0168948Field000Chars00 ++ tail)) fragment0168948Acc00000 =
      SourceJson.object (fuel + 372) (SourceJson.white tail) fragment0168948Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_000"
  err.flush

noncomputable def fragment0168948Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0168948Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0168948Acc00200 : List (String × SourceJson) := (fragment0168948Field001Key00, fragment0168948Field001Value00) :: fragment0168948Acc00100
noncomputable def fragment0168948Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0168948_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 372) (SourceJson.white (fragment0168948Field001Chars00 ++ tail)) fragment0168948Acc00100 =
      SourceJson.object (fuel + 371) (SourceJson.white tail) fragment0168948Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_001"
  err.flush

noncomputable def fragment0168948Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0168948Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '6', '6', '7', '7', '3', '0', '0', '1', '0', '2', '9', '1', '8', '3', '4', '0', '2', '1', '0', '3', '4', '0', '5', '0', '3', '9', '9', '8', '1', '7', '6', '6', '4', '5', '4', '1', '5', '6', '3', '/', '1', '0', '7', '5', '1', '9', '7', '8', '1', '1', '1', '9', '3', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0168948Acc00300 : List (String × SourceJson) := (fragment0168948Field002Key00, fragment0168948Field002Value00) :: fragment0168948Acc00200
noncomputable def fragment0168948Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '6', '6', '7', '7', '3', '0', '0', '1', '0', '2', '9', '1', '8', '3', '4', '0', '2', '1', '0', '3', '4', '0', '5', '0', '3', '9', '9', '8', '1', '7', '6', '6', '4', '5', '4', '1', '5', '6', '3', '/', '1', '0', '7', '5', '1', '9', '7', '8', '1', '1', '1', '9', '3', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0168948_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 371) (SourceJson.white (fragment0168948Field002Chars00 ++ tail)) fragment0168948Acc00200 =
      SourceJson.object (fuel + 370) (SourceJson.white tail) fragment0168948Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_002"
  err.flush

noncomputable def fragment0168948Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0168948Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0168948Acc00400 : List (String × SourceJson) := (fragment0168948Field003Key00, fragment0168948Field003Value00) :: fragment0168948Acc00300
noncomputable def fragment0168948Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0168948_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 370) (SourceJson.white (fragment0168948Field003Chars00 ++ tail)) fragment0168948Acc00300 =
      SourceJson.object (fuel + 369) (SourceJson.white tail) fragment0168948Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_003"
  err.flush

noncomputable def fragment0168948Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0168948Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0168948Acc00500 : List (String × SourceJson) := (fragment0168948Field004Key00, fragment0168948Field004Value00) :: fragment0168948Acc00400
noncomputable def fragment0168948Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0168948_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment0168948Field004Chars00 ++ tail)) fragment0168948Acc00400 =
      SourceJson.object (fuel + 368) (SourceJson.white tail) fragment0168948Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_004"
  err.flush

noncomputable def fragment0168948Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0168948Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '6', '1', '7', '6', '6', '8', '3', '4', '4', '4', '2', '5', '0', '2', '8', '3', '9', '1', '/', '3', '9', '9', '8', '9', '7', '7', '9', '6', '0', '3', '0', '4', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '1', '2', '8', '2', '5', '9', '6', '6', '8', '5', '7', '8', '2', '0', '9', '4', '2', '1', '/', '2', '2', '8', '5', '1', '3', '0', '2', '6', '3', '0', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '4', '9', '5', '6', '6', '7', '9', '5', '1', '2', '2', '4', '3', '6', '0', '1', '1', '/', '9', '2', '7', '2', '9', '9', '2', '3', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '5', '6', '2', '1', '5', '5', '6', '8', '9', '4', '8', '0', '0', '6', '6', '7', '6', '5', '9', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '6', '3', '1', '3', '3', '3', '2', '8', '7', '0', '4', '1', '3', '4', '2', '7', '5', '5', '3', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '3', '9', '9', '5', '9', '1', '0', '7', '6', '6', '9', '6', '8', '5', '9', '3', '/', '3', '8', '7', '7', '7', '9', '6', '8', '0', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '5', '8', '5', '5', '2', '9', '9', '2', '1', '6', '4', '0', '0', '1', '7', '3', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '9', '5', '2', '2', '3', '0', '9', '7', '3', '3', '5', '6', '0', '1', '8', '3', '/', '1', '1', '6', '3', '3', '3', '9', '0', '4', '2', '9', '9', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '1', '5', '9', '9', '5', '0', '2', '8', '2', '7', '6', '6', '2', '9', '6', '1', '9', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '0', '1', '4', '2', '9', '2', '8', '2', '9', '4', '6', '1', '0', '8', '3', '2', '7', '/', '2', '2', '8', '5', '1', '3', '0', '2', '6', '3', '0', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0168948Acc00600 : List (String × SourceJson) := (fragment0168948Field005Key00, fragment0168948Field005Value00) :: fragment0168948Acc00500
noncomputable def fragment0168948Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '1', '7', '6', '6', '8', '3', '4', '4', '4', '2', '5', '0', '2', '8', '3', '9', '1', '/', '3', '9', '9', '8', '9', '7', '7', '9', '6', '0', '3', '0', '4', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '2', '8', '2', '5', '9', '6', '6', '8', '5', '7', '8', '2', '0', '9', '4', '2', '1', '/', '2', '2', '8', '5', '1', '3', '0', '2', '6', '3', '0', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '4', '9', '5', '6', '6', '7', '9', '5', '1', '2', '2', '4', '3', '6', '0', '1', '1', '/', '9', '2', '7', '2', '9', '9', '2', '3', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '5', '6', '2', '1', '5', '5', '6', '8', '9', '4', '8', '0', '0', '6', '6', '7', '6', '5', '9', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '6', '3', '1', '3', '3', '3', '2', '8', '7', '0', '4', '1', '3', '4', '2', '7', '5', '5', '3', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '0', '3', '9', '9', '5', '9', '1', '0', '7', '6', '6', '9', '6', '8', '5', '9', '3', '/', '3', '8', '7', '7', '7', '9', '6', '8', '0', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '5', '8', '5', '5', '2', '9', '9', '2', '1', '6', '4', '0', '0', '1', '7', '3', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '9', '5', '2', '2', '3', '0', '9', '7', '3', '3', '5', '6', '0', '1', '8', '3', '/', '1', '1', '6', '3', '3', '3', '9', '0', '4', '2', '9', '9', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '5', '9', '9', '5', '0', '2', '8', '2', '7', '6', '6', '2', '9', '6', '1', '9', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '0', '1', '4', '2', '9', '2', '8', '2', '9', '4', '6', '1', '0', '8', '3', '2', '7', '/', '2', '2', '8', '5', '1', '3', '0', '2', '6', '3', '0', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0168948_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0168948Field005Chars00 ++ tail)) fragment0168948Acc00500 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment0168948Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_005"
  err.flush

noncomputable def fragment0168948Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0168948Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '5', '2', '5', '8', '8', '0', '9', '2', '6', '7', '1', '2', '8', '8', '6', '9', '8', '0', '6', '5', '9', '9', '7', '8', '1', '7', '4', '5', '2', '8', '3', '3', '1', '8', '0', '5', '3', '4', '1', '7', '0', '8', '5', '0', '8', '1', '6', '0', '0', '/', '6', '7', '9', '8', '8', '2', '7', '6', '1', '7', '5', '7', '1', '0', '8', '4', '7', '6', '2', '6', '0', '0', '4', '2', '9', '5', '9', '2', '5', '5', '8', '5', '8', '2', '3', '5', '2', '9', '2', '3', '4', '8', '4', '5', '2', '8', '0', '8', '2', '6', '3', '9', '1', '4', '4', '7', '3', '2', '8', '8', '5', '6', '8', '3', '6', '7', '7'])
noncomputable def fragment0168948Acc00700 : List (String × SourceJson) := (fragment0168948Field006Key00, fragment0168948Field006Value00) :: fragment0168948Acc00600
noncomputable def fragment0168948Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '5', '2', '5', '8', '8', '0', '9', '2', '6', '7', '1', '2', '8', '8', '6', '9', '8', '0', '6', '5', '9', '9', '7', '8', '1', '7', '4', '5', '2', '8', '3', '3', '1', '8', '0', '5', '3', '4', '1', '7', '0', '8', '5', '0', '8', '1', '6', '0', '0', '/', '6', '7', '9', '8', '8', '2', '7', '6', '1', '7', '5', '7', '1', '0', '8', '4', '7', '6', '2', '6', '0', '0', '4', '2', '9', '5', '9', '2', '5', '5', '8', '5', '8', '2', '3', '5', '2', '9', '2', '3', '4', '8', '4', '5', '2', '8', '0', '8', '2', '6', '3', '9', '1', '4', '4', '7', '3', '2', '8', '8', '5', '6', '8', '3', '6', '7', '7', '"', ',']

theorem object_fragment0168948_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0168948Field006Chars00 ++ tail)) fragment0168948Acc00600 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0168948Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_006"
  err.flush

noncomputable def fragment0168948Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0168948Field007Value00 : SourceJson := .str (String.ofList ['3', '3', '6', '1', '8', '4', '2', '9', '2', '7', '5', '1', '1', '8', '1', '1', '5', '9', '7', '5', '6', '0', '9', '1', '8', '8', '6', '3', '5', '3', '9', '0', '6', '9', '8', '4', '8', '4', '6', '6', '1', '7', '8', '7', '2', '9', '1', '4', '3', '1', '2', '9', '3', '6', '0', '3', '7', '3', '6', '9', '8', '8', '1', '7', '5', '3', '9', '2', '2', '5', '6', '9', '5', '5', '1', '3', '8', '6', '8', '0', '1', '1', '1', '9', '2', '7', '9', '5', '9', '4', '4', '4', '3', '5', '8', '5', '4', '5', '7', '1', '5', '9', '7', '0', '3', '6', '3', '8', '2', '5', '7', '7', '4', '5', '6', '9', '8', '6', '6', '1', '5', '8', '5', '6', '0', '4', '0', '2', '3', '4', '8', '4', '3', '9', '2', '4', '7', '3', '2', '7', '1', '1', '2', '2', '6', '8', '6', '6', '3', '9', '8', '3', '9', '0', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '3', '3', '1', '3', '3', '4', '9', '4', '4', '6', '0', '1', '5', '4', '8', '7', '1', '1', '1', '7', '6', '7', '7', '4', '2', '9', '3', '7', '0', '2', '0', '7', '5', '3', '1', '5', '3', '6', '7', '3', '5', '4', '4', '5', '8', '1', '3', '0', '4', '6', '8', '6', '0', '6', '5', '4', '7', '2', '9', '3', '0', '5', '2', '4', '3', '4', '0', '4', '8', '6', '2', '7', '3', '0', '6', '5', '7', '2', '1', '5', '6', '8', '9', '9', '3', '1', '7', '3', '5', '6', '4', '5', '3', '6', '8', '6', '2', '0', '9', '9', '7', '7', '1', '8', '2', '8', '4', '9', '6', '0', '1', '5', '5', '5', '3', '0', '6', '0', '5', '3', '0', '4', '3', '9', '9', '1', '9', '0', '8', '8', '7', '6', '2', '1', '0', '7', '2', '8', '6', '7', '9', '0', '8', '1', '0', '1', '0', '1', '4', '6', '6', '4', '8', '1', '6', '6', '3', '6', '5', '2', '8', '5', '9', '6', '8', '7', '9', '7', '0', '0', '1', '7', '1', '9', '0', '9', '6', '4', '6', '7', '5', '1', '4', '9', '8', '6', '7'])
noncomputable def fragment0168948Acc00800 : List (String × SourceJson) := (fragment0168948Field007Key00, fragment0168948Field007Value00) :: fragment0168948Acc00700
noncomputable def fragment0168948Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '6', '1', '8', '4', '2', '9', '2', '7', '5', '1', '1', '8', '1', '1', '5', '9', '7', '5', '6', '0', '9', '1', '8', '8', '6', '3', '5', '3', '9', '0', '6', '9', '8', '4', '8', '4', '6', '6', '1', '7', '8', '7', '2', '9', '1', '4', '3', '1', '2', '9', '3', '6', '0', '3', '7', '3', '6', '9', '8', '8', '1', '7', '5', '3', '9', '2', '2', '5', '6', '9', '5', '5', '1', '3', '8', '6', '8', '0', '1', '1', '1', '9', '2', '7', '9', '5', '9', '4', '4', '4', '3', '5', '8', '5', '4', '5', '7', '1', '5', '9', '7', '0', '3', '6', '3', '8', '2', '5', '7', '7', '4', '5', '6', '9', '8', '6', '6', '1', '5', '8', '5', '6', '0', '4', '0', '2', '3', '4', '8', '4', '3', '9', '2', '4', '7', '3', '2', '7', '1', '1', '2', '2', '6', '8', '6', '6', '3', '9', '8', '3', '9', '0', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '3', '3', '1', '3', '3', '4', '9', '4', '4', '6', '0', '1', '5', '4', '8', '7', '1', '1', '1', '7', '6', '7', '7', '4', '2', '9', '3', '7', '0', '2', '0', '7', '5', '3', '1', '5', '3', '6', '7', '3', '5', '4', '4', '5', '8', '1', '3', '0', '4', '6', '8', '6', '0', '6', '5', '4', '7', '2', '9', '3', '0', '5', '2', '4', '3', '4', '0', '4', '8', '6', '2', '7', '3', '0', '6', '5', '7', '2', '1', '5', '6', '8', '9', '9', '3', '1', '7', '3', '5', '6', '4', '5', '3', '6', '8', '6', '2', '0', '9', '9', '7', '7', '1', '8', '2', '8', '4', '9', '6', '0', '1', '5', '5', '5', '3', '0', '6', '0', '5', '3', '0', '4', '3', '9', '9', '1', '9', '0', '8', '8', '7', '6', '2', '1', '0', '7', '2', '8', '6', '7', '9', '0', '8', '1', '0', '1', '0', '1', '4', '6', '6', '4', '8', '1', '6', '6', '3', '6', '5', '2', '8', '5', '9', '6', '8', '7', '9', '7', '0', '0', '1', '7', '1', '9', '0', '9', '6', '4', '6', '7', '5', '1', '4', '9', '8', '6', '7', '"', ',']

theorem object_fragment0168948_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0168948Field007Chars00 ++ tail)) fragment0168948Acc00700 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0168948Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_007"
  err.flush

noncomputable def fragment0168948Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0168948Field008Value00 : SourceJson := .str (String.ofList ['2', '2', '7', '5', '3', '9', '1', '8', '0', '9', '1', '6', '6'])
noncomputable def fragment0168948Acc00900 : List (String × SourceJson) := (fragment0168948Field008Key00, fragment0168948Field008Value00) :: fragment0168948Acc00800
noncomputable def fragment0168948Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '7', '5', '3', '9', '1', '8', '0', '9', '1', '6', '6', '"', ',']

theorem object_fragment0168948_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0168948Field008Chars00 ++ tail)) fragment0168948Acc00800 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0168948Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_008"
  err.flush

noncomputable def fragment0168948Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0168948Field009Value00 : SourceJson := .str (String.ofList ['8', '5', '0', '1', '1', '5', '8', '2', '9', '0', '2', '3', '2'])
noncomputable def fragment0168948Acc01000 : List (String × SourceJson) := (fragment0168948Field009Key00, fragment0168948Field009Value00) :: fragment0168948Acc00900
noncomputable def fragment0168948Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '5', '0', '1', '1', '5', '8', '2', '9', '0', '2', '3', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0168948_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0168948Field009Chars00 ++ tail)) fragment0168948Acc00900 =
      .ok (.obj (fragment0168948Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0168948_object_field_009"
  err.flush

noncomputable def fragment0168948Chars : List Char := '{' :: (fragment0168948Field000Chars00 ++ fragment0168948Field001Chars00 ++ fragment0168948Field002Chars00 ++ fragment0168948Field003Chars00 ++ fragment0168948Field004Chars00 ++ fragment0168948Field005Chars00 ++ fragment0168948Field006Chars00 ++ fragment0168948Field007Chars00 ++ fragment0168948Field008Chars00 ++ fragment0168948Field009Chars00)
noncomputable def fragment0168948Value : SourceJson := .obj (fragment0168948Acc01000.reverse)

theorem value_fragment0168948 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 374) (fragment0168948Chars ++ tail) =
      .ok (fragment0168948Value, tail) := by
  have hinput : fragment0168948Chars ++ tail = '{' :: (fragment0168948Field000Chars00 ++ (fragment0168948Field001Chars00 ++ (fragment0168948Field002Chars00 ++ (fragment0168948Field003Chars00 ++ (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0168948Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 374) (fragment0168948Chars ++ tail) =
        SourceJson.value (fuel + 374) ('{' :: (fragment0168948Field000Chars00 ++ (fragment0168948Field001Chars00 ++ (fragment0168948Field002Chars00 ++ (fragment0168948Field003Chars00 ++ (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 374)) hinput
    _ = SourceJson.object (fuel + 373) (SourceJson.white (fragment0168948Field000Chars00 ++ (fragment0168948Field001Chars00 ++ (fragment0168948Field002Chars00 ++ (fragment0168948Field003Chars00 ++ (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))))))))))) fragment0168948Acc00000 := by rfl
    _ = SourceJson.object (fuel + 372) (SourceJson.white (fragment0168948Field001Chars00 ++ (fragment0168948Field002Chars00 ++ (fragment0168948Field003Chars00 ++ (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail))))))))))) fragment0168948Acc00100 := object_fragment0168948_field_000 fuel (fragment0168948Field001Chars00 ++ (fragment0168948Field002Chars00 ++ (fragment0168948Field003Chars00 ++ (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 371) (SourceJson.white (fragment0168948Field002Chars00 ++ (fragment0168948Field003Chars00 ++ (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))))))))) fragment0168948Acc00200 := object_fragment0168948_field_001 fuel (fragment0168948Field002Chars00 ++ (fragment0168948Field003Chars00 ++ (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 370) (SourceJson.white (fragment0168948Field003Chars00 ++ (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail))))))))) fragment0168948Acc00300 := object_fragment0168948_field_002 fuel (fragment0168948Field003Chars00 ++ (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))))))) fragment0168948Acc00400 := object_fragment0168948_field_003 fuel (fragment0168948Field004Chars00 ++ (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail))))))) fragment0168948Acc00500 := object_fragment0168948_field_004 fuel (fragment0168948Field005Chars00 ++ (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))))) fragment0168948Acc00600 := object_fragment0168948_field_005 fuel (fragment0168948Field006Chars00 ++ (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail))))) fragment0168948Acc00700 := object_fragment0168948_field_006 fuel (fragment0168948Field007Chars00 ++ (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))) fragment0168948Acc00800 := object_fragment0168948_field_007 fuel (fragment0168948Field008Chars00 ++ (fragment0168948Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0168948Field009Chars00 ++ (tail))) fragment0168948Acc00900 := object_fragment0168948_field_008 fuel (fragment0168948Field009Chars00 ++ (tail))
    _ = .ok (fragment0168948Value, tail) := object_fragment0168948_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_before_reader"
  err.flush

noncomputable def chunk0016LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0016SuffixChars00 : List Char := [',']
noncomputable def chunk0016Chars00 : List Char := chunk0016LeadChars00 ++ fragment0155531Chars ++ chunk0016SuffixChars00
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson := fragment0155531Value :: acc

noncomputable def chunk0016AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0016_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 641)
      (SourceJson.white (chunk0016LeadChars00 ++ (fragment0155531Chars ++ rest))) acc =
      (SourceJson.value (fuel + 640) (fragment0155531Chars ++ rest)).bind
        (chunk0016AfterValue00 (fuel + 640) acc) := by rfl

theorem array_chunk0016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 641) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 640) (SourceJson.white tail) (chunk0016Push00 acc) := by
  have hinput : chunk0016Chars00 ++ tail = chunk0016LeadChars00 ++ (fragment0155531Chars ++ (chunk0016SuffixChars00 ++ tail)) := by
    simp only [chunk0016Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 641) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 641)
          (SourceJson.white (chunk0016LeadChars00 ++ (fragment0155531Chars ++ (chunk0016SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 641) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 640) (fragment0155531Chars ++ (chunk0016SuffixChars00 ++ tail))).bind
        (chunk0016AfterValue00 (fuel + 640) acc) := array_chunk0016_head fuel (chunk0016SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0155531Value, chunk0016SuffixChars00 ++ tail)).bind
        (chunk0016AfterValue00 (fuel + 640) acc) :=
      congrArg (fun result => result.bind (chunk0016AfterValue00 (fuel + 640) acc))
        (value_fragment0155531 (fuel + 383) (chunk0016SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 640) (SourceJson.white tail) (chunk0016Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_before_reader"
  err.flush

noncomputable def chunk0017LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0017SuffixChars00 : List Char := [',']
noncomputable def chunk0017Chars00 : List Char := chunk0017LeadChars00 ++ fragment0157200Chars ++ chunk0017SuffixChars00
noncomputable def chunk0017Push00 (acc : List SourceJson) : List SourceJson := fragment0157200Value :: acc

noncomputable def chunk0017AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0017_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 640)
      (SourceJson.white (chunk0017LeadChars00 ++ (fragment0157200Chars ++ rest))) acc =
      (SourceJson.value (fuel + 639) (fragment0157200Chars ++ rest)).bind
        (chunk0017AfterValue00 (fuel + 639) acc) := by rfl

theorem array_chunk0017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 640) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 639) (SourceJson.white tail) (chunk0017Push00 acc) := by
  have hinput : chunk0017Chars00 ++ tail = chunk0017LeadChars00 ++ (fragment0157200Chars ++ (chunk0017SuffixChars00 ++ tail)) := by
    simp only [chunk0017Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 640) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 640)
          (SourceJson.white (chunk0017LeadChars00 ++ (fragment0157200Chars ++ (chunk0017SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 640) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 639) (fragment0157200Chars ++ (chunk0017SuffixChars00 ++ tail))).bind
        (chunk0017AfterValue00 (fuel + 639) acc) := array_chunk0017_head fuel (chunk0017SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0157200Value, chunk0017SuffixChars00 ++ tail)).bind
        (chunk0017AfterValue00 (fuel + 639) acc) :=
      congrArg (fun result => result.bind (chunk0017AfterValue00 (fuel + 639) acc))
        (value_fragment0157200 (fuel + 407) (chunk0017SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 639) (SourceJson.white tail) (chunk0017Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_before_reader"
  err.flush

noncomputable def chunk0018LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0018SuffixChars00 : List Char := [',']
noncomputable def chunk0018Chars00 : List Char := chunk0018LeadChars00 ++ fragment0158782Chars ++ chunk0018SuffixChars00
noncomputable def chunk0018Push00 (acc : List SourceJson) : List SourceJson := fragment0158782Value :: acc

noncomputable def chunk0018AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0018_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 639)
      (SourceJson.white (chunk0018LeadChars00 ++ (fragment0158782Chars ++ rest))) acc =
      (SourceJson.value (fuel + 638) (fragment0158782Chars ++ rest)).bind
        (chunk0018AfterValue00 (fuel + 638) acc) := by rfl

theorem array_chunk0018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 639) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 638) (SourceJson.white tail) (chunk0018Push00 acc) := by
  have hinput : chunk0018Chars00 ++ tail = chunk0018LeadChars00 ++ (fragment0158782Chars ++ (chunk0018SuffixChars00 ++ tail)) := by
    simp only [chunk0018Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 639) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 639)
          (SourceJson.white (chunk0018LeadChars00 ++ (fragment0158782Chars ++ (chunk0018SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 639) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 638) (fragment0158782Chars ++ (chunk0018SuffixChars00 ++ tail))).bind
        (chunk0018AfterValue00 (fuel + 638) acc) := array_chunk0018_head fuel (chunk0018SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0158782Value, chunk0018SuffixChars00 ++ tail)).bind
        (chunk0018AfterValue00 (fuel + 638) acc) :=
      congrArg (fun result => result.bind (chunk0018AfterValue00 (fuel + 638) acc))
        (value_fragment0158782 (fuel + 405) (chunk0018SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 638) (SourceJson.white tail) (chunk0018Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_before_reader"
  err.flush

noncomputable def chunk0019LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0019SuffixChars00 : List Char := [',']
noncomputable def chunk0019Chars00 : List Char := chunk0019LeadChars00 ++ fragment0160379Chars ++ chunk0019SuffixChars00
noncomputable def chunk0019Push00 (acc : List SourceJson) : List SourceJson := fragment0160379Value :: acc

noncomputable def chunk0019AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0019_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 638)
      (SourceJson.white (chunk0019LeadChars00 ++ (fragment0160379Chars ++ rest))) acc =
      (SourceJson.value (fuel + 637) (fragment0160379Chars ++ rest)).bind
        (chunk0019AfterValue00 (fuel + 637) acc) := by rfl

theorem array_chunk0019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 638) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 637) (SourceJson.white tail) (chunk0019Push00 acc) := by
  have hinput : chunk0019Chars00 ++ tail = chunk0019LeadChars00 ++ (fragment0160379Chars ++ (chunk0019SuffixChars00 ++ tail)) := by
    simp only [chunk0019Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 638) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 638)
          (SourceJson.white (chunk0019LeadChars00 ++ (fragment0160379Chars ++ (chunk0019SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 638) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 637) (fragment0160379Chars ++ (chunk0019SuffixChars00 ++ tail))).bind
        (chunk0019AfterValue00 (fuel + 637) acc) := array_chunk0019_head fuel (chunk0019SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0160379Value, chunk0019SuffixChars00 ++ tail)).bind
        (chunk0019AfterValue00 (fuel + 637) acc) :=
      congrArg (fun result => result.bind (chunk0019AfterValue00 (fuel + 637) acc))
        (value_fragment0160379 (fuel + 65) (chunk0019SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 637) (SourceJson.white tail) (chunk0019Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_before_reader"
  err.flush

noncomputable def chunk0020LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0020SuffixChars00 : List Char := [',']
noncomputable def chunk0020Chars00 : List Char := chunk0020LeadChars00 ++ fragment0162686Chars ++ chunk0020SuffixChars00
noncomputable def chunk0020Push00 (acc : List SourceJson) : List SourceJson := fragment0162686Value :: acc

noncomputable def chunk0020AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0020_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 637)
      (SourceJson.white (chunk0020LeadChars00 ++ (fragment0162686Chars ++ rest))) acc =
      (SourceJson.value (fuel + 636) (fragment0162686Chars ++ rest)).bind
        (chunk0020AfterValue00 (fuel + 636) acc) := by rfl

theorem array_chunk0020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 637) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 636) (SourceJson.white tail) (chunk0020Push00 acc) := by
  have hinput : chunk0020Chars00 ++ tail = chunk0020LeadChars00 ++ (fragment0162686Chars ++ (chunk0020SuffixChars00 ++ tail)) := by
    simp only [chunk0020Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 637) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 637)
          (SourceJson.white (chunk0020LeadChars00 ++ (fragment0162686Chars ++ (chunk0020SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 637) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 636) (fragment0162686Chars ++ (chunk0020SuffixChars00 ++ tail))).bind
        (chunk0020AfterValue00 (fuel + 636) acc) := array_chunk0020_head fuel (chunk0020SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0162686Value, chunk0020SuffixChars00 ++ tail)).bind
        (chunk0020AfterValue00 (fuel + 636) acc) :=
      congrArg (fun result => result.bind (chunk0020AfterValue00 (fuel + 636) acc))
        (value_fragment0162686 (fuel + 148) (chunk0020SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 636) (SourceJson.white tail) (chunk0020Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_before_reader"
  err.flush

noncomputable def chunk0021LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0021SuffixChars00 : List Char := [',']
noncomputable def chunk0021Chars00 : List Char := chunk0021LeadChars00 ++ fragment0164829Chars ++ chunk0021SuffixChars00
noncomputable def chunk0021Push00 (acc : List SourceJson) : List SourceJson := fragment0164829Value :: acc

noncomputable def chunk0021AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0021_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 636)
      (SourceJson.white (chunk0021LeadChars00 ++ (fragment0164829Chars ++ rest))) acc =
      (SourceJson.value (fuel + 635) (fragment0164829Chars ++ rest)).bind
        (chunk0021AfterValue00 (fuel + 635) acc) := by rfl

theorem array_chunk0021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 636) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 635) (SourceJson.white tail) (chunk0021Push00 acc) := by
  have hinput : chunk0021Chars00 ++ tail = chunk0021LeadChars00 ++ (fragment0164829Chars ++ (chunk0021SuffixChars00 ++ tail)) := by
    simp only [chunk0021Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 636) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 636)
          (SourceJson.white (chunk0021LeadChars00 ++ (fragment0164829Chars ++ (chunk0021SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 636) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 635) (fragment0164829Chars ++ (chunk0021SuffixChars00 ++ tail))).bind
        (chunk0021AfterValue00 (fuel + 635) acc) := array_chunk0021_head fuel (chunk0021SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0164829Value, chunk0021SuffixChars00 ++ tail)).bind
        (chunk0021AfterValue00 (fuel + 635) acc) :=
      congrArg (fun result => result.bind (chunk0021AfterValue00 (fuel + 635) acc))
        (value_fragment0164829 (fuel + 164) (chunk0021SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 635) (SourceJson.white tail) (chunk0021Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_before_reader"
  err.flush

noncomputable def chunk0022LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0022SuffixChars00 : List Char := [',']
noncomputable def chunk0022Chars00 : List Char := chunk0022LeadChars00 ++ fragment0166929Chars ++ chunk0022SuffixChars00
noncomputable def chunk0022Push00 (acc : List SourceJson) : List SourceJson := fragment0166929Value :: acc

noncomputable def chunk0022AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0022_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 635)
      (SourceJson.white (chunk0022LeadChars00 ++ (fragment0166929Chars ++ rest))) acc =
      (SourceJson.value (fuel + 634) (fragment0166929Chars ++ rest)).bind
        (chunk0022AfterValue00 (fuel + 634) acc) := by rfl

theorem array_chunk0022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 635) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 634) (SourceJson.white tail) (chunk0022Push00 acc) := by
  have hinput : chunk0022Chars00 ++ tail = chunk0022LeadChars00 ++ (fragment0166929Chars ++ (chunk0022SuffixChars00 ++ tail)) := by
    simp only [chunk0022Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 635) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 635)
          (SourceJson.white (chunk0022LeadChars00 ++ (fragment0166929Chars ++ (chunk0022SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 635) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 634) (fragment0166929Chars ++ (chunk0022SuffixChars00 ++ tail))).bind
        (chunk0022AfterValue00 (fuel + 634) acc) := array_chunk0022_head fuel (chunk0022SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0166929Value, chunk0022SuffixChars00 ++ tail)).bind
        (chunk0022AfterValue00 (fuel + 634) acc) :=
      congrArg (fun result => result.bind (chunk0022AfterValue00 (fuel + 634) acc))
        (value_fragment0166929 (fuel + 201) (chunk0022SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 634) (SourceJson.white tail) (chunk0022Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_before_reader"
  err.flush

noncomputable def chunk0023LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0023SuffixChars00 : List Char := [',']
noncomputable def chunk0023Chars00 : List Char := chunk0023LeadChars00 ++ fragment0168948Chars ++ chunk0023SuffixChars00
noncomputable def chunk0023Push00 (acc : List SourceJson) : List SourceJson := fragment0168948Value :: acc

noncomputable def chunk0023AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0023_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 634)
      (SourceJson.white (chunk0023LeadChars00 ++ (fragment0168948Chars ++ rest))) acc =
      (SourceJson.value (fuel + 633) (fragment0168948Chars ++ rest)).bind
        (chunk0023AfterValue00 (fuel + 633) acc) := by rfl

theorem array_chunk0023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 634) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 633) (SourceJson.white tail) (chunk0023Push00 acc) := by
  have hinput : chunk0023Chars00 ++ tail = chunk0023LeadChars00 ++ (fragment0168948Chars ++ (chunk0023SuffixChars00 ++ tail)) := by
    simp only [chunk0023Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 634) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 634)
          (SourceJson.white (chunk0023LeadChars00 ++ (fragment0168948Chars ++ (chunk0023SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 634) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 633) (fragment0168948Chars ++ (chunk0023SuffixChars00 ++ tail))).bind
        (chunk0023AfterValue00 (fuel + 633) acc) := array_chunk0023_head fuel (chunk0023SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0168948Value, chunk0023SuffixChars00 ++ tail)).bind
        (chunk0023AfterValue00 (fuel + 633) acc) :=
      congrArg (fun result => result.bind (chunk0023AfterValue00 (fuel + 633) acc))
        (value_fragment0168948 (fuel + 259) (chunk0023SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 633) (SourceJson.white tail) (chunk0023Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0016Chars00 ++ chunk0017Chars00 ++ chunk0018Chars00 ++ chunk0019Chars00 ++ chunk0020Chars00 ++ chunk0021Chars00 ++ chunk0022Chars00 ++ chunk0023Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0023Push00 (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 641) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 633) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 641) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 641) (SourceJson.white (chunk0016Chars00 ++ (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 641) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 640) (SourceJson.white (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))))) (chunk0016Push00 (acc)) := array_chunk0016 fuel (chunk0017Chars00 ++ (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 639) (SourceJson.white (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))))) (chunk0017Push00 (chunk0016Push00 (acc))) := array_chunk0017 fuel (chunk0018Chars00 ++ (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0016Push00 (acc))
    _ = SourceJson.array (fuel + 638) (SourceJson.white (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))) := array_chunk0018 fuel (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0017Push00 (chunk0016Push00 (acc)))
    _ = SourceJson.array (fuel + 637) (SourceJson.white (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))) := array_chunk0019 fuel (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))
    _ = SourceJson.array (fuel + 636) (SourceJson.white (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))) := array_chunk0020 fuel (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))
    _ = SourceJson.array (fuel + 635) (SourceJson.white (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))) := array_chunk0021 fuel (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))) (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))
    _ = SourceJson.array (fuel + 634) (SourceJson.white (chunk0023Chars00 ++ (tail))) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))) := array_chunk0022 fuel (chunk0023Chars00 ++ (tail)) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc)))))))
    _ = SourceJson.array (fuel + 633) (SourceJson.white tail) (blockPush acc) := array_chunk0023 fuel (tail) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (chunk0018Push00 (chunk0017Push00 (chunk0016Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 155525).take 15300 = blockChars := by rfl

theorem block_original_split : sourceRest 155525 = blockChars ++ sourceRest 170825 := by
  calc
    sourceRest 155525 = (sourceRest 155525).take 15300 ++ (sourceRest 155525).drop 15300 :=
      (List.take_append_drop 15300 (sourceRest 155525)).symm
    _ = blockChars ++ (sourceRest 155525).drop 15300 :=
      congrArg (fun part => part ++ (sourceRest 155525).drop 15300) block_original_prefix
    _ = blockChars ++ sourceRest 170825 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 155525 15300)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 641) (SourceJson.white (sourceRest 155525)) acc =
      SourceJson.array (fuel + 633) (SourceJson.white (sourceRest 170825)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 641) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 170825) acc)

#print axioms object_fragment0155531_field_000
#print axioms object_fragment0155531_field_001
#print axioms object_fragment0155531_field_002
#print axioms object_fragment0155531_field_003
#print axioms object_fragment0155531_field_004
#print axioms object_fragment0155531_field_005
#print axioms object_fragment0155531_field_006
#print axioms object_fragment0155531_field_007
#print axioms object_fragment0155531_field_008
#print axioms object_fragment0155531_field_009
#print axioms value_fragment0155531
#print axioms object_fragment0157200_field_000
#print axioms object_fragment0157200_field_001
#print axioms object_fragment0157200_field_002
#print axioms object_fragment0157200_field_003
#print axioms object_fragment0157200_field_004
#print axioms object_fragment0157200_field_005
#print axioms object_fragment0157200_field_006
#print axioms object_fragment0157200_field_007
#print axioms object_fragment0157200_field_008
#print axioms object_fragment0157200_field_009
#print axioms value_fragment0157200
#print axioms object_fragment0158782_field_000
#print axioms object_fragment0158782_field_001
#print axioms object_fragment0158782_field_002
#print axioms object_fragment0158782_field_003
#print axioms object_fragment0158782_field_004
#print axioms object_fragment0158782_field_005
#print axioms object_fragment0158782_field_006
#print axioms object_fragment0158782_field_007
#print axioms object_fragment0158782_field_008
#print axioms object_fragment0158782_field_009
#print axioms value_fragment0158782
#print axioms object_fragment0160379_field_000
#print axioms object_fragment0160379_field_001
#print axioms object_fragment0160379_field_002
#print axioms object_fragment0160379_field_003
#print axioms object_fragment0160379_field_004
#print axioms object_fragment0160379_field_005
#print axioms object_fragment0160379_field_006
#print axioms object_fragment0160379_field_007
#print axioms object_fragment0160379_field_008
#print axioms object_fragment0160379_field_009
#print axioms value_fragment0160379
#print axioms object_fragment0162686_field_000
#print axioms object_fragment0162686_field_001
#print axioms object_fragment0162686_field_002
#print axioms object_fragment0162686_field_003
#print axioms object_fragment0162686_field_004
#print axioms object_fragment0162686_field_005
#print axioms object_fragment0162686_field_006
#print axioms object_fragment0162686_field_007
#print axioms object_fragment0162686_field_008
#print axioms object_fragment0162686_field_009
#print axioms value_fragment0162686
#print axioms object_fragment0164829_field_000
#print axioms object_fragment0164829_field_001
#print axioms object_fragment0164829_field_002
#print axioms object_fragment0164829_field_003
#print axioms object_fragment0164829_field_004
#print axioms object_fragment0164829_field_005
#print axioms object_fragment0164829_field_006
#print axioms object_fragment0164829_field_007
#print axioms object_fragment0164829_field_008
#print axioms object_fragment0164829_field_009
#print axioms value_fragment0164829
#print axioms object_fragment0166929_field_000
#print axioms object_fragment0166929_field_001
#print axioms object_fragment0166929_field_002
#print axioms object_fragment0166929_field_003
#print axioms object_fragment0166929_field_004
#print axioms object_fragment0166929_field_005
#print axioms object_fragment0166929_field_006
#print axioms object_fragment0166929_field_007
#print axioms object_fragment0166929_field_008
#print axioms object_fragment0166929_field_009
#print axioms value_fragment0166929
#print axioms object_fragment0168948_field_000
#print axioms object_fragment0168948_field_001
#print axioms object_fragment0168948_field_002
#print axioms object_fragment0168948_field_003
#print axioms object_fragment0168948_field_004
#print axioms object_fragment0168948_field_005
#print axioms object_fragment0168948_field_006
#print axioms object_fragment0168948_field_007
#print axioms object_fragment0168948_field_008
#print axioms object_fragment0168948_field_009
#print axioms value_fragment0168948
#print axioms array_chunk0016_head
#print axioms array_chunk0016
#print axioms array_chunk0017_head
#print axioms array_chunk0017
#print axioms array_chunk0018_head
#print axioms array_chunk0018
#print axioms array_chunk0019_head
#print axioms array_chunk0019
#print axioms array_chunk0020_head
#print axioms array_chunk0020
#print axioms array_chunk0021_head
#print axioms array_chunk0021
#print axioms array_chunk0022_head
#print axioms array_chunk0022
#print axioms array_chunk0023_head
#print axioms array_chunk0023
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock002

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
