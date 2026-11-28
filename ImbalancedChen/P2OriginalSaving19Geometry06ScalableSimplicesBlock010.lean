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

namespace SimplicesBlock010

noncomputable def fragment0275447Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0275447Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0275447Field000Value00 : SourceJson := .number (String.ofList ['8', '0'])
noncomputable def fragment0275447Acc00100 : List (String × SourceJson) := (fragment0275447Field000Key00, fragment0275447Field000Value00) :: fragment0275447Acc00000
noncomputable def fragment0275447Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '0', ',']

theorem object_fragment0275447_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 425) (SourceJson.white (fragment0275447Field000Chars00 ++ tail)) fragment0275447Acc00000 =
      SourceJson.object (fuel + 424) (SourceJson.white tail) fragment0275447Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_000"
  err.flush

noncomputable def fragment0275447Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0275447Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['3'])]
noncomputable def fragment0275447Acc00200 : List (String × SourceJson) := (fragment0275447Field001Key00, fragment0275447Field001Value00) :: fragment0275447Acc00100
noncomputable def fragment0275447Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0275447_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 424) (SourceJson.white (fragment0275447Field001Chars00 ++ tail)) fragment0275447Acc00100 =
      SourceJson.object (fuel + 423) (SourceJson.white tail) fragment0275447Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_001"
  err.flush

noncomputable def fragment0275447Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0275447Field002Value00 : SourceJson := .str (String.ofList ['6', '9', '3', '0', '8', '1', '6', '0', '7', '1', '2', '3', '9', '4', '2', '7', '8', '4', '2', '5', '7', '0', '1', '8', '1', '8', '9', '2', '4', '3', '1', '1', '6', '8', '0', '1', '1', '8', '1', '/', '6', '7', '8', '6', '6', '0', '6', '8', '4', '2', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0275447Acc00300 : List (String × SourceJson) := (fragment0275447Field002Key00, fragment0275447Field002Value00) :: fragment0275447Acc00200
noncomputable def fragment0275447Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '9', '3', '0', '8', '1', '6', '0', '7', '1', '2', '3', '9', '4', '2', '7', '8', '4', '2', '5', '7', '0', '1', '8', '1', '8', '9', '2', '4', '3', '1', '1', '6', '8', '0', '1', '1', '8', '1', '/', '6', '7', '8', '6', '6', '0', '6', '8', '4', '2', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0275447_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 423) (SourceJson.white (fragment0275447Field002Chars00 ++ tail)) fragment0275447Acc00200 =
      SourceJson.object (fuel + 422) (SourceJson.white tail) fragment0275447Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_002"
  err.flush

noncomputable def fragment0275447Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0275447Field003Value00 : SourceJson := .str (String.ofList ['4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0275447Acc00400 : List (String × SourceJson) := (fragment0275447Field003Key00, fragment0275447Field003Value00) :: fragment0275447Acc00300
noncomputable def fragment0275447Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0275447_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 422) (SourceJson.white (fragment0275447Field003Chars00 ++ tail)) fragment0275447Acc00300 =
      SourceJson.object (fuel + 421) (SourceJson.white tail) fragment0275447Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_003"
  err.flush

noncomputable def fragment0275447Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0275447Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '2', '1', '7', '0', '3', '/', '1', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0275447Acc00500 : List (String × SourceJson) := (fragment0275447Field004Key00, fragment0275447Field004Value00) :: fragment0275447Acc00400
noncomputable def fragment0275447Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '2', '1', '7', '0', '3', '/', '1', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0275447_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0275447Field004Chars00 ++ tail)) fragment0275447Acc00400 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0275447Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_004"
  err.flush

noncomputable def fragment0275447Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0275447Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '9', '6', '2', '2', '6', '3', '7', '3', '1', '3', '5', '4', '2', '5', '5', '4', '5', '6', '7', '3', '9', '/', '4', '5', '2', '6', '8', '3', '4', '4', '6', '9', '5', '8', '6', '5', '0', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '0', '1', '5', '5', '0', '8', '0', '9', '8', '8', '5', '9', '7', '6', '7', '9', '8', '9', '8', '7', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '1', '6', '2', '9', '7', '6', '6', '2', '4', '2', '7', '3', '3', '5', '5', '1', '6', '6', '3', '/', '1', '2', '9', '3', '3', '8', '1', '2', '7', '7', '0', '2', '4', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '7', '0', '4', '1', '9', '7', '6', '4', '9', '5', '8', '1', '0', '1', '7', '4', '9', '1', '1', '/', '1', '5', '0', '8', '9', '4', '4', '8', '2', '3', '1', '9', '5', '5', '0', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '8', '8', '4', '2', '1', '5', '1', '6', '3', '8', '9', '1', '0', '2', '8', '1', '4', '6', '3', '/', '1', '5', '0', '8', '9', '4', '4', '8', '2', '3', '1', '9', '5', '5', '0', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '1', '4', '4', '9', '4', '9', '5', '3', '1', '3', '6', '7', '2', '6', '8', '4', '3', '3', '/', '5', '1', '7', '3', '5', '2', '5', '1', '0', '8', '0', '9', '8', '8', '6', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '6', '0', '9', '8', '6', '3', '0', '1', '7', '5', '2', '7', '8', '1', '9', '0', '2', '3', '3', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '7', '8', '0', '9', '2', '3', '4', '4', '1', '8', '9', '7', '3', '5', '5', '7', '8', '3', '8', '1', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '9', '8', '5', '0', '8', '0', '1', '5', '3', '7', '3', '8', '7', '5', '7', '2', '8', '8', '9', '/', '4', '5', '2', '6', '8', '3', '4', '4', '6', '9', '5', '8', '6', '5', '0', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '6', '3', '3', '8', '4', '2', '7', '2', '4', '5', '7', '9', '8', '9', '0', '4', '3', '4', '3', '3', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0275447Acc00600 : List (String × SourceJson) := (fragment0275447Field005Key00, fragment0275447Field005Value00) :: fragment0275447Acc00500
noncomputable def fragment0275447Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '6', '2', '2', '6', '3', '7', '3', '1', '3', '5', '4', '2', '5', '5', '4', '5', '6', '7', '3', '9', '/', '4', '5', '2', '6', '8', '3', '4', '4', '6', '9', '5', '8', '6', '5', '0', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '0', '1', '5', '5', '0', '8', '0', '9', '8', '8', '5', '9', '7', '6', '7', '9', '8', '9', '8', '7', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '1', '6', '2', '9', '7', '6', '6', '2', '4', '2', '7', '3', '3', '5', '5', '1', '6', '6', '3', '/', '1', '2', '9', '3', '3', '8', '1', '2', '7', '7', '0', '2', '4', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '7', '0', '4', '1', '9', '7', '6', '4', '9', '5', '8', '1', '0', '1', '7', '4', '9', '1', '1', '/', '1', '5', '0', '8', '9', '4', '4', '8', '2', '3', '1', '9', '5', '5', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '8', '8', '4', '2', '1', '5', '1', '6', '3', '8', '9', '1', '0', '2', '8', '1', '4', '6', '3', '/', '1', '5', '0', '8', '9', '4', '4', '8', '2', '3', '1', '9', '5', '5', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '1', '4', '4', '9', '4', '9', '5', '3', '1', '3', '6', '7', '2', '6', '8', '4', '3', '3', '/', '5', '1', '7', '3', '5', '2', '5', '1', '0', '8', '0', '9', '8', '8', '6', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '6', '0', '9', '8', '6', '3', '0', '1', '7', '5', '2', '7', '8', '1', '9', '0', '2', '3', '3', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '7', '8', '0', '9', '2', '3', '4', '4', '1', '8', '9', '7', '3', '5', '5', '7', '8', '3', '8', '1', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '9', '8', '5', '0', '8', '0', '1', '5', '3', '7', '3', '8', '7', '5', '7', '2', '8', '8', '9', '/', '4', '5', '2', '6', '8', '3', '4', '4', '6', '9', '5', '8', '6', '5', '0', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '6', '3', '3', '8', '4', '2', '7', '2', '4', '5', '7', '9', '8', '9', '0', '4', '3', '4', '3', '3', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0275447_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0275447Field005Chars00 ++ tail)) fragment0275447Acc00500 =
      SourceJson.object (fuel + 419) (SourceJson.white tail) fragment0275447Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_005"
  err.flush

noncomputable def fragment0275447Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0275447Field006Value00 : SourceJson := .str (String.ofList ['2', '1', '7', '8', '3', '1', '9', '6', '5', '2', '4', '0', '3', '3', '5', '8', '5', '2', '3', '8', '6', '7', '2', '0', '2', '8', '5', '8', '5', '5', '2', '1', '3', '9', '1', '9', '2', '4', '7', '4', '2', '8', '8', '3', '8', '5', '8', '2', '3', '9', '0', '6', '2', '5', '0', '/', '7', '4', '3', '5', '6', '8', '1', '3', '2', '3', '0', '8', '6', '8', '5', '2', '8', '5', '1', '8', '1', '0', '6', '2', '9', '7', '9', '7', '0', '5', '5', '4', '8', '2', '8', '0', '7', '2', '3', '3', '4', '0', '4', '4', '2', '8', '4', '1', '1', '9', '4', '5', '3', '4', '1', '7', '7', '7', '7', '3', '0', '6', '1', '7', '7', '7', '3'])
noncomputable def fragment0275447Acc00700 : List (String × SourceJson) := (fragment0275447Field006Key00, fragment0275447Field006Value00) :: fragment0275447Acc00600
noncomputable def fragment0275447Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '7', '8', '3', '1', '9', '6', '5', '2', '4', '0', '3', '3', '5', '8', '5', '2', '3', '8', '6', '7', '2', '0', '2', '8', '5', '8', '5', '5', '2', '1', '3', '9', '1', '9', '2', '4', '7', '4', '2', '8', '8', '3', '8', '5', '8', '2', '3', '9', '0', '6', '2', '5', '0', '/', '7', '4', '3', '5', '6', '8', '1', '3', '2', '3', '0', '8', '6', '8', '5', '2', '8', '5', '1', '8', '1', '0', '6', '2', '9', '7', '9', '7', '0', '5', '5', '4', '8', '2', '8', '0', '7', '2', '3', '3', '4', '0', '4', '4', '2', '8', '4', '1', '1', '9', '4', '5', '3', '4', '1', '7', '7', '7', '7', '3', '0', '6', '1', '7', '7', '7', '3', '"', ',']

theorem object_fragment0275447_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 419) (SourceJson.white (fragment0275447Field006Chars00 ++ tail)) fragment0275447Acc00600 =
      SourceJson.object (fuel + 418) (SourceJson.white tail) fragment0275447Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_006"
  err.flush

noncomputable def fragment0275447Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0275447Field007Value00 : SourceJson := .str (String.ofList ['4', '9', '6', '0', '9', '6', '1', '2', '6', '0', '5', '5', '4', '9', '2', '9', '0', '5', '9', '4', '4', '8', '1', '5', '2', '7', '7', '8', '7', '9', '5', '5', '3', '3', '0', '2', '1', '4', '7', '9', '7', '0', '9', '0', '1', '1', '3', '0', '2', '8', '9', '8', '9', '5', '9', '1', '9', '8', '0', '2', '4', '8', '0', '9', '7', '2', '0', '1', '5', '5', '6', '2', '8', '5', '2', '9', '4', '9', '0', '7', '7', '0', '5', '1', '1', '8', '7', '6', '9', '9', '6', '4', '0', '3', '8', '0', '3', '5', '5', '2', '2', '2', '9', '8', '7', '6', '6', '9', '6', '3', '4', '9', '0', '5', '9', '5', '8', '8', '2', '5', '3', '4', '5', '9', '7', '9', '0', '2', '8', '8', '8', '4', '5', '3', '6', '5', '9', '9', '5', '2', '9', '8', '3', '3', '9', '0', '7', '8', '0', '2', '4', '8', '8', '7', '1', '8', '5', '0', '0', '0', '2', '8', '6', '3', '8', '4', '7', '4', '7', '1', '0', '3', '6', '1', '7', '9', '2', '8', '4', '4', '4', '8', '4', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '8', '2', '9', '4', '6', '9', '9', '9', '1', '3', '3', '9', '8', '6', '5', '9', '2', '1', '3', '2', '3', '8', '1', '2', '9', '5', '0', '4', '0', '2', '5', '3', '7', '2', '8', '7', '4', '6', '8', '8', '0', '4', '0', '0', '9', '3', '6', '3', '9', '3', '9', '3', '4', '7', '0', '6', '9', '0', '9', '9', '6', '7', '1', '2', '7', '5', '3', '5', '2', '0', '5', '6', '9', '9', '9', '3', '7', '9', '2', '6', '1', '4', '8', '4', '7', '4', '4', '8', '5', '5', '3', '6', '0', '7', '9', '8', '4', '7', '8', '3', '8', '5', '5', '6', '4', '2', '9', '0', '5', '0', '6', '1', '9', '0', '4', '1', '4', '3', '3', '1', '8', '9', '3', '0', '6', '5', '8', '0', '5', '9', '9', '1', '8', '1', '3', '9', '0', '6', '4', '9', '3', '6', '6', '4', '9', '3', '5', '3', '4', '9', '4', '1', '9', '6', '8', '1', '1', '6', '1', '3', '8', '3', '1', '7', '3', '3', '8', '9', '1', '8', '9', '1', '9', '5', '9', '7', '7', '4', '7', '7', '9', '9', '1', '7', '3', '0', '6', '7', '2', '9', '4', '0', '4', '1', '5', '8', '7', '2', '2', '9', '3', '8', '5', '7', '2', '6', '5', '5', '0', '1', '9'])
noncomputable def fragment0275447Acc00800 : List (String × SourceJson) := (fragment0275447Field007Key00, fragment0275447Field007Value00) :: fragment0275447Acc00700
noncomputable def fragment0275447Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '9', '6', '0', '9', '6', '1', '2', '6', '0', '5', '5', '4', '9', '2', '9', '0', '5', '9', '4', '4', '8', '1', '5', '2', '7', '7', '8', '7', '9', '5', '5', '3', '3', '0', '2', '1', '4', '7', '9', '7', '0', '9', '0', '1', '1', '3', '0', '2', '8', '9', '8', '9', '5', '9', '1', '9', '8', '0', '2', '4', '8', '0', '9', '7', '2', '0', '1', '5', '5', '6', '2', '8', '5', '2', '9', '4', '9', '0', '7', '7', '0', '5', '1', '1', '8', '7', '6', '9', '9', '6', '4', '0', '3', '8', '0', '3', '5', '5', '2', '2', '2', '9', '8', '7', '6', '6', '9', '6', '3', '4', '9', '0', '5', '9', '5', '8', '8', '2', '5', '3', '4', '5', '9', '7', '9', '0', '2', '8', '8', '8', '4', '5', '3', '6', '5', '9', '9', '5', '2', '9', '8', '3', '3', '9', '0', '7', '8', '0', '2', '4', '8', '8', '7', '1', '8', '5', '0', '0', '0', '2', '8', '6', '3', '8', '4', '7', '4', '7', '1', '0', '3', '6', '1', '7', '9', '2', '8', '4', '4', '4', '8', '4', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '8', '2', '9', '4', '6', '9', '9', '9', '1', '3', '3', '9', '8', '6', '5', '9', '2', '1', '3', '2', '3', '8', '1', '2', '9', '5', '0', '4', '0', '2', '5', '3', '7', '2', '8', '7', '4', '6', '8', '8', '0', '4', '0', '0', '9', '3', '6', '3', '9', '3', '9', '3', '4', '7', '0', '6', '9', '0', '9', '9', '6', '7', '1', '2', '7', '5', '3', '5', '2', '0', '5', '6', '9', '9', '9', '3', '7', '9', '2', '6', '1', '4', '8', '4', '7', '4', '4', '8', '5', '5', '3', '6', '0', '7', '9', '8', '4', '7', '8', '3', '8', '5', '5', '6', '4', '2', '9', '0', '5', '0', '6', '1', '9', '0', '4', '1', '4', '3', '3', '1', '8', '9', '3', '0', '6', '5', '8', '0', '5', '9', '9', '1', '8', '1', '3', '9', '0', '6', '4', '9', '3', '6', '6', '4', '9', '3', '5', '3', '4', '9', '4', '1', '9', '6', '8', '1', '1', '6', '1', '3', '8', '3', '1', '7', '3', '3', '8', '9', '1', '8', '9', '1', '9', '5', '9', '7', '7', '4', '7', '7', '9', '9', '1', '7', '3', '0', '6', '7', '2', '9', '4', '0', '4', '1', '5', '8', '7', '2', '2', '9', '3', '8', '5', '7', '2', '6', '5', '5', '0', '1', '9', '"', ',']

theorem object_fragment0275447_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 418) (SourceJson.white (fragment0275447Field007Chars00 ++ tail)) fragment0275447Acc00700 =
      SourceJson.object (fuel + 417) (SourceJson.white tail) fragment0275447Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_007"
  err.flush

noncomputable def fragment0275447Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0275447Field008Value00 : SourceJson := .str (String.ofList ['2', '3', '2', '1', '0', '2', '8', '2', '4', '1', '1', '2', '1', '3', '1', '7', '5'])
noncomputable def fragment0275447Acc00900 : List (String × SourceJson) := (fragment0275447Field008Key00, fragment0275447Field008Value00) :: fragment0275447Acc00800
noncomputable def fragment0275447Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '2', '1', '0', '2', '8', '2', '4', '1', '1', '2', '1', '3', '1', '7', '5', '"', ',']

theorem object_fragment0275447_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 417) (SourceJson.white (fragment0275447Field008Chars00 ++ tail)) fragment0275447Acc00800 =
      SourceJson.object (fuel + 416) (SourceJson.white tail) fragment0275447Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_008"
  err.flush

noncomputable def fragment0275447Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0275447Field009Value00 : SourceJson := .str (String.ofList ['6', '9', '1', '6', '2', '6', '8', '0', '0', '3', '8', '7', '3', '8', '9', '4', '9'])
noncomputable def fragment0275447Acc01000 : List (String × SourceJson) := (fragment0275447Field009Key00, fragment0275447Field009Value00) :: fragment0275447Acc00900
noncomputable def fragment0275447Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '9', '1', '6', '2', '6', '8', '0', '0', '3', '8', '7', '3', '8', '9', '4', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0275447_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 416) (SourceJson.white (fragment0275447Field009Chars00 ++ tail)) fragment0275447Acc00900 =
      .ok (.obj (fragment0275447Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0275447_object_field_009"
  err.flush

noncomputable def fragment0275447Chars : List Char := '{' :: (fragment0275447Field000Chars00 ++ fragment0275447Field001Chars00 ++ fragment0275447Field002Chars00 ++ fragment0275447Field003Chars00 ++ fragment0275447Field004Chars00 ++ fragment0275447Field005Chars00 ++ fragment0275447Field006Chars00 ++ fragment0275447Field007Chars00 ++ fragment0275447Field008Chars00 ++ fragment0275447Field009Chars00)
noncomputable def fragment0275447Value : SourceJson := .obj (fragment0275447Acc01000.reverse)

theorem value_fragment0275447 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 426) (fragment0275447Chars ++ tail) =
      .ok (fragment0275447Value, tail) := by
  have hinput : fragment0275447Chars ++ tail = '{' :: (fragment0275447Field000Chars00 ++ (fragment0275447Field001Chars00 ++ (fragment0275447Field002Chars00 ++ (fragment0275447Field003Chars00 ++ (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0275447Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 426) (fragment0275447Chars ++ tail) =
        SourceJson.value (fuel + 426) ('{' :: (fragment0275447Field000Chars00 ++ (fragment0275447Field001Chars00 ++ (fragment0275447Field002Chars00 ++ (fragment0275447Field003Chars00 ++ (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 426)) hinput
    _ = SourceJson.object (fuel + 425) (SourceJson.white (fragment0275447Field000Chars00 ++ (fragment0275447Field001Chars00 ++ (fragment0275447Field002Chars00 ++ (fragment0275447Field003Chars00 ++ (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))))))))))) fragment0275447Acc00000 := by rfl
    _ = SourceJson.object (fuel + 424) (SourceJson.white (fragment0275447Field001Chars00 ++ (fragment0275447Field002Chars00 ++ (fragment0275447Field003Chars00 ++ (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail))))))))))) fragment0275447Acc00100 := object_fragment0275447_field_000 fuel (fragment0275447Field001Chars00 ++ (fragment0275447Field002Chars00 ++ (fragment0275447Field003Chars00 ++ (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 423) (SourceJson.white (fragment0275447Field002Chars00 ++ (fragment0275447Field003Chars00 ++ (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))))))))) fragment0275447Acc00200 := object_fragment0275447_field_001 fuel (fragment0275447Field002Chars00 ++ (fragment0275447Field003Chars00 ++ (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 422) (SourceJson.white (fragment0275447Field003Chars00 ++ (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail))))))))) fragment0275447Acc00300 := object_fragment0275447_field_002 fuel (fragment0275447Field003Chars00 ++ (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))))))) fragment0275447Acc00400 := object_fragment0275447_field_003 fuel (fragment0275447Field004Chars00 ++ (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail))))))) fragment0275447Acc00500 := object_fragment0275447_field_004 fuel (fragment0275447Field005Chars00 ++ (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 419) (SourceJson.white (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))))) fragment0275447Acc00600 := object_fragment0275447_field_005 fuel (fragment0275447Field006Chars00 ++ (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 418) (SourceJson.white (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail))))) fragment0275447Acc00700 := object_fragment0275447_field_006 fuel (fragment0275447Field007Chars00 ++ (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 417) (SourceJson.white (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))) fragment0275447Acc00800 := object_fragment0275447_field_007 fuel (fragment0275447Field008Chars00 ++ (fragment0275447Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 416) (SourceJson.white (fragment0275447Field009Chars00 ++ (tail))) fragment0275447Acc00900 := object_fragment0275447_field_008 fuel (fragment0275447Field009Chars00 ++ (tail))
    _ = .ok (fragment0275447Value, tail) := object_fragment0275447_field_009 fuel (tail)

noncomputable def fragment0277441Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0277441Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0277441Field000Value00 : SourceJson := .number (String.ofList ['8', '1'])
noncomputable def fragment0277441Acc00100 : List (String × SourceJson) := (fragment0277441Field000Key00, fragment0277441Field000Value00) :: fragment0277441Acc00000
noncomputable def fragment0277441Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '1', ',']

theorem object_fragment0277441_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 417) (SourceJson.white (fragment0277441Field000Chars00 ++ tail)) fragment0277441Acc00000 =
      SourceJson.object (fuel + 416) (SourceJson.white tail) fragment0277441Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_000"
  err.flush

noncomputable def fragment0277441Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0277441Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0277441Acc00200 : List (String × SourceJson) := (fragment0277441Field001Key00, fragment0277441Field001Value00) :: fragment0277441Acc00100
noncomputable def fragment0277441Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0277441_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 416) (SourceJson.white (fragment0277441Field001Chars00 ++ tail)) fragment0277441Acc00100 =
      SourceJson.object (fuel + 415) (SourceJson.white tail) fragment0277441Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_001"
  err.flush

noncomputable def fragment0277441Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0277441Field002Value00 : SourceJson := .str (String.ofList ['9', '4', '6', '3', '3', '7', '4', '6', '7', '8', '2', '3', '0', '4', '2', '8', '7', '8', '5', '1', '7', '8', '8', '7', '9', '9', '5', '4', '3', '3', '7', '7', '0', '6', '7', '6', '3', '3', '/', '2', '2', '3', '3', '3', '2', '8', '7', '8', '6', '8', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0277441Acc00300 : List (String × SourceJson) := (fragment0277441Field002Key00, fragment0277441Field002Value00) :: fragment0277441Acc00200
noncomputable def fragment0277441Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '4', '6', '3', '3', '7', '4', '6', '7', '8', '2', '3', '0', '4', '2', '8', '7', '8', '5', '1', '7', '8', '8', '7', '9', '9', '5', '4', '3', '3', '7', '7', '0', '6', '7', '6', '3', '3', '/', '2', '2', '3', '3', '3', '2', '8', '7', '8', '6', '8', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0277441_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 415) (SourceJson.white (fragment0277441Field002Chars00 ++ tail)) fragment0277441Acc00200 =
      SourceJson.object (fuel + 414) (SourceJson.white tail) fragment0277441Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_002"
  err.flush

noncomputable def fragment0277441Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0277441Field003Value00 : SourceJson := .str (String.ofList ['9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0277441Acc00400 : List (String × SourceJson) := (fragment0277441Field003Key00, fragment0277441Field003Value00) :: fragment0277441Acc00300
noncomputable def fragment0277441Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0277441_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 414) (SourceJson.white (fragment0277441Field003Chars00 ++ tail)) fragment0277441Acc00300 =
      SourceJson.object (fuel + 413) (SourceJson.white tail) fragment0277441Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_003"
  err.flush

noncomputable def fragment0277441Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0277441Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0277441Acc00500 : List (String × SourceJson) := (fragment0277441Field004Key00, fragment0277441Field004Value00) :: fragment0277441Acc00400
noncomputable def fragment0277441Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0277441_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 413) (SourceJson.white (fragment0277441Field004Chars00 ++ tail)) fragment0277441Acc00400 =
      SourceJson.object (fuel + 412) (SourceJson.white tail) fragment0277441Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_004"
  err.flush

noncomputable def fragment0277441Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0277441Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '6', '8', '6', '7', '3', '1', '4', '0', '8', '7', '9', '2', '2', '7', '1', '2', '9', '3', '7', '3', '6', '1', '/', '8', '8', '8', '1', '6', '5', '6', '7', '0', '0', '1', '8', '7', '5', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '2', '8', '3', '3', '4', '3', '4', '5', '4', '2', '9', '6', '6', '2', '8', '7', '6', '7', '2', '1', '/', '2', '0', '6', '5', '5', '0', '1', '5', '5', '8', '1', '8', '3', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '6', '6', '5', '7', '1', '2', '2', '5', '6', '4', '9', '8', '8', '6', '8', '7', '6', '3', '/', '6', '4', '3', '5', '9', '8', '3', '1', '1', '6', '0', '7', '7', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '2', '7', '6', '0', '6', '1', '9', '4', '0', '6', '3', '7', '0', '4', '5', '7', '5', '3', '2', '3', '/', '4', '2', '2', '9', '3', '6', '0', '3', '3', '3', '4', '2', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '4', '6', '2', '3', '2', '3', '7', '0', '6', '1', '1', '1', '3', '0', '9', '8', '4', '4', '3', '/', '4', '2', '2', '9', '3', '6', '0', '3', '3', '3', '4', '2', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '9', '5', '9', '5', '0', '7', '0', '5', '2', '1', '3', '0', '7', '1', '7', '0', '3', '0', '7', '/', '4', '4', '8', '5', '6', '8', '5', '2', '0', '2', '1', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '1', '6', '2', '4', '0', '7', '8', '2', '0', '6', '0', '0', '0', '2', '3', '4', '1', '7', '/', '5', '6', '0', '7', '1', '0', '6', '5', '0', '2', '6', '4', '3', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '2', '8', '7', '3', '6', '0', '5', '4', '3', '6', '3', '4', '8', '1', '3', '1', '4', '5', '3', '/', '1', '3', '4', '5', '7', '0', '5', '5', '6', '0', '6', '3', '4', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '1', '8', '1', '4', '9', '7', '7', '5', '9', '1', '2', '3', '1', '4', '2', '4', '2', '7', '7', '/', '8', '9', '7', '1', '3', '7', '0', '4', '0', '4', '2', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '3', '7', '8', '7', '3', '1', '8', '6', '2', '9', '6', '8', '0', '5', '0', '7', '7', '8', '7', '/', '2', '0', '6', '5', '5', '0', '1', '5', '5', '8', '1', '8', '3', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0277441Acc00600 : List (String × SourceJson) := (fragment0277441Field005Key00, fragment0277441Field005Value00) :: fragment0277441Acc00500
noncomputable def fragment0277441Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '8', '6', '7', '3', '1', '4', '0', '8', '7', '9', '2', '2', '7', '1', '2', '9', '3', '7', '3', '6', '1', '/', '8', '8', '8', '1', '6', '5', '6', '7', '0', '0', '1', '8', '7', '5', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '2', '8', '3', '3', '4', '3', '4', '5', '4', '2', '9', '6', '6', '2', '8', '7', '6', '7', '2', '1', '/', '2', '0', '6', '5', '5', '0', '1', '5', '5', '8', '1', '8', '3', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '6', '6', '5', '7', '1', '2', '2', '5', '6', '4', '9', '8', '8', '6', '8', '7', '6', '3', '/', '6', '4', '3', '5', '9', '8', '3', '1', '1', '6', '0', '7', '7', '9', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '2', '7', '6', '0', '6', '1', '9', '4', '0', '6', '3', '7', '0', '4', '5', '7', '5', '3', '2', '3', '/', '4', '2', '2', '9', '3', '6', '0', '3', '3', '3', '4', '2', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '4', '6', '2', '3', '2', '3', '7', '0', '6', '1', '1', '1', '3', '0', '9', '8', '4', '4', '3', '/', '4', '2', '2', '9', '3', '6', '0', '3', '3', '3', '4', '2', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '9', '5', '9', '5', '0', '7', '0', '5', '2', '1', '3', '0', '7', '1', '7', '0', '3', '0', '7', '/', '4', '4', '8', '5', '6', '8', '5', '2', '0', '2', '1', '1', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '1', '6', '2', '4', '0', '7', '8', '2', '0', '6', '0', '0', '0', '2', '3', '4', '1', '7', '/', '5', '6', '0', '7', '1', '0', '6', '5', '0', '2', '6', '4', '3', '6', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '2', '8', '7', '3', '6', '0', '5', '4', '3', '6', '3', '4', '8', '1', '3', '1', '4', '5', '3', '/', '1', '3', '4', '5', '7', '0', '5', '5', '6', '0', '6', '3', '4', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '8', '1', '4', '9', '7', '7', '5', '9', '1', '2', '3', '1', '4', '2', '4', '2', '7', '7', '/', '8', '9', '7', '1', '3', '7', '0', '4', '0', '4', '2', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '3', '7', '8', '7', '3', '1', '8', '6', '2', '9', '6', '8', '0', '5', '0', '7', '7', '8', '7', '/', '2', '0', '6', '5', '5', '0', '1', '5', '5', '8', '1', '8', '3', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0277441_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 412) (SourceJson.white (fragment0277441Field005Chars00 ++ tail)) fragment0277441Acc00500 =
      SourceJson.object (fuel + 411) (SourceJson.white tail) fragment0277441Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_005"
  err.flush

noncomputable def fragment0277441Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0277441Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '0', '5', '1', '5', '1', '6', '3', '0', '0', '0', '7', '4', '3', '0', '0', '6', '5', '6', '4', '0', '8', '7', '2', '3', '4', '9', '2', '5', '1', '3', '5', '8', '3', '5', '8', '8', '0', '9', '1', '1', '6', '6', '2', '7', '4', '8', '4', '0', '4', '6', '2', '5', '/', '1', '4', '9', '2', '4', '7', '8', '6', '8', '3', '0', '6', '4', '5', '2', '8', '0', '0', '7', '1', '8', '6', '1', '5', '8', '2', '7', '0', '9', '5', '8', '9', '9', '3', '3', '6', '2', '0', '7', '9', '4', '1', '3', '7', '9', '8', '4', '7', '3', '6', '5', '9', '1', '3', '0', '5', '7', '0', '0', '3', '0', '7', '8', '5', '7', '9', '2'])
noncomputable def fragment0277441Acc00700 : List (String × SourceJson) := (fragment0277441Field006Key00, fragment0277441Field006Value00) :: fragment0277441Acc00600
noncomputable def fragment0277441Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '0', '5', '1', '5', '1', '6', '3', '0', '0', '0', '7', '4', '3', '0', '0', '6', '5', '6', '4', '0', '8', '7', '2', '3', '4', '9', '2', '5', '1', '3', '5', '8', '3', '5', '8', '8', '0', '9', '1', '1', '6', '6', '2', '7', '4', '8', '4', '0', '4', '6', '2', '5', '/', '1', '4', '9', '2', '4', '7', '8', '6', '8', '3', '0', '6', '4', '5', '2', '8', '0', '0', '7', '1', '8', '6', '1', '5', '8', '2', '7', '0', '9', '5', '8', '9', '9', '3', '3', '6', '2', '0', '7', '9', '4', '1', '3', '7', '9', '8', '4', '7', '3', '6', '5', '9', '1', '3', '0', '5', '7', '0', '0', '3', '0', '7', '8', '5', '7', '9', '2', '"', ',']

theorem object_fragment0277441_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 411) (SourceJson.white (fragment0277441Field006Chars00 ++ tail)) fragment0277441Acc00600 =
      SourceJson.object (fuel + 410) (SourceJson.white tail) fragment0277441Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_006"
  err.flush

noncomputable def fragment0277441Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0277441Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '9', '2', '9', '1', '9', '8', '9', '0', '5', '7', '0', '6', '4', '6', '5', '5', '6', '8', '4', '0', '1', '7', '3', '8', '3', '7', '4', '5', '0', '6', '0', '1', '9', '1', '1', '5', '3', '7', '4', '0', '2', '0', '7', '3', '0', '2', '5', '7', '3', '4', '4', '0', '6', '6', '8', '6', '7', '7', '4', '6', '3', '7', '4', '5', '4', '3', '0', '2', '5', '8', '6', '7', '7', '9', '8', '0', '5', '4', '2', '3', '9', '1', '6', '6', '7', '0', '4', '6', '8', '8', '0', '5', '8', '1', '6', '7', '2', '9', '6', '1', '2', '7', '8', '1', '9', '0', '5', '8', '5', '4', '2', '8', '5', '7', '1', '0', '4', '2', '3', '4', '2', '4', '6', '0', '2', '5', '9', '2', '2', '8', '3', '9', '4', '6', '6', '1', '1', '3', '0', '3', '9', '8', '0', '1', '3', '3', '4', '9', '9', '1', '1', '3', '9', '8', '6', '3', '9', '3', '2', '2', '4', '5', '5', '0', '2', '6', '9', '7', '3', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '9', '9', '0', '4', '2', '7', '7', '7', '7', '8', '5', '0', '3', '0', '7', '0', '9', '0', '3', '6', '7', '9', '7', '7', '0', '5', '6', '7', '1', '5', '7', '8', '5', '8', '7', '4', '6', '9', '8', '3', '2', '5', '1', '9', '3', '3', '3', '6', '6', '5', '0', '1', '1', '4', '5', '7', '3', '1', '9', '1', '9', '8', '7', '7', '3', '3', '2', '7', '0', '7', '4', '3', '0', '7', '4', '6', '6', '6', '1', '1', '9', '9', '7', '2', '0', '7', '3', '1', '7', '0', '3', '4', '7', '2', '9', '8', '0', '9', '9', '9', '0', '9', '1', '6', '8', '1', '1', '0', '3', '9', '1', '2', '0', '2', '1', '7', '8', '0', '4', '9', '9', '4', '3', '7', '9', '0', '2', '4', '8', '7', '3', '7', '7', '0', '5', '4', '6', '0', '9', '2', '2', '8', '8', '6', '2', '6', '3', '0', '6', '8', '6', '5', '0', '7', '3', '7', '8', '7', '6', '3', '0', '0', '0', '0', '4', '1', '1', '8', '5', '5', '0', '4', '3', '1', '7', '5', '5', '9', '0', '8', '5', '8', '9', '8', '7', '3', '9', '1', '5', '9', '7', '3', '3', '9', '4', '1', '4', '4', '8', '3', '1', '8', '2', '5', '3', '5', '7', '7'])
noncomputable def fragment0277441Acc00800 : List (String × SourceJson) := (fragment0277441Field007Key00, fragment0277441Field007Value00) :: fragment0277441Acc00700
noncomputable def fragment0277441Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '9', '2', '9', '1', '9', '8', '9', '0', '5', '7', '0', '6', '4', '6', '5', '5', '6', '8', '4', '0', '1', '7', '3', '8', '3', '7', '4', '5', '0', '6', '0', '1', '9', '1', '1', '5', '3', '7', '4', '0', '2', '0', '7', '3', '0', '2', '5', '7', '3', '4', '4', '0', '6', '6', '8', '6', '7', '7', '4', '6', '3', '7', '4', '5', '4', '3', '0', '2', '5', '8', '6', '7', '7', '9', '8', '0', '5', '4', '2', '3', '9', '1', '6', '6', '7', '0', '4', '6', '8', '8', '0', '5', '8', '1', '6', '7', '2', '9', '6', '1', '2', '7', '8', '1', '9', '0', '5', '8', '5', '4', '2', '8', '5', '7', '1', '0', '4', '2', '3', '4', '2', '4', '6', '0', '2', '5', '9', '2', '2', '8', '3', '9', '4', '6', '6', '1', '1', '3', '0', '3', '9', '8', '0', '1', '3', '3', '4', '9', '9', '1', '1', '3', '9', '8', '6', '3', '9', '3', '2', '2', '4', '5', '5', '0', '2', '6', '9', '7', '3', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '9', '9', '0', '4', '2', '7', '7', '7', '7', '8', '5', '0', '3', '0', '7', '0', '9', '0', '3', '6', '7', '9', '7', '7', '0', '5', '6', '7', '1', '5', '7', '8', '5', '8', '7', '4', '6', '9', '8', '3', '2', '5', '1', '9', '3', '3', '3', '6', '6', '5', '0', '1', '1', '4', '5', '7', '3', '1', '9', '1', '9', '8', '7', '7', '3', '3', '2', '7', '0', '7', '4', '3', '0', '7', '4', '6', '6', '6', '1', '1', '9', '9', '7', '2', '0', '7', '3', '1', '7', '0', '3', '4', '7', '2', '9', '8', '0', '9', '9', '9', '0', '9', '1', '6', '8', '1', '1', '0', '3', '9', '1', '2', '0', '2', '1', '7', '8', '0', '4', '9', '9', '4', '3', '7', '9', '0', '2', '4', '8', '7', '3', '7', '7', '0', '5', '4', '6', '0', '9', '2', '2', '8', '8', '6', '2', '6', '3', '0', '6', '8', '6', '5', '0', '7', '3', '7', '8', '7', '6', '3', '0', '0', '0', '0', '4', '1', '1', '8', '5', '5', '0', '4', '3', '1', '7', '5', '5', '9', '0', '8', '5', '8', '9', '8', '7', '3', '9', '1', '5', '9', '7', '3', '3', '9', '4', '1', '4', '4', '8', '3', '1', '8', '2', '5', '3', '5', '7', '7', '"', ',']

theorem object_fragment0277441_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 410) (SourceJson.white (fragment0277441Field007Chars00 ++ tail)) fragment0277441Acc00700 =
      SourceJson.object (fuel + 409) (SourceJson.white tail) fragment0277441Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_007"
  err.flush

noncomputable def fragment0277441Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0277441Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '1', '1', '3', '4', '8', '8', '6', '9', '9', '6', '5', '8', '5', '8', '2'])
noncomputable def fragment0277441Acc00900 : List (String × SourceJson) := (fragment0277441Field008Key00, fragment0277441Field008Value00) :: fragment0277441Acc00800
noncomputable def fragment0277441Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '1', '1', '3', '4', '8', '8', '6', '9', '9', '6', '5', '8', '5', '8', '2', '"', ',']

theorem object_fragment0277441_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 409) (SourceJson.white (fragment0277441Field008Chars00 ++ tail)) fragment0277441Acc00800 =
      SourceJson.object (fuel + 408) (SourceJson.white tail) fragment0277441Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_008"
  err.flush

noncomputable def fragment0277441Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0277441Field009Value00 : SourceJson := .str (String.ofList ['2', '8', '9', '5', '5', '7', '3', '5', '1', '4', '4', '8', '3', '9', '0', '8', '3'])
noncomputable def fragment0277441Acc01000 : List (String × SourceJson) := (fragment0277441Field009Key00, fragment0277441Field009Value00) :: fragment0277441Acc00900
noncomputable def fragment0277441Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '8', '9', '5', '5', '7', '3', '5', '1', '4', '4', '8', '3', '9', '0', '8', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0277441_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 408) (SourceJson.white (fragment0277441Field009Chars00 ++ tail)) fragment0277441Acc00900 =
      .ok (.obj (fragment0277441Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0277441_object_field_009"
  err.flush

noncomputable def fragment0277441Chars : List Char := '{' :: (fragment0277441Field000Chars00 ++ fragment0277441Field001Chars00 ++ fragment0277441Field002Chars00 ++ fragment0277441Field003Chars00 ++ fragment0277441Field004Chars00 ++ fragment0277441Field005Chars00 ++ fragment0277441Field006Chars00 ++ fragment0277441Field007Chars00 ++ fragment0277441Field008Chars00 ++ fragment0277441Field009Chars00)
noncomputable def fragment0277441Value : SourceJson := .obj (fragment0277441Acc01000.reverse)

theorem value_fragment0277441 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 418) (fragment0277441Chars ++ tail) =
      .ok (fragment0277441Value, tail) := by
  have hinput : fragment0277441Chars ++ tail = '{' :: (fragment0277441Field000Chars00 ++ (fragment0277441Field001Chars00 ++ (fragment0277441Field002Chars00 ++ (fragment0277441Field003Chars00 ++ (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0277441Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 418) (fragment0277441Chars ++ tail) =
        SourceJson.value (fuel + 418) ('{' :: (fragment0277441Field000Chars00 ++ (fragment0277441Field001Chars00 ++ (fragment0277441Field002Chars00 ++ (fragment0277441Field003Chars00 ++ (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 418)) hinput
    _ = SourceJson.object (fuel + 417) (SourceJson.white (fragment0277441Field000Chars00 ++ (fragment0277441Field001Chars00 ++ (fragment0277441Field002Chars00 ++ (fragment0277441Field003Chars00 ++ (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))))))))))) fragment0277441Acc00000 := by rfl
    _ = SourceJson.object (fuel + 416) (SourceJson.white (fragment0277441Field001Chars00 ++ (fragment0277441Field002Chars00 ++ (fragment0277441Field003Chars00 ++ (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail))))))))))) fragment0277441Acc00100 := object_fragment0277441_field_000 fuel (fragment0277441Field001Chars00 ++ (fragment0277441Field002Chars00 ++ (fragment0277441Field003Chars00 ++ (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 415) (SourceJson.white (fragment0277441Field002Chars00 ++ (fragment0277441Field003Chars00 ++ (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))))))))) fragment0277441Acc00200 := object_fragment0277441_field_001 fuel (fragment0277441Field002Chars00 ++ (fragment0277441Field003Chars00 ++ (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 414) (SourceJson.white (fragment0277441Field003Chars00 ++ (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail))))))))) fragment0277441Acc00300 := object_fragment0277441_field_002 fuel (fragment0277441Field003Chars00 ++ (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 413) (SourceJson.white (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))))))) fragment0277441Acc00400 := object_fragment0277441_field_003 fuel (fragment0277441Field004Chars00 ++ (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 412) (SourceJson.white (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail))))))) fragment0277441Acc00500 := object_fragment0277441_field_004 fuel (fragment0277441Field005Chars00 ++ (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 411) (SourceJson.white (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))))) fragment0277441Acc00600 := object_fragment0277441_field_005 fuel (fragment0277441Field006Chars00 ++ (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 410) (SourceJson.white (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail))))) fragment0277441Acc00700 := object_fragment0277441_field_006 fuel (fragment0277441Field007Chars00 ++ (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 409) (SourceJson.white (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))) fragment0277441Acc00800 := object_fragment0277441_field_007 fuel (fragment0277441Field008Chars00 ++ (fragment0277441Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 408) (SourceJson.white (fragment0277441Field009Chars00 ++ (tail))) fragment0277441Acc00900 := object_fragment0277441_field_008 fuel (fragment0277441Field009Chars00 ++ (tail))
    _ = .ok (fragment0277441Value, tail) := object_fragment0277441_field_009 fuel (tail)

noncomputable def fragment0279405Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0279405Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0279405Field000Value00 : SourceJson := .number (String.ofList ['8', '2'])
noncomputable def fragment0279405Acc00100 : List (String × SourceJson) := (fragment0279405Field000Key00, fragment0279405Field000Value00) :: fragment0279405Acc00000
noncomputable def fragment0279405Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '2', ',']

theorem object_fragment0279405_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0279405Field000Chars00 ++ tail)) fragment0279405Acc00000 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0279405Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_000"
  err.flush

noncomputable def fragment0279405Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0279405Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0279405Acc00200 : List (String × SourceJson) := (fragment0279405Field001Key00, fragment0279405Field001Value00) :: fragment0279405Acc00100
noncomputable def fragment0279405Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0279405_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0279405Field001Chars00 ++ tail)) fragment0279405Acc00100 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0279405Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_001"
  err.flush

noncomputable def fragment0279405Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0279405Field002Value00 : SourceJson := .str (String.ofList ['3', '0', '0', '1', '6', '4', '1', '6', '7', '4', '9', '6', '0', '9', '5', '9', '8', '4', '1', '8', '2', '6', '8', '7', '1', '8', '2', '1', '2', '1', '2', '6', '7', '7', '1', '0', '0', '0', '8', '6', '9', '/', '6', '8', '9', '1', '4', '1', '4', '5', '4', '2', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0279405Acc00300 : List (String × SourceJson) := (fragment0279405Field002Key00, fragment0279405Field002Value00) :: fragment0279405Acc00200
noncomputable def fragment0279405Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '0', '0', '1', '6', '4', '1', '6', '7', '4', '9', '6', '0', '9', '5', '9', '8', '4', '1', '8', '2', '6', '8', '7', '1', '8', '2', '1', '2', '1', '2', '6', '7', '7', '1', '0', '0', '0', '8', '6', '9', '/', '6', '8', '9', '1', '4', '1', '4', '5', '4', '2', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0279405_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0279405Field002Chars00 ++ tail)) fragment0279405Acc00200 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0279405Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_002"
  err.flush

noncomputable def fragment0279405Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0279405Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0279405Acc00400 : List (String × SourceJson) := (fragment0279405Field003Key00, fragment0279405Field003Value00) :: fragment0279405Acc00300
noncomputable def fragment0279405Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0279405_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0279405Field003Chars00 ++ tail)) fragment0279405Acc00300 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0279405Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_003"
  err.flush

noncomputable def fragment0279405Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0279405Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0279405Acc00500 : List (String × SourceJson) := (fragment0279405Field004Key00, fragment0279405Field004Value00) :: fragment0279405Acc00400
noncomputable def fragment0279405Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0279405_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0279405Field004Chars00 ++ tail)) fragment0279405Acc00400 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0279405Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_004"
  err.flush

noncomputable def fragment0279405Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0279405Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '8', '3', '3', '2', '0', '7', '2', '0', '8', '5', '0', '7', '3', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '6', '1', '4', '1', '7', '2', '1', '7', '7', '3', '1', '9', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '6', '1', '9', '4', '7', '3', '9', '9', '5', '7', '/', '1', '3', '9', '2', '9', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '4', '0', '6', '2', '3', '4', '9', '6', '0', '3', '1', '/', '9', '1', '5', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '9', '0', '8', '8', '1', '8', '3', '3', '0', '7', '1', '/', '9', '1', '5', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '7', '1', '9', '8', '3', '0', '7', '9', '9', '/', '3', '6', '4', '0', '6', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '2', '9', '2', '5', '9', '6', '3', '9', '2', '5', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '8', '2', '5', '5', '0', '0', '5', '8', '8', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '4', '6', '9', '3', '2', '7', '6', '6', '8', '1', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '0', '5', '9', '0', '9', '7', '9', '5', '7', '0', '7', '9', '/', '6', '4', '0', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0279405Acc00600 : List (String × SourceJson) := (fragment0279405Field005Key00, fragment0279405Field005Value00) :: fragment0279405Acc00500
noncomputable def fragment0279405Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '3', '2', '0', '7', '2', '0', '8', '5', '0', '7', '3', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '1', '4', '1', '7', '2', '1', '7', '7', '3', '1', '9', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '1', '9', '4', '7', '3', '9', '9', '5', '7', '/', '1', '3', '9', '2', '9', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '4', '0', '6', '2', '3', '4', '9', '6', '0', '3', '1', '/', '9', '1', '5', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '9', '0', '8', '8', '1', '8', '3', '3', '0', '7', '1', '/', '9', '1', '5', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '7', '1', '9', '8', '3', '0', '7', '9', '9', '/', '3', '6', '4', '0', '6', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '9', '2', '5', '9', '6', '3', '9', '2', '5', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '8', '2', '5', '5', '0', '0', '5', '8', '8', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '4', '6', '9', '3', '2', '7', '6', '6', '8', '1', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '5', '9', '0', '9', '7', '9', '5', '7', '0', '7', '9', '/', '6', '4', '0', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0279405_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0279405Field005Chars00 ++ tail)) fragment0279405Acc00500 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0279405Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_005"
  err.flush

noncomputable def fragment0279405Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0279405Field006Value00 : SourceJson := .str (String.ofList ['3', '5', '5', '9', '3', '9', '1', '8', '9', '1', '4', '3', '1', '5', '1', '7', '4', '2', '4', '4', '6', '0', '7', '6', '6', '7', '5', '8', '5', '8', '1', '0', '1', '8', '4', '6', '9', '0', '2', '4', '4', '9', '7', '1', '2', '8', '3', '8', '2', '2', '0', '0', '0', '0', '0', '/', '7', '2', '3', '9', '3', '6', '9', '5', '7', '4', '3', '6', '2', '7', '6', '2', '7', '1', '0', '8', '7', '9', '1', '2', '2', '4', '5', '8', '8', '1', '9', '4', '2', '5', '8', '7', '3', '1', '5', '0', '0', '8', '2', '0', '9', '5', '6', '8', '7', '1', '3', '0', '5', '3', '0', '1', '2', '5', '1', '7', '6', '8', '3', '9', '4', '0', '1'])
noncomputable def fragment0279405Acc00700 : List (String × SourceJson) := (fragment0279405Field006Key00, fragment0279405Field006Value00) :: fragment0279405Acc00600
noncomputable def fragment0279405Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '5', '5', '9', '3', '9', '1', '8', '9', '1', '4', '3', '1', '5', '1', '7', '4', '2', '4', '4', '6', '0', '7', '6', '6', '7', '5', '8', '5', '8', '1', '0', '1', '8', '4', '6', '9', '0', '2', '4', '4', '9', '7', '1', '2', '8', '3', '8', '2', '2', '0', '0', '0', '0', '0', '/', '7', '2', '3', '9', '3', '6', '9', '5', '7', '4', '3', '6', '2', '7', '6', '2', '7', '1', '0', '8', '7', '9', '1', '2', '2', '4', '5', '8', '8', '1', '9', '4', '2', '5', '8', '7', '3', '1', '5', '0', '0', '8', '2', '0', '9', '5', '6', '8', '7', '1', '3', '0', '5', '3', '0', '1', '2', '5', '1', '7', '6', '8', '3', '9', '4', '0', '1', '"', ',']

theorem object_fragment0279405_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0279405Field006Chars00 ++ tail)) fragment0279405Acc00600 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0279405Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_006"
  err.flush

noncomputable def fragment0279405Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0279405Field007Value00 : SourceJson := .str (String.ofList ['6', '8', '2', '1', '8', '4', '0', '7', '6', '4', '9', '8', '1', '5', '3', '2', '9', '4', '4', '8', '0', '9', '9', '4', '9', '0', '2', '6', '7', '3', '5', '4', '5', '0', '0', '5', '8', '3', '4', '3', '6', '4', '3', '2', '5', '8', '4', '2', '2', '9', '3', '1', '9', '0', '7', '5', '3', '6', '1', '9', '1', '2', '6', '6', '5', '0', '5', '6', '2', '6', '2', '6', '6', '0', '0', '8', '2', '0', '5', '0', '5', '9', '0', '2', '9', '7', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '7', '4', '9', '2', '4', '1', '2', '5', '6', '2', '7', '0', '2', '5', '5', '8', '0', '4', '9', '4', '4', '8', '0', '5', '3', '9', '9', '5', '3', '0', '5', '6', '6', '0', '0', '0', '0', '1', '1', '1', '0', '5', '8', '6', '3', '6', '2', '9', '7', '0', '8', '9', '8', '0', '5', '0', '9', '2', '2', '0', '1', '6', '9', '9', '3', '9', '9', '8', '5', '9', '8', '8', '7', '5', '6', '9', '7', '4', '5', '1', '3', '9', '7', '0', '2', '2', '8', '5', '2', '5', '1', '1', '4', '6', '8', '5', '8', '6', '2', '0', '1', '5', '2', '9', '1', '6', '1', '7', '9', '9', '9', '2', '2', '1', '7', '8', '2', '3', '6', '5', '4', '7'])
noncomputable def fragment0279405Acc00800 : List (String × SourceJson) := (fragment0279405Field007Key00, fragment0279405Field007Value00) :: fragment0279405Acc00700
noncomputable def fragment0279405Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '8', '2', '1', '8', '4', '0', '7', '6', '4', '9', '8', '1', '5', '3', '2', '9', '4', '4', '8', '0', '9', '9', '4', '9', '0', '2', '6', '7', '3', '5', '4', '5', '0', '0', '5', '8', '3', '4', '3', '6', '4', '3', '2', '5', '8', '4', '2', '2', '9', '3', '1', '9', '0', '7', '5', '3', '6', '1', '9', '1', '2', '6', '6', '5', '0', '5', '6', '2', '6', '2', '6', '6', '0', '0', '8', '2', '0', '5', '0', '5', '9', '0', '2', '9', '7', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '7', '4', '9', '2', '4', '1', '2', '5', '6', '2', '7', '0', '2', '5', '5', '8', '0', '4', '9', '4', '4', '8', '0', '5', '3', '9', '9', '5', '3', '0', '5', '6', '6', '0', '0', '0', '0', '1', '1', '1', '0', '5', '8', '6', '3', '6', '2', '9', '7', '0', '8', '9', '8', '0', '5', '0', '9', '2', '2', '0', '1', '6', '9', '9', '3', '9', '9', '8', '5', '9', '8', '8', '7', '5', '6', '9', '7', '4', '5', '1', '3', '9', '7', '0', '2', '2', '8', '5', '2', '5', '1', '1', '4', '6', '8', '5', '8', '6', '2', '0', '1', '5', '2', '9', '1', '6', '1', '7', '9', '9', '9', '2', '2', '1', '7', '8', '2', '3', '6', '5', '4', '7', '"', ',']

theorem object_fragment0279405_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0279405Field007Chars00 ++ tail)) fragment0279405Acc00700 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0279405Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_007"
  err.flush

noncomputable def fragment0279405Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0279405Field008Value00 : SourceJson := .str (String.ofList ['3', '8', '9', '5', '4', '2', '3', '1', '6', '2', '6', '0', '4', '7', '9', '1', '8'])
noncomputable def fragment0279405Acc00900 : List (String × SourceJson) := (fragment0279405Field008Key00, fragment0279405Field008Value00) :: fragment0279405Acc00800
noncomputable def fragment0279405Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '8', '9', '5', '4', '2', '3', '1', '6', '2', '6', '0', '4', '7', '9', '1', '8', '"', ',']

theorem object_fragment0279405_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0279405Field008Chars00 ++ tail)) fragment0279405Acc00800 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0279405Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_008"
  err.flush

noncomputable def fragment0279405Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0279405Field009Value00 : SourceJson := .str (String.ofList ['1', '4', '7', '0', '7', '2', '9', '4', '3', '6', '3', '0', '4', '1', '3', '5', '2', '4'])
noncomputable def fragment0279405Acc01000 : List (String × SourceJson) := (fragment0279405Field009Key00, fragment0279405Field009Value00) :: fragment0279405Acc00900
noncomputable def fragment0279405Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '7', '0', '7', '2', '9', '4', '3', '6', '3', '0', '4', '1', '3', '5', '2', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0279405_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0279405Field009Chars00 ++ tail)) fragment0279405Acc00900 =
      .ok (.obj (fragment0279405Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0279405_object_field_009"
  err.flush

noncomputable def fragment0279405Chars : List Char := '{' :: (fragment0279405Field000Chars00 ++ fragment0279405Field001Chars00 ++ fragment0279405Field002Chars00 ++ fragment0279405Field003Chars00 ++ fragment0279405Field004Chars00 ++ fragment0279405Field005Chars00 ++ fragment0279405Field006Chars00 ++ fragment0279405Field007Chars00 ++ fragment0279405Field008Chars00 ++ fragment0279405Field009Chars00)
noncomputable def fragment0279405Value : SourceJson := .obj (fragment0279405Acc01000.reverse)

theorem value_fragment0279405 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 248) (fragment0279405Chars ++ tail) =
      .ok (fragment0279405Value, tail) := by
  have hinput : fragment0279405Chars ++ tail = '{' :: (fragment0279405Field000Chars00 ++ (fragment0279405Field001Chars00 ++ (fragment0279405Field002Chars00 ++ (fragment0279405Field003Chars00 ++ (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0279405Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 248) (fragment0279405Chars ++ tail) =
        SourceJson.value (fuel + 248) ('{' :: (fragment0279405Field000Chars00 ++ (fragment0279405Field001Chars00 ++ (fragment0279405Field002Chars00 ++ (fragment0279405Field003Chars00 ++ (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 248)) hinput
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0279405Field000Chars00 ++ (fragment0279405Field001Chars00 ++ (fragment0279405Field002Chars00 ++ (fragment0279405Field003Chars00 ++ (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))))))))))) fragment0279405Acc00000 := by rfl
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0279405Field001Chars00 ++ (fragment0279405Field002Chars00 ++ (fragment0279405Field003Chars00 ++ (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail))))))))))) fragment0279405Acc00100 := object_fragment0279405_field_000 fuel (fragment0279405Field001Chars00 ++ (fragment0279405Field002Chars00 ++ (fragment0279405Field003Chars00 ++ (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0279405Field002Chars00 ++ (fragment0279405Field003Chars00 ++ (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))))))))) fragment0279405Acc00200 := object_fragment0279405_field_001 fuel (fragment0279405Field002Chars00 ++ (fragment0279405Field003Chars00 ++ (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0279405Field003Chars00 ++ (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail))))))))) fragment0279405Acc00300 := object_fragment0279405_field_002 fuel (fragment0279405Field003Chars00 ++ (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))))))) fragment0279405Acc00400 := object_fragment0279405_field_003 fuel (fragment0279405Field004Chars00 ++ (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail))))))) fragment0279405Acc00500 := object_fragment0279405_field_004 fuel (fragment0279405Field005Chars00 ++ (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))))) fragment0279405Acc00600 := object_fragment0279405_field_005 fuel (fragment0279405Field006Chars00 ++ (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail))))) fragment0279405Acc00700 := object_fragment0279405_field_006 fuel (fragment0279405Field007Chars00 ++ (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))) fragment0279405Acc00800 := object_fragment0279405_field_007 fuel (fragment0279405Field008Chars00 ++ (fragment0279405Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0279405Field009Chars00 ++ (tail))) fragment0279405Acc00900 := object_fragment0279405_field_008 fuel (fragment0279405Field009Chars00 ++ (tail))
    _ = .ok (fragment0279405Value, tail) := object_fragment0279405_field_009 fuel (tail)

noncomputable def fragment0281047Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0281047Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0281047Field000Value00 : SourceJson := .number (String.ofList ['8', '3'])
noncomputable def fragment0281047Acc00100 : List (String × SourceJson) := (fragment0281047Field000Key00, fragment0281047Field000Value00) :: fragment0281047Acc00000
noncomputable def fragment0281047Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '3', ',']

theorem object_fragment0281047_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0281047Field000Chars00 ++ tail)) fragment0281047Acc00000 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0281047Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_000"
  err.flush

noncomputable def fragment0281047Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0281047Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0281047Acc00200 : List (String × SourceJson) := (fragment0281047Field001Key00, fragment0281047Field001Value00) :: fragment0281047Acc00100
noncomputable def fragment0281047Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0281047_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0281047Field001Chars00 ++ tail)) fragment0281047Acc00100 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0281047Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_001"
  err.flush

noncomputable def fragment0281047Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0281047Field002Value00 : SourceJson := .str (String.ofList ['3', '1', '7', '0', '6', '7', '8', '4', '7', '8', '4', '2', '5', '8', '9', '8', '0', '9', '1', '8', '2', '9', '1', '3', '4', '8', '2', '0', '6', '6', '6', '9', '8', '9', '6', '8', '6', '4', '1', '3', '/', '6', '3', '7', '0', '3', '5', '7', '4', '0', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0281047Acc00300 : List (String × SourceJson) := (fragment0281047Field002Key00, fragment0281047Field002Value00) :: fragment0281047Acc00200
noncomputable def fragment0281047Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '1', '7', '0', '6', '7', '8', '4', '7', '8', '4', '2', '5', '8', '9', '8', '0', '9', '1', '8', '2', '9', '1', '3', '4', '8', '2', '0', '6', '6', '6', '9', '8', '9', '6', '8', '6', '4', '1', '3', '/', '6', '3', '7', '0', '3', '5', '7', '4', '0', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0281047_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0281047Field002Chars00 ++ tail)) fragment0281047Acc00200 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0281047Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_002"
  err.flush

noncomputable def fragment0281047Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0281047Field003Value00 : SourceJson := .str (String.ofList ['9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0281047Acc00400 : List (String × SourceJson) := (fragment0281047Field003Key00, fragment0281047Field003Value00) :: fragment0281047Acc00300
noncomputable def fragment0281047Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0281047_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0281047Field003Chars00 ++ tail)) fragment0281047Acc00300 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0281047Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_003"
  err.flush

noncomputable def fragment0281047Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0281047Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0281047Acc00500 : List (String × SourceJson) := (fragment0281047Field004Key00, fragment0281047Field004Value00) :: fragment0281047Acc00400
noncomputable def fragment0281047Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0281047_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0281047Field004Chars00 ++ tail)) fragment0281047Acc00400 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment0281047Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_004"
  err.flush

noncomputable def fragment0281047Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0281047Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '6', '4', '1', '9', '1', '2', '5', '3', '4', '7', '7', '4', '3', '1', '1', '9', '5', '2', '1', '9', '/', '6', '6', '2', '8', '1', '0', '2', '0', '1', '5', '0', '6', '5', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '1', '2', '3', '1', '2', '6', '2', '8', '5', '6', '0', '2', '7', '1', '6', '8', '7', '/', '7', '7', '0', '7', '0', '9', '5', '3', '6', '6', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '6', '3', '7', '7', '5', '7', '1', '4', '0', '0', '7', '1', '6', '1', '4', '9', '/', '4', '8', '0', '2', '9', '7', '2', '4', '7', '4', '6', '8', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '3', '4', '8', '5', '1', '0', '1', '6', '2', '3', '7', '7', '4', '8', '6', '1', '3', '/', '7', '8', '9', '0', '5', '9', '7', '6', '3', '6', '9', '8', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '3', '9', '9', '0', '7', '8', '8', '3', '7', '1', '1', '7', '0', '2', '6', '1', '/', '2', '6', '3', '0', '1', '9', '9', '2', '1', '2', '3', '2', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '7', '4', '2', '2', '5', '1', '3', '1', '8', '4', '5', '8', '8', '7', '9', '9', '/', '1', '6', '7', '3', '7', '6', '3', '1', '3', '5', '1', '1', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '5', '4', '5', '1', '7', '7', '3', '3', '4', '5', '9', '1', '4', '9', '2', '9', '1', '/', '1', '3', '3', '9', '0', '1', '0', '5', '0', '8', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '3', '5', '9', '6', '5', '6', '7', '0', '2', '8', '6', '3', '3', '0', '5', '4', '3', '/', '4', '0', '1', '7', '0', '3', '1', '5', '2', '4', '2', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '5', '1', '8', '8', '6', '7', '3', '4', '7', '9', '2', '9', '1', '1', '3', '3', '9', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '0', '9', '5', '4', '4', '7', '1', '2', '8', '5', '4', '8', '6', '8', '8', '9', '/', '7', '7', '0', '7', '0', '9', '5', '3', '6', '6', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0281047Acc00600 : List (String × SourceJson) := (fragment0281047Field005Key00, fragment0281047Field005Value00) :: fragment0281047Acc00500
noncomputable def fragment0281047Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '4', '1', '9', '1', '2', '5', '3', '4', '7', '7', '4', '3', '1', '1', '9', '5', '2', '1', '9', '/', '6', '6', '2', '8', '1', '0', '2', '0', '1', '5', '0', '6', '5', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '1', '2', '3', '1', '2', '6', '2', '8', '5', '6', '0', '2', '7', '1', '6', '8', '7', '/', '7', '7', '0', '7', '0', '9', '5', '3', '6', '6', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '6', '3', '7', '7', '5', '7', '1', '4', '0', '0', '7', '1', '6', '1', '4', '9', '/', '4', '8', '0', '2', '9', '7', '2', '4', '7', '4', '6', '8', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '3', '4', '8', '5', '1', '0', '1', '6', '2', '3', '7', '7', '4', '8', '6', '1', '3', '/', '7', '8', '9', '0', '5', '9', '7', '6', '3', '6', '9', '8', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '3', '9', '9', '0', '7', '8', '8', '3', '7', '1', '1', '7', '0', '2', '6', '1', '/', '2', '6', '3', '0', '1', '9', '9', '2', '1', '2', '3', '2', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '7', '4', '2', '2', '5', '1', '3', '1', '8', '4', '5', '8', '8', '7', '9', '9', '/', '1', '6', '7', '3', '7', '6', '3', '1', '3', '5', '1', '1', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '5', '4', '5', '1', '7', '7', '3', '3', '4', '5', '9', '1', '4', '9', '2', '9', '1', '/', '1', '3', '3', '9', '0', '1', '0', '5', '0', '8', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '3', '5', '9', '6', '5', '6', '7', '0', '2', '8', '6', '3', '3', '0', '5', '4', '3', '/', '4', '0', '1', '7', '0', '3', '1', '5', '2', '4', '2', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '5', '1', '8', '8', '6', '7', '3', '4', '7', '9', '2', '9', '1', '1', '3', '3', '9', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '0', '9', '5', '4', '4', '7', '1', '2', '8', '5', '4', '8', '6', '8', '8', '9', '/', '7', '7', '0', '7', '0', '9', '5', '3', '6', '6', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0281047_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment0281047Field005Chars00 ++ tail)) fragment0281047Acc00500 =
      SourceJson.object (fuel + 361) (SourceJson.white tail) fragment0281047Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_005"
  err.flush

noncomputable def fragment0281047Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0281047Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '4', '3', '2', '5', '2', '6', '3', '1', '5', '5', '3', '8', '1', '2', '4', '8', '6', '5', '8', '2', '0', '9', '5', '3', '3', '3', '3', '4', '4', '0', '7', '7', '8', '6', '4', '2', '3', '0', '5', '6', '7', '8', '7', '4', '9', '1', '5', '3', '7', '5', '/', '1', '0', '9', '5', '2', '7', '2', '7', '7', '2', '4', '8', '6', '1', '5', '7', '2', '9', '7', '9', '6', '4', '6', '3', '6', '0', '0', '7', '5', '4', '0', '1', '5', '4', '9', '6', '2', '3', '3', '9', '6', '3', '2', '2', '2', '9', '2', '1', '0', '4', '1', '6', '5', '7', '6', '8', '8', '5', '5', '4', '9', '0', '4', '9', '6'])
noncomputable def fragment0281047Acc00700 : List (String × SourceJson) := (fragment0281047Field006Key00, fragment0281047Field006Value00) :: fragment0281047Acc00600
noncomputable def fragment0281047Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '4', '3', '2', '5', '2', '6', '3', '1', '5', '5', '3', '8', '1', '2', '4', '8', '6', '5', '8', '2', '0', '9', '5', '3', '3', '3', '3', '4', '4', '0', '7', '7', '8', '6', '4', '2', '3', '0', '5', '6', '7', '8', '7', '4', '9', '1', '5', '3', '7', '5', '/', '1', '0', '9', '5', '2', '7', '2', '7', '7', '2', '4', '8', '6', '1', '5', '7', '2', '9', '7', '9', '6', '4', '6', '3', '6', '0', '0', '7', '5', '4', '0', '1', '5', '4', '9', '6', '2', '3', '3', '9', '6', '3', '2', '2', '2', '9', '2', '1', '0', '4', '1', '6', '5', '7', '6', '8', '8', '5', '5', '4', '9', '0', '4', '9', '6', '"', ',']

theorem object_fragment0281047_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 361) (SourceJson.white (fragment0281047Field006Chars00 ++ tail)) fragment0281047Acc00600 =
      SourceJson.object (fuel + 360) (SourceJson.white tail) fragment0281047Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_006"
  err.flush

noncomputable def fragment0281047Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0281047Field007Value00 : SourceJson := .str (String.ofList ['2', '2', '2', '7', '9', '1', '5', '6', '8', '8', '0', '6', '9', '8', '9', '8', '2', '2', '3', '2', '8', '4', '0', '4', '2', '4', '0', '0', '9', '8', '4', '8', '4', '2', '6', '5', '5', '0', '6', '3', '1', '5', '2', '0', '1', '9', '4', '5', '0', '7', '9', '8', '7', '7', '3', '0', '5', '4', '6', '1', '5', '6', '5', '0', '1', '0', '9', '8', '2', '3', '4', '5', '9', '1', '4', '6', '3', '6', '1', '7', '5', '8', '3', '6', '7', '2', '5', '4', '4', '6', '0', '2', '0', '3', '1', '0', '8', '2', '4', '9', '5', '0', '9', '3', '8', '0', '1', '4', '7', '6', '8', '5', '1', '0', '8', '8', '5', '3', '1', '7', '5', '1', '6', '9', '8', '2', '6', '0', '6', '0', '1', '0', '7', '4', '2', '2', '6', '5', '4', '8', '0', '4', '7', '6', '8', '9', '4', '4', '8', '5', '6', '0', '8', '3', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '9', '4', '7', '2', '8', '1', '3', '5', '1', '2', '9', '2', '4', '9', '0', '8', '0', '3', '0', '0', '9', '5', '2', '2', '1', '5', '0', '5', '8', '8', '2', '5', '6', '1', '5', '9', '7', '0', '3', '3', '6', '9', '0', '7', '9', '4', '6', '5', '5', '3', '1', '1', '5', '5', '3', '6', '9', '2', '9', '8', '2', '8', '1', '0', '0', '7', '1', '4', '0', '0', '1', '3', '5', '5', '6', '9', '8', '2', '6', '6', '4', '0', '3', '4', '2', '1', '7', '6', '6', '8', '8', '9', '0', '6', '5', '7', '0', '8', '2', '8', '9', '3', '0', '3', '3', '4', '1', '8', '2', '4', '4', '4', '2', '6', '4', '3', '2', '2', '7', '2', '7', '4', '5', '7', '0', '2', '4', '0', '3', '2', '3', '0', '7', '8', '0', '2', '5', '1', '9', '8', '4', '0', '0', '9', '8', '1', '7', '8', '9', '5', '7', '5', '0', '3', '5', '5', '8', '7', '8', '2', '6', '2', '0', '8', '0', '8', '9', '9', '7', '9', '9', '1', '2', '1', '4', '6', '2', '3', '3', '9', '3', '9', '7'])
noncomputable def fragment0281047Acc00800 : List (String × SourceJson) := (fragment0281047Field007Key00, fragment0281047Field007Value00) :: fragment0281047Acc00700
noncomputable def fragment0281047Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '2', '7', '9', '1', '5', '6', '8', '8', '0', '6', '9', '8', '9', '8', '2', '2', '3', '2', '8', '4', '0', '4', '2', '4', '0', '0', '9', '8', '4', '8', '4', '2', '6', '5', '5', '0', '6', '3', '1', '5', '2', '0', '1', '9', '4', '5', '0', '7', '9', '8', '7', '7', '3', '0', '5', '4', '6', '1', '5', '6', '5', '0', '1', '0', '9', '8', '2', '3', '4', '5', '9', '1', '4', '6', '3', '6', '1', '7', '5', '8', '3', '6', '7', '2', '5', '4', '4', '6', '0', '2', '0', '3', '1', '0', '8', '2', '4', '9', '5', '0', '9', '3', '8', '0', '1', '4', '7', '6', '8', '5', '1', '0', '8', '8', '5', '3', '1', '7', '5', '1', '6', '9', '8', '2', '6', '0', '6', '0', '1', '0', '7', '4', '2', '2', '6', '5', '4', '8', '0', '4', '7', '6', '8', '9', '4', '4', '8', '5', '6', '0', '8', '3', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '9', '4', '7', '2', '8', '1', '3', '5', '1', '2', '9', '2', '4', '9', '0', '8', '0', '3', '0', '0', '9', '5', '2', '2', '1', '5', '0', '5', '8', '8', '2', '5', '6', '1', '5', '9', '7', '0', '3', '3', '6', '9', '0', '7', '9', '4', '6', '5', '5', '3', '1', '1', '5', '5', '3', '6', '9', '2', '9', '8', '2', '8', '1', '0', '0', '7', '1', '4', '0', '0', '1', '3', '5', '5', '6', '9', '8', '2', '6', '6', '4', '0', '3', '4', '2', '1', '7', '6', '6', '8', '8', '9', '0', '6', '5', '7', '0', '8', '2', '8', '9', '3', '0', '3', '3', '4', '1', '8', '2', '4', '4', '4', '2', '6', '4', '3', '2', '2', '7', '2', '7', '4', '5', '7', '0', '2', '4', '0', '3', '2', '3', '0', '7', '8', '0', '2', '5', '1', '9', '8', '4', '0', '0', '9', '8', '1', '7', '8', '9', '5', '7', '5', '0', '3', '5', '5', '8', '7', '8', '2', '6', '2', '0', '8', '0', '8', '9', '9', '7', '9', '9', '1', '2', '1', '4', '6', '2', '3', '3', '9', '3', '9', '7', '"', ',']

theorem object_fragment0281047_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 360) (SourceJson.white (fragment0281047Field007Chars00 ++ tail)) fragment0281047Acc00700 =
      SourceJson.object (fuel + 359) (SourceJson.white tail) fragment0281047Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_007"
  err.flush

noncomputable def fragment0281047Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0281047Field008Value00 : SourceJson := .str (String.ofList ['1', '3', '3', '3', '3', '4', '3', '8', '2', '7', '3', '6', '5', '4', '9', '3', '7'])
noncomputable def fragment0281047Acc00900 : List (String × SourceJson) := (fragment0281047Field008Key00, fragment0281047Field008Value00) :: fragment0281047Acc00800
noncomputable def fragment0281047Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '3', '3', '3', '4', '3', '8', '2', '7', '3', '6', '5', '4', '9', '3', '7', '"', ',']

theorem object_fragment0281047_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 359) (SourceJson.white (fragment0281047Field008Chars00 ++ tail)) fragment0281047Acc00800 =
      SourceJson.object (fuel + 358) (SourceJson.white tail) fragment0281047Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_008"
  err.flush

noncomputable def fragment0281047Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0281047Field009Value00 : SourceJson := .str (String.ofList ['3', '5', '6', '7', '8', '9', '2', '2', '1', '5', '3', '1', '4', '7', '0', '5', '5'])
noncomputable def fragment0281047Acc01000 : List (String × SourceJson) := (fragment0281047Field009Key00, fragment0281047Field009Value00) :: fragment0281047Acc00900
noncomputable def fragment0281047Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '5', '6', '7', '8', '9', '2', '2', '1', '5', '3', '1', '4', '7', '0', '5', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0281047_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 358) (SourceJson.white (fragment0281047Field009Chars00 ++ tail)) fragment0281047Acc00900 =
      .ok (.obj (fragment0281047Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0281047_object_field_009"
  err.flush

noncomputable def fragment0281047Chars : List Char := '{' :: (fragment0281047Field000Chars00 ++ fragment0281047Field001Chars00 ++ fragment0281047Field002Chars00 ++ fragment0281047Field003Chars00 ++ fragment0281047Field004Chars00 ++ fragment0281047Field005Chars00 ++ fragment0281047Field006Chars00 ++ fragment0281047Field007Chars00 ++ fragment0281047Field008Chars00 ++ fragment0281047Field009Chars00)
noncomputable def fragment0281047Value : SourceJson := .obj (fragment0281047Acc01000.reverse)

theorem value_fragment0281047 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 368) (fragment0281047Chars ++ tail) =
      .ok (fragment0281047Value, tail) := by
  have hinput : fragment0281047Chars ++ tail = '{' :: (fragment0281047Field000Chars00 ++ (fragment0281047Field001Chars00 ++ (fragment0281047Field002Chars00 ++ (fragment0281047Field003Chars00 ++ (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0281047Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 368) (fragment0281047Chars ++ tail) =
        SourceJson.value (fuel + 368) ('{' :: (fragment0281047Field000Chars00 ++ (fragment0281047Field001Chars00 ++ (fragment0281047Field002Chars00 ++ (fragment0281047Field003Chars00 ++ (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 368)) hinput
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0281047Field000Chars00 ++ (fragment0281047Field001Chars00 ++ (fragment0281047Field002Chars00 ++ (fragment0281047Field003Chars00 ++ (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))))))))))) fragment0281047Acc00000 := by rfl
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0281047Field001Chars00 ++ (fragment0281047Field002Chars00 ++ (fragment0281047Field003Chars00 ++ (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail))))))))))) fragment0281047Acc00100 := object_fragment0281047_field_000 fuel (fragment0281047Field001Chars00 ++ (fragment0281047Field002Chars00 ++ (fragment0281047Field003Chars00 ++ (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0281047Field002Chars00 ++ (fragment0281047Field003Chars00 ++ (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))))))))) fragment0281047Acc00200 := object_fragment0281047_field_001 fuel (fragment0281047Field002Chars00 ++ (fragment0281047Field003Chars00 ++ (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0281047Field003Chars00 ++ (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail))))))))) fragment0281047Acc00300 := object_fragment0281047_field_002 fuel (fragment0281047Field003Chars00 ++ (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))))))) fragment0281047Acc00400 := object_fragment0281047_field_003 fuel (fragment0281047Field004Chars00 ++ (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail))))))) fragment0281047Acc00500 := object_fragment0281047_field_004 fuel (fragment0281047Field005Chars00 ++ (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 361) (SourceJson.white (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))))) fragment0281047Acc00600 := object_fragment0281047_field_005 fuel (fragment0281047Field006Chars00 ++ (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 360) (SourceJson.white (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail))))) fragment0281047Acc00700 := object_fragment0281047_field_006 fuel (fragment0281047Field007Chars00 ++ (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 359) (SourceJson.white (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))) fragment0281047Acc00800 := object_fragment0281047_field_007 fuel (fragment0281047Field008Chars00 ++ (fragment0281047Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 358) (SourceJson.white (fragment0281047Field009Chars00 ++ (tail))) fragment0281047Acc00900 := object_fragment0281047_field_008 fuel (fragment0281047Field009Chars00 ++ (tail))
    _ = .ok (fragment0281047Value, tail) := object_fragment0281047_field_009 fuel (tail)

noncomputable def fragment0282920Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0282920Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0282920Field000Value00 : SourceJson := .number (String.ofList ['8', '4'])
noncomputable def fragment0282920Acc00100 : List (String × SourceJson) := (fragment0282920Field000Key00, fragment0282920Field000Value00) :: fragment0282920Acc00000
noncomputable def fragment0282920Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '4', ',']

theorem object_fragment0282920_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0282920Field000Chars00 ++ tail)) fragment0282920Acc00000 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0282920Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_000"
  err.flush

noncomputable def fragment0282920Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0282920Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0282920Acc00200 : List (String × SourceJson) := (fragment0282920Field001Key00, fragment0282920Field001Value00) :: fragment0282920Acc00100
noncomputable def fragment0282920Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0282920_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0282920Field001Chars00 ++ tail)) fragment0282920Acc00100 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0282920Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_001"
  err.flush

noncomputable def fragment0282920Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0282920Field002Value00 : SourceJson := .str (String.ofList ['2', '3', '3', '8', '8', '1', '8', '7', '1', '5', '6', '9', '0', '2', '8', '3', '1', '4', '4', '8', '5', '9', '5', '5', '4', '0', '9', '5', '9', '2', '9', '6', '1', '1', '6', '7', '6', '2', '9', '6', '3', '/', '4', '5', '7', '1', '4', '1', '9', '2', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0282920Acc00300 : List (String × SourceJson) := (fragment0282920Field002Key00, fragment0282920Field002Value00) :: fragment0282920Acc00200
noncomputable def fragment0282920Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '3', '3', '8', '8', '1', '8', '7', '1', '5', '6', '9', '0', '2', '8', '3', '1', '4', '4', '8', '5', '9', '5', '5', '4', '0', '9', '5', '9', '2', '9', '6', '1', '1', '6', '7', '6', '2', '9', '6', '3', '/', '4', '5', '7', '1', '4', '1', '9', '2', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0282920_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0282920Field002Chars00 ++ tail)) fragment0282920Acc00200 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0282920Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_002"
  err.flush

noncomputable def fragment0282920Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0282920Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0282920Acc00400 : List (String × SourceJson) := (fragment0282920Field003Key00, fragment0282920Field003Value00) :: fragment0282920Acc00300
noncomputable def fragment0282920Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0282920_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0282920Field003Chars00 ++ tail)) fragment0282920Acc00300 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0282920Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_003"
  err.flush

noncomputable def fragment0282920Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0282920Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0282920Acc00500 : List (String × SourceJson) := (fragment0282920Field004Key00, fragment0282920Field004Value00) :: fragment0282920Acc00400
noncomputable def fragment0282920Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0282920_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0282920Field004Chars00 ++ tail)) fragment0282920Acc00400 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0282920Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_004"
  err.flush

noncomputable def fragment0282920Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0282920Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '8', '1', '6', '8', '8', '8', '8', '4', '9', '/', '1', '9', '9', '2', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '6', '4', '0', '3', '3', '5', '3', '6', '1', '/', '1', '5', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '9', '4', '4', '7', '4', '8', '7', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '9', '1', '8', '0', '1', '1', '1', '1', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '5', '4', '6', '8', '0', '4', '6', '7', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '0', '9', '6', '8', '5', '9', '9', '5', '1', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '9', '3', '9', '5', '9', '7', '7', '3', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '0', '7', '4', '1', '0', '3', '5', '9', '/', '2', '1', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '8', '7', '7', '8', '2', '5', '9', '8', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '9', '6', '0', '6', '7', '7', '0', '0', '1', '/', '4', '7', '8', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0282920Acc00600 : List (String × SourceJson) := (fragment0282920Field005Key00, fragment0282920Field005Value00) :: fragment0282920Acc00500
noncomputable def fragment0282920Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '1', '6', '8', '8', '8', '8', '4', '9', '/', '1', '9', '9', '2', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '6', '6', '4', '0', '3', '3', '5', '3', '6', '1', '/', '1', '5', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '9', '4', '4', '7', '4', '8', '7', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '9', '1', '8', '0', '1', '1', '1', '1', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '5', '4', '6', '8', '0', '4', '6', '7', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '0', '9', '6', '8', '5', '9', '9', '5', '1', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '9', '3', '9', '5', '9', '7', '7', '3', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '0', '7', '4', '1', '0', '3', '5', '9', '/', '2', '1', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '8', '7', '7', '8', '2', '5', '9', '8', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '9', '6', '0', '6', '7', '7', '0', '0', '1', '/', '4', '7', '8', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0282920_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0282920Field005Chars00 ++ tail)) fragment0282920Acc00500 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0282920Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_005"
  err.flush

noncomputable def fragment0282920Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0282920Field006Value00 : SourceJson := .str (String.ofList ['2', '7', '1', '8', '4', '2', '0', '2', '1', '9', '5', '7', '6', '6', '5', '1', '4', '1', '2', '6', '2', '9', '3', '5', '5', '0', '5', '1', '5', '5', '8', '6', '4', '8', '1', '1', '3', '4', '9', '5', '2', '3', '5', '7', '1', '2', '2', '4', '0', '0', '0', '/', '4', '2', '3', '8', '5', '5', '7', '7', '8', '6', '2', '1', '6', '2', '6', '9', '2', '5', '7', '9', '7', '6', '9', '9', '2', '4', '9', '2', '5', '8', '3', '5', '1', '8', '5', '8', '3', '8', '8', '9', '8', '7', '3', '1', '0', '7', '8', '8', '6', '2', '8', '5', '0', '2', '7', '7', '2', '0', '8', '3', '5', '6', '1'])
noncomputable def fragment0282920Acc00700 : List (String × SourceJson) := (fragment0282920Field006Key00, fragment0282920Field006Value00) :: fragment0282920Acc00600
noncomputable def fragment0282920Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '7', '1', '8', '4', '2', '0', '2', '1', '9', '5', '7', '6', '6', '5', '1', '4', '1', '2', '6', '2', '9', '3', '5', '5', '0', '5', '1', '5', '5', '8', '6', '4', '8', '1', '1', '3', '4', '9', '5', '2', '3', '5', '7', '1', '2', '2', '4', '0', '0', '0', '/', '4', '2', '3', '8', '5', '5', '7', '7', '8', '6', '2', '1', '6', '2', '6', '9', '2', '5', '7', '9', '7', '6', '9', '9', '2', '4', '9', '2', '5', '8', '3', '5', '1', '8', '5', '8', '3', '8', '8', '9', '8', '7', '3', '1', '0', '7', '8', '8', '6', '2', '8', '5', '0', '2', '7', '7', '2', '0', '8', '3', '5', '6', '1', '"', ',']

theorem object_fragment0282920_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0282920Field006Chars00 ++ tail)) fragment0282920Acc00600 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0282920Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_006"
  err.flush

noncomputable def fragment0282920Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0282920Field007Value00 : SourceJson := .str (String.ofList ['3', '0', '1', '4', '8', '4', '6', '1', '9', '2', '3', '3', '2', '0', '9', '3', '0', '8', '0', '1', '6', '4', '8', '8', '5', '8', '4', '0', '2', '9', '9', '8', '6', '1', '8', '4', '6', '6', '0', '3', '1', '6', '4', '3', '6', '4', '2', '0', '6', '8', '4', '7', '5', '1', '9', '4', '6', '1', '7', '6', '8', '2', '9', '0', '6', '7', '2', '3', '7', '5', '0', '0', '9', '7', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '1', '8', '2', '5', '0', '7', '0', '9', '1', '6', '1', '7', '1', '2', '5', '7', '5', '0', '0', '2', '6', '4', '0', '0', '9', '8', '5', '3', '4', '2', '4', '4', '9', '6', '3', '1', '9', '1', '9', '7', '9', '3', '7', '3', '3', '9', '6', '4', '2', '8', '5', '2', '7', '0', '6', '1', '9', '1', '1', '6', '8', '8', '6', '4', '8', '0', '0', '4', '0', '6', '9', '2', '7', '5', '4', '1', '4', '7', '8', '1', '0', '4', '5', '4', '6', '4', '6', '4', '7', '4', '9', '7', '1', '9', '1', '5', '7', '0', '1', '0', '1'])
noncomputable def fragment0282920Acc00800 : List (String × SourceJson) := (fragment0282920Field007Key00, fragment0282920Field007Value00) :: fragment0282920Acc00700
noncomputable def fragment0282920Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '1', '4', '8', '4', '6', '1', '9', '2', '3', '3', '2', '0', '9', '3', '0', '8', '0', '1', '6', '4', '8', '8', '5', '8', '4', '0', '2', '9', '9', '8', '6', '1', '8', '4', '6', '6', '0', '3', '1', '6', '4', '3', '6', '4', '2', '0', '6', '8', '4', '7', '5', '1', '9', '4', '6', '1', '7', '6', '8', '2', '9', '0', '6', '7', '2', '3', '7', '5', '0', '0', '9', '7', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '1', '8', '2', '5', '0', '7', '0', '9', '1', '6', '1', '7', '1', '2', '5', '7', '5', '0', '0', '2', '6', '4', '0', '0', '9', '8', '5', '3', '4', '2', '4', '4', '9', '6', '3', '1', '9', '1', '9', '7', '9', '3', '7', '3', '3', '9', '6', '4', '2', '8', '5', '2', '7', '0', '6', '1', '9', '1', '1', '6', '8', '8', '6', '4', '8', '0', '0', '4', '0', '6', '9', '2', '7', '5', '4', '1', '4', '7', '8', '1', '0', '4', '5', '4', '6', '4', '6', '4', '7', '4', '9', '7', '1', '9', '1', '5', '7', '0', '1', '0', '1', '"', ',']

theorem object_fragment0282920_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0282920Field007Chars00 ++ tail)) fragment0282920Acc00700 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0282920Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_007"
  err.flush

noncomputable def fragment0282920Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0282920Field008Value00 : SourceJson := .str (String.ofList ['5', '0', '8', '1', '3', '3', '7', '7', '9', '9', '3', '5', '8', '9', '9', '4', '3'])
noncomputable def fragment0282920Acc00900 : List (String × SourceJson) := (fragment0282920Field008Key00, fragment0282920Field008Value00) :: fragment0282920Acc00800
noncomputable def fragment0282920Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '8', '1', '3', '3', '7', '7', '9', '9', '3', '5', '8', '9', '9', '4', '3', '"', ',']

theorem object_fragment0282920_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0282920Field008Chars00 ++ tail)) fragment0282920Acc00800 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0282920Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_008"
  err.flush

noncomputable def fragment0282920Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0282920Field009Value00 : SourceJson := .str (String.ofList ['1', '8', '1', '1', '9', '5', '2', '1', '7', '5', '8', '7', '6', '2', '5', '4', '8', '3'])
noncomputable def fragment0282920Acc01000 : List (String × SourceJson) := (fragment0282920Field009Key00, fragment0282920Field009Value00) :: fragment0282920Acc00900
noncomputable def fragment0282920Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '1', '1', '9', '5', '2', '1', '7', '5', '8', '7', '6', '2', '5', '4', '8', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0282920_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0282920Field009Chars00 ++ tail)) fragment0282920Acc00900 =
      .ok (.obj (fragment0282920Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0282920_object_field_009"
  err.flush

noncomputable def fragment0282920Chars : List Char := '{' :: (fragment0282920Field000Chars00 ++ fragment0282920Field001Chars00 ++ fragment0282920Field002Chars00 ++ fragment0282920Field003Chars00 ++ fragment0282920Field004Chars00 ++ fragment0282920Field005Chars00 ++ fragment0282920Field006Chars00 ++ fragment0282920Field007Chars00 ++ fragment0282920Field008Chars00 ++ fragment0282920Field009Chars00)
noncomputable def fragment0282920Value : SourceJson := .obj (fragment0282920Acc01000.reverse)

theorem value_fragment0282920 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 206) (fragment0282920Chars ++ tail) =
      .ok (fragment0282920Value, tail) := by
  have hinput : fragment0282920Chars ++ tail = '{' :: (fragment0282920Field000Chars00 ++ (fragment0282920Field001Chars00 ++ (fragment0282920Field002Chars00 ++ (fragment0282920Field003Chars00 ++ (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0282920Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 206) (fragment0282920Chars ++ tail) =
        SourceJson.value (fuel + 206) ('{' :: (fragment0282920Field000Chars00 ++ (fragment0282920Field001Chars00 ++ (fragment0282920Field002Chars00 ++ (fragment0282920Field003Chars00 ++ (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 206)) hinput
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0282920Field000Chars00 ++ (fragment0282920Field001Chars00 ++ (fragment0282920Field002Chars00 ++ (fragment0282920Field003Chars00 ++ (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))))))))))) fragment0282920Acc00000 := by rfl
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0282920Field001Chars00 ++ (fragment0282920Field002Chars00 ++ (fragment0282920Field003Chars00 ++ (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail))))))))))) fragment0282920Acc00100 := object_fragment0282920_field_000 fuel (fragment0282920Field001Chars00 ++ (fragment0282920Field002Chars00 ++ (fragment0282920Field003Chars00 ++ (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0282920Field002Chars00 ++ (fragment0282920Field003Chars00 ++ (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))))))))) fragment0282920Acc00200 := object_fragment0282920_field_001 fuel (fragment0282920Field002Chars00 ++ (fragment0282920Field003Chars00 ++ (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0282920Field003Chars00 ++ (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail))))))))) fragment0282920Acc00300 := object_fragment0282920_field_002 fuel (fragment0282920Field003Chars00 ++ (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))))))) fragment0282920Acc00400 := object_fragment0282920_field_003 fuel (fragment0282920Field004Chars00 ++ (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail))))))) fragment0282920Acc00500 := object_fragment0282920_field_004 fuel (fragment0282920Field005Chars00 ++ (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))))) fragment0282920Acc00600 := object_fragment0282920_field_005 fuel (fragment0282920Field006Chars00 ++ (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail))))) fragment0282920Acc00700 := object_fragment0282920_field_006 fuel (fragment0282920Field007Chars00 ++ (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))) fragment0282920Acc00800 := object_fragment0282920_field_007 fuel (fragment0282920Field008Chars00 ++ (fragment0282920Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0282920Field009Chars00 ++ (tail))) fragment0282920Acc00900 := object_fragment0282920_field_008 fuel (fragment0282920Field009Chars00 ++ (tail))
    _ = .ok (fragment0282920Value, tail) := object_fragment0282920_field_009 fuel (tail)

noncomputable def fragment0284468Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0284468Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0284468Field000Value00 : SourceJson := .number (String.ofList ['8', '5'])
noncomputable def fragment0284468Acc00100 : List (String × SourceJson) := (fragment0284468Field000Key00, fragment0284468Field000Value00) :: fragment0284468Acc00000
noncomputable def fragment0284468Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '5', ',']

theorem object_fragment0284468_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0284468Field000Chars00 ++ tail)) fragment0284468Acc00000 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0284468Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_000"
  err.flush

noncomputable def fragment0284468Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0284468Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0284468Acc00200 : List (String × SourceJson) := (fragment0284468Field001Key00, fragment0284468Field001Value00) :: fragment0284468Acc00100
noncomputable def fragment0284468Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0284468_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0284468Field001Chars00 ++ tail)) fragment0284468Acc00100 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0284468Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_001"
  err.flush

noncomputable def fragment0284468Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0284468Field002Value00 : SourceJson := .str (String.ofList ['9', '8', '6', '4', '6', '1', '7', '0', '3', '4', '4', '2', '3', '3', '1', '8', '3', '1', '1', '4', '3', '0', '1', '1', '9', '4', '3', '9', '8', '6', '1', '6', '2', '7', '7', '5', '2', '1', '1', '/', '2', '1', '2', '9', '5', '4', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0284468Acc00300 : List (String × SourceJson) := (fragment0284468Field002Key00, fragment0284468Field002Value00) :: fragment0284468Acc00200
noncomputable def fragment0284468Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '8', '6', '4', '6', '1', '7', '0', '3', '4', '4', '2', '3', '3', '1', '8', '3', '1', '1', '4', '3', '0', '1', '1', '9', '4', '3', '9', '8', '6', '1', '6', '2', '7', '7', '5', '2', '1', '1', '/', '2', '1', '2', '9', '5', '4', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0284468_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0284468Field002Chars00 ++ tail)) fragment0284468Acc00200 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0284468Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_002"
  err.flush

noncomputable def fragment0284468Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0284468Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0284468Acc00400 : List (String × SourceJson) := (fragment0284468Field003Key00, fragment0284468Field003Value00) :: fragment0284468Acc00300
noncomputable def fragment0284468Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0284468_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0284468Field003Chars00 ++ tail)) fragment0284468Acc00300 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0284468Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_003"
  err.flush

noncomputable def fragment0284468Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0284468Field004Value00 : SourceJson := .arr [.str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '7', '1', '7', '0', '7', '/', '1', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0284468Acc00500 : List (String × SourceJson) := (fragment0284468Field004Key00, fragment0284468Field004Value00) :: fragment0284468Acc00400
noncomputable def fragment0284468Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '7', '1', '7', '0', '7', '/', '1', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0284468_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0284468Field004Chars00 ++ tail)) fragment0284468Acc00400 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0284468Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_004"
  err.flush

noncomputable def fragment0284468Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0284468Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '6', '2', '3', '4', '6', '8', '0', '3', '0', '0', '3', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '6', '5', '5', '7', '2', '5', '2', '1', '4', '1', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '9', '2', '2', '4', '1', '7', '1', '4', '2', '1', '/', '2', '3', '9', '0', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '8', '5', '4', '3', '6', '7', '4', '1', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '1', '1', '1', '9', '5', '4', '5', '3', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '7', '2', '7', '1', '6', '4', '2', '3', '/', '5', '4', '3', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '2', '7', '2', '7', '9', '0', '9', '7', '9', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '1', '4', '5', '1', '2', '8', '6', '9', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '8', '1', '3', '4', '8', '7', '0', '7', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '1', '9', '7', '9', '3', '5', '4', '2', '1', '/', '9', '5', '6', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0284468Acc00600 : List (String × SourceJson) := (fragment0284468Field005Key00, fragment0284468Field005Value00) :: fragment0284468Acc00500
noncomputable def fragment0284468Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '2', '3', '4', '6', '8', '0', '3', '0', '0', '3', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '5', '5', '7', '2', '5', '2', '1', '4', '1', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '2', '2', '4', '1', '7', '1', '4', '2', '1', '/', '2', '3', '9', '0', '8', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '5', '4', '3', '6', '7', '4', '1', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '1', '1', '1', '9', '5', '4', '5', '3', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '7', '2', '7', '1', '6', '4', '2', '3', '/', '5', '4', '3', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '2', '7', '2', '7', '9', '0', '9', '7', '9', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '1', '4', '5', '1', '2', '8', '6', '9', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '8', '1', '3', '4', '8', '7', '0', '7', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '1', '9', '7', '9', '3', '5', '4', '2', '1', '/', '9', '5', '6', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0284468_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0284468Field005Chars00 ++ tail)) fragment0284468Acc00500 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0284468Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_005"
  err.flush

noncomputable def fragment0284468Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0284468Field006Value00 : SourceJson := .str (String.ofList ['1', '7', '6', '1', '1', '3', '0', '2', '4', '9', '6', '1', '6', '1', '7', '7', '3', '7', '2', '9', '7', '4', '5', '5', '9', '6', '4', '5', '1', '1', '0', '9', '6', '0', '3', '2', '3', '3', '9', '3', '1', '2', '5', '8', '5', '6', '4', '6', '0', '8', '0', '0', '/', '2', '8', '3', '1', '2', '2', '1', '6', '5', '7', '8', '2', '5', '7', '0', '7', '1', '4', '1', '7', '4', '3', '7', '2', '6', '1', '7', '9', '7', '1', '5', '5', '9', '2', '8', '4', '9', '4', '7', '7', '3', '1', '3', '4', '2', '5', '4', '6', '4', '2', '8', '4', '3', '9', '0', '3', '9', '0', '6', '0', '7', '9', '6', '9'])
noncomputable def fragment0284468Acc00700 : List (String × SourceJson) := (fragment0284468Field006Key00, fragment0284468Field006Value00) :: fragment0284468Acc00600
noncomputable def fragment0284468Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '6', '1', '1', '3', '0', '2', '4', '9', '6', '1', '6', '1', '7', '7', '3', '7', '2', '9', '7', '4', '5', '5', '9', '6', '4', '5', '1', '1', '0', '9', '6', '0', '3', '2', '3', '3', '9', '3', '1', '2', '5', '8', '5', '6', '4', '6', '0', '8', '0', '0', '/', '2', '8', '3', '1', '2', '2', '1', '6', '5', '7', '8', '2', '5', '7', '0', '7', '1', '4', '1', '7', '4', '3', '7', '2', '6', '1', '7', '9', '7', '1', '5', '5', '9', '2', '8', '4', '9', '4', '7', '7', '3', '1', '3', '4', '2', '5', '4', '6', '4', '2', '8', '4', '3', '9', '0', '3', '9', '0', '6', '0', '7', '9', '6', '9', '"', ',']

theorem object_fragment0284468_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0284468Field006Chars00 ++ tail)) fragment0284468Acc00600 =
      SourceJson.object (fuel + 208) (SourceJson.white tail) fragment0284468Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_006"
  err.flush

noncomputable def fragment0284468Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0284468Field007Value00 : SourceJson := .str (String.ofList ['9', '5', '7', '0', '3', '9', '4', '9', '0', '9', '6', '6', '2', '3', '2', '2', '6', '9', '4', '7', '3', '2', '3', '0', '2', '8', '0', '6', '4', '9', '5', '1', '3', '5', '0', '4', '8', '6', '9', '2', '0', '3', '9', '2', '9', '0', '6', '2', '1', '0', '4', '0', '0', '6', '9', '0', '2', '8', '2', '5', '7', '2', '2', '2', '7', '0', '6', '2', '4', '7', '9', '3', '1', '8', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '8', '8', '0', '5', '9', '4', '2', '3', '8', '3', '7', '3', '8', '6', '5', '0', '7', '2', '1', '7', '7', '8', '2', '1', '2', '4', '3', '4', '3', '5', '1', '9', '3', '6', '7', '4', '7', '1', '6', '4', '1', '6', '9', '9', '1', '1', '4', '3', '7', '5', '5', '8', '0', '9', '6', '7', '7', '0', '2', '3', '4', '3', '0', '3', '3', '0', '6', '0', '9', '8', '4', '8', '1', '3', '7', '5', '7', '1', '7', '3', '0', '4', '1', '0', '9', '1', '2', '4', '0', '3', '7', '1', '0', '9', '4', '1', '8', '2', '3', '7', '3', '4', '9', '2', '4', '7'])
noncomputable def fragment0284468Acc00800 : List (String × SourceJson) := (fragment0284468Field007Key00, fragment0284468Field007Value00) :: fragment0284468Acc00700
noncomputable def fragment0284468Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '5', '7', '0', '3', '9', '4', '9', '0', '9', '6', '6', '2', '3', '2', '2', '6', '9', '4', '7', '3', '2', '3', '0', '2', '8', '0', '6', '4', '9', '5', '1', '3', '5', '0', '4', '8', '6', '9', '2', '0', '3', '9', '2', '9', '0', '6', '2', '1', '0', '4', '0', '0', '6', '9', '0', '2', '8', '2', '5', '7', '2', '2', '2', '7', '0', '6', '2', '4', '7', '9', '3', '1', '8', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '3', '8', '8', '0', '5', '9', '4', '2', '3', '8', '3', '7', '3', '8', '6', '5', '0', '7', '2', '1', '7', '7', '8', '2', '1', '2', '4', '3', '4', '3', '5', '1', '9', '3', '6', '7', '4', '7', '1', '6', '4', '1', '6', '9', '9', '1', '1', '4', '3', '7', '5', '5', '8', '0', '9', '6', '7', '7', '0', '2', '3', '4', '3', '0', '3', '3', '0', '6', '0', '9', '8', '4', '8', '1', '3', '7', '5', '7', '1', '7', '3', '0', '4', '1', '0', '9', '1', '2', '4', '0', '3', '7', '1', '0', '9', '4', '1', '8', '2', '3', '7', '3', '4', '9', '2', '4', '7', '"', ',']

theorem object_fragment0284468_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0284468Field007Chars00 ++ tail)) fragment0284468Acc00700 =
      SourceJson.object (fuel + 207) (SourceJson.white tail) fragment0284468Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_007"
  err.flush

noncomputable def fragment0284468Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0284468Field008Value00 : SourceJson := .str (String.ofList ['4', '9', '2', '8', '3', '0', '0', '5', '8', '8', '5', '3', '5', '8', '0', '2', '1'])
noncomputable def fragment0284468Acc00900 : List (String × SourceJson) := (fragment0284468Field008Key00, fragment0284468Field008Value00) :: fragment0284468Acc00800
noncomputable def fragment0284468Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '2', '8', '3', '0', '0', '5', '8', '8', '5', '3', '5', '8', '0', '2', '1', '"', ',']

theorem object_fragment0284468_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 207) (SourceJson.white (fragment0284468Field008Chars00 ++ tail)) fragment0284468Acc00800 =
      SourceJson.object (fuel + 206) (SourceJson.white tail) fragment0284468Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_008"
  err.flush

noncomputable def fragment0284468Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0284468Field009Value00 : SourceJson := .str (String.ofList ['1', '7', '2', '7', '9', '7', '2', '9', '6', '0', '2', '3', '2', '4', '4', '0', '6', '4'])
noncomputable def fragment0284468Acc01000 : List (String × SourceJson) := (fragment0284468Field009Key00, fragment0284468Field009Value00) :: fragment0284468Acc00900
noncomputable def fragment0284468Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '2', '7', '9', '7', '2', '9', '6', '0', '2', '3', '2', '4', '4', '0', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0284468_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0284468Field009Chars00 ++ tail)) fragment0284468Acc00900 =
      .ok (.obj (fragment0284468Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0284468_object_field_009"
  err.flush

noncomputable def fragment0284468Chars : List Char := '{' :: (fragment0284468Field000Chars00 ++ fragment0284468Field001Chars00 ++ fragment0284468Field002Chars00 ++ fragment0284468Field003Chars00 ++ fragment0284468Field004Chars00 ++ fragment0284468Field005Chars00 ++ fragment0284468Field006Chars00 ++ fragment0284468Field007Chars00 ++ fragment0284468Field008Chars00 ++ fragment0284468Field009Chars00)
noncomputable def fragment0284468Value : SourceJson := .obj (fragment0284468Acc01000.reverse)

theorem value_fragment0284468 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 216) (fragment0284468Chars ++ tail) =
      .ok (fragment0284468Value, tail) := by
  have hinput : fragment0284468Chars ++ tail = '{' :: (fragment0284468Field000Chars00 ++ (fragment0284468Field001Chars00 ++ (fragment0284468Field002Chars00 ++ (fragment0284468Field003Chars00 ++ (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0284468Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 216) (fragment0284468Chars ++ tail) =
        SourceJson.value (fuel + 216) ('{' :: (fragment0284468Field000Chars00 ++ (fragment0284468Field001Chars00 ++ (fragment0284468Field002Chars00 ++ (fragment0284468Field003Chars00 ++ (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 216)) hinput
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0284468Field000Chars00 ++ (fragment0284468Field001Chars00 ++ (fragment0284468Field002Chars00 ++ (fragment0284468Field003Chars00 ++ (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))))))))))) fragment0284468Acc00000 := by rfl
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0284468Field001Chars00 ++ (fragment0284468Field002Chars00 ++ (fragment0284468Field003Chars00 ++ (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail))))))))))) fragment0284468Acc00100 := object_fragment0284468_field_000 fuel (fragment0284468Field001Chars00 ++ (fragment0284468Field002Chars00 ++ (fragment0284468Field003Chars00 ++ (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0284468Field002Chars00 ++ (fragment0284468Field003Chars00 ++ (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))))))))) fragment0284468Acc00200 := object_fragment0284468_field_001 fuel (fragment0284468Field002Chars00 ++ (fragment0284468Field003Chars00 ++ (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0284468Field003Chars00 ++ (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail))))))))) fragment0284468Acc00300 := object_fragment0284468_field_002 fuel (fragment0284468Field003Chars00 ++ (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))))))) fragment0284468Acc00400 := object_fragment0284468_field_003 fuel (fragment0284468Field004Chars00 ++ (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail))))))) fragment0284468Acc00500 := object_fragment0284468_field_004 fuel (fragment0284468Field005Chars00 ++ (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))))) fragment0284468Acc00600 := object_fragment0284468_field_005 fuel (fragment0284468Field006Chars00 ++ (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail))))) fragment0284468Acc00700 := object_fragment0284468_field_006 fuel (fragment0284468Field007Chars00 ++ (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 207) (SourceJson.white (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))) fragment0284468Acc00800 := object_fragment0284468_field_007 fuel (fragment0284468Field008Chars00 ++ (fragment0284468Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0284468Field009Chars00 ++ (tail))) fragment0284468Acc00900 := object_fragment0284468_field_008 fuel (fragment0284468Field009Chars00 ++ (tail))
    _ = .ok (fragment0284468Value, tail) := object_fragment0284468_field_009 fuel (tail)

noncomputable def fragment0286038Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0286038Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0286038Field000Value00 : SourceJson := .number (String.ofList ['8', '6'])
noncomputable def fragment0286038Acc00100 : List (String × SourceJson) := (fragment0286038Field000Key00, fragment0286038Field000Value00) :: fragment0286038Acc00000
noncomputable def fragment0286038Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '6', ',']

theorem object_fragment0286038_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 305) (SourceJson.white (fragment0286038Field000Chars00 ++ tail)) fragment0286038Acc00000 =
      SourceJson.object (fuel + 304) (SourceJson.white tail) fragment0286038Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_000"
  err.flush

noncomputable def fragment0286038Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0286038Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '4']), .number (String.ofList ['4']), .number (String.ofList ['3'])]
noncomputable def fragment0286038Acc00200 : List (String × SourceJson) := (fragment0286038Field001Key00, fragment0286038Field001Value00) :: fragment0286038Acc00100
noncomputable def fragment0286038Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0286038_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 304) (SourceJson.white (fragment0286038Field001Chars00 ++ tail)) fragment0286038Acc00100 =
      SourceJson.object (fuel + 303) (SourceJson.white tail) fragment0286038Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_001"
  err.flush

noncomputable def fragment0286038Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0286038Field002Value00 : SourceJson := .str (String.ofList ['8', '9', '8', '2', '1', '8', '4', '2', '5', '2', '9', '6', '8', '0', '4', '5', '6', '5', '5', '2', '8', '8', '7', '6', '2', '1', '4', '2', '4', '1', '8', '2', '9', '7', '3', '4', '4', '2', '5', '8', '3', '/', '1', '1', '4', '9', '0', '5', '7', '3', '7', '0', '9', '8', '1', '0', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0286038Acc00300 : List (String × SourceJson) := (fragment0286038Field002Key00, fragment0286038Field002Value00) :: fragment0286038Acc00200
noncomputable def fragment0286038Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '9', '8', '2', '1', '8', '4', '2', '5', '2', '9', '6', '8', '0', '4', '5', '6', '5', '5', '2', '8', '8', '7', '6', '2', '1', '4', '2', '4', '1', '8', '2', '9', '7', '3', '4', '4', '2', '5', '8', '3', '/', '1', '1', '4', '9', '0', '5', '7', '3', '7', '0', '9', '8', '1', '0', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0286038_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 303) (SourceJson.white (fragment0286038Field002Chars00 ++ tail)) fragment0286038Acc00200 =
      SourceJson.object (fuel + 302) (SourceJson.white tail) fragment0286038Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_002"
  err.flush

noncomputable def fragment0286038Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0286038Field003Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '1', '7', '0', '3', '/', '7', '2', '2', '4', '0', '0', '0', '0', '0'])
noncomputable def fragment0286038Acc00400 : List (String × SourceJson) := (fragment0286038Field003Key00, fragment0286038Field003Value00) :: fragment0286038Acc00300
noncomputable def fragment0286038Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '0', '7', '1', '7', '0', '3', '/', '7', '2', '2', '4', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0286038_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 302) (SourceJson.white (fragment0286038Field003Chars00 ++ tail)) fragment0286038Acc00300 =
      SourceJson.object (fuel + 301) (SourceJson.white tail) fragment0286038Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_003"
  err.flush

noncomputable def fragment0286038Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0286038Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['2', '5', '/', '6', '8', '8']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0286038Acc00500 : List (String × SourceJson) := (fragment0286038Field004Key00, fragment0286038Field004Value00) :: fragment0286038Acc00400
noncomputable def fragment0286038Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '/', '6', '8', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0286038_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 301) (SourceJson.white (fragment0286038Field004Chars00 ++ tail)) fragment0286038Acc00400 =
      SourceJson.object (fuel + 300) (SourceJson.white tail) fragment0286038Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_004"
  err.flush

noncomputable def fragment0286038Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0286038Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '1', '7', '6', '4', '4', '4', '1', '9', '4', '3', '0', '5', '3', '4', '0', '0', '9', '7', '/', '7', '1', '5', '8', '2', '3', '6', '9', '9', '3', '6', '1', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '9', '9', '5', '6', '7', '3', '7', '4', '5', '9', '7', '6', '8', '1', '8', '3', '5', '7', '/', '1', '7', '8', '9', '5', '5', '9', '2', '4', '8', '4', '0', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '0', '8', '1', '2', '4', '2', '1', '5', '1', '7', '1', '/', '1', '6', '6', '9', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '9', '3', '4', '2', '4', '8', '1', '5', '1', '5', '1', '/', '3', '7', '1', '0', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '1', '9', '7', '8', '0', '5', '4', '4', '2', '3', '7', '/', '1', '1', '1', '3', '2', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '5', '1', '3', '7', '3', '7', '7', '4', '9', '3', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '3', '7', '4', '9', '2', '5', '7', '9', '8', '9', '1', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '1', '5', '7', '3', '2', '6', '8', '1', '9', '0', '3', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '9', '6', '5', '8', '0', '8', '0', '2', '6', '2', '5', '5', '9', '3', '3', '7', '3', '/', '2', '5', '5', '6', '5', '1', '3', '2', '1', '2', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '7', '8', '6', '8', '0', '1', '2', '0', '9', '4', '3', '1', '1', '8', '7', '9', '/', '1', '7', '8', '9', '5', '5', '9', '2', '4', '8', '4', '0', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0286038Acc00600 : List (String × SourceJson) := (fragment0286038Field005Key00, fragment0286038Field005Value00) :: fragment0286038Acc00500
noncomputable def fragment0286038Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '7', '6', '4', '4', '4', '1', '9', '4', '3', '0', '5', '3', '4', '0', '0', '9', '7', '/', '7', '1', '5', '8', '2', '3', '6', '9', '9', '3', '6', '1', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '7', '9', '9', '5', '6', '7', '3', '7', '4', '5', '9', '7', '6', '8', '1', '8', '3', '5', '7', '/', '1', '7', '8', '9', '5', '5', '9', '2', '4', '8', '4', '0', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '8', '1', '2', '4', '2', '1', '5', '1', '7', '1', '/', '1', '6', '6', '9', '8', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '9', '3', '4', '2', '4', '8', '1', '5', '1', '5', '1', '/', '3', '7', '1', '0', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '1', '9', '7', '8', '0', '5', '4', '4', '2', '3', '7', '/', '1', '1', '1', '3', '2', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '5', '1', '3', '7', '3', '7', '7', '4', '9', '3', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '3', '7', '4', '9', '2', '5', '7', '9', '8', '9', '1', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '1', '5', '7', '3', '2', '6', '8', '1', '9', '0', '3', '/', '3', '3', '3', '9', '6', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '9', '6', '5', '8', '0', '8', '0', '2', '6', '2', '5', '5', '9', '3', '3', '7', '3', '/', '2', '5', '5', '6', '5', '1', '3', '2', '1', '2', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '7', '8', '6', '8', '0', '1', '2', '0', '9', '4', '3', '1', '1', '8', '7', '9', '/', '1', '7', '8', '9', '5', '5', '9', '2', '4', '8', '4', '0', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0286038_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 300) (SourceJson.white (fragment0286038Field005Chars00 ++ tail)) fragment0286038Acc00500 =
      SourceJson.object (fuel + 299) (SourceJson.white tail) fragment0286038Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_005"
  err.flush

noncomputable def fragment0286038Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0286038Field006Value00 : SourceJson := .str (String.ofList ['1', '7', '6', '3', '4', '4', '9', '1', '1', '1', '7', '1', '6', '7', '5', '0', '7', '7', '0', '7', '1', '6', '3', '0', '3', '8', '8', '1', '4', '4', '1', '1', '5', '3', '0', '5', '6', '5', '3', '7', '2', '7', '8', '2', '3', '6', '8', '6', '9', '2', '6', '3', '3', '9', '/', '7', '0', '4', '1', '1', '4', '3', '1', '8', '3', '7', '8', '8', '6', '4', '0', '5', '1', '4', '3', '5', '0', '3', '5', '3', '9', '9', '4', '2', '2', '4', '1', '2', '9', '7', '8', '7', '5', '7', '1', '6', '8', '0', '7', '4', '4', '7', '1', '3', '5', '6', '7', '4', '2', '6', '6', '4', '2', '9', '5', '3', '2', '1', '6', '0', '0'])
noncomputable def fragment0286038Acc00700 : List (String × SourceJson) := (fragment0286038Field006Key00, fragment0286038Field006Value00) :: fragment0286038Acc00600
noncomputable def fragment0286038Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '6', '3', '4', '4', '9', '1', '1', '1', '7', '1', '6', '7', '5', '0', '7', '7', '0', '7', '1', '6', '3', '0', '3', '8', '8', '1', '4', '4', '1', '1', '5', '3', '0', '5', '6', '5', '3', '7', '2', '7', '8', '2', '3', '6', '8', '6', '9', '2', '6', '3', '3', '9', '/', '7', '0', '4', '1', '1', '4', '3', '1', '8', '3', '7', '8', '8', '6', '4', '0', '5', '1', '4', '3', '5', '0', '3', '5', '3', '9', '9', '4', '2', '2', '4', '1', '2', '9', '7', '8', '7', '5', '7', '1', '6', '8', '0', '7', '4', '4', '7', '1', '3', '5', '6', '7', '4', '2', '6', '6', '4', '2', '9', '5', '3', '2', '1', '6', '0', '0', '"', ',']

theorem object_fragment0286038_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 299) (SourceJson.white (fragment0286038Field006Chars00 ++ tail)) fragment0286038Acc00600 =
      SourceJson.object (fuel + 298) (SourceJson.white tail) fragment0286038Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_006"
  err.flush

noncomputable def fragment0286038Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0286038Field007Value00 : SourceJson := .str (String.ofList ['6', '3', '4', '9', '8', '9', '5', '2', '9', '0', '2', '5', '7', '4', '1', '2', '7', '8', '9', '2', '9', '2', '2', '3', '4', '6', '9', '0', '1', '5', '1', '6', '6', '4', '1', '8', '1', '0', '0', '8', '7', '3', '6', '9', '6', '9', '1', '0', '2', '1', '9', '5', '8', '1', '8', '3', '4', '7', '8', '6', '1', '1', '7', '3', '1', '8', '3', '5', '3', '4', '7', '4', '3', '1', '7', '3', '4', '5', '0', '0', '8', '0', '5', '1', '7', '1', '1', '9', '8', '5', '4', '1', '8', '3', '5', '6', '7', '0', '1', '2', '5', '8', '7', '1', '2', '1', '7', '6', '2', '1', '0', '9', '0', '6', '8', '7', '0', '7', '1', '0', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '7', '8', '1', '2', '9', '8', '7', '4', '2', '1', '5', '9', '2', '7', '8', '9', '4', '3', '0', '4', '4', '8', '3', '7', '1', '0', '8', '0', '5', '8', '1', '1', '6', '0', '6', '7', '5', '3', '3', '3', '9', '1', '5', '5', '7', '9', '2', '6', '5', '3', '3', '0', '2', '6', '1', '2', '3', '1', '8', '1', '9', '4', '4', '0', '1', '3', '0', '9', '3', '0', '5', '1', '6', '0', '8', '1', '5', '7', '7', '4', '6', '0', '8', '9', '2', '8', '8', '6', '3', '2', '5', '4', '3', '8', '6', '6', '4', '9', '0', '1', '7', '2', '0', '5', '6', '8', '4', '3', '1', '2', '9', '0', '8', '7', '3', '9', '6', '7', '3', '2', '4', '0', '0', '3', '0', '3', '0', '4', '9', '4', '2', '1', '5', '2', '0', '3', '7', '3', '8', '7', '5', '1', '6', '9', '2', '3', '2', '4', '6', '5', '8', '9'])
noncomputable def fragment0286038Acc00800 : List (String × SourceJson) := (fragment0286038Field007Key00, fragment0286038Field007Value00) :: fragment0286038Acc00700
noncomputable def fragment0286038Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '3', '4', '9', '8', '9', '5', '2', '9', '0', '2', '5', '7', '4', '1', '2', '7', '8', '9', '2', '9', '2', '2', '3', '4', '6', '9', '0', '1', '5', '1', '6', '6', '4', '1', '8', '1', '0', '0', '8', '7', '3', '6', '9', '6', '9', '1', '0', '2', '1', '9', '5', '8', '1', '8', '3', '4', '7', '8', '6', '1', '1', '7', '3', '1', '8', '3', '5', '3', '4', '7', '4', '3', '1', '7', '3', '4', '5', '0', '0', '8', '0', '5', '1', '7', '1', '1', '9', '8', '5', '4', '1', '8', '3', '5', '6', '7', '0', '1', '2', '5', '8', '7', '1', '2', '1', '7', '6', '2', '1', '0', '9', '0', '6', '8', '7', '0', '7', '1', '0', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '7', '8', '1', '2', '9', '8', '7', '4', '2', '1', '5', '9', '2', '7', '8', '9', '4', '3', '0', '4', '4', '8', '3', '7', '1', '0', '8', '0', '5', '8', '1', '1', '6', '0', '6', '7', '5', '3', '3', '3', '9', '1', '5', '5', '7', '9', '2', '6', '5', '3', '3', '0', '2', '6', '1', '2', '3', '1', '8', '1', '9', '4', '4', '0', '1', '3', '0', '9', '3', '0', '5', '1', '6', '0', '8', '1', '5', '7', '7', '4', '6', '0', '8', '9', '2', '8', '8', '6', '3', '2', '5', '4', '3', '8', '6', '6', '4', '9', '0', '1', '7', '2', '0', '5', '6', '8', '4', '3', '1', '2', '9', '0', '8', '7', '3', '9', '6', '7', '3', '2', '4', '0', '0', '3', '0', '3', '0', '4', '9', '4', '2', '1', '5', '2', '0', '3', '7', '3', '8', '7', '5', '1', '6', '9', '2', '3', '2', '4', '6', '5', '8', '9', '"', ',']

theorem object_fragment0286038_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 298) (SourceJson.white (fragment0286038Field007Chars00 ++ tail)) fragment0286038Acc00700 =
      SourceJson.object (fuel + 297) (SourceJson.white tail) fragment0286038Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_007"
  err.flush

noncomputable def fragment0286038Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0286038Field008Value00 : SourceJson := .str (String.ofList ['1', '9', '8', '4', '2', '6', '3', '4', '8', '0', '5', '4', '3', '9', '8', '1', '8'])
noncomputable def fragment0286038Acc00900 : List (String × SourceJson) := (fragment0286038Field008Key00, fragment0286038Field008Value00) :: fragment0286038Acc00800
noncomputable def fragment0286038Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '8', '4', '2', '6', '3', '4', '8', '0', '5', '4', '3', '9', '8', '1', '8', '"', ',']

theorem object_fragment0286038_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 297) (SourceJson.white (fragment0286038Field008Chars00 ++ tail)) fragment0286038Acc00800 =
      SourceJson.object (fuel + 296) (SourceJson.white tail) fragment0286038Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_008"
  err.flush

noncomputable def fragment0286038Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0286038Field009Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '9', '1', '1', '3', '0', '9', '3', '3', '7', '1', '0', '6', '6', '4'])
noncomputable def fragment0286038Acc01000 : List (String × SourceJson) := (fragment0286038Field009Key00, fragment0286038Field009Value00) :: fragment0286038Acc00900
noncomputable def fragment0286038Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '7', '2', '9', '1', '1', '3', '0', '9', '3', '3', '7', '1', '0', '6', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0286038_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 296) (SourceJson.white (fragment0286038Field009Chars00 ++ tail)) fragment0286038Acc00900 =
      .ok (.obj (fragment0286038Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0286038_object_field_009"
  err.flush

noncomputable def fragment0286038Chars : List Char := '{' :: (fragment0286038Field000Chars00 ++ fragment0286038Field001Chars00 ++ fragment0286038Field002Chars00 ++ fragment0286038Field003Chars00 ++ fragment0286038Field004Chars00 ++ fragment0286038Field005Chars00 ++ fragment0286038Field006Chars00 ++ fragment0286038Field007Chars00 ++ fragment0286038Field008Chars00 ++ fragment0286038Field009Chars00)
noncomputable def fragment0286038Value : SourceJson := .obj (fragment0286038Acc01000.reverse)

theorem value_fragment0286038 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 306) (fragment0286038Chars ++ tail) =
      .ok (fragment0286038Value, tail) := by
  have hinput : fragment0286038Chars ++ tail = '{' :: (fragment0286038Field000Chars00 ++ (fragment0286038Field001Chars00 ++ (fragment0286038Field002Chars00 ++ (fragment0286038Field003Chars00 ++ (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0286038Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 306) (fragment0286038Chars ++ tail) =
        SourceJson.value (fuel + 306) ('{' :: (fragment0286038Field000Chars00 ++ (fragment0286038Field001Chars00 ++ (fragment0286038Field002Chars00 ++ (fragment0286038Field003Chars00 ++ (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 306)) hinput
    _ = SourceJson.object (fuel + 305) (SourceJson.white (fragment0286038Field000Chars00 ++ (fragment0286038Field001Chars00 ++ (fragment0286038Field002Chars00 ++ (fragment0286038Field003Chars00 ++ (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))))))))))) fragment0286038Acc00000 := by rfl
    _ = SourceJson.object (fuel + 304) (SourceJson.white (fragment0286038Field001Chars00 ++ (fragment0286038Field002Chars00 ++ (fragment0286038Field003Chars00 ++ (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail))))))))))) fragment0286038Acc00100 := object_fragment0286038_field_000 fuel (fragment0286038Field001Chars00 ++ (fragment0286038Field002Chars00 ++ (fragment0286038Field003Chars00 ++ (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 303) (SourceJson.white (fragment0286038Field002Chars00 ++ (fragment0286038Field003Chars00 ++ (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))))))))) fragment0286038Acc00200 := object_fragment0286038_field_001 fuel (fragment0286038Field002Chars00 ++ (fragment0286038Field003Chars00 ++ (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 302) (SourceJson.white (fragment0286038Field003Chars00 ++ (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail))))))))) fragment0286038Acc00300 := object_fragment0286038_field_002 fuel (fragment0286038Field003Chars00 ++ (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 301) (SourceJson.white (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))))))) fragment0286038Acc00400 := object_fragment0286038_field_003 fuel (fragment0286038Field004Chars00 ++ (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 300) (SourceJson.white (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail))))))) fragment0286038Acc00500 := object_fragment0286038_field_004 fuel (fragment0286038Field005Chars00 ++ (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 299) (SourceJson.white (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))))) fragment0286038Acc00600 := object_fragment0286038_field_005 fuel (fragment0286038Field006Chars00 ++ (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 298) (SourceJson.white (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail))))) fragment0286038Acc00700 := object_fragment0286038_field_006 fuel (fragment0286038Field007Chars00 ++ (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 297) (SourceJson.white (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))) fragment0286038Acc00800 := object_fragment0286038_field_007 fuel (fragment0286038Field008Chars00 ++ (fragment0286038Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 296) (SourceJson.white (fragment0286038Field009Chars00 ++ (tail))) fragment0286038Acc00900 := object_fragment0286038_field_008 fuel (fragment0286038Field009Chars00 ++ (tail))
    _ = .ok (fragment0286038Value, tail) := object_fragment0286038_field_009 fuel (tail)

noncomputable def fragment0287777Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0287777Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0287777Field000Value00 : SourceJson := .number (String.ofList ['8', '7'])
noncomputable def fragment0287777Acc00100 : List (String × SourceJson) := (fragment0287777Field000Key00, fragment0287777Field000Value00) :: fragment0287777Acc00000
noncomputable def fragment0287777Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', '7', ',']

theorem object_fragment0287777_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 422) (SourceJson.white (fragment0287777Field000Chars00 ++ tail)) fragment0287777Acc00000 =
      SourceJson.object (fuel + 421) (SourceJson.white tail) fragment0287777Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_000"
  err.flush

noncomputable def fragment0287777Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0287777Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '4']), .number (String.ofList ['7']), .number (String.ofList ['3'])]
noncomputable def fragment0287777Acc00200 : List (String × SourceJson) := (fragment0287777Field001Key00, fragment0287777Field001Value00) :: fragment0287777Acc00100
noncomputable def fragment0287777Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0287777_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0287777Field001Chars00 ++ tail)) fragment0287777Acc00100 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0287777Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_001"
  err.flush

noncomputable def fragment0287777Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0287777Field002Value00 : SourceJson := .str (String.ofList ['7', '4', '6', '8', '3', '3', '0', '5', '3', '6', '9', '6', '5', '6', '4', '8', '0', '5', '7', '4', '4', '3', '6', '5', '2', '9', '3', '8', '8', '1', '4', '7', '6', '4', '4', '4', '9', '3', '4', '9', '/', '1', '0', '1', '7', '9', '9', '1', '0', '2', '6', '3', '3', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0287777Acc00300 : List (String × SourceJson) := (fragment0287777Field002Key00, fragment0287777Field002Value00) :: fragment0287777Acc00200
noncomputable def fragment0287777Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '4', '6', '8', '3', '3', '0', '5', '3', '6', '9', '6', '5', '6', '4', '8', '0', '5', '7', '4', '4', '3', '6', '5', '2', '9', '3', '8', '8', '1', '4', '7', '6', '4', '4', '4', '9', '3', '4', '9', '/', '1', '0', '1', '7', '9', '9', '1', '0', '2', '6', '3', '3', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0287777_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0287777Field002Chars00 ++ tail)) fragment0287777Acc00200 =
      SourceJson.object (fuel + 419) (SourceJson.white tail) fragment0287777Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_002"
  err.flush

noncomputable def fragment0287777Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0287777Field003Value00 : SourceJson := .str (String.ofList ['4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0287777Acc00400 : List (String × SourceJson) := (fragment0287777Field003Key00, fragment0287777Field003Value00) :: fragment0287777Acc00300
noncomputable def fragment0287777Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0287777_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 419) (SourceJson.white (fragment0287777Field003Chars00 ++ tail)) fragment0287777Acc00300 =
      SourceJson.object (fuel + 418) (SourceJson.white tail) fragment0287777Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_003"
  err.flush

noncomputable def fragment0287777Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0287777Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['5', '9', '2', '1', '7', '0', '3', '/', '1', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0287777Acc00500 : List (String × SourceJson) := (fragment0287777Field004Key00, fragment0287777Field004Value00) :: fragment0287777Acc00400
noncomputable def fragment0287777Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '2', '1', '7', '0', '3', '/', '1', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0287777_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 418) (SourceJson.white (fragment0287777Field004Chars00 ++ tail)) fragment0287777Acc00400 =
      SourceJson.object (fuel + 417) (SourceJson.white tail) fragment0287777Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_004"
  err.flush

noncomputable def fragment0287777Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0287777Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '2', '4', '6', '8', '3', '1', '7', '2', '7', '8', '3', '3', '1', '9', '2', '1', '2', '3', '7', '0', '7', '/', '2', '5', '8', '6', '7', '6', '2', '5', '5', '4', '0', '4', '9', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '7', '4', '0', '9', '8', '2', '7', '0', '2', '6', '7', '5', '3', '8', '0', '5', '2', '8', '1', '/', '2', '5', '8', '6', '7', '6', '2', '5', '5', '4', '0', '4', '9', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '4', '8', '7', '4', '4', '9', '3', '9', '6', '5', '7', '0', '5', '2', '8', '9', '3', '5', '3', '3', '/', '4', '5', '2', '6', '8', '3', '4', '4', '6', '9', '5', '8', '6', '5', '0', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '7', '2', '3', '5', '9', '2', '3', '0', '9', '0', '2', '6', '2', '9', '8', '6', '7', '8', '1', '7', '/', '6', '0', '3', '5', '7', '7', '9', '2', '9', '2', '7', '8', '2', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '1', '9', '4', '1', '3', '2', '4', '1', '9', '6', '6', '7', '0', '7', '0', '5', '8', '7', '/', '8', '0', '4', '7', '7', '0', '5', '7', '2', '3', '7', '0', '9', '3', '4', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '6', '3', '9', '7', '4', '5', '8', '5', '4', '9', '2', '5', '4', '6', '0', '8', '7', '0', '6', '9', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '2', '4', '5', '9', '4', '7', '1', '9', '2', '5', '6', '0', '5', '6', '0', '1', '3', '6', '3', '1', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '5', '6', '6', '8', '0', '3', '0', '4', '6', '7', '7', '2', '0', '3', '8', '7', '5', '8', '7', '/', '7', '2', '4', '2', '9', '3', '5', '1', '5', '1', '3', '3', '8', '4', '0', '9', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '4', '1', '4', '1', '7', '5', '1', '8', '0', '3', '0', '4', '6', '3', '7', '6', '8', '4', '1', '/', '2', '5', '8', '6', '7', '6', '2', '5', '5', '4', '0', '4', '9', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '3', '7', '6', '5', '3', '7', '1', '6', '2', '6', '8', '2', '1', '7', '7', '6', '1', '7', '1', '/', '2', '5', '8', '6', '7', '6', '2', '5', '5', '4', '0', '4', '9', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0287777Acc00600 : List (String × SourceJson) := (fragment0287777Field005Key00, fragment0287777Field005Value00) :: fragment0287777Acc00500
noncomputable def fragment0287777Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '6', '8', '3', '1', '7', '2', '7', '8', '3', '3', '1', '9', '2', '1', '2', '3', '7', '0', '7', '/', '2', '5', '8', '6', '7', '6', '2', '5', '5', '4', '0', '4', '9', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '7', '4', '0', '9', '8', '2', '7', '0', '2', '6', '7', '5', '3', '8', '0', '5', '2', '8', '1', '/', '2', '5', '8', '6', '7', '6', '2', '5', '5', '4', '0', '4', '9', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '4', '8', '7', '4', '4', '9', '3', '9', '6', '5', '7', '0', '5', '2', '8', '9', '3', '5', '3', '3', '/', '4', '5', '2', '6', '8', '3', '4', '4', '6', '9', '5', '8', '6', '5', '0', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '7', '2', '3', '5', '9', '2', '3', '0', '9', '0', '2', '6', '2', '9', '8', '6', '7', '8', '1', '7', '/', '6', '0', '3', '5', '7', '7', '9', '2', '9', '2', '7', '8', '2', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '1', '9', '4', '1', '3', '2', '4', '1', '9', '6', '6', '7', '0', '7', '0', '5', '8', '7', '/', '8', '0', '4', '7', '7', '0', '5', '7', '2', '3', '7', '0', '9', '3', '4', '4', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '6', '3', '9', '7', '4', '5', '8', '5', '4', '9', '2', '5', '4', '6', '0', '8', '7', '0', '6', '9', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '2', '4', '5', '9', '4', '7', '1', '9', '2', '5', '6', '0', '5', '6', '0', '1', '3', '6', '3', '1', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '5', '6', '6', '8', '0', '3', '0', '4', '6', '7', '7', '2', '0', '3', '8', '7', '5', '8', '7', '/', '7', '2', '4', '2', '9', '3', '5', '1', '5', '1', '3', '3', '8', '4', '0', '9', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '4', '1', '4', '1', '7', '5', '1', '8', '0', '3', '0', '4', '6', '3', '7', '6', '8', '4', '1', '/', '2', '5', '8', '6', '7', '6', '2', '5', '5', '4', '0', '4', '9', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '3', '7', '6', '5', '3', '7', '1', '6', '2', '6', '8', '2', '1', '7', '7', '6', '1', '7', '1', '/', '2', '5', '8', '6', '7', '6', '2', '5', '5', '4', '0', '4', '9', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0287777_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 417) (SourceJson.white (fragment0287777Field005Chars00 ++ tail)) fragment0287777Acc00500 =
      SourceJson.object (fuel + 416) (SourceJson.white tail) fragment0287777Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_005"
  err.flush

noncomputable def fragment0287777Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0287777Field006Value00 : SourceJson := .str (String.ofList ['4', '6', '3', '6', '2', '0', '9', '4', '5', '8', '5', '4', '8', '2', '6', '7', '3', '7', '0', '7', '9', '5', '6', '6', '3', '0', '0', '5', '3', '1', '8', '9', '4', '2', '1', '7', '8', '0', '9', '5', '3', '2', '8', '1', '5', '7', '3', '1', '8', '2', '1', '1', '4', '0', '1', '8', '7', '5', '/', '1', '9', '1', '5', '5', '8', '1', '4', '3', '5', '0', '2', '5', '8', '6', '0', '4', '6', '9', '6', '2', '3', '0', '6', '7', '5', '4', '6', '3', '2', '6', '6', '2', '1', '9', '1', '0', '3', '1', '4', '1', '0', '0', '7', '0', '5', '9', '5', '2', '5', '4', '6', '9', '5', '0', '5', '0', '6', '8', '8', '8', '1', '1', '5', '6', '3', '4', '9', '9', '5', '2'])
noncomputable def fragment0287777Acc00700 : List (String × SourceJson) := (fragment0287777Field006Key00, fragment0287777Field006Value00) :: fragment0287777Acc00600
noncomputable def fragment0287777Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '6', '3', '6', '2', '0', '9', '4', '5', '8', '5', '4', '8', '2', '6', '7', '3', '7', '0', '7', '9', '5', '6', '6', '3', '0', '0', '5', '3', '1', '8', '9', '4', '2', '1', '7', '8', '0', '9', '5', '3', '2', '8', '1', '5', '7', '3', '1', '8', '2', '1', '1', '4', '0', '1', '8', '7', '5', '/', '1', '9', '1', '5', '5', '8', '1', '4', '3', '5', '0', '2', '5', '8', '6', '0', '4', '6', '9', '6', '2', '3', '0', '6', '7', '5', '4', '6', '3', '2', '6', '6', '2', '1', '9', '1', '0', '3', '1', '4', '1', '0', '0', '7', '0', '5', '9', '5', '2', '5', '4', '6', '9', '5', '0', '5', '0', '6', '8', '8', '8', '1', '1', '5', '6', '3', '4', '9', '9', '5', '2', '"', ',']

theorem object_fragment0287777_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 416) (SourceJson.white (fragment0287777Field006Chars00 ++ tail)) fragment0287777Acc00600 =
      SourceJson.object (fuel + 415) (SourceJson.white tail) fragment0287777Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_006"
  err.flush

noncomputable def fragment0287777Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0287777Field007Value00 : SourceJson := .str (String.ofList ['7', '0', '9', '2', '9', '7', '3', '0', '7', '6', '1', '6', '9', '6', '6', '0', '8', '3', '9', '9', '7', '8', '9', '0', '1', '2', '9', '2', '8', '8', '1', '1', '7', '2', '0', '0', '0', '6', '4', '9', '0', '9', '5', '8', '0', '4', '5', '1', '3', '2', '7', '0', '4', '1', '7', '1', '3', '8', '8', '7', '0', '3', '2', '8', '9', '1', '5', '9', '3', '4', '5', '6', '3', '7', '9', '1', '9', '7', '6', '2', '4', '5', '6', '9', '4', '3', '0', '1', '2', '2', '7', '9', '1', '2', '2', '2', '3', '2', '2', '3', '1', '3', '7', '2', '1', '3', '4', '9', '7', '5', '7', '5', '4', '1', '9', '5', '5', '7', '2', '7', '5', '7', '0', '5', '8', '3', '4', '1', '0', '9', '4', '8', '9', '2', '8', '5', '8', '1', '8', '4', '5', '1', '0', '2', '6', '9', '2', '7', '2', '5', '0', '6', '1', '7', '0', '4', '8', '4', '1', '9', '7', '0', '4', '4', '9', '8', '5', '5', '7', '2', '7', '1', '3', '4', '4', '2', '9', '1', '0', '9', '9', '7', '0', '5', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '1', '4', '2', '5', '6', '9', '9', '0', '1', '0', '0', '9', '9', '8', '4', '8', '5', '5', '2', '5', '8', '8', '6', '3', '9', '0', '0', '6', '9', '0', '8', '5', '2', '1', '4', '9', '9', '7', '4', '3', '7', '9', '8', '5', '5', '2', '4', '9', '3', '6', '6', '9', '8', '5', '2', '4', '2', '6', '0', '6', '2', '6', '1', '7', '7', '6', '6', '9', '7', '5', '4', '8', '4', '6', '2', '0', '0', '1', '2', '2', '1', '7', '7', '7', '2', '7', '4', '9', '8', '1', '6', '8', '2', '6', '4', '1', '9', '7', '8', '3', '1', '7', '8', '7', '6', '7', '3', '8', '3', '6', '8', '9', '5', '4', '1', '5', '2', '0', '3', '7', '7', '7', '6', '2', '5', '5', '1', '0', '0', '1', '2', '2', '5', '3', '3', '5', '3', '3', '1', '7', '0', '0', '5', '7', '7', '8', '7', '7', '7', '5', '7', '3', '2', '0', '6', '5', '9', '4', '7', '8', '9', '5', '3', '1', '0', '1', '1', '6', '2', '1', '3', '3', '0', '2', '7', '4', '2', '0', '4', '3', '7', '7', '8', '1', '7', '2', '1', '0', '4', '7', '9', '6', '3', '4', '0', '7', '9', '2', '6', '5', '8', '0', '9', '9', '2', '2', '0', '4', '1'])
noncomputable def fragment0287777Acc00800 : List (String × SourceJson) := (fragment0287777Field007Key00, fragment0287777Field007Value00) :: fragment0287777Acc00700
noncomputable def fragment0287777Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '0', '9', '2', '9', '7', '3', '0', '7', '6', '1', '6', '9', '6', '6', '0', '8', '3', '9', '9', '7', '8', '9', '0', '1', '2', '9', '2', '8', '8', '1', '1', '7', '2', '0', '0', '0', '6', '4', '9', '0', '9', '5', '8', '0', '4', '5', '1', '3', '2', '7', '0', '4', '1', '7', '1', '3', '8', '8', '7', '0', '3', '2', '8', '9', '1', '5', '9', '3', '4', '5', '6', '3', '7', '9', '1', '9', '7', '6', '2', '4', '5', '6', '9', '4', '3', '0', '1', '2', '2', '7', '9', '1', '2', '2', '2', '3', '2', '2', '3', '1', '3', '7', '2', '1', '3', '4', '9', '7', '5', '7', '5', '4', '1', '9', '5', '5', '7', '2', '7', '5', '7', '0', '5', '8', '3', '4', '1', '0', '9', '4', '8', '9', '2', '8', '5', '8', '1', '8', '4', '5', '1', '0', '2', '6', '9', '2', '7', '2', '5', '0', '6', '1', '7', '0', '4', '8', '4', '1', '9', '7', '0', '4', '4', '9', '8', '5', '5', '7', '2', '7', '1', '3', '4', '4', '2', '9', '1', '0', '9', '9', '7', '0', '5', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '1', '4', '2', '5', '6', '9', '9', '0', '1', '0', '0', '9', '9', '8', '4', '8', '5', '5', '2', '5', '8', '8', '6', '3', '9', '0', '0', '6', '9', '0', '8', '5', '2', '1', '4', '9', '9', '7', '4', '3', '7', '9', '8', '5', '5', '2', '4', '9', '3', '6', '6', '9', '8', '5', '2', '4', '2', '6', '0', '6', '2', '6', '1', '7', '7', '6', '6', '9', '7', '5', '4', '8', '4', '6', '2', '0', '0', '1', '2', '2', '1', '7', '7', '7', '2', '7', '4', '9', '8', '1', '6', '8', '2', '6', '4', '1', '9', '7', '8', '3', '1', '7', '8', '7', '6', '7', '3', '8', '3', '6', '8', '9', '5', '4', '1', '5', '2', '0', '3', '7', '7', '7', '6', '2', '5', '5', '1', '0', '0', '1', '2', '2', '5', '3', '3', '5', '3', '3', '1', '7', '0', '0', '5', '7', '7', '8', '7', '7', '7', '5', '7', '3', '2', '0', '6', '5', '9', '4', '7', '8', '9', '5', '3', '1', '0', '1', '1', '6', '2', '1', '3', '3', '0', '2', '7', '4', '2', '0', '4', '3', '7', '7', '8', '1', '7', '2', '1', '0', '4', '7', '9', '6', '3', '4', '0', '7', '9', '2', '6', '5', '8', '0', '9', '9', '2', '2', '0', '4', '1', '"', ',']

theorem object_fragment0287777_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 415) (SourceJson.white (fragment0287777Field007Chars00 ++ tail)) fragment0287777Acc00700 =
      SourceJson.object (fuel + 414) (SourceJson.white tail) fragment0287777Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_007"
  err.flush

noncomputable def fragment0287777Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0287777Field008Value00 : SourceJson := .str (String.ofList ['1', '9', '1', '7', '5', '2', '9', '3', '1', '8', '8', '5', '7', '0', '3', '2', '9'])
noncomputable def fragment0287777Acc00900 : List (String × SourceJson) := (fragment0287777Field008Key00, fragment0287777Field008Value00) :: fragment0287777Acc00800
noncomputable def fragment0287777Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '1', '7', '5', '2', '9', '3', '1', '8', '8', '5', '7', '0', '3', '2', '9', '"', ',']

theorem object_fragment0287777_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 414) (SourceJson.white (fragment0287777Field008Chars00 ++ tail)) fragment0287777Acc00800 =
      SourceJson.object (fuel + 413) (SourceJson.white tail) fragment0287777Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_008"
  err.flush

noncomputable def fragment0287777Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0287777Field009Value00 : SourceJson := .str (String.ofList ['5', '2', '4', '5', '0', '0', '4', '1', '4', '8', '2', '7', '9', '0', '1', '1', '5'])
noncomputable def fragment0287777Acc01000 : List (String × SourceJson) := (fragment0287777Field009Key00, fragment0287777Field009Value00) :: fragment0287777Acc00900
noncomputable def fragment0287777Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '2', '4', '5', '0', '0', '4', '1', '4', '8', '2', '7', '9', '0', '1', '1', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0287777_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 413) (SourceJson.white (fragment0287777Field009Chars00 ++ tail)) fragment0287777Acc00900 =
      .ok (.obj (fragment0287777Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0287777_object_field_009"
  err.flush

noncomputable def fragment0287777Chars : List Char := '{' :: (fragment0287777Field000Chars00 ++ fragment0287777Field001Chars00 ++ fragment0287777Field002Chars00 ++ fragment0287777Field003Chars00 ++ fragment0287777Field004Chars00 ++ fragment0287777Field005Chars00 ++ fragment0287777Field006Chars00 ++ fragment0287777Field007Chars00 ++ fragment0287777Field008Chars00 ++ fragment0287777Field009Chars00)
noncomputable def fragment0287777Value : SourceJson := .obj (fragment0287777Acc01000.reverse)

theorem value_fragment0287777 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 423) (fragment0287777Chars ++ tail) =
      .ok (fragment0287777Value, tail) := by
  have hinput : fragment0287777Chars ++ tail = '{' :: (fragment0287777Field000Chars00 ++ (fragment0287777Field001Chars00 ++ (fragment0287777Field002Chars00 ++ (fragment0287777Field003Chars00 ++ (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0287777Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 423) (fragment0287777Chars ++ tail) =
        SourceJson.value (fuel + 423) ('{' :: (fragment0287777Field000Chars00 ++ (fragment0287777Field001Chars00 ++ (fragment0287777Field002Chars00 ++ (fragment0287777Field003Chars00 ++ (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 423)) hinput
    _ = SourceJson.object (fuel + 422) (SourceJson.white (fragment0287777Field000Chars00 ++ (fragment0287777Field001Chars00 ++ (fragment0287777Field002Chars00 ++ (fragment0287777Field003Chars00 ++ (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))))))))))) fragment0287777Acc00000 := by rfl
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0287777Field001Chars00 ++ (fragment0287777Field002Chars00 ++ (fragment0287777Field003Chars00 ++ (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail))))))))))) fragment0287777Acc00100 := object_fragment0287777_field_000 fuel (fragment0287777Field001Chars00 ++ (fragment0287777Field002Chars00 ++ (fragment0287777Field003Chars00 ++ (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0287777Field002Chars00 ++ (fragment0287777Field003Chars00 ++ (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))))))))) fragment0287777Acc00200 := object_fragment0287777_field_001 fuel (fragment0287777Field002Chars00 ++ (fragment0287777Field003Chars00 ++ (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 419) (SourceJson.white (fragment0287777Field003Chars00 ++ (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail))))))))) fragment0287777Acc00300 := object_fragment0287777_field_002 fuel (fragment0287777Field003Chars00 ++ (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 418) (SourceJson.white (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))))))) fragment0287777Acc00400 := object_fragment0287777_field_003 fuel (fragment0287777Field004Chars00 ++ (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 417) (SourceJson.white (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail))))))) fragment0287777Acc00500 := object_fragment0287777_field_004 fuel (fragment0287777Field005Chars00 ++ (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 416) (SourceJson.white (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))))) fragment0287777Acc00600 := object_fragment0287777_field_005 fuel (fragment0287777Field006Chars00 ++ (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 415) (SourceJson.white (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail))))) fragment0287777Acc00700 := object_fragment0287777_field_006 fuel (fragment0287777Field007Chars00 ++ (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 414) (SourceJson.white (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))) fragment0287777Acc00800 := object_fragment0287777_field_007 fuel (fragment0287777Field008Chars00 ++ (fragment0287777Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 413) (SourceJson.white (fragment0287777Field009Chars00 ++ (tail))) fragment0287777Acc00900 := object_fragment0287777_field_008 fuel (fragment0287777Field009Chars00 ++ (tail))
    _ = .ok (fragment0287777Value, tail) := object_fragment0287777_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0080_before_reader"
  err.flush

noncomputable def chunk0080LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0080SuffixChars00 : List Char := [',']
noncomputable def chunk0080Chars00 : List Char := chunk0080LeadChars00 ++ fragment0275447Chars ++ chunk0080SuffixChars00
noncomputable def chunk0080Push00 (acc : List SourceJson) : List SourceJson := fragment0275447Value :: acc

noncomputable def chunk0080AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0080_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 577)
      (SourceJson.white (chunk0080LeadChars00 ++ (fragment0275447Chars ++ rest))) acc =
      (SourceJson.value (fuel + 576) (fragment0275447Chars ++ rest)).bind
        (chunk0080AfterValue00 (fuel + 576) acc) := by rfl

theorem array_chunk0080 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 577) (SourceJson.white (chunk0080Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 576) (SourceJson.white tail) (chunk0080Push00 acc) := by
  have hinput : chunk0080Chars00 ++ tail = chunk0080LeadChars00 ++ (fragment0275447Chars ++ (chunk0080SuffixChars00 ++ tail)) := by
    simp only [chunk0080Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 577) (SourceJson.white (chunk0080Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 577)
          (SourceJson.white (chunk0080LeadChars00 ++ (fragment0275447Chars ++ (chunk0080SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 577) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 576) (fragment0275447Chars ++ (chunk0080SuffixChars00 ++ tail))).bind
        (chunk0080AfterValue00 (fuel + 576) acc) := array_chunk0080_head fuel (chunk0080SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0275447Value, chunk0080SuffixChars00 ++ tail)).bind
        (chunk0080AfterValue00 (fuel + 576) acc) :=
      congrArg (fun result => result.bind (chunk0080AfterValue00 (fuel + 576) acc))
        (value_fragment0275447 (fuel + 150) (chunk0080SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 576) (SourceJson.white tail) (chunk0080Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0080_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0081_before_reader"
  err.flush

noncomputable def chunk0081LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0081SuffixChars00 : List Char := [',']
noncomputable def chunk0081Chars00 : List Char := chunk0081LeadChars00 ++ fragment0277441Chars ++ chunk0081SuffixChars00
noncomputable def chunk0081Push00 (acc : List SourceJson) : List SourceJson := fragment0277441Value :: acc

noncomputable def chunk0081AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0081_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 576)
      (SourceJson.white (chunk0081LeadChars00 ++ (fragment0277441Chars ++ rest))) acc =
      (SourceJson.value (fuel + 575) (fragment0277441Chars ++ rest)).bind
        (chunk0081AfterValue00 (fuel + 575) acc) := by rfl

theorem array_chunk0081 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 576) (SourceJson.white (chunk0081Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 575) (SourceJson.white tail) (chunk0081Push00 acc) := by
  have hinput : chunk0081Chars00 ++ tail = chunk0081LeadChars00 ++ (fragment0277441Chars ++ (chunk0081SuffixChars00 ++ tail)) := by
    simp only [chunk0081Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 576) (SourceJson.white (chunk0081Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 576)
          (SourceJson.white (chunk0081LeadChars00 ++ (fragment0277441Chars ++ (chunk0081SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 576) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 575) (fragment0277441Chars ++ (chunk0081SuffixChars00 ++ tail))).bind
        (chunk0081AfterValue00 (fuel + 575) acc) := array_chunk0081_head fuel (chunk0081SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0277441Value, chunk0081SuffixChars00 ++ tail)).bind
        (chunk0081AfterValue00 (fuel + 575) acc) :=
      congrArg (fun result => result.bind (chunk0081AfterValue00 (fuel + 575) acc))
        (value_fragment0277441 (fuel + 157) (chunk0081SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 575) (SourceJson.white tail) (chunk0081Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0081_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0082_before_reader"
  err.flush

noncomputable def chunk0082LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0082SuffixChars00 : List Char := [',']
noncomputable def chunk0082Chars00 : List Char := chunk0082LeadChars00 ++ fragment0279405Chars ++ chunk0082SuffixChars00
noncomputable def chunk0082Push00 (acc : List SourceJson) : List SourceJson := fragment0279405Value :: acc

noncomputable def chunk0082AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0082_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 575)
      (SourceJson.white (chunk0082LeadChars00 ++ (fragment0279405Chars ++ rest))) acc =
      (SourceJson.value (fuel + 574) (fragment0279405Chars ++ rest)).bind
        (chunk0082AfterValue00 (fuel + 574) acc) := by rfl

theorem array_chunk0082 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 575) (SourceJson.white (chunk0082Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 574) (SourceJson.white tail) (chunk0082Push00 acc) := by
  have hinput : chunk0082Chars00 ++ tail = chunk0082LeadChars00 ++ (fragment0279405Chars ++ (chunk0082SuffixChars00 ++ tail)) := by
    simp only [chunk0082Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 575) (SourceJson.white (chunk0082Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 575)
          (SourceJson.white (chunk0082LeadChars00 ++ (fragment0279405Chars ++ (chunk0082SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 575) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 574) (fragment0279405Chars ++ (chunk0082SuffixChars00 ++ tail))).bind
        (chunk0082AfterValue00 (fuel + 574) acc) := array_chunk0082_head fuel (chunk0082SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0279405Value, chunk0082SuffixChars00 ++ tail)).bind
        (chunk0082AfterValue00 (fuel + 574) acc) :=
      congrArg (fun result => result.bind (chunk0082AfterValue00 (fuel + 574) acc))
        (value_fragment0279405 (fuel + 326) (chunk0082SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 574) (SourceJson.white tail) (chunk0082Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0082_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0083_before_reader"
  err.flush

noncomputable def chunk0083LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0083SuffixChars00 : List Char := [',']
noncomputable def chunk0083Chars00 : List Char := chunk0083LeadChars00 ++ fragment0281047Chars ++ chunk0083SuffixChars00
noncomputable def chunk0083Push00 (acc : List SourceJson) : List SourceJson := fragment0281047Value :: acc

noncomputable def chunk0083AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0083_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 574)
      (SourceJson.white (chunk0083LeadChars00 ++ (fragment0281047Chars ++ rest))) acc =
      (SourceJson.value (fuel + 573) (fragment0281047Chars ++ rest)).bind
        (chunk0083AfterValue00 (fuel + 573) acc) := by rfl

theorem array_chunk0083 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 574) (SourceJson.white (chunk0083Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 573) (SourceJson.white tail) (chunk0083Push00 acc) := by
  have hinput : chunk0083Chars00 ++ tail = chunk0083LeadChars00 ++ (fragment0281047Chars ++ (chunk0083SuffixChars00 ++ tail)) := by
    simp only [chunk0083Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 574) (SourceJson.white (chunk0083Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 574)
          (SourceJson.white (chunk0083LeadChars00 ++ (fragment0281047Chars ++ (chunk0083SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 574) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 573) (fragment0281047Chars ++ (chunk0083SuffixChars00 ++ tail))).bind
        (chunk0083AfterValue00 (fuel + 573) acc) := array_chunk0083_head fuel (chunk0083SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0281047Value, chunk0083SuffixChars00 ++ tail)).bind
        (chunk0083AfterValue00 (fuel + 573) acc) :=
      congrArg (fun result => result.bind (chunk0083AfterValue00 (fuel + 573) acc))
        (value_fragment0281047 (fuel + 205) (chunk0083SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 573) (SourceJson.white tail) (chunk0083Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0083_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0084_before_reader"
  err.flush

noncomputable def chunk0084LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0084SuffixChars00 : List Char := [',']
noncomputable def chunk0084Chars00 : List Char := chunk0084LeadChars00 ++ fragment0282920Chars ++ chunk0084SuffixChars00
noncomputable def chunk0084Push00 (acc : List SourceJson) : List SourceJson := fragment0282920Value :: acc

noncomputable def chunk0084AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0084_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 573)
      (SourceJson.white (chunk0084LeadChars00 ++ (fragment0282920Chars ++ rest))) acc =
      (SourceJson.value (fuel + 572) (fragment0282920Chars ++ rest)).bind
        (chunk0084AfterValue00 (fuel + 572) acc) := by rfl

theorem array_chunk0084 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 573) (SourceJson.white (chunk0084Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 572) (SourceJson.white tail) (chunk0084Push00 acc) := by
  have hinput : chunk0084Chars00 ++ tail = chunk0084LeadChars00 ++ (fragment0282920Chars ++ (chunk0084SuffixChars00 ++ tail)) := by
    simp only [chunk0084Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 573) (SourceJson.white (chunk0084Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 573)
          (SourceJson.white (chunk0084LeadChars00 ++ (fragment0282920Chars ++ (chunk0084SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 573) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 572) (fragment0282920Chars ++ (chunk0084SuffixChars00 ++ tail))).bind
        (chunk0084AfterValue00 (fuel + 572) acc) := array_chunk0084_head fuel (chunk0084SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0282920Value, chunk0084SuffixChars00 ++ tail)).bind
        (chunk0084AfterValue00 (fuel + 572) acc) :=
      congrArg (fun result => result.bind (chunk0084AfterValue00 (fuel + 572) acc))
        (value_fragment0282920 (fuel + 366) (chunk0084SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 572) (SourceJson.white tail) (chunk0084Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0084_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0085_before_reader"
  err.flush

noncomputable def chunk0085LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0085SuffixChars00 : List Char := [',']
noncomputable def chunk0085Chars00 : List Char := chunk0085LeadChars00 ++ fragment0284468Chars ++ chunk0085SuffixChars00
noncomputable def chunk0085Push00 (acc : List SourceJson) : List SourceJson := fragment0284468Value :: acc

noncomputable def chunk0085AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0085_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 572)
      (SourceJson.white (chunk0085LeadChars00 ++ (fragment0284468Chars ++ rest))) acc =
      (SourceJson.value (fuel + 571) (fragment0284468Chars ++ rest)).bind
        (chunk0085AfterValue00 (fuel + 571) acc) := by rfl

theorem array_chunk0085 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 572) (SourceJson.white (chunk0085Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 571) (SourceJson.white tail) (chunk0085Push00 acc) := by
  have hinput : chunk0085Chars00 ++ tail = chunk0085LeadChars00 ++ (fragment0284468Chars ++ (chunk0085SuffixChars00 ++ tail)) := by
    simp only [chunk0085Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 572) (SourceJson.white (chunk0085Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 572)
          (SourceJson.white (chunk0085LeadChars00 ++ (fragment0284468Chars ++ (chunk0085SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 572) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 571) (fragment0284468Chars ++ (chunk0085SuffixChars00 ++ tail))).bind
        (chunk0085AfterValue00 (fuel + 571) acc) := array_chunk0085_head fuel (chunk0085SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0284468Value, chunk0085SuffixChars00 ++ tail)).bind
        (chunk0085AfterValue00 (fuel + 571) acc) :=
      congrArg (fun result => result.bind (chunk0085AfterValue00 (fuel + 571) acc))
        (value_fragment0284468 (fuel + 355) (chunk0085SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 571) (SourceJson.white tail) (chunk0085Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0085_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0086_before_reader"
  err.flush

noncomputable def chunk0086LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0086SuffixChars00 : List Char := [',']
noncomputable def chunk0086Chars00 : List Char := chunk0086LeadChars00 ++ fragment0286038Chars ++ chunk0086SuffixChars00
noncomputable def chunk0086Push00 (acc : List SourceJson) : List SourceJson := fragment0286038Value :: acc

noncomputable def chunk0086AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0086_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 571)
      (SourceJson.white (chunk0086LeadChars00 ++ (fragment0286038Chars ++ rest))) acc =
      (SourceJson.value (fuel + 570) (fragment0286038Chars ++ rest)).bind
        (chunk0086AfterValue00 (fuel + 570) acc) := by rfl

theorem array_chunk0086 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 571) (SourceJson.white (chunk0086Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 570) (SourceJson.white tail) (chunk0086Push00 acc) := by
  have hinput : chunk0086Chars00 ++ tail = chunk0086LeadChars00 ++ (fragment0286038Chars ++ (chunk0086SuffixChars00 ++ tail)) := by
    simp only [chunk0086Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 571) (SourceJson.white (chunk0086Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 571)
          (SourceJson.white (chunk0086LeadChars00 ++ (fragment0286038Chars ++ (chunk0086SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 571) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 570) (fragment0286038Chars ++ (chunk0086SuffixChars00 ++ tail))).bind
        (chunk0086AfterValue00 (fuel + 570) acc) := array_chunk0086_head fuel (chunk0086SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0286038Value, chunk0086SuffixChars00 ++ tail)).bind
        (chunk0086AfterValue00 (fuel + 570) acc) :=
      congrArg (fun result => result.bind (chunk0086AfterValue00 (fuel + 570) acc))
        (value_fragment0286038 (fuel + 264) (chunk0086SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 570) (SourceJson.white tail) (chunk0086Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0086_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0087_before_reader"
  err.flush

noncomputable def chunk0087LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0087SuffixChars00 : List Char := [',']
noncomputable def chunk0087Chars00 : List Char := chunk0087LeadChars00 ++ fragment0287777Chars ++ chunk0087SuffixChars00
noncomputable def chunk0087Push00 (acc : List SourceJson) : List SourceJson := fragment0287777Value :: acc

noncomputable def chunk0087AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0087_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 570)
      (SourceJson.white (chunk0087LeadChars00 ++ (fragment0287777Chars ++ rest))) acc =
      (SourceJson.value (fuel + 569) (fragment0287777Chars ++ rest)).bind
        (chunk0087AfterValue00 (fuel + 569) acc) := by rfl

theorem array_chunk0087 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 570) (SourceJson.white (chunk0087Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 569) (SourceJson.white tail) (chunk0087Push00 acc) := by
  have hinput : chunk0087Chars00 ++ tail = chunk0087LeadChars00 ++ (fragment0287777Chars ++ (chunk0087SuffixChars00 ++ tail)) := by
    simp only [chunk0087Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 570) (SourceJson.white (chunk0087Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 570)
          (SourceJson.white (chunk0087LeadChars00 ++ (fragment0287777Chars ++ (chunk0087SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 570) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 569) (fragment0287777Chars ++ (chunk0087SuffixChars00 ++ tail))).bind
        (chunk0087AfterValue00 (fuel + 569) acc) := array_chunk0087_head fuel (chunk0087SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0287777Value, chunk0087SuffixChars00 ++ tail)).bind
        (chunk0087AfterValue00 (fuel + 569) acc) :=
      congrArg (fun result => result.bind (chunk0087AfterValue00 (fuel + 569) acc))
        (value_fragment0287777 (fuel + 146) (chunk0087SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 569) (SourceJson.white tail) (chunk0087Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0087_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0080Chars00 ++ chunk0081Chars00 ++ chunk0082Chars00 ++ chunk0083Chars00 ++ chunk0084Chars00 ++ chunk0085Chars00 ++ chunk0086Chars00 ++ chunk0087Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0087Push00 (chunk0086Push00 (chunk0085Push00 (chunk0084Push00 (chunk0083Push00 (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 577) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 569) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0080Chars00 ++ (chunk0081Chars00 ++ (chunk0082Chars00 ++ (chunk0083Chars00 ++ (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 577) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 577) (SourceJson.white (chunk0080Chars00 ++ (chunk0081Chars00 ++ (chunk0082Chars00 ++ (chunk0083Chars00 ++ (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 577) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 576) (SourceJson.white (chunk0081Chars00 ++ (chunk0082Chars00 ++ (chunk0083Chars00 ++ (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail))))))))) (chunk0080Push00 (acc)) := array_chunk0080 fuel (chunk0081Chars00 ++ (chunk0082Chars00 ++ (chunk0083Chars00 ++ (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 575) (SourceJson.white (chunk0082Chars00 ++ (chunk0083Chars00 ++ (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail)))))))) (chunk0081Push00 (chunk0080Push00 (acc))) := array_chunk0081 fuel (chunk0082Chars00 ++ (chunk0083Chars00 ++ (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail))))))) (chunk0080Push00 (acc))
    _ = SourceJson.array (fuel + 574) (SourceJson.white (chunk0083Chars00 ++ (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail))))))) (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc)))) := array_chunk0082 fuel (chunk0083Chars00 ++ (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail)))))) (chunk0081Push00 (chunk0080Push00 (acc)))
    _ = SourceJson.array (fuel + 573) (SourceJson.white (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail)))))) (chunk0083Push00 (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc))))) := array_chunk0083 fuel (chunk0084Chars00 ++ (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail))))) (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc))))
    _ = SourceJson.array (fuel + 572) (SourceJson.white (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail))))) (chunk0084Push00 (chunk0083Push00 (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc)))))) := array_chunk0084 fuel (chunk0085Chars00 ++ (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail)))) (chunk0083Push00 (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc)))))
    _ = SourceJson.array (fuel + 571) (SourceJson.white (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail)))) (chunk0085Push00 (chunk0084Push00 (chunk0083Push00 (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc))))))) := array_chunk0085 fuel (chunk0086Chars00 ++ (chunk0087Chars00 ++ (tail))) (chunk0084Push00 (chunk0083Push00 (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc))))))
    _ = SourceJson.array (fuel + 570) (SourceJson.white (chunk0087Chars00 ++ (tail))) (chunk0086Push00 (chunk0085Push00 (chunk0084Push00 (chunk0083Push00 (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc)))))))) := array_chunk0086 fuel (chunk0087Chars00 ++ (tail)) (chunk0085Push00 (chunk0084Push00 (chunk0083Push00 (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc)))))))
    _ = SourceJson.array (fuel + 569) (SourceJson.white tail) (blockPush acc) := array_chunk0087 fuel (tail) (chunk0086Push00 (chunk0085Push00 (chunk0084Push00 (chunk0083Push00 (chunk0082Push00 (chunk0081Push00 (chunk0080Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 275441).take 14318 = blockChars := by rfl

theorem block_original_split : sourceRest 275441 = blockChars ++ sourceRest 289759 := by
  calc
    sourceRest 275441 = (sourceRest 275441).take 14318 ++ (sourceRest 275441).drop 14318 :=
      (List.take_append_drop 14318 (sourceRest 275441)).symm
    _ = blockChars ++ (sourceRest 275441).drop 14318 :=
      congrArg (fun part => part ++ (sourceRest 275441).drop 14318) block_original_prefix
    _ = blockChars ++ sourceRest 289759 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 275441 14318)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 577) (SourceJson.white (sourceRest 275441)) acc =
      SourceJson.array (fuel + 569) (SourceJson.white (sourceRest 289759)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 577) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 289759) acc)

#print axioms object_fragment0275447_field_000
#print axioms object_fragment0275447_field_001
#print axioms object_fragment0275447_field_002
#print axioms object_fragment0275447_field_003
#print axioms object_fragment0275447_field_004
#print axioms object_fragment0275447_field_005
#print axioms object_fragment0275447_field_006
#print axioms object_fragment0275447_field_007
#print axioms object_fragment0275447_field_008
#print axioms object_fragment0275447_field_009
#print axioms value_fragment0275447
#print axioms object_fragment0277441_field_000
#print axioms object_fragment0277441_field_001
#print axioms object_fragment0277441_field_002
#print axioms object_fragment0277441_field_003
#print axioms object_fragment0277441_field_004
#print axioms object_fragment0277441_field_005
#print axioms object_fragment0277441_field_006
#print axioms object_fragment0277441_field_007
#print axioms object_fragment0277441_field_008
#print axioms object_fragment0277441_field_009
#print axioms value_fragment0277441
#print axioms object_fragment0279405_field_000
#print axioms object_fragment0279405_field_001
#print axioms object_fragment0279405_field_002
#print axioms object_fragment0279405_field_003
#print axioms object_fragment0279405_field_004
#print axioms object_fragment0279405_field_005
#print axioms object_fragment0279405_field_006
#print axioms object_fragment0279405_field_007
#print axioms object_fragment0279405_field_008
#print axioms object_fragment0279405_field_009
#print axioms value_fragment0279405
#print axioms object_fragment0281047_field_000
#print axioms object_fragment0281047_field_001
#print axioms object_fragment0281047_field_002
#print axioms object_fragment0281047_field_003
#print axioms object_fragment0281047_field_004
#print axioms object_fragment0281047_field_005
#print axioms object_fragment0281047_field_006
#print axioms object_fragment0281047_field_007
#print axioms object_fragment0281047_field_008
#print axioms object_fragment0281047_field_009
#print axioms value_fragment0281047
#print axioms object_fragment0282920_field_000
#print axioms object_fragment0282920_field_001
#print axioms object_fragment0282920_field_002
#print axioms object_fragment0282920_field_003
#print axioms object_fragment0282920_field_004
#print axioms object_fragment0282920_field_005
#print axioms object_fragment0282920_field_006
#print axioms object_fragment0282920_field_007
#print axioms object_fragment0282920_field_008
#print axioms object_fragment0282920_field_009
#print axioms value_fragment0282920
#print axioms object_fragment0284468_field_000
#print axioms object_fragment0284468_field_001
#print axioms object_fragment0284468_field_002
#print axioms object_fragment0284468_field_003
#print axioms object_fragment0284468_field_004
#print axioms object_fragment0284468_field_005
#print axioms object_fragment0284468_field_006
#print axioms object_fragment0284468_field_007
#print axioms object_fragment0284468_field_008
#print axioms object_fragment0284468_field_009
#print axioms value_fragment0284468
#print axioms object_fragment0286038_field_000
#print axioms object_fragment0286038_field_001
#print axioms object_fragment0286038_field_002
#print axioms object_fragment0286038_field_003
#print axioms object_fragment0286038_field_004
#print axioms object_fragment0286038_field_005
#print axioms object_fragment0286038_field_006
#print axioms object_fragment0286038_field_007
#print axioms object_fragment0286038_field_008
#print axioms object_fragment0286038_field_009
#print axioms value_fragment0286038
#print axioms object_fragment0287777_field_000
#print axioms object_fragment0287777_field_001
#print axioms object_fragment0287777_field_002
#print axioms object_fragment0287777_field_003
#print axioms object_fragment0287777_field_004
#print axioms object_fragment0287777_field_005
#print axioms object_fragment0287777_field_006
#print axioms object_fragment0287777_field_007
#print axioms object_fragment0287777_field_008
#print axioms object_fragment0287777_field_009
#print axioms value_fragment0287777
#print axioms array_chunk0080_head
#print axioms array_chunk0080
#print axioms array_chunk0081_head
#print axioms array_chunk0081
#print axioms array_chunk0082_head
#print axioms array_chunk0082
#print axioms array_chunk0083_head
#print axioms array_chunk0083
#print axioms array_chunk0084_head
#print axioms array_chunk0084
#print axioms array_chunk0085_head
#print axioms array_chunk0085
#print axioms array_chunk0086_head
#print axioms array_chunk0086
#print axioms array_chunk0087_head
#print axioms array_chunk0087
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock010

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
