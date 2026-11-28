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

namespace SimplicesBlock007

noncomputable def fragment0232054Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0232054Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0232054Field000Value00 : SourceJson := .number (String.ofList ['5', '6'])
noncomputable def fragment0232054Acc00100 : List (String × SourceJson) := (fragment0232054Field000Key00, fragment0232054Field000Value00) :: fragment0232054Acc00000
noncomputable def fragment0232054Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '6', ',']

theorem object_fragment0232054_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 378) (SourceJson.white (fragment0232054Field000Chars00 ++ tail)) fragment0232054Acc00000 =
      SourceJson.object (fuel + 377) (SourceJson.white tail) fragment0232054Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_000"
  err.flush

noncomputable def fragment0232054Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0232054Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0232054Acc00200 : List (String × SourceJson) := (fragment0232054Field001Key00, fragment0232054Field001Value00) :: fragment0232054Acc00100
noncomputable def fragment0232054Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0232054_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 377) (SourceJson.white (fragment0232054Field001Chars00 ++ tail)) fragment0232054Acc00100 =
      SourceJson.object (fuel + 376) (SourceJson.white tail) fragment0232054Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_001"
  err.flush

noncomputable def fragment0232054Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0232054Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '5', '2', '0', '0', '2', '2', '1', '7', '1', '5', '1', '7', '4', '9', '3', '6', '0', '2', '7', '7', '6', '5', '7', '1', '9', '3', '2', '7', '0', '9', '4', '0', '3', '7', '/', '1', '6', '3', '3', '3', '3', '0', '0', '0', '8', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0232054Acc00300 : List (String × SourceJson) := (fragment0232054Field002Key00, fragment0232054Field002Value00) :: fragment0232054Acc00200
noncomputable def fragment0232054Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '8', '5', '2', '0', '0', '2', '2', '1', '7', '1', '5', '1', '7', '4', '9', '3', '6', '0', '2', '7', '7', '6', '5', '7', '1', '9', '3', '2', '7', '0', '9', '4', '0', '3', '7', '/', '1', '6', '3', '3', '3', '3', '0', '0', '0', '8', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0232054_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 376) (SourceJson.white (fragment0232054Field002Chars00 ++ tail)) fragment0232054Acc00200 =
      SourceJson.object (fuel + 375) (SourceJson.white tail) fragment0232054Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_002"
  err.flush

noncomputable def fragment0232054Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0232054Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0232054Acc00400 : List (String × SourceJson) := (fragment0232054Field003Key00, fragment0232054Field003Value00) :: fragment0232054Acc00300
noncomputable def fragment0232054Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0232054_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 375) (SourceJson.white (fragment0232054Field003Chars00 ++ tail)) fragment0232054Acc00300 =
      SourceJson.object (fuel + 374) (SourceJson.white tail) fragment0232054Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_003"
  err.flush

noncomputable def fragment0232054Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0232054Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0232054Acc00500 : List (String × SourceJson) := (fragment0232054Field004Key00, fragment0232054Field004Value00) :: fragment0232054Acc00400
noncomputable def fragment0232054Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0232054_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 374) (SourceJson.white (fragment0232054Field004Chars00 ++ tail)) fragment0232054Acc00400 =
      SourceJson.object (fuel + 373) (SourceJson.white tail) fragment0232054Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_004"
  err.flush

noncomputable def fragment0232054Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0232054Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '7', '7', '4', '5', '4', '1', '4', '0', '0', '6', '1', '8', '2', '8', '2', '2', '2', '4', '4', '7', '/', '3', '1', '9', '9', '1', '8', '2', '3', '6', '8', '2', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '5', '4', '8', '0', '4', '3', '9', '8', '1', '1', '3', '1', '5', '5', '4', '7', '2', '3', '/', '4', '5', '7', '0', '2', '6', '0', '5', '2', '6', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '7', '5', '7', '6', '7', '0', '7', '2', '9', '2', '0', '2', '2', '2', '0', '7', '/', '1', '3', '9', '0', '9', '4', '8', '8', '5', '5', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '0', '5', '9', '9', '3', '6', '3', '9', '6', '7', '4', '4', '2', '4', '9', '5', '5', '7', '/', '1', '0', '6', '6', '3', '9', '4', '1', '2', '2', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '2', '6', '8', '1', '4', '1', '2', '5', '1', '5', '1', '9', '3', '6', '2', '7', '9', '/', '3', '5', '5', '4', '6', '4', '7', '0', '7', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '0', '9', '0', '2', '4', '4', '1', '8', '0', '1', '8', '9', '5', '0', '9', '9', '3', '/', '7', '2', '7', '0', '8', '6', '9', '0', '1', '8', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '0', '6', '2', '0', '5', '9', '0', '0', '3', '5', '5', '7', '7', '9', '5', '8', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '1', '0', '5', '9', '6', '6', '1', '1', '9', '0', '9', '9', '4', '5', '7', '1', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '5', '2', '5', '1', '4', '0', '0', '9', '9', '5', '4', '0', '8', '9', '2', '3', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '3', '3', '3', '6', '6', '7', '8', '0', '5', '5', '0', '5', '9', '5', '2', '8', '1', '/', '4', '5', '7', '0', '2', '6', '0', '5', '2', '6', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0232054Acc00600 : List (String × SourceJson) := (fragment0232054Field005Key00, fragment0232054Field005Value00) :: fragment0232054Acc00500
noncomputable def fragment0232054Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '4', '5', '4', '1', '4', '0', '0', '6', '1', '8', '2', '8', '2', '2', '2', '4', '4', '7', '/', '3', '1', '9', '9', '1', '8', '2', '3', '6', '8', '2', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '5', '4', '8', '0', '4', '3', '9', '8', '1', '1', '3', '1', '5', '5', '4', '7', '2', '3', '/', '4', '5', '7', '0', '2', '6', '0', '5', '2', '6', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '7', '5', '7', '6', '7', '0', '7', '2', '9', '2', '0', '2', '2', '2', '0', '7', '/', '1', '3', '9', '0', '9', '4', '8', '8', '5', '5', '7', '5', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '0', '5', '9', '9', '3', '6', '3', '9', '6', '7', '4', '4', '2', '4', '9', '5', '5', '7', '/', '1', '0', '6', '6', '3', '9', '4', '1', '2', '2', '7', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '8', '2', '6', '8', '1', '4', '1', '2', '5', '1', '5', '1', '9', '3', '6', '2', '7', '9', '/', '3', '5', '5', '4', '6', '4', '7', '0', '7', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '0', '9', '0', '2', '4', '4', '1', '8', '0', '1', '8', '9', '5', '0', '9', '9', '3', '/', '7', '2', '7', '0', '8', '6', '9', '0', '1', '8', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '0', '6', '2', '0', '5', '9', '0', '0', '3', '5', '5', '7', '7', '9', '5', '8', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '1', '0', '5', '9', '6', '6', '1', '1', '9', '0', '9', '9', '4', '5', '7', '1', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '5', '2', '5', '1', '4', '0', '0', '9', '9', '5', '4', '0', '8', '9', '2', '3', '1', '/', '2', '9', '0', '8', '3', '4', '7', '6', '0', '7', '4', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '3', '3', '3', '6', '6', '7', '8', '0', '5', '5', '0', '5', '9', '5', '2', '8', '1', '/', '4', '5', '7', '0', '2', '6', '0', '5', '2', '6', '0', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0232054_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 373) (SourceJson.white (fragment0232054Field005Chars00 ++ tail)) fragment0232054Acc00500 =
      SourceJson.object (fuel + 372) (SourceJson.white tail) fragment0232054Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_005"
  err.flush

noncomputable def fragment0232054Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0232054Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '0', '4', '6', '1', '1', '6', '4', '3', '7', '8', '5', '2', '3', '7', '2', '0', '6', '3', '7', '6', '5', '1', '4', '8', '5', '7', '0', '9', '0', '8', '1', '5', '2', '4', '4', '4', '0', '9', '2', '0', '2', '0', '/', '6', '1', '9', '1', '4', '3', '8', '4', '9', '8', '0', '7', '1', '3', '0', '0', '8', '1', '6', '5', '5', '7', '8', '5', '7', '8', '1', '2', '5', '2', '1', '6', '7', '7', '5', '7', '2', '0', '7', '3', '9', '7', '5', '1', '7', '0', '7', '3', '4', '9', '8', '5', '3', '1', '5', '3', '5', '7', '4', '7'])
noncomputable def fragment0232054Acc00700 : List (String × SourceJson) := (fragment0232054Field006Key00, fragment0232054Field006Value00) :: fragment0232054Acc00600
noncomputable def fragment0232054Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '0', '4', '6', '1', '1', '6', '4', '3', '7', '8', '5', '2', '3', '7', '2', '0', '6', '3', '7', '6', '5', '1', '4', '8', '5', '7', '0', '9', '0', '8', '1', '5', '2', '4', '4', '4', '0', '9', '2', '0', '2', '0', '/', '6', '1', '9', '1', '4', '3', '8', '4', '9', '8', '0', '7', '1', '3', '0', '0', '8', '1', '6', '5', '5', '7', '8', '5', '7', '8', '1', '2', '5', '2', '1', '6', '7', '7', '5', '7', '2', '0', '7', '3', '9', '7', '5', '1', '7', '0', '7', '3', '4', '9', '8', '5', '3', '1', '5', '3', '5', '7', '4', '7', '"', ',']

theorem object_fragment0232054_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 372) (SourceJson.white (fragment0232054Field006Chars00 ++ tail)) fragment0232054Acc00600 =
      SourceJson.object (fuel + 371) (SourceJson.white tail) fragment0232054Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_006"
  err.flush

noncomputable def fragment0232054Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0232054Field007Value00 : SourceJson := .str (String.ofList ['7', '9', '8', '3', '5', '1', '9', '9', '4', '9', '2', '2', '6', '1', '4', '9', '5', '3', '3', '2', '7', '7', '8', '4', '3', '2', '7', '8', '7', '3', '7', '9', '1', '2', '3', '0', '5', '1', '8', '5', '3', '8', '3', '4', '8', '8', '2', '0', '7', '2', '5', '8', '1', '0', '5', '5', '8', '2', '0', '3', '3', '8', '1', '3', '4', '4', '8', '6', '2', '2', '3', '3', '5', '3', '5', '2', '6', '8', '8', '8', '5', '8', '9', '6', '3', '0', '2', '9', '3', '6', '3', '4', '0', '6', '1', '1', '1', '6', '3', '4', '6', '9', '1', '5', '1', '4', '6', '3', '7', '3', '2', '0', '4', '2', '7', '1', '8', '5', '5', '9', '9', '4', '4', '2', '4', '8', '2', '3', '5', '9', '9', '3', '7', '8', '0', '1', '9', '7', '3', '5', '2', '3', '9', '6', '8', '7', '0', '0', '8', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '7', '0', '9', '3', '6', '6', '7', '9', '3', '2', '8', '3', '6', '4', '7', '3', '0', '0', '0', '5', '6', '0', '3', '3', '3', '3', '9', '5', '8', '5', '7', '9', '3', '4', '4', '1', '1', '6', '6', '9', '4', '1', '5', '4', '0', '7', '7', '1', '5', '3', '8', '9', '8', '0', '8', '6', '8', '3', '8', '9', '1', '0', '3', '7', '7', '7', '1', '7', '8', '8', '8', '2', '1', '9', '7', '7', '3', '3', '0', '0', '4', '7', '9', '6', '1', '9', '7', '8', '1', '5', '4', '0', '6', '2', '7', '0', '1', '2', '9', '0', '3', '0', '3', '5', '3', '3', '2', '5', '9', '4', '6', '3', '2', '5', '5', '6', '1', '8', '3', '9', '1', '7', '9', '0', '9', '2', '3', '5', '9', '7', '1', '5', '9', '4', '6', '0', '9', '9', '4', '1', '3', '2', '7', '0', '5', '7', '9', '6', '9', '5', '4', '0', '6', '5', '3', '0', '0', '7', '5', '1', '4', '7', '5', '2', '1', '7', '4', '2', '9', '3', '0', '9', '6', '7', '8', '4', '9', '6', '0', '8', '3', '2', '8', '8', '9', '5', '2', '2', '0', '3'])
noncomputable def fragment0232054Acc00800 : List (String × SourceJson) := (fragment0232054Field007Key00, fragment0232054Field007Value00) :: fragment0232054Acc00700
noncomputable def fragment0232054Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '9', '8', '3', '5', '1', '9', '9', '4', '9', '2', '2', '6', '1', '4', '9', '5', '3', '3', '2', '7', '7', '8', '4', '3', '2', '7', '8', '7', '3', '7', '9', '1', '2', '3', '0', '5', '1', '8', '5', '3', '8', '3', '4', '8', '8', '2', '0', '7', '2', '5', '8', '1', '0', '5', '5', '8', '2', '0', '3', '3', '8', '1', '3', '4', '4', '8', '6', '2', '2', '3', '3', '5', '3', '5', '2', '6', '8', '8', '8', '5', '8', '9', '6', '3', '0', '2', '9', '3', '6', '3', '4', '0', '6', '1', '1', '1', '6', '3', '4', '6', '9', '1', '5', '1', '4', '6', '3', '7', '3', '2', '0', '4', '2', '7', '1', '8', '5', '5', '9', '9', '4', '4', '2', '4', '8', '2', '3', '5', '9', '9', '3', '7', '8', '0', '1', '9', '7', '3', '5', '2', '3', '9', '6', '8', '7', '0', '0', '8', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '7', '0', '9', '3', '6', '6', '7', '9', '3', '2', '8', '3', '6', '4', '7', '3', '0', '0', '0', '5', '6', '0', '3', '3', '3', '3', '9', '5', '8', '5', '7', '9', '3', '4', '4', '1', '1', '6', '6', '9', '4', '1', '5', '4', '0', '7', '7', '1', '5', '3', '8', '9', '8', '0', '8', '6', '8', '3', '8', '9', '1', '0', '3', '7', '7', '7', '1', '7', '8', '8', '8', '2', '1', '9', '7', '7', '3', '3', '0', '0', '4', '7', '9', '6', '1', '9', '7', '8', '1', '5', '4', '0', '6', '2', '7', '0', '1', '2', '9', '0', '3', '0', '3', '5', '3', '3', '2', '5', '9', '4', '6', '3', '2', '5', '5', '6', '1', '8', '3', '9', '1', '7', '9', '0', '9', '2', '3', '5', '9', '7', '1', '5', '9', '4', '6', '0', '9', '9', '4', '1', '3', '2', '7', '0', '5', '7', '9', '6', '9', '5', '4', '0', '6', '5', '3', '0', '0', '7', '5', '1', '4', '7', '5', '2', '1', '7', '4', '2', '9', '3', '0', '9', '6', '7', '8', '4', '9', '6', '0', '8', '3', '2', '8', '8', '9', '5', '2', '2', '0', '3', '"', ',']

theorem object_fragment0232054_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 371) (SourceJson.white (fragment0232054Field007Chars00 ++ tail)) fragment0232054Acc00700 =
      SourceJson.object (fuel + 370) (SourceJson.white tail) fragment0232054Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_007"
  err.flush

noncomputable def fragment0232054Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0232054Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '1', '3', '5', '0', '5', '9', '3', '8', '1', '7', '9'])
noncomputable def fragment0232054Acc00900 : List (String × SourceJson) := (fragment0232054Field008Key00, fragment0232054Field008Value00) :: fragment0232054Acc00800
noncomputable def fragment0232054Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '1', '3', '5', '0', '5', '9', '3', '8', '1', '7', '9', '"', ',']

theorem object_fragment0232054_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 370) (SourceJson.white (fragment0232054Field008Chars00 ++ tail)) fragment0232054Acc00800 =
      SourceJson.object (fuel + 369) (SourceJson.white tail) fragment0232054Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_008"
  err.flush

noncomputable def fragment0232054Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0232054Field009Value00 : SourceJson := .str (String.ofList ['4', '6', '1', '3', '7', '7', '7', '0', '2', '9', '3', '1', '5'])
noncomputable def fragment0232054Acc01000 : List (String × SourceJson) := (fragment0232054Field009Key00, fragment0232054Field009Value00) :: fragment0232054Acc00900
noncomputable def fragment0232054Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '1', '3', '7', '7', '7', '0', '2', '9', '3', '1', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0232054_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment0232054Field009Chars00 ++ tail)) fragment0232054Acc00900 =
      .ok (.obj (fragment0232054Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0232054_object_field_009"
  err.flush

noncomputable def fragment0232054Chars : List Char := '{' :: (fragment0232054Field000Chars00 ++ fragment0232054Field001Chars00 ++ fragment0232054Field002Chars00 ++ fragment0232054Field003Chars00 ++ fragment0232054Field004Chars00 ++ fragment0232054Field005Chars00 ++ fragment0232054Field006Chars00 ++ fragment0232054Field007Chars00 ++ fragment0232054Field008Chars00 ++ fragment0232054Field009Chars00)
noncomputable def fragment0232054Value : SourceJson := .obj (fragment0232054Acc01000.reverse)

theorem value_fragment0232054 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 379) (fragment0232054Chars ++ tail) =
      .ok (fragment0232054Value, tail) := by
  have hinput : fragment0232054Chars ++ tail = '{' :: (fragment0232054Field000Chars00 ++ (fragment0232054Field001Chars00 ++ (fragment0232054Field002Chars00 ++ (fragment0232054Field003Chars00 ++ (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0232054Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 379) (fragment0232054Chars ++ tail) =
        SourceJson.value (fuel + 379) ('{' :: (fragment0232054Field000Chars00 ++ (fragment0232054Field001Chars00 ++ (fragment0232054Field002Chars00 ++ (fragment0232054Field003Chars00 ++ (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 379)) hinput
    _ = SourceJson.object (fuel + 378) (SourceJson.white (fragment0232054Field000Chars00 ++ (fragment0232054Field001Chars00 ++ (fragment0232054Field002Chars00 ++ (fragment0232054Field003Chars00 ++ (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))))))))))) fragment0232054Acc00000 := by rfl
    _ = SourceJson.object (fuel + 377) (SourceJson.white (fragment0232054Field001Chars00 ++ (fragment0232054Field002Chars00 ++ (fragment0232054Field003Chars00 ++ (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail))))))))))) fragment0232054Acc00100 := object_fragment0232054_field_000 fuel (fragment0232054Field001Chars00 ++ (fragment0232054Field002Chars00 ++ (fragment0232054Field003Chars00 ++ (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 376) (SourceJson.white (fragment0232054Field002Chars00 ++ (fragment0232054Field003Chars00 ++ (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))))))))) fragment0232054Acc00200 := object_fragment0232054_field_001 fuel (fragment0232054Field002Chars00 ++ (fragment0232054Field003Chars00 ++ (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 375) (SourceJson.white (fragment0232054Field003Chars00 ++ (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail))))))))) fragment0232054Acc00300 := object_fragment0232054_field_002 fuel (fragment0232054Field003Chars00 ++ (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 374) (SourceJson.white (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))))))) fragment0232054Acc00400 := object_fragment0232054_field_003 fuel (fragment0232054Field004Chars00 ++ (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 373) (SourceJson.white (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail))))))) fragment0232054Acc00500 := object_fragment0232054_field_004 fuel (fragment0232054Field005Chars00 ++ (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 372) (SourceJson.white (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))))) fragment0232054Acc00600 := object_fragment0232054_field_005 fuel (fragment0232054Field006Chars00 ++ (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 371) (SourceJson.white (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail))))) fragment0232054Acc00700 := object_fragment0232054_field_006 fuel (fragment0232054Field007Chars00 ++ (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 370) (SourceJson.white (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))) fragment0232054Acc00800 := object_fragment0232054_field_007 fuel (fragment0232054Field008Chars00 ++ (fragment0232054Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment0232054Field009Chars00 ++ (tail))) fragment0232054Acc00900 := object_fragment0232054_field_008 fuel (fragment0232054Field009Chars00 ++ (tail))
    _ = .ok (fragment0232054Value, tail) := object_fragment0232054_field_009 fuel (tail)

noncomputable def fragment0233927Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0233927Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0233927Field000Value00 : SourceJson := .number (String.ofList ['5', '7'])
noncomputable def fragment0233927Acc00100 : List (String × SourceJson) := (fragment0233927Field000Key00, fragment0233927Field000Value00) :: fragment0233927Acc00000
noncomputable def fragment0233927Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '7', ',']

theorem object_fragment0233927_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0233927Field000Chars00 ++ tail)) fragment0233927Acc00000 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0233927Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_000"
  err.flush

noncomputable def fragment0233927Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0233927Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0233927Acc00200 : List (String × SourceJson) := (fragment0233927Field001Key00, fragment0233927Field001Value00) :: fragment0233927Acc00100
noncomputable def fragment0233927Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0233927_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0233927Field001Chars00 ++ tail)) fragment0233927Acc00100 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0233927Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_001"
  err.flush

noncomputable def fragment0233927Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0233927Field002Value00 : SourceJson := .str (String.ofList ['2', '4', '0', '1', '4', '2', '1', '6', '6', '3', '1', '2', '7', '1', '9', '9', '1', '6', '6', '4', '2', '1', '1', '1', '3', '5', '9', '0', '1', '0', '1', '1', '5', '3', '7', '4', '5', '7', '/', '3', '5', '9', '9', '9', '9', '2', '6', '7', '1', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0233927Acc00300 : List (String × SourceJson) := (fragment0233927Field002Key00, fragment0233927Field002Value00) :: fragment0233927Acc00200
noncomputable def fragment0233927Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '4', '0', '1', '4', '2', '1', '6', '6', '3', '1', '2', '7', '1', '9', '9', '1', '6', '6', '4', '2', '1', '1', '1', '3', '5', '9', '0', '1', '0', '1', '1', '5', '3', '7', '4', '5', '7', '/', '3', '5', '9', '9', '9', '9', '2', '6', '7', '1', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0233927_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0233927Field002Chars00 ++ tail)) fragment0233927Acc00200 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0233927Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_002"
  err.flush

noncomputable def fragment0233927Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0233927Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0233927Acc00400 : List (String × SourceJson) := (fragment0233927Field003Key00, fragment0233927Field003Value00) :: fragment0233927Acc00300
noncomputable def fragment0233927Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0233927_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0233927Field003Chars00 ++ tail)) fragment0233927Acc00300 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0233927Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_003"
  err.flush

noncomputable def fragment0233927Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0233927Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0233927Acc00500 : List (String × SourceJson) := (fragment0233927Field004Key00, fragment0233927Field004Value00) :: fragment0233927Acc00400
noncomputable def fragment0233927Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0233927_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0233927Field004Chars00 ++ tail)) fragment0233927Acc00400 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0233927Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_004"
  err.flush

noncomputable def fragment0233927Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0233927Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '7', '4', '2', '6', '0', '3', '5', '8', '4', '5', '9', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '7', '0', '8', '0', '7', '5', '9', '7', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '2', '8', '5', '1', '1', '8', '5', '1', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '1', '2', '1', '8', '2', '4', '6', '0', '1', '/', '5', '9', '7', '7', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '9', '8', '5', '0', '9', '4', '8', '3', '/', '2', '9', '8', '8', '5', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '2', '6', '5', '3', '3', '7', '1', '6', '7', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '2', '6', '3', '7', '0', '9', '4', '3', '/', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '6', '4', '1', '9', '8', '9', '4', '3', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '2', '7', '9', '1', '8', '7', '0', '3', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '1', '1', '1', '4', '9', '0', '8', '7', '7', '/', '9', '5', '6', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0233927Acc00600 : List (String × SourceJson) := (fragment0233927Field005Key00, fragment0233927Field005Value00) :: fragment0233927Acc00500
noncomputable def fragment0233927Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '4', '2', '6', '0', '3', '5', '8', '4', '5', '9', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '7', '0', '8', '0', '7', '5', '9', '7', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '2', '8', '5', '1', '1', '8', '5', '1', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '1', '2', '1', '8', '2', '4', '6', '0', '1', '/', '5', '9', '7', '7', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '9', '8', '5', '0', '9', '4', '8', '3', '/', '2', '9', '8', '8', '5', '6', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '2', '6', '5', '3', '3', '7', '1', '6', '7', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '2', '6', '3', '7', '0', '9', '4', '3', '/', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '6', '4', '1', '9', '8', '9', '4', '3', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '2', '7', '9', '1', '8', '7', '0', '3', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '1', '1', '1', '4', '9', '0', '8', '7', '7', '/', '9', '5', '6', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0233927_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0233927Field005Chars00 ++ tail)) fragment0233927Acc00500 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0233927Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_005"
  err.flush

noncomputable def fragment0233927Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0233927Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '6', '8', '3', '9', '5', '7', '6', '1', '1', '0', '1', '1', '3', '9', '3', '6', '9', '0', '6', '6', '8', '9', '3', '4', '5', '3', '4', '4', '2', '9', '8', '6', '9', '7', '9', '5', '8', '4', '7', '2', '3', '2', '0', '0', '0', '/', '1', '5', '0', '9', '9', '2', '8', '3', '4', '4', '0', '8', '0', '0', '3', '7', '0', '1', '4', '3', '6', '3', '6', '4', '8', '1', '1', '8', '4', '3', '4', '4', '4', '4', '9', '0', '1', '2', '0', '5', '2', '2', '4', '8', '9', '1', '9', '7', '4', '7', '2', '8', '7', '1', '3', '1', '8', '7', '9', '0', '8', '6', '9'])
noncomputable def fragment0233927Acc00700 : List (String × SourceJson) := (fragment0233927Field006Key00, fragment0233927Field006Value00) :: fragment0233927Acc00600
noncomputable def fragment0233927Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '6', '8', '3', '9', '5', '7', '6', '1', '1', '0', '1', '1', '3', '9', '3', '6', '9', '0', '6', '6', '8', '9', '3', '4', '5', '3', '4', '4', '2', '9', '8', '6', '9', '7', '9', '5', '8', '4', '7', '2', '3', '2', '0', '0', '0', '/', '1', '5', '0', '9', '9', '2', '8', '3', '4', '4', '0', '8', '0', '0', '3', '7', '0', '1', '4', '3', '6', '3', '6', '4', '8', '1', '1', '8', '4', '3', '4', '4', '4', '4', '9', '0', '1', '2', '0', '5', '2', '2', '4', '8', '9', '1', '9', '7', '4', '7', '2', '8', '7', '1', '3', '1', '8', '7', '9', '0', '8', '6', '9', '"', ',']

theorem object_fragment0233927_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0233927Field006Chars00 ++ tail)) fragment0233927Acc00600 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0233927Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_006"
  err.flush

noncomputable def fragment0233927Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0233927Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '9', '1', '3', '0', '2', '9', '2', '9', '8', '4', '2', '0', '7', '8', '8', '8', '3', '2', '6', '9', '7', '4', '3', '2', '5', '7', '6', '3', '9', '4', '4', '4', '2', '6', '7', '7', '6', '1', '8', '7', '1', '5', '6', '4', '0', '5', '9', '2', '8', '7', '7', '1', '6', '1', '2', '8', '7', '7', '3', '3', '2', '8', '8', '8', '2', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '9', '2', '9', '3', '3', '5', '7', '7', '9', '8', '6', '3', '2', '6', '8', '9', '7', '6', '2', '3', '7', '8', '9', '2', '3', '9', '7', '3', '7', '2', '0', '6', '2', '5', '9', '9', '7', '3', '3', '7', '2', '4', '6', '1', '1', '0', '7', '4', '8', '1', '9', '1', '6', '0', '1', '6', '6', '9', '3', '2', '0', '8', '9', '8', '5', '8', '4', '5', '1', '8', '2', '1', '2', '2', '3', '5', '7', '0', '9', '5', '4', '1', '7', '3', '5', '0', '9', '4', '4', '9', '7', '2', '3', '0', '4', '2', '3', '6', '4', '5', '9', '2', '7'])
noncomputable def fragment0233927Acc00800 : List (String × SourceJson) := (fragment0233927Field007Key00, fragment0233927Field007Value00) :: fragment0233927Acc00700
noncomputable def fragment0233927Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '9', '1', '3', '0', '2', '9', '2', '9', '8', '4', '2', '0', '7', '8', '8', '8', '3', '2', '6', '9', '7', '4', '3', '2', '5', '7', '6', '3', '9', '4', '4', '4', '2', '6', '7', '7', '6', '1', '8', '7', '1', '5', '6', '4', '0', '5', '9', '2', '8', '7', '7', '1', '6', '1', '2', '8', '7', '7', '3', '3', '2', '8', '8', '8', '2', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '9', '2', '9', '3', '3', '5', '7', '7', '9', '8', '6', '3', '2', '6', '8', '9', '7', '6', '2', '3', '7', '8', '9', '2', '3', '9', '7', '3', '7', '2', '0', '6', '2', '5', '9', '9', '7', '3', '3', '7', '2', '4', '6', '1', '1', '0', '7', '4', '8', '1', '9', '1', '6', '0', '1', '6', '6', '9', '3', '2', '0', '8', '9', '8', '5', '8', '4', '5', '1', '8', '2', '1', '2', '2', '3', '5', '7', '0', '9', '5', '4', '1', '7', '3', '5', '0', '9', '4', '4', '9', '7', '2', '3', '0', '4', '2', '3', '6', '4', '5', '9', '2', '7', '"', ',']

theorem object_fragment0233927_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0233927Field007Chars00 ++ tail)) fragment0233927Acc00700 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0233927Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_007"
  err.flush

noncomputable def fragment0233927Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0233927Field008Value00 : SourceJson := .str (String.ofList ['5', '6', '0', '6', '0', '2', '9', '8', '0', '4', '1', '2', '5'])
noncomputable def fragment0233927Acc00900 : List (String × SourceJson) := (fragment0233927Field008Key00, fragment0233927Field008Value00) :: fragment0233927Acc00800
noncomputable def fragment0233927Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '0', '6', '0', '2', '9', '8', '0', '4', '1', '2', '5', '"', ',']

theorem object_fragment0233927_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0233927Field008Chars00 ++ tail)) fragment0233927Acc00800 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0233927Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_008"
  err.flush

noncomputable def fragment0233927Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0233927Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '5', '9', '9', '2', '9', '7', '5', '2', '0', '2', '1', '3'])
noncomputable def fragment0233927Acc01000 : List (String × SourceJson) := (fragment0233927Field009Key00, fragment0233927Field009Value00) :: fragment0233927Acc00900
noncomputable def fragment0233927Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '5', '9', '9', '2', '9', '7', '5', '2', '0', '2', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0233927_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0233927Field009Chars00 ++ tail)) fragment0233927Acc00900 =
      .ok (.obj (fragment0233927Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0233927_object_field_009"
  err.flush

noncomputable def fragment0233927Chars : List Char := '{' :: (fragment0233927Field000Chars00 ++ fragment0233927Field001Chars00 ++ fragment0233927Field002Chars00 ++ fragment0233927Field003Chars00 ++ fragment0233927Field004Chars00 ++ fragment0233927Field005Chars00 ++ fragment0233927Field006Chars00 ++ fragment0233927Field007Chars00 ++ fragment0233927Field008Chars00 ++ fragment0233927Field009Chars00)
noncomputable def fragment0233927Value : SourceJson := .obj (fragment0233927Acc01000.reverse)

theorem value_fragment0233927 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 205) (fragment0233927Chars ++ tail) =
      .ok (fragment0233927Value, tail) := by
  have hinput : fragment0233927Chars ++ tail = '{' :: (fragment0233927Field000Chars00 ++ (fragment0233927Field001Chars00 ++ (fragment0233927Field002Chars00 ++ (fragment0233927Field003Chars00 ++ (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0233927Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 205) (fragment0233927Chars ++ tail) =
        SourceJson.value (fuel + 205) ('{' :: (fragment0233927Field000Chars00 ++ (fragment0233927Field001Chars00 ++ (fragment0233927Field002Chars00 ++ (fragment0233927Field003Chars00 ++ (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 205)) hinput
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0233927Field000Chars00 ++ (fragment0233927Field001Chars00 ++ (fragment0233927Field002Chars00 ++ (fragment0233927Field003Chars00 ++ (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))))))))))) fragment0233927Acc00000 := by rfl
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0233927Field001Chars00 ++ (fragment0233927Field002Chars00 ++ (fragment0233927Field003Chars00 ++ (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail))))))))))) fragment0233927Acc00100 := object_fragment0233927_field_000 fuel (fragment0233927Field001Chars00 ++ (fragment0233927Field002Chars00 ++ (fragment0233927Field003Chars00 ++ (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0233927Field002Chars00 ++ (fragment0233927Field003Chars00 ++ (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))))))))) fragment0233927Acc00200 := object_fragment0233927_field_001 fuel (fragment0233927Field002Chars00 ++ (fragment0233927Field003Chars00 ++ (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0233927Field003Chars00 ++ (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail))))))))) fragment0233927Acc00300 := object_fragment0233927_field_002 fuel (fragment0233927Field003Chars00 ++ (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))))))) fragment0233927Acc00400 := object_fragment0233927_field_003 fuel (fragment0233927Field004Chars00 ++ (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail))))))) fragment0233927Acc00500 := object_fragment0233927_field_004 fuel (fragment0233927Field005Chars00 ++ (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))))) fragment0233927Acc00600 := object_fragment0233927_field_005 fuel (fragment0233927Field006Chars00 ++ (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail))))) fragment0233927Acc00700 := object_fragment0233927_field_006 fuel (fragment0233927Field007Chars00 ++ (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))) fragment0233927Acc00800 := object_fragment0233927_field_007 fuel (fragment0233927Field008Chars00 ++ (fragment0233927Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0233927Field009Chars00 ++ (tail))) fragment0233927Acc00900 := object_fragment0233927_field_008 fuel (fragment0233927Field009Chars00 ++ (tail))
    _ = .ok (fragment0233927Value, tail) := object_fragment0233927_field_009 fuel (tail)

noncomputable def fragment0235463Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0235463Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0235463Field000Value00 : SourceJson := .number (String.ofList ['5', '8'])
noncomputable def fragment0235463Acc00100 : List (String × SourceJson) := (fragment0235463Field000Key00, fragment0235463Field000Value00) :: fragment0235463Acc00000
noncomputable def fragment0235463Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '8', ',']

theorem object_fragment0235463_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 359) (SourceJson.white (fragment0235463Field000Chars00 ++ tail)) fragment0235463Acc00000 =
      SourceJson.object (fuel + 358) (SourceJson.white tail) fragment0235463Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_000"
  err.flush

noncomputable def fragment0235463Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0235463Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0235463Acc00200 : List (String × SourceJson) := (fragment0235463Field001Key00, fragment0235463Field001Value00) :: fragment0235463Acc00100
noncomputable def fragment0235463Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0235463_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 358) (SourceJson.white (fragment0235463Field001Chars00 ++ tail)) fragment0235463Acc00100 =
      SourceJson.object (fuel + 357) (SourceJson.white tail) fragment0235463Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_001"
  err.flush

noncomputable def fragment0235463Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0235463Field002Value00 : SourceJson := .str (String.ofList ['2', '5', '3', '6', '7', '8', '6', '3', '2', '0', '2', '8', '9', '0', '7', '3', '0', '4', '2', '0', '2', '0', '9', '3', '5', '5', '1', '4', '8', '1', '7', '2', '2', '7', '7', '/', '5', '9', '7', '2', '2', '1', '0', '0', '6', '4', '4', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0235463Acc00300 : List (String × SourceJson) := (fragment0235463Field002Key00, fragment0235463Field002Value00) :: fragment0235463Acc00200
noncomputable def fragment0235463Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '5', '3', '6', '7', '8', '6', '3', '2', '0', '2', '8', '9', '0', '7', '3', '0', '4', '2', '0', '2', '0', '9', '3', '5', '5', '1', '4', '8', '1', '7', '2', '2', '7', '7', '/', '5', '9', '7', '2', '2', '1', '0', '0', '6', '4', '4', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0235463_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 357) (SourceJson.white (fragment0235463Field002Chars00 ++ tail)) fragment0235463Acc00200 =
      SourceJson.object (fuel + 356) (SourceJson.white tail) fragment0235463Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_002"
  err.flush

noncomputable def fragment0235463Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0235463Field003Value00 : SourceJson := .str (String.ofList ['9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0235463Acc00400 : List (String × SourceJson) := (fragment0235463Field003Key00, fragment0235463Field003Value00) :: fragment0235463Acc00300
noncomputable def fragment0235463Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0235463_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 356) (SourceJson.white (fragment0235463Field003Chars00 ++ tail)) fragment0235463Acc00300 =
      SourceJson.object (fuel + 355) (SourceJson.white tail) fragment0235463Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_003"
  err.flush

noncomputable def fragment0235463Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0235463Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0235463Acc00500 : List (String × SourceJson) := (fragment0235463Field004Key00, fragment0235463Field004Value00) :: fragment0235463Acc00400
noncomputable def fragment0235463Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0235463_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 355) (SourceJson.white (fragment0235463Field004Chars00 ++ tail)) fragment0235463Acc00400 =
      SourceJson.object (fuel + 354) (SourceJson.white tail) fragment0235463Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_004"
  err.flush

noncomputable def fragment0235463Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0235463Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '6', '8', '6', '2', '8', '6', '7', '3', '0', '8', '9', '3', '4', '5', '7', '6', '9', '7', '7', '9', '/', '6', '6', '2', '8', '1', '0', '2', '0', '1', '5', '0', '6', '5', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '6', '3', '9', '1', '0', '5', '3', '1', '0', '2', '4', '3', '9', '4', '6', '4', '7', '/', '7', '7', '0', '7', '0', '9', '5', '3', '6', '6', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '4', '8', '3', '1', '3', '7', '2', '9', '5', '5', '6', '1', '9', '5', '1', '/', '1', '6', '0', '0', '9', '9', '0', '8', '2', '4', '8', '9', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '3', '4', '8', '5', '1', '0', '1', '6', '2', '3', '7', '7', '4', '8', '6', '1', '3', '/', '7', '8', '9', '0', '5', '9', '7', '6', '3', '6', '9', '8', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '3', '9', '9', '0', '7', '8', '8', '3', '7', '1', '1', '7', '0', '2', '6', '1', '/', '2', '6', '3', '0', '1', '9', '9', '2', '1', '2', '3', '2', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '2', '1', '0', '6', '1', '9', '3', '4', '4', '7', '3', '1', '7', '4', '0', '3', '7', '/', '5', '0', '2', '1', '2', '8', '9', '4', '0', '5', '3', '5', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '3', '9', '9', '0', '4', '0', '6', '0', '1', '8', '9', '0', '4', '1', '5', '8', '3', '/', '6', '6', '9', '5', '0', '5', '2', '5', '4', '0', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '0', '5', '9', '0', '8', '3', '7', '2', '9', '4', '2', '7', '5', '5', '3', '7', '9', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '9', '6', '7', '3', '5', '9', '3', '5', '3', '2', '5', '4', '4', '2', '6', '5', '9', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '0', '8', '1', '5', '3', '7', '7', '2', '1', '0', '6', '8', '6', '1', '2', '0', '9', '/', '7', '7', '0', '7', '0', '9', '5', '3', '6', '6', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0235463Acc00600 : List (String × SourceJson) := (fragment0235463Field005Key00, fragment0235463Field005Value00) :: fragment0235463Acc00500
noncomputable def fragment0235463Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '8', '6', '2', '8', '6', '7', '3', '0', '8', '9', '3', '4', '5', '7', '6', '9', '7', '7', '9', '/', '6', '6', '2', '8', '1', '0', '2', '0', '1', '5', '0', '6', '5', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '6', '3', '9', '1', '0', '5', '3', '1', '0', '2', '4', '3', '9', '4', '6', '4', '7', '/', '7', '7', '0', '7', '0', '9', '5', '3', '6', '6', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '2', '4', '8', '3', '1', '3', '7', '2', '9', '5', '5', '6', '1', '9', '5', '1', '/', '1', '6', '0', '0', '9', '9', '0', '8', '2', '4', '8', '9', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '3', '4', '8', '5', '1', '0', '1', '6', '2', '3', '7', '7', '4', '8', '6', '1', '3', '/', '7', '8', '9', '0', '5', '9', '7', '6', '3', '6', '9', '8', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '3', '9', '9', '0', '7', '8', '8', '3', '7', '1', '1', '7', '0', '2', '6', '1', '/', '2', '6', '3', '0', '1', '9', '9', '2', '1', '2', '3', '2', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '1', '0', '6', '1', '9', '3', '4', '4', '7', '3', '1', '7', '4', '0', '3', '7', '/', '5', '0', '2', '1', '2', '8', '9', '4', '0', '5', '3', '5', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '3', '9', '9', '0', '4', '0', '6', '0', '1', '8', '9', '0', '4', '1', '5', '8', '3', '/', '6', '6', '9', '5', '0', '5', '2', '5', '4', '0', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '0', '5', '9', '0', '8', '3', '7', '2', '9', '4', '2', '7', '5', '5', '3', '7', '9', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '9', '6', '7', '3', '5', '9', '3', '5', '3', '2', '5', '4', '4', '2', '6', '5', '9', '/', '2', '0', '0', '8', '5', '1', '5', '7', '6', '2', '1', '4', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '0', '8', '1', '5', '3', '7', '7', '2', '1', '0', '6', '8', '6', '1', '2', '0', '9', '/', '7', '7', '0', '7', '0', '9', '5', '3', '6', '6', '3', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0235463_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 354) (SourceJson.white (fragment0235463Field005Chars00 ++ tail)) fragment0235463Acc00500 =
      SourceJson.object (fuel + 353) (SourceJson.white tail) fragment0235463Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_005"
  err.flush

noncomputable def fragment0235463Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0235463Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '0', '6', '7', '6', '0', '7', '6', '5', '0', '9', '6', '3', '9', '8', '2', '3', '9', '3', '2', '4', '9', '7', '9', '8', '8', '0', '1', '6', '0', '8', '9', '3', '9', '8', '0', '6', '0', '0', '8', '7', '1', '2', '5', '/', '9', '3', '3', '4', '7', '8', '3', '5', '4', '4', '9', '9', '5', '6', '8', '8', '3', '9', '8', '1', '2', '6', '7', '2', '1', '0', '6', '5', '4', '4', '4', '1', '1', '5', '7', '9', '1', '4', '0', '2', '9', '7', '0', '3', '5', '6', '6', '8', '1', '1', '9', '5', '7', '6', '6', '4', '9', '1', '4', '0', '2', '2'])
noncomputable def fragment0235463Acc00700 : List (String × SourceJson) := (fragment0235463Field006Key00, fragment0235463Field006Value00) :: fragment0235463Acc00600
noncomputable def fragment0235463Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '4', '0', '6', '7', '6', '0', '7', '6', '5', '0', '9', '6', '3', '9', '8', '2', '3', '9', '3', '2', '4', '9', '7', '9', '8', '8', '0', '1', '6', '0', '8', '9', '3', '9', '8', '0', '6', '0', '0', '8', '7', '1', '2', '5', '/', '9', '3', '3', '4', '7', '8', '3', '5', '4', '4', '9', '9', '5', '6', '8', '8', '3', '9', '8', '1', '2', '6', '7', '2', '1', '0', '6', '5', '4', '4', '4', '1', '1', '5', '7', '9', '1', '4', '0', '2', '9', '7', '0', '3', '5', '6', '6', '8', '1', '1', '9', '5', '7', '6', '6', '4', '9', '1', '4', '0', '2', '2', '"', ',']

theorem object_fragment0235463_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 353) (SourceJson.white (fragment0235463Field006Chars00 ++ tail)) fragment0235463Acc00600 =
      SourceJson.object (fuel + 352) (SourceJson.white tail) fragment0235463Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_006"
  err.flush

noncomputable def fragment0235463Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0235463Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '0', '5', '4', '2', '8', '6', '3', '5', '7', '0', '1', '0', '7', '6', '9', '9', '4', '2', '2', '3', '4', '4', '9', '4', '6', '0', '1', '9', '9', '8', '0', '5', '6', '9', '5', '2', '8', '4', '9', '6', '3', '7', '9', '3', '6', '4', '7', '2', '9', '3', '3', '2', '5', '7', '9', '4', '1', '4', '8', '6', '0', '0', '9', '4', '2', '7', '8', '3', '1', '4', '4', '2', '9', '6', '2', '9', '6', '8', '0', '7', '4', '2', '4', '6', '6', '6', '1', '9', '4', '7', '5', '1', '4', '4', '8', '1', '8', '6', '4', '1', '3', '1', '7', '1', '6', '2', '1', '5', '3', '6', '4', '0', '2', '0', '2', '0', '8', '7', '5', '9', '9', '9', '8', '7', '4', '3', '8', '4', '8', '2', '0', '7', '1', '2', '4', '0', '6', '9', '3', '9', '7', '0', '8', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '8', '6', '5', '0', '1', '8', '8', '0', '8', '9', '5', '4', '3', '9', '6', '7', '9', '4', '8', '9', '3', '2', '0', '5', '4', '1', '7', '7', '5', '7', '8', '1', '8', '9', '0', '6', '1', '4', '9', '0', '4', '5', '9', '9', '3', '3', '9', '0', '0', '6', '1', '1', '6', '8', '8', '1', '4', '8', '9', '7', '4', '0', '1', '5', '4', '4', '4', '7', '6', '0', '4', '4', '7', '5', '5', '5', '1', '8', '1', '0', '7', '3', '0', '9', '2', '6', '4', '4', '6', '4', '5', '6', '3', '7', '8', '2', '6', '8', '7', '4', '6', '3', '5', '8', '9', '2', '2', '3', '4', '6', '3', '6', '6', '0', '1', '7', '1', '0', '4', '5', '8', '5', '8', '5', '9', '1', '1', '7', '6', '9', '4', '2', '2', '9', '0', '2', '7', '1', '7', '4', '5', '5', '0', '4', '1', '1', '3', '1', '6', '0', '1', '6', '2', '7', '5', '2', '0', '5', '3', '0', '4', '8', '1', '3', '2', '9', '7', '8', '9', '4', '7', '3', '2', '0', '7', '4', '4', '6', '6', '0', '7'])
noncomputable def fragment0235463Acc00800 : List (String × SourceJson) := (fragment0235463Field007Key00, fragment0235463Field007Value00) :: fragment0235463Acc00700
noncomputable def fragment0235463Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '0', '5', '4', '2', '8', '6', '3', '5', '7', '0', '1', '0', '7', '6', '9', '9', '4', '2', '2', '3', '4', '4', '9', '4', '6', '0', '1', '9', '9', '8', '0', '5', '6', '9', '5', '2', '8', '4', '9', '6', '3', '7', '9', '3', '6', '4', '7', '2', '9', '3', '3', '2', '5', '7', '9', '4', '1', '4', '8', '6', '0', '0', '9', '4', '2', '7', '8', '3', '1', '4', '4', '2', '9', '6', '2', '9', '6', '8', '0', '7', '4', '2', '4', '6', '6', '6', '1', '9', '4', '7', '5', '1', '4', '4', '8', '1', '8', '6', '4', '1', '3', '1', '7', '1', '6', '2', '1', '5', '3', '6', '4', '0', '2', '0', '2', '0', '8', '7', '5', '9', '9', '9', '8', '7', '4', '3', '8', '4', '8', '2', '0', '7', '1', '2', '4', '0', '6', '9', '3', '9', '7', '0', '8', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '8', '6', '5', '0', '1', '8', '8', '0', '8', '9', '5', '4', '3', '9', '6', '7', '9', '4', '8', '9', '3', '2', '0', '5', '4', '1', '7', '7', '5', '7', '8', '1', '8', '9', '0', '6', '1', '4', '9', '0', '4', '5', '9', '9', '3', '3', '9', '0', '0', '6', '1', '1', '6', '8', '8', '1', '4', '8', '9', '7', '4', '0', '1', '5', '4', '4', '4', '7', '6', '0', '4', '4', '7', '5', '5', '5', '1', '8', '1', '0', '7', '3', '0', '9', '2', '6', '4', '4', '6', '4', '5', '6', '3', '7', '8', '2', '6', '8', '7', '4', '6', '3', '5', '8', '9', '2', '2', '3', '4', '6', '3', '6', '6', '0', '1', '7', '1', '0', '4', '5', '8', '5', '8', '5', '9', '1', '1', '7', '6', '9', '4', '2', '2', '9', '0', '2', '7', '1', '7', '4', '5', '5', '0', '4', '1', '1', '3', '1', '6', '0', '1', '6', '2', '7', '5', '2', '0', '5', '3', '0', '4', '8', '1', '3', '2', '9', '7', '8', '9', '4', '7', '3', '2', '0', '7', '4', '4', '6', '6', '0', '7', '"', ',']

theorem object_fragment0235463_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 352) (SourceJson.white (fragment0235463Field007Chars00 ++ tail)) fragment0235463Acc00700 =
      SourceJson.object (fuel + 351) (SourceJson.white tail) fragment0235463Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_007"
  err.flush

noncomputable def fragment0235463Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0235463Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '7', '8', '8', '7', '1', '4', '6', '0', '3', '4'])
noncomputable def fragment0235463Acc00900 : List (String × SourceJson) := (fragment0235463Field008Key00, fragment0235463Field008Value00) :: fragment0235463Acc00800
noncomputable def fragment0235463Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '3', '7', '8', '8', '7', '1', '4', '6', '0', '3', '4', '"', ',']

theorem object_fragment0235463_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 351) (SourceJson.white (fragment0235463Field008Chars00 ++ tail)) fragment0235463Acc00800 =
      SourceJson.object (fuel + 350) (SourceJson.white tail) fragment0235463Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_008"
  err.flush

noncomputable def fragment0235463Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0235463Field009Value00 : SourceJson := .str (String.ofList ['3', '0', '5', '6', '9', '1', '1', '1', '5', '6', '1', '6', '8'])
noncomputable def fragment0235463Acc01000 : List (String × SourceJson) := (fragment0235463Field009Key00, fragment0235463Field009Value00) :: fragment0235463Acc00900
noncomputable def fragment0235463Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '5', '6', '9', '1', '1', '1', '5', '6', '1', '6', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0235463_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 350) (SourceJson.white (fragment0235463Field009Chars00 ++ tail)) fragment0235463Acc00900 =
      .ok (.obj (fragment0235463Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0235463_object_field_009"
  err.flush

noncomputable def fragment0235463Chars : List Char := '{' :: (fragment0235463Field000Chars00 ++ fragment0235463Field001Chars00 ++ fragment0235463Field002Chars00 ++ fragment0235463Field003Chars00 ++ fragment0235463Field004Chars00 ++ fragment0235463Field005Chars00 ++ fragment0235463Field006Chars00 ++ fragment0235463Field007Chars00 ++ fragment0235463Field008Chars00 ++ fragment0235463Field009Chars00)
noncomputable def fragment0235463Value : SourceJson := .obj (fragment0235463Acc01000.reverse)

theorem value_fragment0235463 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 360) (fragment0235463Chars ++ tail) =
      .ok (fragment0235463Value, tail) := by
  have hinput : fragment0235463Chars ++ tail = '{' :: (fragment0235463Field000Chars00 ++ (fragment0235463Field001Chars00 ++ (fragment0235463Field002Chars00 ++ (fragment0235463Field003Chars00 ++ (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0235463Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 360) (fragment0235463Chars ++ tail) =
        SourceJson.value (fuel + 360) ('{' :: (fragment0235463Field000Chars00 ++ (fragment0235463Field001Chars00 ++ (fragment0235463Field002Chars00 ++ (fragment0235463Field003Chars00 ++ (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 360)) hinput
    _ = SourceJson.object (fuel + 359) (SourceJson.white (fragment0235463Field000Chars00 ++ (fragment0235463Field001Chars00 ++ (fragment0235463Field002Chars00 ++ (fragment0235463Field003Chars00 ++ (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))))))))))) fragment0235463Acc00000 := by rfl
    _ = SourceJson.object (fuel + 358) (SourceJson.white (fragment0235463Field001Chars00 ++ (fragment0235463Field002Chars00 ++ (fragment0235463Field003Chars00 ++ (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail))))))))))) fragment0235463Acc00100 := object_fragment0235463_field_000 fuel (fragment0235463Field001Chars00 ++ (fragment0235463Field002Chars00 ++ (fragment0235463Field003Chars00 ++ (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 357) (SourceJson.white (fragment0235463Field002Chars00 ++ (fragment0235463Field003Chars00 ++ (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))))))))) fragment0235463Acc00200 := object_fragment0235463_field_001 fuel (fragment0235463Field002Chars00 ++ (fragment0235463Field003Chars00 ++ (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 356) (SourceJson.white (fragment0235463Field003Chars00 ++ (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail))))))))) fragment0235463Acc00300 := object_fragment0235463_field_002 fuel (fragment0235463Field003Chars00 ++ (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 355) (SourceJson.white (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))))))) fragment0235463Acc00400 := object_fragment0235463_field_003 fuel (fragment0235463Field004Chars00 ++ (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 354) (SourceJson.white (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail))))))) fragment0235463Acc00500 := object_fragment0235463_field_004 fuel (fragment0235463Field005Chars00 ++ (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 353) (SourceJson.white (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))))) fragment0235463Acc00600 := object_fragment0235463_field_005 fuel (fragment0235463Field006Chars00 ++ (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 352) (SourceJson.white (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail))))) fragment0235463Acc00700 := object_fragment0235463_field_006 fuel (fragment0235463Field007Chars00 ++ (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 351) (SourceJson.white (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))) fragment0235463Acc00800 := object_fragment0235463_field_007 fuel (fragment0235463Field008Chars00 ++ (fragment0235463Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 350) (SourceJson.white (fragment0235463Field009Chars00 ++ (tail))) fragment0235463Acc00900 := object_fragment0235463_field_008 fuel (fragment0235463Field009Chars00 ++ (tail))
    _ = .ok (fragment0235463Value, tail) := object_fragment0235463_field_009 fuel (tail)

noncomputable def fragment0237303Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0237303Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0237303Field000Value00 : SourceJson := .number (String.ofList ['5', '9'])
noncomputable def fragment0237303Acc00100 : List (String × SourceJson) := (fragment0237303Field000Key00, fragment0237303Field000Value00) :: fragment0237303Acc00000
noncomputable def fragment0237303Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '9', ',']

theorem object_fragment0237303_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0237303Field000Chars00 ++ tail)) fragment0237303Acc00000 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0237303Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_000"
  err.flush

noncomputable def fragment0237303Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0237303Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0237303Acc00200 : List (String × SourceJson) := (fragment0237303Field001Key00, fragment0237303Field001Value00) :: fragment0237303Acc00100
noncomputable def fragment0237303Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0237303_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0237303Field001Chars00 ++ tail)) fragment0237303Acc00100 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0237303Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_001"
  err.flush

noncomputable def fragment0237303Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0237303Field002Value00 : SourceJson := .str (String.ofList ['1', '8', '7', '1', '2', '3', '4', '6', '1', '5', '5', '4', '6', '6', '0', '1', '5', '7', '7', '4', '1', '8', '1', '1', '2', '6', '2', '0', '5', '9', '7', '9', '7', '2', '2', '7', '/', '4', '2', '8', '5', '7', '0', '5', '5', '6', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0237303Acc00300 : List (String × SourceJson) := (fragment0237303Field002Key00, fragment0237303Field002Value00) :: fragment0237303Acc00200
noncomputable def fragment0237303Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '8', '7', '1', '2', '3', '4', '6', '1', '5', '5', '4', '6', '6', '0', '1', '5', '7', '7', '4', '1', '8', '1', '1', '2', '6', '2', '0', '5', '9', '7', '9', '7', '2', '2', '7', '/', '4', '2', '8', '5', '7', '0', '5', '5', '6', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0237303_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0237303Field002Chars00 ++ tail)) fragment0237303Acc00200 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0237303Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_002"
  err.flush

noncomputable def fragment0237303Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0237303Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0237303Acc00400 : List (String × SourceJson) := (fragment0237303Field003Key00, fragment0237303Field003Value00) :: fragment0237303Acc00300
noncomputable def fragment0237303Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0237303_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0237303Field003Chars00 ++ tail)) fragment0237303Acc00300 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0237303Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_003"
  err.flush

noncomputable def fragment0237303Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0237303Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0237303Acc00500 : List (String × SourceJson) := (fragment0237303Field004Key00, fragment0237303Field004Value00) :: fragment0237303Acc00400
noncomputable def fragment0237303Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0237303_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0237303Field004Chars00 ++ tail)) fragment0237303Acc00400 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0237303Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_004"
  err.flush

noncomputable def fragment0237303Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0237303Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '9', '5', '0', '2', '7', '5', '5', '0', '9', '/', '1', '9', '9', '2', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '7', '0', '7', '4', '2', '8', '6', '4', '1', '/', '1', '5', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '0', '3', '5', '3', '4', '5', '1', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '9', '1', '8', '0', '1', '1', '1', '1', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '5', '4', '6', '8', '0', '4', '6', '7', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '9', '9', '9', '8', '5', '1', '4', '7', '1', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '9', '0', '2', '8', '4', '0', '9', '2', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '5', '4', '4', '5', '1', '9', '3', '4', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '7', '1', '9', '5', '8', '8', '6', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '0', '2', '7', '7', '7', '0', '2', '8', '1', '/', '4', '7', '8', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0237303Acc00600 : List (String × SourceJson) := (fragment0237303Field005Key00, fragment0237303Field005Value00) :: fragment0237303Acc00500
noncomputable def fragment0237303Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '5', '0', '2', '7', '5', '5', '0', '9', '/', '1', '9', '9', '2', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '7', '0', '7', '4', '2', '8', '6', '4', '1', '/', '1', '5', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '0', '3', '5', '3', '4', '5', '1', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '9', '1', '8', '0', '1', '1', '1', '1', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '5', '4', '6', '8', '0', '4', '6', '7', '9', '/', '6', '8', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '9', '9', '9', '8', '5', '1', '4', '7', '1', '/', '4', '3', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '9', '0', '2', '8', '4', '0', '9', '2', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '5', '4', '4', '5', '1', '9', '3', '4', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '0', '7', '1', '9', '5', '8', '8', '6', '1', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '0', '2', '7', '7', '7', '0', '2', '8', '1', '/', '4', '7', '8', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0237303_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0237303Field005Chars00 ++ tail)) fragment0237303Acc00500 =
      SourceJson.object (fuel + 193) (SourceJson.white tail) fragment0237303Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_005"
  err.flush

noncomputable def fragment0237303Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0237303Field006Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '1', '9', '2', '0', '5', '9', '6', '5', '6', '4', '5', '4', '7', '8', '0', '0', '6', '4', '9', '6', '3', '6', '7', '7', '5', '8', '3', '2', '3', '3', '5', '9', '7', '2', '7', '2', '8', '3', '2', '0', '0', '0', '/', '1', '0', '5', '0', '8', '9', '0', '2', '4', '8', '1', '8', '0', '0', '5', '6', '0', '1', '6', '8', '4', '9', '4', '0', '5', '7', '4', '9', '7', '4', '7', '1', '4', '4', '6', '7', '6', '1', '1', '7', '0', '1', '0', '9', '9', '5', '1', '5', '3', '2', '9', '9', '6', '1', '1', '3', '1', '7', '8', '3', '9', '9'])
noncomputable def fragment0237303Acc00700 : List (String × SourceJson) := (fragment0237303Field006Key00, fragment0237303Field006Value00) :: fragment0237303Acc00600
noncomputable def fragment0237303Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '7', '5', '1', '9', '2', '0', '5', '9', '6', '5', '6', '4', '5', '4', '7', '8', '0', '0', '6', '4', '9', '6', '3', '6', '7', '7', '5', '8', '3', '2', '3', '3', '5', '9', '7', '2', '7', '2', '8', '3', '2', '0', '0', '0', '/', '1', '0', '5', '0', '8', '9', '0', '2', '4', '8', '1', '8', '0', '0', '5', '6', '0', '1', '6', '8', '4', '9', '4', '0', '5', '7', '4', '9', '7', '4', '7', '1', '4', '4', '6', '7', '6', '1', '1', '7', '0', '1', '0', '9', '9', '5', '1', '5', '3', '2', '9', '9', '6', '1', '1', '3', '1', '7', '8', '3', '9', '9', '"', ',']

theorem object_fragment0237303_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment0237303Field006Chars00 ++ tail)) fragment0237303Acc00600 =
      SourceJson.object (fuel + 192) (SourceJson.white tail) fragment0237303Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_006"
  err.flush

noncomputable def fragment0237303Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0237303Field007Value00 : SourceJson := .str (String.ofList ['3', '7', '4', '2', '4', '2', '2', '9', '1', '9', '0', '5', '5', '4', '8', '7', '8', '5', '7', '6', '6', '0', '6', '7', '7', '2', '1', '7', '8', '6', '7', '4', '7', '7', '2', '6', '5', '7', '1', '3', '8', '6', '1', '5', '4', '7', '1', '4', '6', '7', '0', '1', '3', '3', '0', '3', '1', '7', '5', '6', '8', '0', '7', '5', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '1', '1', '4', '1', '3', '2', '2', '2', '2', '1', '8', '4', '1', '5', '5', '7', '2', '8', '2', '6', '1', '7', '5', '9', '9', '3', '9', '2', '7', '3', '0', '6', '9', '3', '0', '3', '7', '1', '6', '7', '7', '5', '7', '0', '3', '3', '0', '2', '3', '6', '5', '4', '1', '2', '6', '8', '6', '7', '9', '0', '0', '1', '4', '1', '4', '8', '3', '8', '7', '5', '8', '1', '9', '9', '2', '9', '1', '8', '6', '4', '3', '1', '2', '5', '6', '6', '5', '4', '4', '4', '4', '4', '0', '4', '0', '0', '4', '8', '8', '9'])
noncomputable def fragment0237303Acc00800 : List (String × SourceJson) := (fragment0237303Field007Key00, fragment0237303Field007Value00) :: fragment0237303Acc00700
noncomputable def fragment0237303Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '7', '4', '2', '4', '2', '2', '9', '1', '9', '0', '5', '5', '4', '8', '7', '8', '5', '7', '6', '6', '0', '6', '7', '7', '2', '1', '7', '8', '6', '7', '4', '7', '7', '2', '6', '5', '7', '1', '3', '8', '6', '1', '5', '4', '7', '1', '4', '6', '7', '0', '1', '3', '3', '0', '3', '1', '7', '5', '6', '8', '0', '7', '5', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '1', '1', '4', '1', '3', '2', '2', '2', '2', '1', '8', '4', '1', '5', '5', '7', '2', '8', '2', '6', '1', '7', '5', '9', '9', '3', '9', '2', '7', '3', '0', '6', '9', '3', '0', '3', '7', '1', '6', '7', '7', '5', '7', '0', '3', '3', '0', '2', '3', '6', '5', '4', '1', '2', '6', '8', '6', '7', '9', '0', '0', '1', '4', '1', '4', '8', '3', '8', '7', '5', '8', '1', '9', '9', '2', '9', '1', '8', '6', '4', '3', '1', '2', '5', '6', '6', '5', '4', '4', '4', '4', '4', '0', '4', '0', '0', '4', '8', '8', '9', '"', ',']

theorem object_fragment0237303_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (fragment0237303Field007Chars00 ++ tail)) fragment0237303Acc00700 =
      SourceJson.object (fuel + 191) (SourceJson.white tail) fragment0237303Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_007"
  err.flush

noncomputable def fragment0237303Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0237303Field008Value00 : SourceJson := .str (String.ofList ['4', '3', '3', '6', '4', '5', '7', '5', '9', '4', '7', '2', '0'])
noncomputable def fragment0237303Acc00900 : List (String × SourceJson) := (fragment0237303Field008Key00, fragment0237303Field008Value00) :: fragment0237303Acc00800
noncomputable def fragment0237303Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '3', '3', '6', '4', '5', '7', '5', '9', '4', '7', '2', '0', '"', ',']

theorem object_fragment0237303_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 191) (SourceJson.white (fragment0237303Field008Chars00 ++ tail)) fragment0237303Acc00800 =
      SourceJson.object (fuel + 190) (SourceJson.white tail) fragment0237303Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_008"
  err.flush

noncomputable def fragment0237303Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0237303Field009Value00 : SourceJson := .str (String.ofList ['1', '5', '5', '1', '2', '3', '5', '9', '5', '3', '4', '8', '9', '4'])
noncomputable def fragment0237303Acc01000 : List (String × SourceJson) := (fragment0237303Field009Key00, fragment0237303Field009Value00) :: fragment0237303Acc00900
noncomputable def fragment0237303Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '5', '1', '2', '3', '5', '9', '5', '3', '4', '8', '9', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0237303_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 190) (SourceJson.white (fragment0237303Field009Chars00 ++ tail)) fragment0237303Acc00900 =
      .ok (.obj (fragment0237303Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0237303_object_field_009"
  err.flush

noncomputable def fragment0237303Chars : List Char := '{' :: (fragment0237303Field000Chars00 ++ fragment0237303Field001Chars00 ++ fragment0237303Field002Chars00 ++ fragment0237303Field003Chars00 ++ fragment0237303Field004Chars00 ++ fragment0237303Field005Chars00 ++ fragment0237303Field006Chars00 ++ fragment0237303Field007Chars00 ++ fragment0237303Field008Chars00 ++ fragment0237303Field009Chars00)
noncomputable def fragment0237303Value : SourceJson := .obj (fragment0237303Acc01000.reverse)

theorem value_fragment0237303 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 200) (fragment0237303Chars ++ tail) =
      .ok (fragment0237303Value, tail) := by
  have hinput : fragment0237303Chars ++ tail = '{' :: (fragment0237303Field000Chars00 ++ (fragment0237303Field001Chars00 ++ (fragment0237303Field002Chars00 ++ (fragment0237303Field003Chars00 ++ (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0237303Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 200) (fragment0237303Chars ++ tail) =
        SourceJson.value (fuel + 200) ('{' :: (fragment0237303Field000Chars00 ++ (fragment0237303Field001Chars00 ++ (fragment0237303Field002Chars00 ++ (fragment0237303Field003Chars00 ++ (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 200)) hinput
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0237303Field000Chars00 ++ (fragment0237303Field001Chars00 ++ (fragment0237303Field002Chars00 ++ (fragment0237303Field003Chars00 ++ (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))))))))))) fragment0237303Acc00000 := by rfl
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0237303Field001Chars00 ++ (fragment0237303Field002Chars00 ++ (fragment0237303Field003Chars00 ++ (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail))))))))))) fragment0237303Acc00100 := object_fragment0237303_field_000 fuel (fragment0237303Field001Chars00 ++ (fragment0237303Field002Chars00 ++ (fragment0237303Field003Chars00 ++ (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0237303Field002Chars00 ++ (fragment0237303Field003Chars00 ++ (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))))))))) fragment0237303Acc00200 := object_fragment0237303_field_001 fuel (fragment0237303Field002Chars00 ++ (fragment0237303Field003Chars00 ++ (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0237303Field003Chars00 ++ (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail))))))))) fragment0237303Acc00300 := object_fragment0237303_field_002 fuel (fragment0237303Field003Chars00 ++ (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))))))) fragment0237303Acc00400 := object_fragment0237303_field_003 fuel (fragment0237303Field004Chars00 ++ (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail))))))) fragment0237303Acc00500 := object_fragment0237303_field_004 fuel (fragment0237303Field005Chars00 ++ (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))))) fragment0237303Acc00600 := object_fragment0237303_field_005 fuel (fragment0237303Field006Chars00 ++ (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 192) (SourceJson.white (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail))))) fragment0237303Acc00700 := object_fragment0237303_field_006 fuel (fragment0237303Field007Chars00 ++ (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 191) (SourceJson.white (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))) fragment0237303Acc00800 := object_fragment0237303_field_007 fuel (fragment0237303Field008Chars00 ++ (fragment0237303Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 190) (SourceJson.white (fragment0237303Field009Chars00 ++ (tail))) fragment0237303Acc00900 := object_fragment0237303_field_008 fuel (fragment0237303Field009Chars00 ++ (tail))
    _ = .ok (fragment0237303Value, tail) := object_fragment0237303_field_009 fuel (tail)

noncomputable def fragment0238823Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0238823Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0238823Field000Value00 : SourceJson := .number (String.ofList ['6', '0'])
noncomputable def fragment0238823Acc00100 : List (String × SourceJson) := (fragment0238823Field000Key00, fragment0238823Field000Value00) :: fragment0238823Acc00000
noncomputable def fragment0238823Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '0', ',']

theorem object_fragment0238823_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0238823Field000Chars00 ++ tail)) fragment0238823Acc00000 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0238823Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_000"
  err.flush

noncomputable def fragment0238823Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0238823Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0238823Acc00200 : List (String × SourceJson) := (fragment0238823Field001Key00, fragment0238823Field001Value00) :: fragment0238823Acc00100
noncomputable def fragment0238823Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0238823_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0238823Field001Chars00 ++ tail)) fragment0238823Acc00100 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0238823Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_001"
  err.flush

noncomputable def fragment0238823Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0238823Field002Value00 : SourceJson := .str (String.ofList ['7', '8', '9', '2', '4', '5', '1', '3', '2', '1', '7', '2', '4', '4', '1', '5', '4', '3', '8', '5', '6', '1', '2', '0', '7', '9', '1', '8', '3', '7', '7', '2', '1', '9', '/', '1', '9', '9', '6', '4', '4', '6', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0238823Acc00300 : List (String × SourceJson) := (fragment0238823Field002Key00, fragment0238823Field002Value00) :: fragment0238823Acc00200
noncomputable def fragment0238823Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '8', '9', '2', '4', '5', '1', '3', '2', '1', '7', '2', '4', '4', '1', '5', '4', '3', '8', '5', '6', '1', '2', '0', '7', '9', '1', '8', '3', '7', '7', '2', '1', '9', '/', '1', '9', '9', '6', '4', '4', '6', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0238823_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0238823Field002Chars00 ++ tail)) fragment0238823Acc00200 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0238823Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_002"
  err.flush

noncomputable def fragment0238823Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0238823Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0238823Acc00400 : List (String × SourceJson) := (fragment0238823Field003Key00, fragment0238823Field003Value00) :: fragment0238823Acc00300
noncomputable def fragment0238823Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0238823_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0238823Field003Chars00 ++ tail)) fragment0238823Acc00300 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0238823Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_003"
  err.flush

noncomputable def fragment0238823Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0238823Field004Value00 : SourceJson := .arr [.str (String.ofList ['4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '7', '1', '7', '0', '7', '/', '1', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0238823Acc00500 : List (String × SourceJson) := (fragment0238823Field004Key00, fragment0238823Field004Value00) :: fragment0238823Acc00400
noncomputable def fragment0238823Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '8', '7', '9', '/', '5', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '7', '1', '7', '0', '7', '/', '1', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0238823_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0238823Field004Chars00 ++ tail)) fragment0238823Acc00400 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0238823Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_004"
  err.flush

noncomputable def fragment0238823Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0238823Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '7', '7', '8', '2', '9', '9', '8', '5', '0', '9', '/', '4', '5', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '3', '8', '4', '4', '9', '1', '2', '4', '3', '/', '4', '5', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '3', '9', '3', '9', '5', '9', '7', '2', '3', '/', '3', '4', '1', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '8', '5', '4', '3', '6', '7', '4', '1', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '1', '1', '1', '9', '5', '4', '5', '3', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '1', '5', '1', '2', '9', '0', '9', '/', '7', '7', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '9', '9', '1', '2', '2', '3', '1', '1', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '2', '0', '9', '9', '3', '4', '1', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '8', '3', '4', '5', '0', '2', '1', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '3', '3', '3', '1', '6', '0', '2', '8', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0238823Acc00600 : List (String × SourceJson) := (fragment0238823Field005Key00, fragment0238823Field005Value00) :: fragment0238823Acc00500
noncomputable def fragment0238823Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '7', '8', '2', '9', '9', '8', '5', '0', '9', '/', '4', '5', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '3', '8', '4', '4', '9', '1', '2', '4', '3', '/', '4', '5', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '3', '9', '3', '9', '5', '9', '7', '2', '3', '/', '3', '4', '1', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '8', '5', '4', '3', '6', '7', '4', '1', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '1', '1', '1', '9', '5', '4', '5', '3', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '1', '5', '1', '2', '9', '0', '9', '/', '7', '7', '6', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '9', '9', '1', '2', '2', '3', '1', '1', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '2', '0', '9', '9', '3', '4', '1', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '8', '3', '4', '5', '0', '2', '1', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '3', '3', '3', '1', '6', '0', '2', '8', '3', '/', '1', '3', '6', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0238823_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0238823Field005Chars00 ++ tail)) fragment0238823Acc00500 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0238823Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_005"
  err.flush

noncomputable def fragment0238823Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0238823Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '6', '6', '3', '4', '1', '3', '0', '5', '0', '6', '5', '7', '1', '5', '1', '2', '9', '8', '3', '6', '8', '3', '0', '2', '8', '1', '7', '0', '2', '3', '5', '9', '0', '1', '8', '3', '0', '6', '2', '7', '3', '2', '8', '0', '0', '/', '2', '5', '7', '3', '8', '5', '7', '8', '3', '7', '8', '0', '2', '7', '0', '4', '7', '5', '9', '7', '7', '5', '0', '7', '9', '4', '1', '7', '6', '7', '0', '5', '3', '9', '6', '3', '8', '8', '1', '2', '8', '5', '0', '0', '3', '4', '3', '0', '3', '6', '8', '5', '5', '6', '0', '9', '3', '0', '9', '6', '5', '2', '7'])
noncomputable def fragment0238823Acc00700 : List (String × SourceJson) := (fragment0238823Field006Key00, fragment0238823Field006Value00) :: fragment0238823Acc00600
noncomputable def fragment0238823Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '6', '6', '3', '4', '1', '3', '0', '5', '0', '6', '5', '7', '1', '5', '1', '2', '9', '8', '3', '6', '8', '3', '0', '2', '8', '1', '7', '0', '2', '3', '5', '9', '0', '1', '8', '3', '0', '6', '2', '7', '3', '2', '8', '0', '0', '/', '2', '5', '7', '3', '8', '5', '7', '8', '3', '7', '8', '0', '2', '7', '0', '4', '7', '5', '9', '7', '7', '5', '0', '7', '9', '4', '1', '7', '6', '7', '0', '5', '3', '9', '6', '3', '8', '8', '1', '2', '8', '5', '0', '0', '3', '4', '3', '0', '3', '6', '8', '5', '5', '6', '0', '9', '3', '0', '9', '6', '5', '2', '7', '"', ',']

theorem object_fragment0238823_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0238823Field006Chars00 ++ tail)) fragment0238823Acc00600 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0238823Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_006"
  err.flush

noncomputable def fragment0238823Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0238823Field007Value00 : SourceJson := .str (String.ofList ['1', '9', '0', '9', '1', '2', '6', '5', '5', '4', '4', '6', '1', '0', '1', '4', '0', '6', '7', '0', '0', '6', '8', '9', '6', '7', '5', '2', '6', '1', '5', '1', '5', '8', '2', '4', '2', '5', '7', '8', '8', '9', '1', '0', '3', '6', '5', '7', '1', '9', '8', '7', '2', '3', '2', '1', '4', '4', '5', '5', '5', '1', '8', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '2', '2', '9', '3', '5', '8', '7', '3', '5', '5', '0', '3', '5', '2', '3', '0', '0', '6', '4', '6', '0', '2', '5', '7', '3', '2', '4', '4', '7', '4', '3', '5', '5', '9', '3', '4', '9', '9', '0', '1', '8', '5', '3', '2', '0', '8', '2', '5', '0', '0', '7', '6', '3', '8', '5', '8', '5', '6', '4', '5', '9', '7', '0', '5', '1', '1', '2', '6', '1', '5', '5', '5', '2', '7', '9', '1', '8', '4', '8', '3', '4', '8', '9', '9', '9', '4', '4', '4', '2', '6', '0', '4', '8', '8', '2', '2', '6', '8', '7', '2', '7', '7'])
noncomputable def fragment0238823Acc00800 : List (String × SourceJson) := (fragment0238823Field007Key00, fragment0238823Field007Value00) :: fragment0238823Acc00700
noncomputable def fragment0238823Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '0', '9', '1', '2', '6', '5', '5', '4', '4', '6', '1', '0', '1', '4', '0', '6', '7', '0', '0', '6', '8', '9', '6', '7', '5', '2', '6', '1', '5', '1', '5', '8', '2', '4', '2', '5', '7', '8', '8', '9', '1', '0', '3', '6', '5', '7', '1', '9', '8', '7', '2', '3', '2', '1', '4', '4', '5', '5', '5', '1', '8', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '2', '2', '9', '3', '5', '8', '7', '3', '5', '5', '0', '3', '5', '2', '3', '0', '0', '6', '4', '6', '0', '2', '5', '7', '3', '2', '4', '4', '7', '4', '3', '5', '5', '9', '3', '4', '9', '9', '0', '1', '8', '5', '3', '2', '0', '8', '2', '5', '0', '0', '7', '6', '3', '8', '5', '8', '5', '6', '4', '5', '9', '7', '0', '5', '1', '1', '2', '6', '1', '5', '5', '5', '2', '7', '9', '1', '8', '4', '8', '3', '4', '8', '9', '9', '9', '4', '4', '4', '2', '6', '0', '4', '8', '8', '2', '2', '6', '8', '7', '2', '7', '7', '"', ',']

theorem object_fragment0238823_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0238823Field007Chars00 ++ tail)) fragment0238823Acc00700 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0238823Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_007"
  err.flush

noncomputable def fragment0238823Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0238823Field008Value00 : SourceJson := .str (String.ofList ['4', '2', '0', '5', '8', '5', '4', '3', '1', '6', '3', '4', '0'])
noncomputable def fragment0238823Acc00900 : List (String × SourceJson) := (fragment0238823Field008Key00, fragment0238823Field008Value00) :: fragment0238823Acc00800
noncomputable def fragment0238823Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '0', '5', '8', '5', '4', '3', '1', '6', '3', '4', '0', '"', ',']

theorem object_fragment0238823_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0238823Field008Chars00 ++ tail)) fragment0238823Acc00800 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0238823Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_008"
  err.flush

noncomputable def fragment0238823Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0238823Field009Value00 : SourceJson := .str (String.ofList ['1', '4', '7', '8', '6', '5', '1', '7', '2', '0', '2', '8', '9', '7'])
noncomputable def fragment0238823Acc01000 : List (String × SourceJson) := (fragment0238823Field009Key00, fragment0238823Field009Value00) :: fragment0238823Acc00900
noncomputable def fragment0238823Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '7', '8', '6', '5', '1', '7', '2', '0', '2', '8', '9', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0238823_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0238823Field009Chars00 ++ tail)) fragment0238823Acc00900 =
      .ok (.obj (fragment0238823Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0238823_object_field_009"
  err.flush

noncomputable def fragment0238823Chars : List Char := '{' :: (fragment0238823Field000Chars00 ++ fragment0238823Field001Chars00 ++ fragment0238823Field002Chars00 ++ fragment0238823Field003Chars00 ++ fragment0238823Field004Chars00 ++ fragment0238823Field005Chars00 ++ fragment0238823Field006Chars00 ++ fragment0238823Field007Chars00 ++ fragment0238823Field008Chars00 ++ fragment0238823Field009Chars00)
noncomputable def fragment0238823Value : SourceJson := .obj (fragment0238823Acc01000.reverse)

theorem value_fragment0238823 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 204) (fragment0238823Chars ++ tail) =
      .ok (fragment0238823Value, tail) := by
  have hinput : fragment0238823Chars ++ tail = '{' :: (fragment0238823Field000Chars00 ++ (fragment0238823Field001Chars00 ++ (fragment0238823Field002Chars00 ++ (fragment0238823Field003Chars00 ++ (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0238823Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 204) (fragment0238823Chars ++ tail) =
        SourceJson.value (fuel + 204) ('{' :: (fragment0238823Field000Chars00 ++ (fragment0238823Field001Chars00 ++ (fragment0238823Field002Chars00 ++ (fragment0238823Field003Chars00 ++ (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 204)) hinput
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0238823Field000Chars00 ++ (fragment0238823Field001Chars00 ++ (fragment0238823Field002Chars00 ++ (fragment0238823Field003Chars00 ++ (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))))))))))) fragment0238823Acc00000 := by rfl
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0238823Field001Chars00 ++ (fragment0238823Field002Chars00 ++ (fragment0238823Field003Chars00 ++ (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail))))))))))) fragment0238823Acc00100 := object_fragment0238823_field_000 fuel (fragment0238823Field001Chars00 ++ (fragment0238823Field002Chars00 ++ (fragment0238823Field003Chars00 ++ (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0238823Field002Chars00 ++ (fragment0238823Field003Chars00 ++ (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))))))))) fragment0238823Acc00200 := object_fragment0238823_field_001 fuel (fragment0238823Field002Chars00 ++ (fragment0238823Field003Chars00 ++ (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0238823Field003Chars00 ++ (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail))))))))) fragment0238823Acc00300 := object_fragment0238823_field_002 fuel (fragment0238823Field003Chars00 ++ (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))))))) fragment0238823Acc00400 := object_fragment0238823_field_003 fuel (fragment0238823Field004Chars00 ++ (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail))))))) fragment0238823Acc00500 := object_fragment0238823_field_004 fuel (fragment0238823Field005Chars00 ++ (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))))) fragment0238823Acc00600 := object_fragment0238823_field_005 fuel (fragment0238823Field006Chars00 ++ (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail))))) fragment0238823Acc00700 := object_fragment0238823_field_006 fuel (fragment0238823Field007Chars00 ++ (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))) fragment0238823Acc00800 := object_fragment0238823_field_007 fuel (fragment0238823Field008Chars00 ++ (fragment0238823Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0238823Field009Chars00 ++ (tail))) fragment0238823Acc00900 := object_fragment0238823_field_008 fuel (fragment0238823Field009Chars00 ++ (tail))
    _ = .ok (fragment0238823Value, tail) := object_fragment0238823_field_009 fuel (tail)

noncomputable def fragment0240346Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0240346Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0240346Field000Value00 : SourceJson := .number (String.ofList ['6', '1'])
noncomputable def fragment0240346Acc00100 : List (String × SourceJson) := (fragment0240346Field000Key00, fragment0240346Field000Value00) :: fragment0240346Acc00000
noncomputable def fragment0240346Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '1', ',']

theorem object_fragment0240346_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 484) (SourceJson.white (fragment0240346Field000Chars00 ++ tail)) fragment0240346Acc00000 =
      SourceJson.object (fuel + 483) (SourceJson.white tail) fragment0240346Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_000"
  err.flush

noncomputable def fragment0240346Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0240346Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0240346Acc00200 : List (String × SourceJson) := (fragment0240346Field001Key00, fragment0240346Field001Value00) :: fragment0240346Acc00100
noncomputable def fragment0240346Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0240346_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 483) (SourceJson.white (fragment0240346Field001Chars00 ++ tail)) fragment0240346Acc00100 =
      SourceJson.object (fuel + 482) (SourceJson.white tail) fragment0240346Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_001"
  err.flush

noncomputable def fragment0240346Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0240346Field002Value00 : SourceJson := .str (String.ofList ['4', '7', '8', '0', '2', '5', '2', '2', '9', '2', '8', '3', '4', '8', '6', '2', '3', '4', '6', '9', '1', '0', '1', '9', '6', '2', '1', '6', '9', '1', '6', '2', '3', '9', '2', '9', '4', '6', '4', '3', '/', '2', '6', '8', '1', '1', '3', '3', '8', '6', '5', '6', '2', '2', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0240346Acc00300 : List (String × SourceJson) := (fragment0240346Field002Key00, fragment0240346Field002Value00) :: fragment0240346Acc00200
noncomputable def fragment0240346Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '7', '8', '0', '2', '5', '2', '2', '9', '2', '8', '3', '4', '8', '6', '2', '3', '4', '6', '9', '1', '0', '1', '9', '6', '2', '1', '6', '9', '1', '6', '2', '3', '9', '2', '9', '4', '6', '4', '3', '/', '2', '6', '8', '1', '1', '3', '3', '8', '6', '5', '6', '2', '2', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0240346_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 482) (SourceJson.white (fragment0240346Field002Chars00 ++ tail)) fragment0240346Acc00200 =
      SourceJson.object (fuel + 481) (SourceJson.white tail) fragment0240346Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_002"
  err.flush

noncomputable def fragment0240346Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0240346Field003Value00 : SourceJson := .str (String.ofList ['1', '5', '4', '4', '2', '3', '4', '4', '5', '9', '/', '5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0'])
noncomputable def fragment0240346Acc00400 : List (String × SourceJson) := (fragment0240346Field003Key00, fragment0240346Field003Value00) :: fragment0240346Acc00300
noncomputable def fragment0240346Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '5', '4', '4', '2', '3', '4', '4', '5', '9', '/', '5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0240346_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 481) (SourceJson.white (fragment0240346Field003Chars00 ++ tail)) fragment0240346Acc00300 =
      SourceJson.object (fuel + 480) (SourceJson.white tail) fragment0240346Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_003"
  err.flush

noncomputable def fragment0240346Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0240346Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0240346Acc00500 : List (String × SourceJson) := (fragment0240346Field004Key00, fragment0240346Field004Value00) :: fragment0240346Acc00400
noncomputable def fragment0240346Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0240346_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 480) (SourceJson.white (fragment0240346Field004Chars00 ++ tail)) fragment0240346Acc00400 =
      SourceJson.object (fuel + 479) (SourceJson.white tail) fragment0240346Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_004"
  err.flush

noncomputable def fragment0240346Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0240346Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '4', '3', '8', '7', '6', '3', '4', '3', '1', '4', '0', '9', '8', '7', '2', '0', '6', '8', '8', '5', '2', '7', '4', '9', '3', '/', '3', '9', '7', '1', '0', '5', '2', '1', '9', '3', '5', '8', '4', '2', '7', '3', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '0', '7', '5', '7', '9', '2', '6', '0', '3', '0', '4', '5', '8', '3', '1', '8', '5', '4', '5', '5', '4', '1', '/', '2', '8', '3', '6', '4', '6', '5', '8', '5', '2', '5', '6', '0', '1', '9', '5', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '9', '1', '8', '2', '7', '4', '4', '3', '9', '6', '0', '8', '6', '7', '1', '6', '1', '3', '2', '4', '9', '6', '7', '/', '7', '9', '4', '2', '1', '0', '4', '3', '8', '7', '1', '6', '8', '5', '4', '6', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '0', '2', '9', '5', '5', '9', '7', '3', '4', '9', '7', '1', '2', '2', '2', '4', '8', '2', '9', '9', '6', '9', '1', '/', '4', '4', '1', '2', '2', '8', '0', '2', '1', '5', '0', '9', '3', '6', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '3', '6', '9', '3', '7', '0', '1', '0', '0', '4', '2', '2', '0', '8', '0', '5', '9', '2', '4', '8', '1', '9', '3', '/', '1', '3', '2', '3', '6', '8', '4', '0', '6', '4', '5', '2', '8', '0', '9', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '9', '5', '1', '9', '4', '5', '3', '4', '2', '8', '0', '1', '6', '4', '2', '6', '2', '7', '7', '0', '3', '3', '/', '3', '6', '1', '0', '0', '4', '7', '4', '4', '8', '7', '1', '2', '9', '7', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '0', '1', '2', '5', '6', '9', '0', '1', '3', '3', '3', '8', '9', '6', '1', '3', '1', '8', '2', '6', '1', '6', '3', '/', '7', '2', '2', '0', '0', '9', '4', '8', '9', '7', '4', '2', '5', '9', '5', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '5', '4', '6', '3', '0', '2', '2', '3', '6', '3', '6', '6', '3', '1', '4', '2', '8', '2', '7', '6', '3', '/', '1', '1', '8', '3', '6', '2', '2', '1', '1', '4', '3', '3', '2', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '8', '7', '4', '1', '5', '1', '2', '9', '7', '2', '3', '9', '0', '2', '1', '0', '4', '9', '7', '1', '5', '9', '/', '3', '6', '1', '0', '0', '4', '7', '4', '4', '8', '7', '1', '2', '9', '7', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '9', '9', '4', '8', '6', '4', '0', '6', '7', '3', '1', '6', '7', '4', '2', '6', '3', '4', '3', '9', '2', '7', '/', '2', '8', '3', '6', '4', '6', '5', '8', '5', '2', '5', '6', '0', '1', '9', '5', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0240346Acc00600 : List (String × SourceJson) := (fragment0240346Field005Key00, fragment0240346Field005Value00) :: fragment0240346Acc00500
noncomputable def fragment0240346Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '3', '8', '7', '6', '3', '4', '3', '1', '4', '0', '9', '8', '7', '2', '0', '6', '8', '8', '5', '2', '7', '4', '9', '3', '/', '3', '9', '7', '1', '0', '5', '2', '1', '9', '3', '5', '8', '4', '2', '7', '3', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '0', '7', '5', '7', '9', '2', '6', '0', '3', '0', '4', '5', '8', '3', '1', '8', '5', '4', '5', '5', '4', '1', '/', '2', '8', '3', '6', '4', '6', '5', '8', '5', '2', '5', '6', '0', '1', '9', '5', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '9', '1', '8', '2', '7', '4', '4', '3', '9', '6', '0', '8', '6', '7', '1', '6', '1', '3', '2', '4', '9', '6', '7', '/', '7', '9', '4', '2', '1', '0', '4', '3', '8', '7', '1', '6', '8', '5', '4', '6', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '0', '2', '9', '5', '5', '9', '7', '3', '4', '9', '7', '1', '2', '2', '2', '4', '8', '2', '9', '9', '6', '9', '1', '/', '4', '4', '1', '2', '2', '8', '0', '2', '1', '5', '0', '9', '3', '6', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '3', '6', '9', '3', '7', '0', '1', '0', '0', '4', '2', '2', '0', '8', '0', '5', '9', '2', '4', '8', '1', '9', '3', '/', '1', '3', '2', '3', '6', '8', '4', '0', '6', '4', '5', '2', '8', '0', '9', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '9', '5', '1', '9', '4', '5', '3', '4', '2', '8', '0', '1', '6', '4', '2', '6', '2', '7', '7', '0', '3', '3', '/', '3', '6', '1', '0', '0', '4', '7', '4', '4', '8', '7', '1', '2', '9', '7', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '0', '1', '2', '5', '6', '9', '0', '1', '3', '3', '3', '8', '9', '6', '1', '3', '1', '8', '2', '6', '1', '6', '3', '/', '7', '2', '2', '0', '0', '9', '4', '8', '9', '7', '4', '2', '5', '9', '5', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '5', '4', '6', '3', '0', '2', '2', '3', '6', '3', '6', '6', '3', '1', '4', '2', '8', '2', '7', '6', '3', '/', '1', '1', '8', '3', '6', '2', '2', '1', '1', '4', '3', '3', '2', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '8', '7', '4', '1', '5', '1', '2', '9', '7', '2', '3', '9', '0', '2', '1', '0', '4', '9', '7', '1', '5', '9', '/', '3', '6', '1', '0', '0', '4', '7', '4', '4', '8', '7', '1', '2', '9', '7', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '9', '9', '4', '8', '6', '4', '0', '6', '7', '3', '1', '6', '7', '4', '2', '6', '3', '4', '3', '9', '2', '7', '/', '2', '8', '3', '6', '4', '6', '5', '8', '5', '2', '5', '6', '0', '1', '9', '5', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0240346_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 479) (SourceJson.white (fragment0240346Field005Chars00 ++ tail)) fragment0240346Acc00500 =
      SourceJson.object (fuel + 478) (SourceJson.white tail) fragment0240346Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_005"
  err.flush

noncomputable def fragment0240346Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0240346Field006Value00 : SourceJson := .str (String.ofList ['6', '9', '2', '7', '7', '2', '7', '0', '7', '9', '2', '1', '7', '8', '0', '3', '9', '9', '6', '9', '3', '8', '9', '6', '9', '8', '9', '1', '3', '3', '4', '6', '1', '7', '9', '5', '6', '0', '9', '4', '2', '7', '6', '2', '9', '6', '0', '8', '1', '0', '7', '1', '4', '6', '8', '7', '5', '/', '6', '1', '3', '9', '6', '1', '0', '6', '7', '9', '0', '4', '7', '7', '7', '4', '8', '6', '8', '5', '6', '2', '5', '6', '4', '6', '3', '2', '2', '3', '7', '6', '0', '3', '2', '7', '0', '7', '0', '6', '1', '2', '9', '8', '1', '3', '6', '9', '6', '5', '7', '8', '2', '9', '5', '9', '5', '4', '0', '2', '9', '8', '9', '2', '4', '6', '1', '2', '0', '6', '4'])
noncomputable def fragment0240346Acc00700 : List (String × SourceJson) := (fragment0240346Field006Key00, fragment0240346Field006Value00) :: fragment0240346Acc00600
noncomputable def fragment0240346Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '9', '2', '7', '7', '2', '7', '0', '7', '9', '2', '1', '7', '8', '0', '3', '9', '9', '6', '9', '3', '8', '9', '6', '9', '8', '9', '1', '3', '3', '4', '6', '1', '7', '9', '5', '6', '0', '9', '4', '2', '7', '6', '2', '9', '6', '0', '8', '1', '0', '7', '1', '4', '6', '8', '7', '5', '/', '6', '1', '3', '9', '6', '1', '0', '6', '7', '9', '0', '4', '7', '7', '7', '4', '8', '6', '8', '5', '6', '2', '5', '6', '4', '6', '3', '2', '2', '3', '7', '6', '0', '3', '2', '7', '0', '7', '0', '6', '1', '2', '9', '8', '1', '3', '6', '9', '6', '5', '7', '8', '2', '9', '5', '9', '5', '4', '0', '2', '9', '8', '9', '2', '4', '6', '1', '2', '0', '6', '4', '"', ',']

theorem object_fragment0240346_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 478) (SourceJson.white (fragment0240346Field006Chars00 ++ tail)) fragment0240346Acc00600 =
      SourceJson.object (fuel + 477) (SourceJson.white tail) fragment0240346Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_006"
  err.flush

noncomputable def fragment0240346Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0240346Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '5', '6', '2', '7', '5', '9', '7', '1', '6', '5', '0', '2', '9', '7', '6', '3', '1', '4', '9', '1', '8', '1', '3', '3', '9', '6', '2', '1', '7', '9', '2', '0', '2', '7', '5', '6', '3', '0', '5', '8', '3', '7', '1', '5', '9', '2', '1', '3', '9', '3', '4', '4', '8', '9', '0', '4', '3', '0', '4', '3', '4', '0', '3', '8', '4', '7', '4', '4', '5', '0', '8', '8', '6', '0', '9', '7', '0', '7', '8', '7', '4', '4', '8', '9', '0', '0', '2', '0', '9', '8', '5', '5', '7', '0', '8', '0', '7', '1', '1', '7', '1', '0', '5', '4', '3', '3', '7', '8', '0', '9', '2', '6', '9', '9', '1', '8', '3', '5', '8', '9', '4', '3', '0', '8', '5', '9', '0', '2', '8', '7', '4', '8', '2', '4', '3', '2', '1', '9', '8', '4', '6', '5', '7', '2', '5', '1', '3', '6', '2', '3', '7', '0', '4', '9', '0', '6', '3', '8', '6', '5', '0', '6', '1', '2', '3', '7', '8', '6', '0', '7', '4', '9', '4', '0', '2', '7', '7', '7', '3', '0', '1', '6', '4', '5', '9', '0', '9', '2', '8', '2', '6', '0', '8', '0', '4', '7', '6', '6', '5', '9', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '7', '5', '3', '2', '7', '7', '9', '6', '3', '2', '3', '7', '5', '5', '1', '7', '7', '6', '5', '5', '5', '8', '3', '4', '2', '1', '0', '7', '6', '6', '4', '4', '9', '7', '7', '4', '7', '2', '0', '1', '0', '2', '8', '3', '1', '9', '8', '8', '0', '5', '7', '1', '0', '8', '5', '3', '3', '1', '0', '0', '8', '8', '3', '7', '6', '4', '2', '4', '8', '9', '6', '1', '7', '9', '6', '8', '8', '8', '7', '5', '7', '9', '9', '3', '5', '7', '2', '1', '7', '7', '5', '0', '0', '1', '7', '5', '5', '7', '1', '2', '7', '4', '4', '4', '7', '1', '8', '1', '3', '1', '6', '6', '2', '0', '5', '6', '1', '6', '9', '5', '3', '0', '4', '8', '6', '2', '9', '6', '0', '9', '1', '6', '6', '6', '0', '7', '4', '2', '9', '7', '8', '0', '7', '4', '6', '4', '7', '3', '7', '8', '3', '3', '4', '3', '6', '1', '3', '8', '0', '2', '1', '8', '8', '6', '6', '4', '2', '7', '4', '8', '3', '7', '0', '4', '7', '4', '1', '8', '4', '3', '5', '7', '6', '4', '9', '0', '9', '5', '8', '5', '6', '9', '6', '8', '4', '6', '2', '4', '2', '6', '8', '1', '0', '8', '7', '1', '7', '4', '3', '5', '0', '8', '5', '0', '4', '8', '6', '3', '6', '7', '9', '9', '9', '6', '2', '0', '4', '7', '4', '5', '8', '8', '6', '3', '1', '8', '5', '6', '5', '4', '1'])
noncomputable def fragment0240346Acc00800 : List (String × SourceJson) := (fragment0240346Field007Key00, fragment0240346Field007Value00) :: fragment0240346Acc00700
noncomputable def fragment0240346Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '5', '6', '2', '7', '5', '9', '7', '1', '6', '5', '0', '2', '9', '7', '6', '3', '1', '4', '9', '1', '8', '1', '3', '3', '9', '6', '2', '1', '7', '9', '2', '0', '2', '7', '5', '6', '3', '0', '5', '8', '3', '7', '1', '5', '9', '2', '1', '3', '9', '3', '4', '4', '8', '9', '0', '4', '3', '0', '4', '3', '4', '0', '3', '8', '4', '7', '4', '4', '5', '0', '8', '8', '6', '0', '9', '7', '0', '7', '8', '7', '4', '4', '8', '9', '0', '0', '2', '0', '9', '8', '5', '5', '7', '0', '8', '0', '7', '1', '1', '7', '1', '0', '5', '4', '3', '3', '7', '8', '0', '9', '2', '6', '9', '9', '1', '8', '3', '5', '8', '9', '4', '3', '0', '8', '5', '9', '0', '2', '8', '7', '4', '8', '2', '4', '3', '2', '1', '9', '8', '4', '6', '5', '7', '2', '5', '1', '3', '6', '2', '3', '7', '0', '4', '9', '0', '6', '3', '8', '6', '5', '0', '6', '1', '2', '3', '7', '8', '6', '0', '7', '4', '9', '4', '0', '2', '7', '7', '7', '3', '0', '1', '6', '4', '5', '9', '0', '9', '2', '8', '2', '6', '0', '8', '0', '4', '7', '6', '6', '5', '9', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '4', '7', '5', '3', '2', '7', '7', '9', '6', '3', '2', '3', '7', '5', '5', '1', '7', '7', '6', '5', '5', '5', '8', '3', '4', '2', '1', '0', '7', '6', '6', '4', '4', '9', '7', '7', '4', '7', '2', '0', '1', '0', '2', '8', '3', '1', '9', '8', '8', '0', '5', '7', '1', '0', '8', '5', '3', '3', '1', '0', '0', '8', '8', '3', '7', '6', '4', '2', '4', '8', '9', '6', '1', '7', '9', '6', '8', '8', '8', '7', '5', '7', '9', '9', '3', '5', '7', '2', '1', '7', '7', '5', '0', '0', '1', '7', '5', '5', '7', '1', '2', '7', '4', '4', '4', '7', '1', '8', '1', '3', '1', '6', '6', '2', '0', '5', '6', '1', '6', '9', '5', '3', '0', '4', '8', '6', '2', '9', '6', '0', '9', '1', '6', '6', '6', '0', '7', '4', '2', '9', '7', '8', '0', '7', '4', '6', '4', '7', '3', '7', '8', '3', '3', '4', '3', '6', '1', '3', '8', '0', '2', '1', '8', '8', '6', '6', '4', '2', '7', '4', '8', '3', '7', '0', '4', '7', '4', '1', '8', '4', '3', '5', '7', '6', '4', '9', '0', '9', '5', '8', '5', '6', '9', '6', '8', '4', '6', '2', '4', '2', '6', '8', '1', '0', '8', '7', '1', '7', '4', '3', '5', '0', '8', '5', '0', '4', '8', '6', '3', '6', '7', '9', '9', '9', '6', '2', '0', '4', '7', '4', '5', '8', '8', '6', '3', '1', '8', '5', '6', '5', '4', '1', '"', ',']

theorem object_fragment0240346_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 477) (SourceJson.white (fragment0240346Field007Chars00 ++ tail)) fragment0240346Acc00700 =
      SourceJson.object (fuel + 476) (SourceJson.white tail) fragment0240346Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_007"
  err.flush

noncomputable def fragment0240346Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0240346Field008Value00 : SourceJson := .str (String.ofList ['8', '9', '3', '9', '8', '3', '5', '3', '6', '7', '0', '8', '3', '3', '3'])
noncomputable def fragment0240346Acc00900 : List (String × SourceJson) := (fragment0240346Field008Key00, fragment0240346Field008Value00) :: fragment0240346Acc00800
noncomputable def fragment0240346Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '9', '3', '9', '8', '3', '5', '3', '6', '7', '0', '8', '3', '3', '3', '"', ',']

theorem object_fragment0240346_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment0240346Field008Chars00 ++ tail)) fragment0240346Acc00800 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment0240346Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_008"
  err.flush

noncomputable def fragment0240346Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0240346Field009Value00 : SourceJson := .str (String.ofList ['2', '4', '0', '8', '0', '2', '6', '2', '1', '3', '5', '3', '7', '2', '4', '3'])
noncomputable def fragment0240346Acc01000 : List (String × SourceJson) := (fragment0240346Field009Key00, fragment0240346Field009Value00) :: fragment0240346Acc00900
noncomputable def fragment0240346Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '0', '8', '0', '2', '6', '2', '1', '3', '5', '3', '7', '2', '4', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0240346_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment0240346Field009Chars00 ++ tail)) fragment0240346Acc00900 =
      .ok (.obj (fragment0240346Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0240346_object_field_009"
  err.flush

noncomputable def fragment0240346Chars : List Char := '{' :: (fragment0240346Field000Chars00 ++ fragment0240346Field001Chars00 ++ fragment0240346Field002Chars00 ++ fragment0240346Field003Chars00 ++ fragment0240346Field004Chars00 ++ fragment0240346Field005Chars00 ++ fragment0240346Field006Chars00 ++ fragment0240346Field007Chars00 ++ fragment0240346Field008Chars00 ++ fragment0240346Field009Chars00)
noncomputable def fragment0240346Value : SourceJson := .obj (fragment0240346Acc01000.reverse)

theorem value_fragment0240346 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 485) (fragment0240346Chars ++ tail) =
      .ok (fragment0240346Value, tail) := by
  have hinput : fragment0240346Chars ++ tail = '{' :: (fragment0240346Field000Chars00 ++ (fragment0240346Field001Chars00 ++ (fragment0240346Field002Chars00 ++ (fragment0240346Field003Chars00 ++ (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0240346Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 485) (fragment0240346Chars ++ tail) =
        SourceJson.value (fuel + 485) ('{' :: (fragment0240346Field000Chars00 ++ (fragment0240346Field001Chars00 ++ (fragment0240346Field002Chars00 ++ (fragment0240346Field003Chars00 ++ (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 485)) hinput
    _ = SourceJson.object (fuel + 484) (SourceJson.white (fragment0240346Field000Chars00 ++ (fragment0240346Field001Chars00 ++ (fragment0240346Field002Chars00 ++ (fragment0240346Field003Chars00 ++ (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))))))))))) fragment0240346Acc00000 := by rfl
    _ = SourceJson.object (fuel + 483) (SourceJson.white (fragment0240346Field001Chars00 ++ (fragment0240346Field002Chars00 ++ (fragment0240346Field003Chars00 ++ (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail))))))))))) fragment0240346Acc00100 := object_fragment0240346_field_000 fuel (fragment0240346Field001Chars00 ++ (fragment0240346Field002Chars00 ++ (fragment0240346Field003Chars00 ++ (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 482) (SourceJson.white (fragment0240346Field002Chars00 ++ (fragment0240346Field003Chars00 ++ (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))))))))) fragment0240346Acc00200 := object_fragment0240346_field_001 fuel (fragment0240346Field002Chars00 ++ (fragment0240346Field003Chars00 ++ (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 481) (SourceJson.white (fragment0240346Field003Chars00 ++ (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail))))))))) fragment0240346Acc00300 := object_fragment0240346_field_002 fuel (fragment0240346Field003Chars00 ++ (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 480) (SourceJson.white (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))))))) fragment0240346Acc00400 := object_fragment0240346_field_003 fuel (fragment0240346Field004Chars00 ++ (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 479) (SourceJson.white (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail))))))) fragment0240346Acc00500 := object_fragment0240346_field_004 fuel (fragment0240346Field005Chars00 ++ (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 478) (SourceJson.white (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))))) fragment0240346Acc00600 := object_fragment0240346_field_005 fuel (fragment0240346Field006Chars00 ++ (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 477) (SourceJson.white (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail))))) fragment0240346Acc00700 := object_fragment0240346_field_006 fuel (fragment0240346Field007Chars00 ++ (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))) fragment0240346Acc00800 := object_fragment0240346_field_007 fuel (fragment0240346Field008Chars00 ++ (fragment0240346Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment0240346Field009Chars00 ++ (tail))) fragment0240346Acc00900 := object_fragment0240346_field_008 fuel (fragment0240346Field009Chars00 ++ (tail))
    _ = .ok (fragment0240346Value, tail) := object_fragment0240346_field_009 fuel (tail)

noncomputable def fragment0242459Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0242459Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0242459Field000Value00 : SourceJson := .number (String.ofList ['6', '2'])
noncomputable def fragment0242459Acc00100 : List (String × SourceJson) := (fragment0242459Field000Key00, fragment0242459Field000Value00) :: fragment0242459Acc00000
noncomputable def fragment0242459Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '2', ',']

theorem object_fragment0242459_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 478) (SourceJson.white (fragment0242459Field000Chars00 ++ tail)) fragment0242459Acc00000 =
      SourceJson.object (fuel + 477) (SourceJson.white tail) fragment0242459Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_000"
  err.flush

noncomputable def fragment0242459Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0242459Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0242459Acc00200 : List (String × SourceJson) := (fragment0242459Field001Key00, fragment0242459Field001Value00) :: fragment0242459Acc00100
noncomputable def fragment0242459Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0242459_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 477) (SourceJson.white (fragment0242459Field001Chars00 ++ tail)) fragment0242459Acc00100 =
      SourceJson.object (fuel + 476) (SourceJson.white tail) fragment0242459Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_001"
  err.flush

noncomputable def fragment0242459Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0242459Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '6', '6', '6', '7', '4', '6', '0', '4', '1', '9', '6', '5', '0', '3', '6', '4', '8', '1', '7', '7', '2', '4', '8', '7', '4', '4', '4', '8', '3', '5', '3', '8', '3', '7', '7', '2', '9', '/', '8', '3', '1', '3', '5', '9', '3', '3', '8', '1', '7', '7', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0242459Acc00300 : List (String × SourceJson) := (fragment0242459Field002Key00, fragment0242459Field002Value00) :: fragment0242459Acc00200
noncomputable def fragment0242459Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '6', '6', '6', '7', '4', '6', '0', '4', '1', '9', '6', '5', '0', '3', '6', '4', '8', '1', '7', '7', '2', '4', '8', '7', '4', '4', '4', '8', '3', '5', '3', '8', '3', '7', '7', '2', '9', '/', '8', '3', '1', '3', '5', '9', '3', '3', '8', '1', '7', '7', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0242459_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment0242459Field002Chars00 ++ tail)) fragment0242459Acc00200 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment0242459Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_002"
  err.flush

noncomputable def fragment0242459Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0242459Field003Value00 : SourceJson := .str (String.ofList ['2', '4', '2', '7', '7', '4', '2', '3', '/', '1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0'])
noncomputable def fragment0242459Acc00400 : List (String × SourceJson) := (fragment0242459Field003Key00, fragment0242459Field003Value00) :: fragment0242459Acc00300
noncomputable def fragment0242459Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '4', '2', '7', '7', '4', '2', '3', '/', '1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0', '"', ',']

theorem object_fragment0242459_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment0242459Field003Chars00 ++ tail)) fragment0242459Acc00300 =
      SourceJson.object (fuel + 474) (SourceJson.white tail) fragment0242459Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_003"
  err.flush

noncomputable def fragment0242459Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0242459Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0242459Acc00500 : List (String × SourceJson) := (fragment0242459Field004Key00, fragment0242459Field004Value00) :: fragment0242459Acc00400
noncomputable def fragment0242459Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0242459_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 474) (SourceJson.white (fragment0242459Field004Chars00 ++ tail)) fragment0242459Acc00400 =
      SourceJson.object (fuel + 473) (SourceJson.white tail) fragment0242459Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_004"
  err.flush

noncomputable def fragment0242459Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0242459Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '7', '1', '5', '1', '6', '2', '4', '6', '2', '3', '8', '4', '0', '4', '2', '5', '1', '8', '9', '5', '7', '2', '3', '1', '/', '9', '9', '8', '8', '8', '3', '6', '9', '4', '6', '0', '3', '2', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '1', '6', '4', '4', '8', '9', '9', '2', '2', '4', '6', '5', '8', '9', '0', '8', '3', '1', '4', '9', '8', '7', '/', '7', '1', '3', '4', '8', '8', '3', '5', '3', '2', '8', '8', '0', '3', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '5', '7', '1', '9', '1', '4', '1', '6', '5', '1', '5', '2', '3', '1', '9', '3', '8', '6', '6', '4', '8', '9', '/', '1', '9', '9', '7', '7', '6', '7', '3', '8', '9', '2', '0', '6', '5', '0', '2', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '6', '6', '9', '4', '1', '2', '9', '0', '5', '1', '4', '9', '7', '9', '5', '7', '6', '5', '7', '6', '3', '9', '1', '/', '3', '3', '2', '9', '6', '1', '2', '3', '1', '5', '3', '4', '4', '1', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '6', '2', '8', '2', '5', '6', '4', '8', '8', '0', '2', '9', '6', '6', '2', '8', '4', '4', '0', '8', '7', '7', '/', '1', '1', '0', '9', '8', '7', '0', '7', '7', '1', '7', '8', '1', '3', '9', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '4', '9', '2', '3', '4', '9', '8', '3', '3', '3', '7', '6', '1', '3', '5', '0', '0', '5', '0', '3', '1', '1', '/', '9', '0', '8', '0', '7', '6', '0', '8', '6', '0', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '0', '7', '6', '4', '6', '8', '2', '5', '2', '1', '8', '5', '2', '2', '3', '5', '3', '1', '7', '2', '0', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '2', '8', '6', '8', '5', '7', '2', '3', '8', '8', '3', '6', '9', '3', '1', '2', '8', '8', '0', '7', '0', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '2', '3', '5', '5', '8', '6', '2', '1', '5', '1', '1', '1', '4', '9', '8', '6', '9', '0', '1', '3', '3', '/', '9', '0', '8', '0', '7', '6', '0', '8', '6', '0', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '8', '8', '3', '5', '9', '9', '0', '4', '9', '8', '1', '4', '0', '1', '6', '3', '1', '9', '4', '4', '8', '9', '/', '7', '1', '3', '4', '8', '8', '3', '5', '3', '2', '8', '8', '0', '3', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0242459Acc00600 : List (String × SourceJson) := (fragment0242459Field005Key00, fragment0242459Field005Value00) :: fragment0242459Acc00500
noncomputable def fragment0242459Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '1', '5', '1', '6', '2', '4', '6', '2', '3', '8', '4', '0', '4', '2', '5', '1', '8', '9', '5', '7', '2', '3', '1', '/', '9', '9', '8', '8', '8', '3', '6', '9', '4', '6', '0', '3', '2', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '1', '6', '4', '4', '8', '9', '9', '2', '2', '4', '6', '5', '8', '9', '0', '8', '3', '1', '4', '9', '8', '7', '/', '7', '1', '3', '4', '8', '8', '3', '5', '3', '2', '8', '8', '0', '3', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '5', '7', '1', '9', '1', '4', '1', '6', '5', '1', '5', '2', '3', '1', '9', '3', '8', '6', '6', '4', '8', '9', '/', '1', '9', '9', '7', '7', '6', '7', '3', '8', '9', '2', '0', '6', '5', '0', '2', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '6', '6', '9', '4', '1', '2', '9', '0', '5', '1', '4', '9', '7', '9', '5', '7', '6', '5', '7', '6', '3', '9', '1', '/', '3', '3', '2', '9', '6', '1', '2', '3', '1', '5', '3', '4', '4', '1', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '6', '2', '8', '2', '5', '6', '4', '8', '8', '0', '2', '9', '6', '6', '2', '8', '4', '4', '0', '8', '7', '7', '/', '1', '1', '0', '9', '8', '7', '0', '7', '7', '1', '7', '8', '1', '3', '9', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '4', '9', '2', '3', '4', '9', '8', '3', '3', '3', '7', '6', '1', '3', '5', '0', '0', '5', '0', '3', '1', '1', '/', '9', '0', '8', '0', '7', '6', '0', '8', '6', '0', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '0', '7', '6', '4', '6', '8', '2', '5', '2', '1', '8', '5', '2', '2', '3', '5', '3', '1', '7', '2', '0', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '2', '8', '6', '8', '5', '7', '2', '3', '8', '8', '3', '6', '9', '3', '1', '2', '8', '8', '0', '7', '0', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '2', '3', '5', '5', '8', '6', '2', '1', '5', '1', '1', '1', '4', '9', '8', '6', '9', '0', '1', '3', '3', '/', '9', '0', '8', '0', '7', '6', '0', '8', '6', '0', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '8', '3', '5', '9', '9', '0', '4', '9', '8', '1', '4', '0', '1', '6', '3', '1', '9', '4', '4', '8', '9', '/', '7', '1', '3', '4', '8', '8', '3', '5', '3', '2', '8', '8', '0', '3', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0242459_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 473) (SourceJson.white (fragment0242459Field005Chars00 ++ tail)) fragment0242459Acc00500 =
      SourceJson.object (fuel + 472) (SourceJson.white tail) fragment0242459Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_005"
  err.flush

noncomputable def fragment0242459Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0242459Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '1', '0', '9', '3', '8', '4', '3', '3', '4', '5', '9', '7', '3', '3', '0', '5', '7', '0', '6', '9', '8', '3', '4', '2', '2', '6', '8', '7', '6', '2', '3', '2', '6', '9', '5', '2', '6', '0', '9', '3', '3', '4', '5', '6', '9', '7', '5', '2', '5', '0', '0', '0', '0', '0', '/', '3', '3', '2', '8', '2', '8', '5', '5', '3', '8', '4', '3', '8', '6', '7', '1', '5', '5', '2', '6', '8', '3', '6', '4', '6', '6', '0', '3', '7', '7', '7', '9', '4', '0', '0', '1', '8', '2', '6', '0', '6', '4', '0', '6', '3', '1', '3', '4', '3', '8', '8', '7', '8', '7', '5', '9', '6', '5', '2', '2', '4', '7', '6', '8', '0', '8', '6', '0', '7'])
noncomputable def fragment0242459Acc00700 : List (String × SourceJson) := (fragment0242459Field006Key00, fragment0242459Field006Value00) :: fragment0242459Acc00600
noncomputable def fragment0242459Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '1', '0', '9', '3', '8', '4', '3', '3', '4', '5', '9', '7', '3', '3', '0', '5', '7', '0', '6', '9', '8', '3', '4', '2', '2', '6', '8', '7', '6', '2', '3', '2', '6', '9', '5', '2', '6', '0', '9', '3', '3', '4', '5', '6', '9', '7', '5', '2', '5', '0', '0', '0', '0', '0', '/', '3', '3', '2', '8', '2', '8', '5', '5', '3', '8', '4', '3', '8', '6', '7', '1', '5', '5', '2', '6', '8', '3', '6', '4', '6', '6', '0', '3', '7', '7', '7', '9', '4', '0', '0', '1', '8', '2', '6', '0', '6', '4', '0', '6', '3', '1', '3', '4', '3', '8', '8', '7', '8', '7', '5', '9', '6', '5', '2', '2', '4', '7', '6', '8', '0', '8', '6', '0', '7', '"', ',']

theorem object_fragment0242459_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment0242459Field006Chars00 ++ tail)) fragment0242459Acc00600 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment0242459Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_006"
  err.flush

noncomputable def fragment0242459Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0242459Field007Value00 : SourceJson := .str (String.ofList ['4', '6', '3', '5', '1', '9', '2', '2', '8', '1', '2', '7', '1', '9', '4', '3', '6', '9', '0', '4', '8', '0', '0', '0', '1', '5', '6', '1', '8', '3', '3', '3', '3', '2', '2', '4', '4', '5', '4', '0', '1', '9', '9', '5', '2', '1', '8', '9', '3', '6', '6', '5', '4', '1', '8', '1', '4', '8', '6', '6', '1', '0', '7', '4', '3', '9', '2', '4', '4', '3', '2', '6', '0', '6', '4', '3', '2', '3', '1', '4', '2', '8', '3', '8', '6', '6', '5', '8', '6', '5', '7', '4', '9', '3', '5', '5', '1', '5', '2', '3', '4', '0', '9', '3', '0', '3', '9', '0', '2', '4', '5', '6', '6', '0', '1', '0', '8', '6', '4', '5', '5', '1', '9', '5', '7', '9', '1', '7', '1', '3', '9', '4', '3', '0', '7', '2', '2', '9', '2', '0', '3', '1', '2', '1', '6', '4', '4', '6', '8', '8', '8', '5', '6', '9', '1', '4', '4', '4', '4', '6', '1', '1', '0', '5', '1', '0', '0', '3', '7', '1', '3', '6', '1', '7', '4', '6', '7', '9', '9', '2', '2', '0', '2', '5', '1', '7', '3', '6', '0', '8', '9', '0', '5', '1', '9', '4', '8', '6', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '9', '7', '8', '0', '4', '7', '4', '7', '0', '4', '7', '4', '8', '6', '8', '7', '8', '3', '9', '5', '9', '0', '6', '4', '4', '4', '5', '2', '4', '7', '1', '6', '5', '9', '9', '0', '6', '8', '4', '3', '7', '6', '9', '2', '5', '2', '9', '7', '8', '0', '7', '6', '5', '6', '6', '5', '0', '5', '3', '0', '9', '9', '5', '0', '6', '4', '9', '4', '4', '3', '9', '8', '2', '6', '3', '6', '4', '9', '5', '2', '7', '6', '3', '9', '7', '9', '4', '8', '8', '1', '3', '8', '3', '0', '4', '4', '4', '4', '7', '9', '8', '2', '8', '1', '8', '6', '1', '3', '7', '3', '7', '6', '7', '1', '8', '2', '0', '4', '1', '1', '3', '4', '7', '1', '1', '6', '7', '7', '1', '7', '9', '2', '4', '0', '4', '0', '2', '1', '8', '0', '5', '9', '1', '8', '1', '9', '2', '9', '3', '2', '3', '9', '1', '1', '9', '9', '8', '1', '9', '3', '4', '8', '4', '8', '4', '4', '0', '5', '0', '3', '7', '7', '7', '8', '4', '1', '2', '1', '7', '0', '7', '9', '6', '9', '9', '6', '7', '3', '5', '7', '4', '8', '6', '9', '1', '4', '2', '3', '3', '2', '9', '2', '1', '2', '3', '8', '0', '8', '2', '6', '1', '0', '7', '3', '4', '4', '1', '1', '4', '5', '0', '4', '5', '1', '0', '9', '8', '8', '0', '4', '6', '0', '6', '5', '8', '9', '3', '9'])
noncomputable def fragment0242459Acc00800 : List (String × SourceJson) := (fragment0242459Field007Key00, fragment0242459Field007Value00) :: fragment0242459Acc00700
noncomputable def fragment0242459Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '6', '3', '5', '1', '9', '2', '2', '8', '1', '2', '7', '1', '9', '4', '3', '6', '9', '0', '4', '8', '0', '0', '0', '1', '5', '6', '1', '8', '3', '3', '3', '3', '2', '2', '4', '4', '5', '4', '0', '1', '9', '9', '5', '2', '1', '8', '9', '3', '6', '6', '5', '4', '1', '8', '1', '4', '8', '6', '6', '1', '0', '7', '4', '3', '9', '2', '4', '4', '3', '2', '6', '0', '6', '4', '3', '2', '3', '1', '4', '2', '8', '3', '8', '6', '6', '5', '8', '6', '5', '7', '4', '9', '3', '5', '5', '1', '5', '2', '3', '4', '0', '9', '3', '0', '3', '9', '0', '2', '4', '5', '6', '6', '0', '1', '0', '8', '6', '4', '5', '5', '1', '9', '5', '7', '9', '1', '7', '1', '3', '9', '4', '3', '0', '7', '2', '2', '9', '2', '0', '3', '1', '2', '1', '6', '4', '4', '6', '8', '8', '8', '5', '6', '9', '1', '4', '4', '4', '4', '6', '1', '1', '0', '5', '1', '0', '0', '3', '7', '1', '3', '6', '1', '7', '4', '6', '7', '9', '9', '2', '2', '0', '2', '5', '1', '7', '3', '6', '0', '8', '9', '0', '5', '1', '9', '4', '8', '6', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '9', '7', '8', '0', '4', '7', '4', '7', '0', '4', '7', '4', '8', '6', '8', '7', '8', '3', '9', '5', '9', '0', '6', '4', '4', '4', '5', '2', '4', '7', '1', '6', '5', '9', '9', '0', '6', '8', '4', '3', '7', '6', '9', '2', '5', '2', '9', '7', '8', '0', '7', '6', '5', '6', '6', '5', '0', '5', '3', '0', '9', '9', '5', '0', '6', '4', '9', '4', '4', '3', '9', '8', '2', '6', '3', '6', '4', '9', '5', '2', '7', '6', '3', '9', '7', '9', '4', '8', '8', '1', '3', '8', '3', '0', '4', '4', '4', '4', '7', '9', '8', '2', '8', '1', '8', '6', '1', '3', '7', '3', '7', '6', '7', '1', '8', '2', '0', '4', '1', '1', '3', '4', '7', '1', '1', '6', '7', '7', '1', '7', '9', '2', '4', '0', '4', '0', '2', '1', '8', '0', '5', '9', '1', '8', '1', '9', '2', '9', '3', '2', '3', '9', '1', '1', '9', '9', '8', '1', '9', '3', '4', '8', '4', '8', '4', '4', '0', '5', '0', '3', '7', '7', '7', '8', '4', '1', '2', '1', '7', '0', '7', '9', '6', '9', '9', '6', '7', '3', '5', '7', '4', '8', '6', '9', '1', '4', '2', '3', '3', '2', '9', '2', '1', '2', '3', '8', '0', '8', '2', '6', '1', '0', '7', '3', '4', '4', '1', '1', '4', '5', '0', '4', '5', '1', '0', '9', '8', '8', '0', '4', '6', '0', '6', '5', '8', '9', '3', '9', '"', ',']

theorem object_fragment0242459_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment0242459Field007Chars00 ++ tail)) fragment0242459Acc00700 =
      SourceJson.object (fuel + 470) (SourceJson.white tail) fragment0242459Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_007"
  err.flush

noncomputable def fragment0242459Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0242459Field008Value00 : SourceJson := .str (String.ofList ['4', '5', '4', '8', '8', '9', '2', '7', '8', '6', '1', '6', '1', '7', '4', '8'])
noncomputable def fragment0242459Acc00900 : List (String × SourceJson) := (fragment0242459Field008Key00, fragment0242459Field008Value00) :: fragment0242459Acc00800
noncomputable def fragment0242459Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '4', '8', '8', '9', '2', '7', '8', '6', '1', '6', '1', '7', '4', '8', '"', ',']

theorem object_fragment0242459_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment0242459Field008Chars00 ++ tail)) fragment0242459Acc00800 =
      SourceJson.object (fuel + 469) (SourceJson.white tail) fragment0242459Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_008"
  err.flush

noncomputable def fragment0242459Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0242459Field009Value00 : SourceJson := .str (String.ofList ['1', '5', '3', '1', '5', '5', '8', '2', '6', '3', '0', '2', '2', '3', '4', '0', '7'])
noncomputable def fragment0242459Acc01000 : List (String × SourceJson) := (fragment0242459Field009Key00, fragment0242459Field009Value00) :: fragment0242459Acc00900
noncomputable def fragment0242459Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '3', '1', '5', '5', '8', '2', '6', '3', '0', '2', '2', '3', '4', '0', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0242459_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 469) (SourceJson.white (fragment0242459Field009Chars00 ++ tail)) fragment0242459Acc00900 =
      .ok (.obj (fragment0242459Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0242459_object_field_009"
  err.flush

noncomputable def fragment0242459Chars : List Char := '{' :: (fragment0242459Field000Chars00 ++ fragment0242459Field001Chars00 ++ fragment0242459Field002Chars00 ++ fragment0242459Field003Chars00 ++ fragment0242459Field004Chars00 ++ fragment0242459Field005Chars00 ++ fragment0242459Field006Chars00 ++ fragment0242459Field007Chars00 ++ fragment0242459Field008Chars00 ++ fragment0242459Field009Chars00)
noncomputable def fragment0242459Value : SourceJson := .obj (fragment0242459Acc01000.reverse)

theorem value_fragment0242459 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 479) (fragment0242459Chars ++ tail) =
      .ok (fragment0242459Value, tail) := by
  have hinput : fragment0242459Chars ++ tail = '{' :: (fragment0242459Field000Chars00 ++ (fragment0242459Field001Chars00 ++ (fragment0242459Field002Chars00 ++ (fragment0242459Field003Chars00 ++ (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0242459Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 479) (fragment0242459Chars ++ tail) =
        SourceJson.value (fuel + 479) ('{' :: (fragment0242459Field000Chars00 ++ (fragment0242459Field001Chars00 ++ (fragment0242459Field002Chars00 ++ (fragment0242459Field003Chars00 ++ (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 479)) hinput
    _ = SourceJson.object (fuel + 478) (SourceJson.white (fragment0242459Field000Chars00 ++ (fragment0242459Field001Chars00 ++ (fragment0242459Field002Chars00 ++ (fragment0242459Field003Chars00 ++ (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))))))))))) fragment0242459Acc00000 := by rfl
    _ = SourceJson.object (fuel + 477) (SourceJson.white (fragment0242459Field001Chars00 ++ (fragment0242459Field002Chars00 ++ (fragment0242459Field003Chars00 ++ (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail))))))))))) fragment0242459Acc00100 := object_fragment0242459_field_000 fuel (fragment0242459Field001Chars00 ++ (fragment0242459Field002Chars00 ++ (fragment0242459Field003Chars00 ++ (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment0242459Field002Chars00 ++ (fragment0242459Field003Chars00 ++ (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))))))))) fragment0242459Acc00200 := object_fragment0242459_field_001 fuel (fragment0242459Field002Chars00 ++ (fragment0242459Field003Chars00 ++ (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment0242459Field003Chars00 ++ (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail))))))))) fragment0242459Acc00300 := object_fragment0242459_field_002 fuel (fragment0242459Field003Chars00 ++ (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 474) (SourceJson.white (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))))))) fragment0242459Acc00400 := object_fragment0242459_field_003 fuel (fragment0242459Field004Chars00 ++ (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 473) (SourceJson.white (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail))))))) fragment0242459Acc00500 := object_fragment0242459_field_004 fuel (fragment0242459Field005Chars00 ++ (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))))) fragment0242459Acc00600 := object_fragment0242459_field_005 fuel (fragment0242459Field006Chars00 ++ (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail))))) fragment0242459Acc00700 := object_fragment0242459_field_006 fuel (fragment0242459Field007Chars00 ++ (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))) fragment0242459Acc00800 := object_fragment0242459_field_007 fuel (fragment0242459Field008Chars00 ++ (fragment0242459Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 469) (SourceJson.white (fragment0242459Field009Chars00 ++ (tail))) fragment0242459Acc00900 := object_fragment0242459_field_008 fuel (fragment0242459Field009Chars00 ++ (tail))
    _ = .ok (fragment0242459Value, tail) := object_fragment0242459_field_009 fuel (tail)

noncomputable def fragment0244554Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0244554Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0244554Field000Value00 : SourceJson := .number (String.ofList ['6', '3'])
noncomputable def fragment0244554Acc00100 : List (String × SourceJson) := (fragment0244554Field000Key00, fragment0244554Field000Value00) :: fragment0244554Acc00000
noncomputable def fragment0244554Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '3', ',']

theorem object_fragment0244554_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0244554Field000Chars00 ++ tail)) fragment0244554Acc00000 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0244554Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_000"
  err.flush

noncomputable def fragment0244554Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0244554Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0244554Acc00200 : List (String × SourceJson) := (fragment0244554Field001Key00, fragment0244554Field001Value00) :: fragment0244554Acc00100
noncomputable def fragment0244554Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0244554_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0244554Field001Chars00 ++ tail)) fragment0244554Acc00100 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0244554Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_001"
  err.flush

noncomputable def fragment0244554Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0244554Field002Value00 : SourceJson := .str (String.ofList ['9', '6', '4', '5', '7', '3', '9', '0', '8', '9', '4', '2', '6', '1', '7', '1', '2', '9', '6', '2', '5', '4', '8', '9', '7', '1', '6', '6', '5', '1', '0', '5', '0', '7', '/', '1', '8', '1', '2', '5', '5', '6', '6', '9', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0244554Acc00300 : List (String × SourceJson) := (fragment0244554Field002Key00, fragment0244554Field002Value00) :: fragment0244554Acc00200
noncomputable def fragment0244554Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '6', '4', '5', '7', '3', '9', '0', '8', '9', '4', '2', '6', '1', '7', '1', '2', '9', '6', '2', '5', '4', '8', '9', '7', '1', '6', '6', '5', '1', '0', '5', '0', '7', '/', '1', '8', '1', '2', '5', '5', '6', '6', '9', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0244554_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0244554Field002Chars00 ++ tail)) fragment0244554Acc00200 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0244554Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_002"
  err.flush

noncomputable def fragment0244554Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0244554Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0244554Acc00400 : List (String × SourceJson) := (fragment0244554Field003Key00, fragment0244554Field003Value00) :: fragment0244554Acc00300
noncomputable def fragment0244554Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0244554_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0244554Field003Chars00 ++ tail)) fragment0244554Acc00300 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0244554Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_003"
  err.flush

noncomputable def fragment0244554Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0244554Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0244554Acc00500 : List (String × SourceJson) := (fragment0244554Field004Key00, fragment0244554Field004Value00) :: fragment0244554Acc00400
noncomputable def fragment0244554Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0244554_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0244554Field004Chars00 ++ tail)) fragment0244554Acc00400 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0244554Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_004"
  err.flush

noncomputable def fragment0244554Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0244554Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '8', '7', '4', '0', '7', '7', '5', '3', '6', '1', '6', '0', '2', '5', '7', '3', '2', '3', '3', '7', '/', '6', '6', '9', '8', '2', '8', '8', '0', '8', '3', '5', '0', '9', '6', '1', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '3', '1', '8', '9', '5', '2', '5', '6', '2', '2', '9', '3', '0', '8', '3', '5', '4', '2', '3', '/', '1', '5', '3', '1', '0', '3', '7', '2', '7', '6', '2', '3', '0', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '5', '1', '4', '6', '3', '1', '9', '3', '3', '1', '4', '5', '4', '6', '3', '5', '9', '0', '3', '9', '/', '4', '2', '8', '6', '9', '0', '4', '3', '7', '3', '4', '4', '6', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '2', '8', '7', '7', '6', '9', '0', '2', '6', '9', '4', '2', '4', '3', '9', '6', '5', '9', '3', '/', '2', '3', '8', '1', '6', '1', '3', '5', '4', '0', '8', '0', '3', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '7', '9', '8', '0', '6', '9', '7', '1', '3', '8', '1', '9', '4', '7', '6', '6', '1', '5', '3', '9', '/', '7', '1', '4', '4', '8', '4', '0', '6', '2', '2', '4', '1', '0', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '3', '9', '8', '8', '9', '6', '4', '8', '4', '0', '6', '3', '8', '2', '5', '5', '7', '4', '9', '/', '1', '9', '4', '8', '5', '9', '2', '8', '9', '7', '0', '2', '0', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '9', '0', '2', '5', '7', '1', '3', '0', '5', '4', '8', '7', '1', '1', '1', '6', '0', '7', '7', '/', '1', '9', '4', '8', '5', '9', '2', '8', '9', '7', '0', '2', '0', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '1', '8', '2', '3', '6', '5', '9', '8', '4', '7', '7', '2', '4', '0', '0', '6', '3', '/', '3', '0', '4', '4', '6', '7', '6', '4', '0', '1', '5', '9', '5', '2', '8', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '9', '5', '7', '4', '0', '5', '2', '4', '5', '5', '7', '5', '9', '3', '8', '9', '3', '8', '1', '/', '6', '0', '8', '9', '3', '5', '2', '8', '0', '3', '1', '9', '0', '5', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '8', '3', '6', '1', '1', '3', '7', '9', '0', '0', '1', '1', '9', '5', '2', '5', '9', '8', '1', '/', '1', '5', '3', '1', '0', '3', '7', '2', '7', '6', '2', '3', '0', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0244554Acc00600 : List (String × SourceJson) := (fragment0244554Field005Key00, fragment0244554Field005Value00) :: fragment0244554Acc00500
noncomputable def fragment0244554Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '7', '4', '0', '7', '7', '5', '3', '6', '1', '6', '0', '2', '5', '7', '3', '2', '3', '3', '7', '/', '6', '6', '9', '8', '2', '8', '8', '0', '8', '3', '5', '0', '9', '6', '1', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '3', '1', '8', '9', '5', '2', '5', '6', '2', '2', '9', '3', '0', '8', '3', '5', '4', '2', '3', '/', '1', '5', '3', '1', '0', '3', '7', '2', '7', '6', '2', '3', '0', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '5', '1', '4', '6', '3', '1', '9', '3', '3', '1', '4', '5', '4', '6', '3', '5', '9', '0', '3', '9', '/', '4', '2', '8', '6', '9', '0', '4', '3', '7', '3', '4', '4', '6', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '7', '2', '8', '7', '7', '6', '9', '0', '2', '6', '9', '4', '2', '4', '3', '9', '6', '5', '9', '3', '/', '2', '3', '8', '1', '6', '1', '3', '5', '4', '0', '8', '0', '3', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '7', '9', '8', '0', '6', '9', '7', '1', '3', '8', '1', '9', '4', '7', '6', '6', '1', '5', '3', '9', '/', '7', '1', '4', '4', '8', '4', '0', '6', '2', '2', '4', '1', '0', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '3', '9', '8', '8', '9', '6', '4', '8', '4', '0', '6', '3', '8', '2', '5', '5', '7', '4', '9', '/', '1', '9', '4', '8', '5', '9', '2', '8', '9', '7', '0', '2', '0', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '9', '0', '2', '5', '7', '1', '3', '0', '5', '4', '8', '7', '1', '1', '1', '6', '0', '7', '7', '/', '1', '9', '4', '8', '5', '9', '2', '8', '9', '7', '0', '2', '0', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '1', '8', '2', '3', '6', '5', '9', '8', '4', '7', '7', '2', '4', '0', '0', '6', '3', '/', '3', '0', '4', '4', '6', '7', '6', '4', '0', '1', '5', '9', '5', '2', '8', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '7', '4', '0', '5', '2', '4', '5', '5', '7', '5', '9', '3', '8', '9', '3', '8', '1', '/', '6', '0', '8', '9', '3', '5', '2', '8', '0', '3', '1', '9', '0', '5', '6', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '8', '3', '6', '1', '1', '3', '7', '9', '0', '0', '1', '1', '9', '5', '2', '5', '9', '8', '1', '/', '1', '5', '3', '1', '0', '3', '7', '2', '7', '6', '2', '3', '0', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0244554_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0244554Field005Chars00 ++ tail)) fragment0244554Acc00500 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0244554Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_005"
  err.flush

noncomputable def fragment0244554Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0244554Field006Value00 : SourceJson := .str (String.ofList ['1', '6', '0', '4', '8', '7', '7', '3', '1', '5', '6', '1', '0', '3', '9', '0', '5', '9', '9', '8', '4', '2', '0', '3', '9', '9', '0', '4', '2', '3', '2', '9', '0', '0', '8', '0', '2', '4', '0', '9', '1', '5', '2', '2', '7', '5', '0', '/', '1', '2', '1', '0', '2', '2', '6', '0', '7', '4', '8', '3', '7', '1', '7', '6', '9', '1', '8', '0', '0', '9', '3', '5', '4', '7', '8', '2', '2', '8', '6', '0', '9', '3', '3', '9', '1', '6', '2', '0', '9', '0', '7', '4', '3', '6', '6', '6', '8', '7', '8', '4', '3', '8', '5', '1', '7', '6', '8', '5', '9', '3', '9', '3'])
noncomputable def fragment0244554Acc00700 : List (String × SourceJson) := (fragment0244554Field006Key00, fragment0244554Field006Value00) :: fragment0244554Acc00600
noncomputable def fragment0244554Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '0', '4', '8', '7', '7', '3', '1', '5', '6', '1', '0', '3', '9', '0', '5', '9', '9', '8', '4', '2', '0', '3', '9', '9', '0', '4', '2', '3', '2', '9', '0', '0', '8', '0', '2', '4', '0', '9', '1', '5', '2', '2', '7', '5', '0', '/', '1', '2', '1', '0', '2', '2', '6', '0', '7', '4', '8', '3', '7', '1', '7', '6', '9', '1', '8', '0', '0', '9', '3', '5', '4', '7', '8', '2', '2', '8', '6', '0', '9', '3', '3', '9', '1', '6', '2', '0', '9', '0', '7', '4', '3', '6', '6', '6', '8', '7', '8', '4', '3', '8', '5', '1', '7', '6', '8', '5', '9', '3', '9', '3', '"', ',']

theorem object_fragment0244554_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0244554Field006Chars00 ++ tail)) fragment0244554Acc00600 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0244554Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_006"
  err.flush

noncomputable def fragment0244554Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0244554Field007Value00 : SourceJson := .str (String.ofList ['2', '4', '1', '3', '3', '9', '6', '1', '8', '7', '4', '6', '2', '6', '3', '0', '8', '1', '8', '5', '8', '0', '9', '1', '0', '1', '2', '5', '2', '7', '5', '5', '8', '8', '3', '8', '2', '3', '6', '5', '6', '9', '5', '9', '2', '4', '1', '7', '3', '0', '7', '9', '5', '8', '8', '2', '0', '1', '0', '1', '9', '7', '6', '7', '1', '6', '1', '2', '1', '1', '0', '2', '7', '7', '4', '3', '4', '8', '0', '9', '5', '6', '5', '6', '8', '2', '1', '5', '0', '6', '6', '1', '9', '9', '0', '7', '7', '3', '0', '2', '1', '3', '3', '1', '2', '8', '8', '7', '7', '3', '6', '6', '6', '1', '8', '8', '5', '3', '2', '9', '3', '3', '2', '2', '1', '5', '9', '2', '2', '8', '0', '3', '9', '0', '9', '7', '4', '6', '4', '7', '4', '7', '2', '3', '5', '4', '9', '6', '9', '2', '8', '8', '0', '5', '4', '9', '9', '8', '9', '1', '3', '3', '5', '1', '1', '9', '6', '7', '7', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '7', '3', '3', '4', '5', '3', '3', '5', '0', '9', '4', '2', '9', '3', '8', '0', '7', '6', '7', '2', '9', '0', '8', '0', '5', '6', '6', '3', '0', '7', '3', '8', '3', '7', '0', '4', '6', '9', '3', '8', '5', '9', '5', '6', '0', '5', '0', '5', '7', '9', '9', '5', '8', '4', '0', '3', '5', '0', '5', '9', '3', '3', '8', '7', '8', '5', '5', '4', '2', '6', '4', '6', '0', '2', '7', '8', '6', '3', '1', '5', '2', '7', '2', '8', '2', '8', '5', '1', '8', '8', '5', '6', '2', '8', '4', '7', '4', '9', '7', '3', '4', '9', '0', '1', '8', '3', '1', '3', '4', '4', '8', '2', '6', '5', '0', '6', '4', '3', '7', '9', '7', '3', '0', '4', '0', '2', '2', '3', '2', '5', '2', '1', '2', '8', '9', '3', '6', '3', '6', '2', '2', '0', '5', '1', '0', '3', '9', '4', '7', '5', '3', '6', '8', '2', '6', '3', '1', '5', '7', '5', '3', '4', '0', '1', '0', '0', '9', '4', '8', '0', '7', '3', '5', '5', '6', '4', '2', '3', '6', '7', '1', '0', '8', '6', '6', '1', '8', '1', '3', '1', '8', '0', '7', '5', '0', '0', '4', '4', '5', '3', '1', '3'])
noncomputable def fragment0244554Acc00800 : List (String × SourceJson) := (fragment0244554Field007Key00, fragment0244554Field007Value00) :: fragment0244554Acc00700
noncomputable def fragment0244554Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '1', '3', '3', '9', '6', '1', '8', '7', '4', '6', '2', '6', '3', '0', '8', '1', '8', '5', '8', '0', '9', '1', '0', '1', '2', '5', '2', '7', '5', '5', '8', '8', '3', '8', '2', '3', '6', '5', '6', '9', '5', '9', '2', '4', '1', '7', '3', '0', '7', '9', '5', '8', '8', '2', '0', '1', '0', '1', '9', '7', '6', '7', '1', '6', '1', '2', '1', '1', '0', '2', '7', '7', '4', '3', '4', '8', '0', '9', '5', '6', '5', '6', '8', '2', '1', '5', '0', '6', '6', '1', '9', '9', '0', '7', '7', '3', '0', '2', '1', '3', '3', '1', '2', '8', '8', '7', '7', '3', '6', '6', '6', '1', '8', '8', '5', '3', '2', '9', '3', '3', '2', '2', '1', '5', '9', '2', '2', '8', '0', '3', '9', '0', '9', '7', '4', '6', '4', '7', '4', '7', '2', '3', '5', '4', '9', '6', '9', '2', '8', '8', '0', '5', '4', '9', '9', '8', '9', '1', '3', '3', '5', '1', '1', '9', '6', '7', '7', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '7', '3', '3', '4', '5', '3', '3', '5', '0', '9', '4', '2', '9', '3', '8', '0', '7', '6', '7', '2', '9', '0', '8', '0', '5', '6', '6', '3', '0', '7', '3', '8', '3', '7', '0', '4', '6', '9', '3', '8', '5', '9', '5', '6', '0', '5', '0', '5', '7', '9', '9', '5', '8', '4', '0', '3', '5', '0', '5', '9', '3', '3', '8', '7', '8', '5', '5', '4', '2', '6', '4', '6', '0', '2', '7', '8', '6', '3', '1', '5', '2', '7', '2', '8', '2', '8', '5', '1', '8', '8', '5', '6', '2', '8', '4', '7', '4', '9', '7', '3', '4', '9', '0', '1', '8', '3', '1', '3', '4', '4', '8', '2', '6', '5', '0', '6', '4', '3', '7', '9', '7', '3', '0', '4', '0', '2', '2', '3', '2', '5', '2', '1', '2', '8', '9', '3', '6', '3', '6', '2', '2', '0', '5', '1', '0', '3', '9', '4', '7', '5', '3', '6', '8', '2', '6', '3', '1', '5', '7', '5', '3', '4', '0', '1', '0', '0', '9', '4', '8', '0', '7', '3', '5', '5', '6', '4', '2', '3', '6', '7', '1', '0', '8', '6', '6', '1', '8', '1', '3', '1', '8', '0', '7', '5', '0', '0', '4', '4', '5', '3', '1', '3', '"', ',']

theorem object_fragment0244554_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0244554Field007Chars00 ++ tail)) fragment0244554Acc00700 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0244554Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_007"
  err.flush

noncomputable def fragment0244554Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0244554Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '5', '0', '6', '4', '2', '3', '8', '3', '4', '3', '8'])
noncomputable def fragment0244554Acc00900 : List (String × SourceJson) := (fragment0244554Field008Key00, fragment0244554Field008Value00) :: fragment0244554Acc00800
noncomputable def fragment0244554Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '5', '0', '6', '4', '2', '3', '8', '3', '4', '3', '8', '"', ',']

theorem object_fragment0244554_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0244554Field008Chars00 ++ tail)) fragment0244554Acc00800 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0244554Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_008"
  err.flush

noncomputable def fragment0244554Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0244554Field009Value00 : SourceJson := .str (String.ofList ['3', '4', '9', '3', '4', '5', '6', '6', '2', '7', '4', '4', '1'])
noncomputable def fragment0244554Acc01000 : List (String × SourceJson) := (fragment0244554Field009Key00, fragment0244554Field009Value00) :: fragment0244554Acc00900
noncomputable def fragment0244554Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '9', '3', '4', '5', '6', '6', '2', '7', '4', '4', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0244554_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0244554Field009Chars00 ++ tail)) fragment0244554Acc00900 =
      .ok (.obj (fragment0244554Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0244554_object_field_009"
  err.flush

noncomputable def fragment0244554Chars : List Char := '{' :: (fragment0244554Field000Chars00 ++ fragment0244554Field001Chars00 ++ fragment0244554Field002Chars00 ++ fragment0244554Field003Chars00 ++ fragment0244554Field004Chars00 ++ fragment0244554Field005Chars00 ++ fragment0244554Field006Chars00 ++ fragment0244554Field007Chars00 ++ fragment0244554Field008Chars00 ++ fragment0244554Field009Chars00)
noncomputable def fragment0244554Value : SourceJson := .obj (fragment0244554Acc01000.reverse)

theorem value_fragment0244554 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 404) (fragment0244554Chars ++ tail) =
      .ok (fragment0244554Value, tail) := by
  have hinput : fragment0244554Chars ++ tail = '{' :: (fragment0244554Field000Chars00 ++ (fragment0244554Field001Chars00 ++ (fragment0244554Field002Chars00 ++ (fragment0244554Field003Chars00 ++ (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0244554Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 404) (fragment0244554Chars ++ tail) =
        SourceJson.value (fuel + 404) ('{' :: (fragment0244554Field000Chars00 ++ (fragment0244554Field001Chars00 ++ (fragment0244554Field002Chars00 ++ (fragment0244554Field003Chars00 ++ (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 404)) hinput
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0244554Field000Chars00 ++ (fragment0244554Field001Chars00 ++ (fragment0244554Field002Chars00 ++ (fragment0244554Field003Chars00 ++ (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))))))))))) fragment0244554Acc00000 := by rfl
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0244554Field001Chars00 ++ (fragment0244554Field002Chars00 ++ (fragment0244554Field003Chars00 ++ (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail))))))))))) fragment0244554Acc00100 := object_fragment0244554_field_000 fuel (fragment0244554Field001Chars00 ++ (fragment0244554Field002Chars00 ++ (fragment0244554Field003Chars00 ++ (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0244554Field002Chars00 ++ (fragment0244554Field003Chars00 ++ (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))))))))) fragment0244554Acc00200 := object_fragment0244554_field_001 fuel (fragment0244554Field002Chars00 ++ (fragment0244554Field003Chars00 ++ (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0244554Field003Chars00 ++ (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail))))))))) fragment0244554Acc00300 := object_fragment0244554_field_002 fuel (fragment0244554Field003Chars00 ++ (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))))))) fragment0244554Acc00400 := object_fragment0244554_field_003 fuel (fragment0244554Field004Chars00 ++ (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail))))))) fragment0244554Acc00500 := object_fragment0244554_field_004 fuel (fragment0244554Field005Chars00 ++ (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))))) fragment0244554Acc00600 := object_fragment0244554_field_005 fuel (fragment0244554Field006Chars00 ++ (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail))))) fragment0244554Acc00700 := object_fragment0244554_field_006 fuel (fragment0244554Field007Chars00 ++ (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))) fragment0244554Acc00800 := object_fragment0244554_field_007 fuel (fragment0244554Field008Chars00 ++ (fragment0244554Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0244554Field009Chars00 ++ (tail))) fragment0244554Acc00900 := object_fragment0244554_field_008 fuel (fragment0244554Field009Chars00 ++ (tail))
    _ = .ok (fragment0244554Value, tail) := object_fragment0244554_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0056_before_reader"
  err.flush

noncomputable def chunk0056LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0056SuffixChars00 : List Char := [',']
noncomputable def chunk0056Chars00 : List Char := chunk0056LeadChars00 ++ fragment0232054Chars ++ chunk0056SuffixChars00
noncomputable def chunk0056Push00 (acc : List SourceJson) : List SourceJson := fragment0232054Value :: acc

noncomputable def chunk0056AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0056_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 601)
      (SourceJson.white (chunk0056LeadChars00 ++ (fragment0232054Chars ++ rest))) acc =
      (SourceJson.value (fuel + 600) (fragment0232054Chars ++ rest)).bind
        (chunk0056AfterValue00 (fuel + 600) acc) := by rfl

theorem array_chunk0056 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 601) (SourceJson.white (chunk0056Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 600) (SourceJson.white tail) (chunk0056Push00 acc) := by
  have hinput : chunk0056Chars00 ++ tail = chunk0056LeadChars00 ++ (fragment0232054Chars ++ (chunk0056SuffixChars00 ++ tail)) := by
    simp only [chunk0056Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 601) (SourceJson.white (chunk0056Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 601)
          (SourceJson.white (chunk0056LeadChars00 ++ (fragment0232054Chars ++ (chunk0056SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 601) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 600) (fragment0232054Chars ++ (chunk0056SuffixChars00 ++ tail))).bind
        (chunk0056AfterValue00 (fuel + 600) acc) := array_chunk0056_head fuel (chunk0056SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0232054Value, chunk0056SuffixChars00 ++ tail)).bind
        (chunk0056AfterValue00 (fuel + 600) acc) :=
      congrArg (fun result => result.bind (chunk0056AfterValue00 (fuel + 600) acc))
        (value_fragment0232054 (fuel + 221) (chunk0056SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 600) (SourceJson.white tail) (chunk0056Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0056_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0057_before_reader"
  err.flush

noncomputable def chunk0057LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0057SuffixChars00 : List Char := [',']
noncomputable def chunk0057Chars00 : List Char := chunk0057LeadChars00 ++ fragment0233927Chars ++ chunk0057SuffixChars00
noncomputable def chunk0057Push00 (acc : List SourceJson) : List SourceJson := fragment0233927Value :: acc

noncomputable def chunk0057AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0057_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 600)
      (SourceJson.white (chunk0057LeadChars00 ++ (fragment0233927Chars ++ rest))) acc =
      (SourceJson.value (fuel + 599) (fragment0233927Chars ++ rest)).bind
        (chunk0057AfterValue00 (fuel + 599) acc) := by rfl

theorem array_chunk0057 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 600) (SourceJson.white (chunk0057Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 599) (SourceJson.white tail) (chunk0057Push00 acc) := by
  have hinput : chunk0057Chars00 ++ tail = chunk0057LeadChars00 ++ (fragment0233927Chars ++ (chunk0057SuffixChars00 ++ tail)) := by
    simp only [chunk0057Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 600) (SourceJson.white (chunk0057Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 600)
          (SourceJson.white (chunk0057LeadChars00 ++ (fragment0233927Chars ++ (chunk0057SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 600) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 599) (fragment0233927Chars ++ (chunk0057SuffixChars00 ++ tail))).bind
        (chunk0057AfterValue00 (fuel + 599) acc) := array_chunk0057_head fuel (chunk0057SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0233927Value, chunk0057SuffixChars00 ++ tail)).bind
        (chunk0057AfterValue00 (fuel + 599) acc) :=
      congrArg (fun result => result.bind (chunk0057AfterValue00 (fuel + 599) acc))
        (value_fragment0233927 (fuel + 394) (chunk0057SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 599) (SourceJson.white tail) (chunk0057Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0057_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0058_before_reader"
  err.flush

noncomputable def chunk0058LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0058SuffixChars00 : List Char := [',']
noncomputable def chunk0058Chars00 : List Char := chunk0058LeadChars00 ++ fragment0235463Chars ++ chunk0058SuffixChars00
noncomputable def chunk0058Push00 (acc : List SourceJson) : List SourceJson := fragment0235463Value :: acc

noncomputable def chunk0058AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0058_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 599)
      (SourceJson.white (chunk0058LeadChars00 ++ (fragment0235463Chars ++ rest))) acc =
      (SourceJson.value (fuel + 598) (fragment0235463Chars ++ rest)).bind
        (chunk0058AfterValue00 (fuel + 598) acc) := by rfl

theorem array_chunk0058 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 599) (SourceJson.white (chunk0058Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 598) (SourceJson.white tail) (chunk0058Push00 acc) := by
  have hinput : chunk0058Chars00 ++ tail = chunk0058LeadChars00 ++ (fragment0235463Chars ++ (chunk0058SuffixChars00 ++ tail)) := by
    simp only [chunk0058Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 599) (SourceJson.white (chunk0058Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 599)
          (SourceJson.white (chunk0058LeadChars00 ++ (fragment0235463Chars ++ (chunk0058SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 599) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 598) (fragment0235463Chars ++ (chunk0058SuffixChars00 ++ tail))).bind
        (chunk0058AfterValue00 (fuel + 598) acc) := array_chunk0058_head fuel (chunk0058SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0235463Value, chunk0058SuffixChars00 ++ tail)).bind
        (chunk0058AfterValue00 (fuel + 598) acc) :=
      congrArg (fun result => result.bind (chunk0058AfterValue00 (fuel + 598) acc))
        (value_fragment0235463 (fuel + 238) (chunk0058SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 598) (SourceJson.white tail) (chunk0058Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0058_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0059_before_reader"
  err.flush

noncomputable def chunk0059LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0059SuffixChars00 : List Char := [',']
noncomputable def chunk0059Chars00 : List Char := chunk0059LeadChars00 ++ fragment0237303Chars ++ chunk0059SuffixChars00
noncomputable def chunk0059Push00 (acc : List SourceJson) : List SourceJson := fragment0237303Value :: acc

noncomputable def chunk0059AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0059_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 598)
      (SourceJson.white (chunk0059LeadChars00 ++ (fragment0237303Chars ++ rest))) acc =
      (SourceJson.value (fuel + 597) (fragment0237303Chars ++ rest)).bind
        (chunk0059AfterValue00 (fuel + 597) acc) := by rfl

theorem array_chunk0059 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 598) (SourceJson.white (chunk0059Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 597) (SourceJson.white tail) (chunk0059Push00 acc) := by
  have hinput : chunk0059Chars00 ++ tail = chunk0059LeadChars00 ++ (fragment0237303Chars ++ (chunk0059SuffixChars00 ++ tail)) := by
    simp only [chunk0059Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 598) (SourceJson.white (chunk0059Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 598)
          (SourceJson.white (chunk0059LeadChars00 ++ (fragment0237303Chars ++ (chunk0059SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 598) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 597) (fragment0237303Chars ++ (chunk0059SuffixChars00 ++ tail))).bind
        (chunk0059AfterValue00 (fuel + 597) acc) := array_chunk0059_head fuel (chunk0059SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0237303Value, chunk0059SuffixChars00 ++ tail)).bind
        (chunk0059AfterValue00 (fuel + 597) acc) :=
      congrArg (fun result => result.bind (chunk0059AfterValue00 (fuel + 597) acc))
        (value_fragment0237303 (fuel + 397) (chunk0059SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 597) (SourceJson.white tail) (chunk0059Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0059_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0060_before_reader"
  err.flush

noncomputable def chunk0060LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0060SuffixChars00 : List Char := [',']
noncomputable def chunk0060Chars00 : List Char := chunk0060LeadChars00 ++ fragment0238823Chars ++ chunk0060SuffixChars00
noncomputable def chunk0060Push00 (acc : List SourceJson) : List SourceJson := fragment0238823Value :: acc

noncomputable def chunk0060AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0060_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 597)
      (SourceJson.white (chunk0060LeadChars00 ++ (fragment0238823Chars ++ rest))) acc =
      (SourceJson.value (fuel + 596) (fragment0238823Chars ++ rest)).bind
        (chunk0060AfterValue00 (fuel + 596) acc) := by rfl

theorem array_chunk0060 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 597) (SourceJson.white (chunk0060Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 596) (SourceJson.white tail) (chunk0060Push00 acc) := by
  have hinput : chunk0060Chars00 ++ tail = chunk0060LeadChars00 ++ (fragment0238823Chars ++ (chunk0060SuffixChars00 ++ tail)) := by
    simp only [chunk0060Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 597) (SourceJson.white (chunk0060Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 597)
          (SourceJson.white (chunk0060LeadChars00 ++ (fragment0238823Chars ++ (chunk0060SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 597) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 596) (fragment0238823Chars ++ (chunk0060SuffixChars00 ++ tail))).bind
        (chunk0060AfterValue00 (fuel + 596) acc) := array_chunk0060_head fuel (chunk0060SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0238823Value, chunk0060SuffixChars00 ++ tail)).bind
        (chunk0060AfterValue00 (fuel + 596) acc) :=
      congrArg (fun result => result.bind (chunk0060AfterValue00 (fuel + 596) acc))
        (value_fragment0238823 (fuel + 392) (chunk0060SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 596) (SourceJson.white tail) (chunk0060Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0060_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0061_before_reader"
  err.flush

noncomputable def chunk0061LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0061SuffixChars00 : List Char := [',']
noncomputable def chunk0061Chars00 : List Char := chunk0061LeadChars00 ++ fragment0240346Chars ++ chunk0061SuffixChars00
noncomputable def chunk0061Push00 (acc : List SourceJson) : List SourceJson := fragment0240346Value :: acc

noncomputable def chunk0061AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0061_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 596)
      (SourceJson.white (chunk0061LeadChars00 ++ (fragment0240346Chars ++ rest))) acc =
      (SourceJson.value (fuel + 595) (fragment0240346Chars ++ rest)).bind
        (chunk0061AfterValue00 (fuel + 595) acc) := by rfl

theorem array_chunk0061 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 596) (SourceJson.white (chunk0061Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 595) (SourceJson.white tail) (chunk0061Push00 acc) := by
  have hinput : chunk0061Chars00 ++ tail = chunk0061LeadChars00 ++ (fragment0240346Chars ++ (chunk0061SuffixChars00 ++ tail)) := by
    simp only [chunk0061Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 596) (SourceJson.white (chunk0061Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 596)
          (SourceJson.white (chunk0061LeadChars00 ++ (fragment0240346Chars ++ (chunk0061SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 596) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 595) (fragment0240346Chars ++ (chunk0061SuffixChars00 ++ tail))).bind
        (chunk0061AfterValue00 (fuel + 595) acc) := array_chunk0061_head fuel (chunk0061SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0240346Value, chunk0061SuffixChars00 ++ tail)).bind
        (chunk0061AfterValue00 (fuel + 595) acc) :=
      congrArg (fun result => result.bind (chunk0061AfterValue00 (fuel + 595) acc))
        (value_fragment0240346 (fuel + 110) (chunk0061SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 595) (SourceJson.white tail) (chunk0061Push00 acc) := by rfl

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
noncomputable def chunk0062Chars00 : List Char := chunk0062LeadChars00 ++ fragment0242459Chars ++ chunk0062SuffixChars00
noncomputable def chunk0062Push00 (acc : List SourceJson) : List SourceJson := fragment0242459Value :: acc

noncomputable def chunk0062AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0062_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 595)
      (SourceJson.white (chunk0062LeadChars00 ++ (fragment0242459Chars ++ rest))) acc =
      (SourceJson.value (fuel + 594) (fragment0242459Chars ++ rest)).bind
        (chunk0062AfterValue00 (fuel + 594) acc) := by rfl

theorem array_chunk0062 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 595) (SourceJson.white (chunk0062Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 594) (SourceJson.white tail) (chunk0062Push00 acc) := by
  have hinput : chunk0062Chars00 ++ tail = chunk0062LeadChars00 ++ (fragment0242459Chars ++ (chunk0062SuffixChars00 ++ tail)) := by
    simp only [chunk0062Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 595) (SourceJson.white (chunk0062Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 595)
          (SourceJson.white (chunk0062LeadChars00 ++ (fragment0242459Chars ++ (chunk0062SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 595) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 594) (fragment0242459Chars ++ (chunk0062SuffixChars00 ++ tail))).bind
        (chunk0062AfterValue00 (fuel + 594) acc) := array_chunk0062_head fuel (chunk0062SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0242459Value, chunk0062SuffixChars00 ++ tail)).bind
        (chunk0062AfterValue00 (fuel + 594) acc) :=
      congrArg (fun result => result.bind (chunk0062AfterValue00 (fuel + 594) acc))
        (value_fragment0242459 (fuel + 115) (chunk0062SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 594) (SourceJson.white tail) (chunk0062Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0062_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0063_before_reader"
  err.flush

noncomputable def chunk0063LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0063SuffixChars00 : List Char := [',']
noncomputable def chunk0063Chars00 : List Char := chunk0063LeadChars00 ++ fragment0244554Chars ++ chunk0063SuffixChars00
noncomputable def chunk0063Push00 (acc : List SourceJson) : List SourceJson := fragment0244554Value :: acc

noncomputable def chunk0063AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0063_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 594)
      (SourceJson.white (chunk0063LeadChars00 ++ (fragment0244554Chars ++ rest))) acc =
      (SourceJson.value (fuel + 593) (fragment0244554Chars ++ rest)).bind
        (chunk0063AfterValue00 (fuel + 593) acc) := by rfl

theorem array_chunk0063 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 594) (SourceJson.white (chunk0063Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 593) (SourceJson.white tail) (chunk0063Push00 acc) := by
  have hinput : chunk0063Chars00 ++ tail = chunk0063LeadChars00 ++ (fragment0244554Chars ++ (chunk0063SuffixChars00 ++ tail)) := by
    simp only [chunk0063Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 594) (SourceJson.white (chunk0063Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 594)
          (SourceJson.white (chunk0063LeadChars00 ++ (fragment0244554Chars ++ (chunk0063SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 594) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 593) (fragment0244554Chars ++ (chunk0063SuffixChars00 ++ tail))).bind
        (chunk0063AfterValue00 (fuel + 593) acc) := array_chunk0063_head fuel (chunk0063SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0244554Value, chunk0063SuffixChars00 ++ tail)).bind
        (chunk0063AfterValue00 (fuel + 593) acc) :=
      congrArg (fun result => result.bind (chunk0063AfterValue00 (fuel + 593) acc))
        (value_fragment0244554 (fuel + 189) (chunk0063SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 593) (SourceJson.white tail) (chunk0063Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0063_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0056Chars00 ++ chunk0057Chars00 ++ chunk0058Chars00 ++ chunk0059Chars00 ++ chunk0060Chars00 ++ chunk0061Chars00 ++ chunk0062Chars00 ++ chunk0063Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0063Push00 (chunk0062Push00 (chunk0061Push00 (chunk0060Push00 (chunk0059Push00 (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 601) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 593) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0056Chars00 ++ (chunk0057Chars00 ++ (chunk0058Chars00 ++ (chunk0059Chars00 ++ (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 601) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 601) (SourceJson.white (chunk0056Chars00 ++ (chunk0057Chars00 ++ (chunk0058Chars00 ++ (chunk0059Chars00 ++ (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 601) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 600) (SourceJson.white (chunk0057Chars00 ++ (chunk0058Chars00 ++ (chunk0059Chars00 ++ (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail))))))))) (chunk0056Push00 (acc)) := array_chunk0056 fuel (chunk0057Chars00 ++ (chunk0058Chars00 ++ (chunk0059Chars00 ++ (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 599) (SourceJson.white (chunk0058Chars00 ++ (chunk0059Chars00 ++ (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail)))))))) (chunk0057Push00 (chunk0056Push00 (acc))) := array_chunk0057 fuel (chunk0058Chars00 ++ (chunk0059Chars00 ++ (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail))))))) (chunk0056Push00 (acc))
    _ = SourceJson.array (fuel + 598) (SourceJson.white (chunk0059Chars00 ++ (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail))))))) (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc)))) := array_chunk0058 fuel (chunk0059Chars00 ++ (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail)))))) (chunk0057Push00 (chunk0056Push00 (acc)))
    _ = SourceJson.array (fuel + 597) (SourceJson.white (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail)))))) (chunk0059Push00 (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc))))) := array_chunk0059 fuel (chunk0060Chars00 ++ (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail))))) (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc))))
    _ = SourceJson.array (fuel + 596) (SourceJson.white (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail))))) (chunk0060Push00 (chunk0059Push00 (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc)))))) := array_chunk0060 fuel (chunk0061Chars00 ++ (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail)))) (chunk0059Push00 (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc)))))
    _ = SourceJson.array (fuel + 595) (SourceJson.white (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail)))) (chunk0061Push00 (chunk0060Push00 (chunk0059Push00 (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc))))))) := array_chunk0061 fuel (chunk0062Chars00 ++ (chunk0063Chars00 ++ (tail))) (chunk0060Push00 (chunk0059Push00 (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc))))))
    _ = SourceJson.array (fuel + 594) (SourceJson.white (chunk0063Chars00 ++ (tail))) (chunk0062Push00 (chunk0061Push00 (chunk0060Push00 (chunk0059Push00 (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc)))))))) := array_chunk0062 fuel (chunk0063Chars00 ++ (tail)) (chunk0061Push00 (chunk0060Push00 (chunk0059Push00 (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc)))))))
    _ = SourceJson.array (fuel + 593) (SourceJson.white tail) (blockPush acc) := array_chunk0063 fuel (tail) (chunk0062Push00 (chunk0061Push00 (chunk0060Push00 (chunk0059Push00 (chunk0058Push00 (chunk0057Push00 (chunk0056Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 232048).take 14432 = blockChars := by rfl

theorem block_original_split : sourceRest 232048 = blockChars ++ sourceRest 246480 := by
  calc
    sourceRest 232048 = (sourceRest 232048).take 14432 ++ (sourceRest 232048).drop 14432 :=
      (List.take_append_drop 14432 (sourceRest 232048)).symm
    _ = blockChars ++ (sourceRest 232048).drop 14432 :=
      congrArg (fun part => part ++ (sourceRest 232048).drop 14432) block_original_prefix
    _ = blockChars ++ sourceRest 246480 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 232048 14432)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 601) (SourceJson.white (sourceRest 232048)) acc =
      SourceJson.array (fuel + 593) (SourceJson.white (sourceRest 246480)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 601) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 246480) acc)

#print axioms object_fragment0232054_field_000
#print axioms object_fragment0232054_field_001
#print axioms object_fragment0232054_field_002
#print axioms object_fragment0232054_field_003
#print axioms object_fragment0232054_field_004
#print axioms object_fragment0232054_field_005
#print axioms object_fragment0232054_field_006
#print axioms object_fragment0232054_field_007
#print axioms object_fragment0232054_field_008
#print axioms object_fragment0232054_field_009
#print axioms value_fragment0232054
#print axioms object_fragment0233927_field_000
#print axioms object_fragment0233927_field_001
#print axioms object_fragment0233927_field_002
#print axioms object_fragment0233927_field_003
#print axioms object_fragment0233927_field_004
#print axioms object_fragment0233927_field_005
#print axioms object_fragment0233927_field_006
#print axioms object_fragment0233927_field_007
#print axioms object_fragment0233927_field_008
#print axioms object_fragment0233927_field_009
#print axioms value_fragment0233927
#print axioms object_fragment0235463_field_000
#print axioms object_fragment0235463_field_001
#print axioms object_fragment0235463_field_002
#print axioms object_fragment0235463_field_003
#print axioms object_fragment0235463_field_004
#print axioms object_fragment0235463_field_005
#print axioms object_fragment0235463_field_006
#print axioms object_fragment0235463_field_007
#print axioms object_fragment0235463_field_008
#print axioms object_fragment0235463_field_009
#print axioms value_fragment0235463
#print axioms object_fragment0237303_field_000
#print axioms object_fragment0237303_field_001
#print axioms object_fragment0237303_field_002
#print axioms object_fragment0237303_field_003
#print axioms object_fragment0237303_field_004
#print axioms object_fragment0237303_field_005
#print axioms object_fragment0237303_field_006
#print axioms object_fragment0237303_field_007
#print axioms object_fragment0237303_field_008
#print axioms object_fragment0237303_field_009
#print axioms value_fragment0237303
#print axioms object_fragment0238823_field_000
#print axioms object_fragment0238823_field_001
#print axioms object_fragment0238823_field_002
#print axioms object_fragment0238823_field_003
#print axioms object_fragment0238823_field_004
#print axioms object_fragment0238823_field_005
#print axioms object_fragment0238823_field_006
#print axioms object_fragment0238823_field_007
#print axioms object_fragment0238823_field_008
#print axioms object_fragment0238823_field_009
#print axioms value_fragment0238823
#print axioms object_fragment0240346_field_000
#print axioms object_fragment0240346_field_001
#print axioms object_fragment0240346_field_002
#print axioms object_fragment0240346_field_003
#print axioms object_fragment0240346_field_004
#print axioms object_fragment0240346_field_005
#print axioms object_fragment0240346_field_006
#print axioms object_fragment0240346_field_007
#print axioms object_fragment0240346_field_008
#print axioms object_fragment0240346_field_009
#print axioms value_fragment0240346
#print axioms object_fragment0242459_field_000
#print axioms object_fragment0242459_field_001
#print axioms object_fragment0242459_field_002
#print axioms object_fragment0242459_field_003
#print axioms object_fragment0242459_field_004
#print axioms object_fragment0242459_field_005
#print axioms object_fragment0242459_field_006
#print axioms object_fragment0242459_field_007
#print axioms object_fragment0242459_field_008
#print axioms object_fragment0242459_field_009
#print axioms value_fragment0242459
#print axioms object_fragment0244554_field_000
#print axioms object_fragment0244554_field_001
#print axioms object_fragment0244554_field_002
#print axioms object_fragment0244554_field_003
#print axioms object_fragment0244554_field_004
#print axioms object_fragment0244554_field_005
#print axioms object_fragment0244554_field_006
#print axioms object_fragment0244554_field_007
#print axioms object_fragment0244554_field_008
#print axioms object_fragment0244554_field_009
#print axioms value_fragment0244554
#print axioms array_chunk0056_head
#print axioms array_chunk0056
#print axioms array_chunk0057_head
#print axioms array_chunk0057
#print axioms array_chunk0058_head
#print axioms array_chunk0058
#print axioms array_chunk0059_head
#print axioms array_chunk0059
#print axioms array_chunk0060_head
#print axioms array_chunk0060
#print axioms array_chunk0061_head
#print axioms array_chunk0061
#print axioms array_chunk0062_head
#print axioms array_chunk0062
#print axioms array_chunk0063_head
#print axioms array_chunk0063
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock007

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
