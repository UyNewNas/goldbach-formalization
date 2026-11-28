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

namespace SimplicesBlock000

noncomputable def fragment0124037Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0124037Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0124037Field000Value00 : SourceJson := .number (String.ofList ['0'])
noncomputable def fragment0124037Acc00100 : List (String × SourceJson) := (fragment0124037Field000Key00, fragment0124037Field000Value00) :: fragment0124037Acc00000
noncomputable def fragment0124037Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '0', ',']

theorem object_fragment0124037_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 565) (SourceJson.white (fragment0124037Field000Chars00 ++ tail)) fragment0124037Acc00000 =
      SourceJson.object (fuel + 564) (SourceJson.white tail) fragment0124037Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_000"
  err.flush

noncomputable def fragment0124037Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0124037Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['6']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0124037Acc00200 : List (String × SourceJson) := (fragment0124037Field001Key00, fragment0124037Field001Value00) :: fragment0124037Acc00100
noncomputable def fragment0124037Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0124037_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 564) (SourceJson.white (fragment0124037Field001Chars00 ++ tail)) fragment0124037Acc00100 =
      SourceJson.object (fuel + 563) (SourceJson.white tail) fragment0124037Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_001"
  err.flush

noncomputable def fragment0124037Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0124037Field002Value00 : SourceJson := .str (String.ofList ['7', '9', '0', '6', '5', '7', '1', '6', '6', '8', '7', '0', '9', '1', '7', '4', '1', '5', '1', '3', '3', '5', '0', '2', '7', '1', '7', '5', '3', '6', '7', '7', '2', '3', '6', '7', '9', '9', '4', '6', '6', '0', '9', '2', '5', '9', '/', '2', '4', '8', '5', '8', '5', '3', '9', '2', '1', '9', '7', '6', '4', '7', '0', '4', '7', '0', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0124037Acc00300 : List (String × SourceJson) := (fragment0124037Field002Key00, fragment0124037Field002Value00) :: fragment0124037Acc00200
noncomputable def fragment0124037Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '9', '0', '6', '5', '7', '1', '6', '6', '8', '7', '0', '9', '1', '7', '4', '1', '5', '1', '3', '3', '5', '0', '2', '7', '1', '7', '5', '3', '6', '7', '7', '2', '3', '6', '7', '9', '9', '4', '6', '6', '0', '9', '2', '5', '9', '/', '2', '4', '8', '5', '8', '5', '3', '9', '2', '1', '9', '7', '6', '4', '7', '0', '4', '7', '0', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0124037_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 563) (SourceJson.white (fragment0124037Field002Chars00 ++ tail)) fragment0124037Acc00200 =
      SourceJson.object (fuel + 562) (SourceJson.white tail) fragment0124037Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_002"
  err.flush

noncomputable def fragment0124037Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0124037Field003Value00 : SourceJson := .str (String.ofList ['2', '0', '1', '9', '3', '8', '7', '9', '4', '3', '2', '3', '5', '8', '9', '/', '3', '8', '7', '6', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0124037Acc00400 : List (String × SourceJson) := (fragment0124037Field003Key00, fragment0124037Field003Value00) :: fragment0124037Acc00300
noncomputable def fragment0124037Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '0', '1', '9', '3', '8', '7', '9', '4', '3', '2', '3', '5', '8', '9', '/', '3', '8', '7', '6', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0124037_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 562) (SourceJson.white (fragment0124037Field003Chars00 ++ tail)) fragment0124037Acc00300 =
      SourceJson.object (fuel + 561) (SourceJson.white tail) fragment0124037Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_003"
  err.flush

noncomputable def fragment0124037Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0124037Field004Value00 : SourceJson := .arr [.str (String.ofList ['5', '3', '9', '0', '5', '9', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '5', '/', '5', '5', '0', '4']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0124037Acc00500 : List (String × SourceJson) := (fragment0124037Field004Key00, fragment0124037Field004Value00) :: fragment0124037Acc00400
noncomputable def fragment0124037Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '5', '9', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '5', '/', '5', '5', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0124037_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 561) (SourceJson.white (fragment0124037Field004Chars00 ++ tail)) fragment0124037Acc00400 =
      SourceJson.object (fuel + 560) (SourceJson.white tail) fragment0124037Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_004"
  err.flush

noncomputable def fragment0124037Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0124037Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '7', '6', '0', '8', '2', '9', '7', '4', '3', '5', '1', '6', '9', '9', '5', '2', '9', '9', '0', '0', '0', '3', '4', '0', '0', '0', '0', '4', '9', '/', '7', '8', '2', '8', '1', '4', '1', '8', '3', '6', '8', '9', '9', '4', '1', '9', '9', '8', '7', '4', '7', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '2', '7', '4', '2', '0', '3', '8', '9', '8', '4', '5', '5', '9', '8', '1', '7', '5', '4', '5', '2', '5', '1', '5', '0', '4', '1', '/', '1', '7', '4', '7', '3', '5', '3', '0', '8', '8', '5', '9', '3', '6', '2', '0', '5', '3', '2', '9', '1', '9', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '4', '9', '0', '4', '2', '5', '0', '9', '3', '9', '8', '7', '1', '5', '1', '1', '5', '5', '9', '2', '7', '7', '3', '1', '3', '7', '0', '3', '/', '9', '7', '8', '5', '1', '7', '7', '2', '9', '6', '1', '2', '4', '2', '7', '4', '9', '8', '4', '3', '4', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '3', '1', '0', '1', '2', '4', '7', '2', '7', '5', '0', '9', '9', '2', '7', '3', '0', '0', '3', '7', '2', '0', '3', '5', '7', '5', '1', '3', '/', '9', '7', '8', '5', '1', '7', '7', '2', '9', '6', '1', '2', '4', '2', '7', '4', '9', '8', '4', '3', '4', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '4', '2', '5', '0', '2', '1', '6', '9', '3', '3', '9', '1', '6', '8', '8', '8', '6', '6', '8', '6', '4', '4', '5', '9', '0', '9', '7', '/', '3', '2', '6', '1', '7', '2', '5', '7', '6', '5', '3', '7', '4', '7', '5', '8', '3', '2', '8', '1', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '8', '4', '6', '2', '5', '1', '2', '8', '0', '3', '1', '8', '2', '2', '1', '7', '0', '6', '0', '1', '7', '6', '8', '1', '4', '2', '7', '/', '3', '5', '5', '8', '2', '4', '6', '2', '8', '9', '4', '9', '9', '7', '3', '6', '3', '5', '7', '9', '4', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '4', '3', '4', '4', '5', '1', '5', '3', '9', '2', '2', '0', '9', '3', '7', '5', '7', '9', '6', '3', '7', '4', '1', '1', '1', '/', '1', '1', '1', '1', '9', '5', '1', '9', '6', '5', '4', '6', '8', '6', '6', '7', '6', '1', '1', '8', '5', '7', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '7', '0', '9', '1', '3', '0', '7', '2', '2', '8', '2', '8', '6', '6', '0', '0', '7', '8', '1', '7', '4', '2', '6', '6', '9', '9', '/', '3', '5', '5', '8', '2', '4', '6', '2', '8', '9', '4', '9', '9', '7', '3', '6', '3', '5', '7', '9', '4', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '9', '8', '2', '8', '2', '1', '1', '2', '3', '3', '8', '0', '1', '5', '5', '6', '3', '9', '5', '3', '6', '4', '7', '2', '9', '/', '8', '8', '9', '5', '6', '1', '5', '7', '2', '3', '7', '4', '9', '3', '4', '0', '8', '9', '4', '8', '6', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '2', '0', '8', '2', '1', '1', '6', '0', '0', '2', '6', '8', '8', '2', '4', '5', '7', '2', '0', '1', '1', '6', '5', '0', '9', '3', '9', '/', '9', '3', '1', '9', '2', '1', '6', '4', '7', '2', '4', '9', '9', '3', '0', '9', '5', '0', '8', '9', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0124037Acc00600 : List (String × SourceJson) := (fragment0124037Field005Key00, fragment0124037Field005Value00) :: fragment0124037Acc00500
noncomputable def fragment0124037Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '6', '0', '8', '2', '9', '7', '4', '3', '5', '1', '6', '9', '9', '5', '2', '9', '9', '0', '0', '0', '3', '4', '0', '0', '0', '0', '4', '9', '/', '7', '8', '2', '8', '1', '4', '1', '8', '3', '6', '8', '9', '9', '4', '1', '9', '9', '8', '7', '4', '7', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '2', '7', '4', '2', '0', '3', '8', '9', '8', '4', '5', '5', '9', '8', '1', '7', '5', '4', '5', '2', '5', '1', '5', '0', '4', '1', '/', '1', '7', '4', '7', '3', '5', '3', '0', '8', '8', '5', '9', '3', '6', '2', '0', '5', '3', '2', '9', '1', '9', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '4', '9', '0', '4', '2', '5', '0', '9', '3', '9', '8', '7', '1', '5', '1', '1', '5', '5', '9', '2', '7', '7', '3', '1', '3', '7', '0', '3', '/', '9', '7', '8', '5', '1', '7', '7', '2', '9', '6', '1', '2', '4', '2', '7', '4', '9', '8', '4', '3', '4', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '3', '1', '0', '1', '2', '4', '7', '2', '7', '5', '0', '9', '9', '2', '7', '3', '0', '0', '3', '7', '2', '0', '3', '5', '7', '5', '1', '3', '/', '9', '7', '8', '5', '1', '7', '7', '2', '9', '6', '1', '2', '4', '2', '7', '4', '9', '8', '4', '3', '4', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '4', '2', '5', '0', '2', '1', '6', '9', '3', '3', '9', '1', '6', '8', '8', '8', '6', '6', '8', '6', '4', '4', '5', '9', '0', '9', '7', '/', '3', '2', '6', '1', '7', '2', '5', '7', '6', '5', '3', '7', '4', '7', '5', '8', '3', '2', '8', '1', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '4', '6', '2', '5', '1', '2', '8', '0', '3', '1', '8', '2', '2', '1', '7', '0', '6', '0', '1', '7', '6', '8', '1', '4', '2', '7', '/', '3', '5', '5', '8', '2', '4', '6', '2', '8', '9', '4', '9', '9', '7', '3', '6', '3', '5', '7', '9', '4', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '4', '3', '4', '4', '5', '1', '5', '3', '9', '2', '2', '0', '9', '3', '7', '5', '7', '9', '6', '3', '7', '4', '1', '1', '1', '/', '1', '1', '1', '1', '9', '5', '1', '9', '6', '5', '4', '6', '8', '6', '6', '7', '6', '1', '1', '8', '5', '7', '6', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '7', '0', '9', '1', '3', '0', '7', '2', '2', '8', '2', '8', '6', '6', '0', '0', '7', '8', '1', '7', '4', '2', '6', '6', '9', '9', '/', '3', '5', '5', '8', '2', '4', '6', '2', '8', '9', '4', '9', '9', '7', '3', '6', '3', '5', '7', '9', '4', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '9', '8', '2', '8', '2', '1', '1', '2', '3', '3', '8', '0', '1', '5', '5', '6', '3', '9', '5', '3', '6', '4', '7', '2', '9', '/', '8', '8', '9', '5', '6', '1', '5', '7', '2', '3', '7', '4', '9', '3', '4', '0', '8', '9', '4', '8', '6', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '2', '0', '8', '2', '1', '1', '6', '0', '0', '2', '6', '8', '8', '2', '4', '5', '7', '2', '0', '1', '1', '6', '5', '0', '9', '3', '9', '/', '9', '3', '1', '9', '2', '1', '6', '4', '7', '2', '4', '9', '9', '3', '0', '9', '5', '0', '8', '9', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0124037_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 560) (SourceJson.white (fragment0124037Field005Chars00 ++ tail)) fragment0124037Acc00500 =
      SourceJson.object (fuel + 559) (SourceJson.white tail) fragment0124037Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_005"
  err.flush

noncomputable def fragment0124037Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0124037Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '9', '6', '6', '4', '3', '5', '5', '0', '0', '1', '2', '1', '7', '7', '7', '8', '4', '5', '6', '2', '5', '0', '1', '8', '3', '2', '2', '0', '7', '3', '3', '4', '7', '3', '5', '1', '0', '3', '7', '2', '6', '5', '9', '6', '0', '2', '1', '9', '3', '6', '9', '8', '9', '5', '1', '0', '5', '5', '1', '/', '3', '8', '8', '5', '7', '0', '9', '0', '6', '3', '2', '9', '8', '4', '4', '8', '1', '9', '8', '7', '4', '9', '5', '6', '6', '1', '3', '4', '4', '5', '7', '9', '9', '6', '6', '5', '3', '7', '4', '4', '3', '7', '0', '9', '2', '5', '8', '6', '5', '5', '5', '5', '7', '3', '1', '0', '6', '0', '9', '0', '1', '4', '0', '5', '2', '3', '1', '4', '4', '0', '2', '9', '0', '1', '7', '6', '0'])
noncomputable def fragment0124037Acc00700 : List (String × SourceJson) := (fragment0124037Field006Key00, fragment0124037Field006Value00) :: fragment0124037Acc00600
noncomputable def fragment0124037Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '9', '6', '6', '4', '3', '5', '5', '0', '0', '1', '2', '1', '7', '7', '7', '8', '4', '5', '6', '2', '5', '0', '1', '8', '3', '2', '2', '0', '7', '3', '3', '4', '7', '3', '5', '1', '0', '3', '7', '2', '6', '5', '9', '6', '0', '2', '1', '9', '3', '6', '9', '8', '9', '5', '1', '0', '5', '5', '1', '/', '3', '8', '8', '5', '7', '0', '9', '0', '6', '3', '2', '9', '8', '4', '4', '8', '1', '9', '8', '7', '4', '9', '5', '6', '6', '1', '3', '4', '4', '5', '7', '9', '9', '6', '6', '5', '3', '7', '4', '4', '3', '7', '0', '9', '2', '5', '8', '6', '5', '5', '5', '5', '7', '3', '1', '0', '6', '0', '9', '0', '1', '4', '0', '5', '2', '3', '1', '4', '4', '0', '2', '9', '0', '1', '7', '6', '0', '"', ',']

theorem object_fragment0124037_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 559) (SourceJson.white (fragment0124037Field006Chars00 ++ tail)) fragment0124037Acc00600 =
      SourceJson.object (fuel + 558) (SourceJson.white tail) fragment0124037Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_006"
  err.flush

noncomputable def fragment0124037Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0124037Field007Value00 : SourceJson := .str (String.ofList ['3', '6', '9', '7', '2', '1', '7', '7', '3', '1', '1', '0', '7', '1', '9', '0', '8', '4', '1', '2', '3', '4', '4', '0', '5', '8', '4', '5', '8', '0', '0', '6', '6', '0', '0', '6', '1', '4', '1', '0', '4', '6', '4', '4', '2', '2', '3', '9', '9', '8', '5', '4', '7', '9', '6', '3', '4', '2', '8', '2', '1', '3', '5', '8', '8', '5', '3', '9', '7', '6', '2', '5', '9', '7', '5', '5', '3', '5', '9', '3', '8', '4', '5', '0', '4', '8', '1', '7', '2', '2', '0', '5', '1', '2', '7', '1', '5', '4', '9', '2', '4', '3', '6', '0', '3', '2', '8', '7', '3', '4', '5', '2', '7', '4', '9', '6', '9', '9', '0', '2', '2', '5', '3', '5', '4', '7', '0', '9', '0', '6', '3', '2', '5', '6', '1', '9', '2', '9', '5', '2', '2', '9', '8', '7', '7', '6', '0', '1', '0', '4', '3', '4', '4', '6', '5', '5', '6', '1', '4', '3', '6', '7', '1', '8', '2', '2', '0', '7', '4', '0', '7', '6', '2', '5', '2', '6', '9', '4', '9', '1', '9', '4', '5', '1', '7', '9', '1', '0', '8', '3', '0', '5', '9', '5', '7', '1', '6', '2', '2', '9', '2', '9', '3', '2', '3', '3', '5', '9', '6', '2', '0', '8', '9', '8', '0', '7', '0', '4', '5', '8', '8', '0', '8', '0', '7', '9', '5', '2', '2', '6', '6', '4', '5', '7', '3', '3', '9', '0', '2', '9', '3', '1', '3', '7', '9', '2', '0', '8', '7', '6', '4', '7', '8', '1', '9', '6', '5', '7', '8', '9', '7', '9', '4', '9', '2', '1', '8', '7', '5', '/', '4', '3', '8', '6', '1', '0', '8', '1', '6', '7', '9', '8', '1', '6', '8', '3', '4', '1', '7', '5', '5', '7', '5', '5', '2', '6', '2', '7', '0', '8', '4', '9', '8', '5', '9', '6', '0', '9', '9', '7', '8', '8', '8', '5', '3', '7', '8', '3', '9', '7', '7', '9', '7', '8', '1', '2', '3', '9', '6', '7', '0', '4', '9', '1', '5', '4', '1', '5', '0', '0', '5', '4', '6', '8', '7', '6', '0', '9', '0', '1', '6', '3', '8', '4', '3', '7', '0', '9', '0', '0', '1', '3', '0', '6', '5', '1', '2', '9', '8', '7', '9', '3', '8', '4', '3', '8', '8', '1', '0', '8', '8', '6', '4', '5', '1', '0', '6', '6', '6', '1', '5', '6', '2', '9', '9', '9', '5', '7', '4', '9', '0', '1', '7', '2', '3', '6', '8', '0', '7', '6', '2', '9', '6', '0', '9', '3', '4', '1', '2', '6', '5', '4', '3', '6', '9', '3', '0', '8', '8', '7', '3', '5', '3', '7', '0', '9', '9', '9', '1', '4', '1', '2', '1', '8', '0', '1', '7', '9', '5', '2', '9', '3', '2', '6', '3', '3', '9', '6', '6', '3', '8', '4', '4', '6', '4', '2', '2', '2', '2', '3', '9', '1', '2', '6', '7', '5', '9', '3', '3', '7', '3', '3', '6', '0', '1', '7', '9', '6', '8', '7', '6', '7', '8', '2', '9', '4', '0', '7', '9', '4', '8', '6', '3', '6', '2', '1', '7', '6', '9', '7', '5', '4', '9', '0', '6', '5', '3', '8', '3', '6', '0', '6', '8', '7', '3', '5', '3', '7', '0', '4', '2', '8', '6', '1', '4', '4', '9', '7', '8', '0', '4', '0', '8', '1', '0', '6', '3', '1', '2', '5', '0', '2', '3', '5', '2'])
noncomputable def fragment0124037Acc00800 : List (String × SourceJson) := (fragment0124037Field007Key00, fragment0124037Field007Value00) :: fragment0124037Acc00700
noncomputable def fragment0124037Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '6', '9', '7', '2', '1', '7', '7', '3', '1', '1', '0', '7', '1', '9', '0', '8', '4', '1', '2', '3', '4', '4', '0', '5', '8', '4', '5', '8', '0', '0', '6', '6', '0', '0', '6', '1', '4', '1', '0', '4', '6', '4', '4', '2', '2', '3', '9', '9', '8', '5', '4', '7', '9', '6', '3', '4', '2', '8', '2', '1', '3', '5', '8', '8', '5', '3', '9', '7', '6', '2', '5', '9', '7', '5', '5', '3', '5', '9', '3', '8', '4', '5', '0', '4', '8', '1', '7', '2', '2', '0', '5', '1', '2', '7', '1', '5', '4', '9', '2', '4', '3', '6', '0', '3', '2', '8', '7', '3', '4', '5', '2', '7', '4', '9', '6', '9', '9', '0', '2', '2', '5', '3', '5', '4', '7', '0', '9', '0', '6', '3', '2', '5', '6', '1', '9', '2', '9', '5', '2', '2', '9', '8', '7', '7', '6', '0', '1', '0', '4', '3', '4', '4', '6', '5', '5', '6', '1', '4', '3', '6', '7', '1', '8', '2', '2', '0', '7', '4', '0', '7', '6', '2', '5', '2', '6', '9', '4', '9', '1', '9', '4', '5', '1', '7', '9', '1', '0', '8', '3', '0', '5', '9', '5', '7', '1', '6', '2', '2', '9', '2', '9', '3', '2', '3', '3', '5', '9', '6', '2', '0', '8', '9', '8', '0', '7', '0', '4', '5', '8', '8', '0', '8', '0', '7', '9', '5', '2', '2', '6', '6', '4', '5', '7', '3', '3', '9', '0', '2', '9', '3', '1', '3', '7', '9', '2', '0', '8', '7', '6', '4', '7', '8', '1', '9', '6', '5', '7', '8', '9', '7', '9', '4', '9', '2', '1', '8', '7', '5', '/', '4', '3', '8', '6', '1', '0', '8', '1', '6', '7', '9', '8', '1', '6', '8', '3', '4', '1', '7', '5', '5', '7', '5', '5', '2', '6', '2', '7', '0', '8', '4', '9', '8', '5', '9', '6', '0', '9', '9', '7', '8', '8', '8', '5', '3', '7', '8', '3', '9', '7', '7', '9', '7', '8', '1', '2', '3', '9', '6', '7', '0', '4', '9', '1', '5', '4', '1', '5', '0', '0', '5', '4', '6', '8', '7', '6', '0', '9', '0', '1', '6', '3', '8', '4', '3', '7', '0', '9', '0', '0', '1', '3', '0', '6', '5', '1', '2', '9', '8', '7', '9', '3', '8', '4', '3', '8', '8', '1', '0', '8', '8', '6', '4', '5', '1', '0', '6', '6', '6', '1', '5', '6', '2', '9', '9', '9', '5', '7', '4', '9', '0', '1', '7', '2', '3', '6', '8', '0', '7', '6', '2', '9', '6', '0', '9', '3', '4', '1', '2', '6', '5', '4', '3', '6', '9', '3', '0', '8', '8', '7', '3', '5', '3', '7', '0', '9', '9', '9', '1', '4', '1', '2', '1', '8', '0', '1', '7', '9', '5', '2', '9', '3', '2', '6', '3', '3', '9', '6', '6', '3', '8', '4', '4', '6', '4', '2', '2', '2', '2', '3', '9', '1', '2', '6', '7', '5', '9', '3', '3', '7', '3', '3', '6', '0', '1', '7', '9', '6', '8', '7', '6', '7', '8', '2', '9', '4', '0', '7', '9', '4', '8', '6', '3', '6', '2', '1', '7', '6', '9', '7', '5', '4', '9', '0', '6', '5', '3', '8', '3', '6', '0', '6', '8', '7', '3', '5', '3', '7', '0', '4', '2', '8', '6', '1', '4', '4', '9', '7', '8', '0', '4', '0', '8', '1', '0', '6', '3', '1', '2', '5', '0', '2', '3', '5', '2', '"', ',']

theorem object_fragment0124037_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 558) (SourceJson.white (fragment0124037Field007Chars00 ++ tail)) fragment0124037Acc00700 =
      SourceJson.object (fuel + 557) (SourceJson.white tail) fragment0124037Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_007"
  err.flush

noncomputable def fragment0124037Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0124037Field008Value00 : SourceJson := .str (String.ofList ['3', '2', '5', '5', '4', '9', '6', '8', '1', '1', '4', '4', '5'])
noncomputable def fragment0124037Acc00900 : List (String × SourceJson) := (fragment0124037Field008Key00, fragment0124037Field008Value00) :: fragment0124037Acc00800
noncomputable def fragment0124037Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '5', '5', '4', '9', '6', '8', '1', '1', '4', '4', '5', '"', ',']

theorem object_fragment0124037_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 557) (SourceJson.white (fragment0124037Field008Chars00 ++ tail)) fragment0124037Acc00800 =
      SourceJson.object (fuel + 556) (SourceJson.white tail) fragment0124037Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_008"
  err.flush

noncomputable def fragment0124037Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0124037Field009Value00 : SourceJson := .str (String.ofList ['6', '6', '7', '8', '4', '4', '3', '7', '5', '9', '9', '8', '5'])
noncomputable def fragment0124037Acc01000 : List (String × SourceJson) := (fragment0124037Field009Key00, fragment0124037Field009Value00) :: fragment0124037Acc00900
noncomputable def fragment0124037Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '7', '8', '4', '4', '3', '7', '5', '9', '9', '8', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0124037_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 556) (SourceJson.white (fragment0124037Field009Chars00 ++ tail)) fragment0124037Acc00900 =
      .ok (.obj (fragment0124037Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0124037_object_field_009"
  err.flush

noncomputable def fragment0124037Chars : List Char := '{' :: (fragment0124037Field000Chars00 ++ fragment0124037Field001Chars00 ++ fragment0124037Field002Chars00 ++ fragment0124037Field003Chars00 ++ fragment0124037Field004Chars00 ++ fragment0124037Field005Chars00 ++ fragment0124037Field006Chars00 ++ fragment0124037Field007Chars00 ++ fragment0124037Field008Chars00 ++ fragment0124037Field009Chars00)
noncomputable def fragment0124037Value : SourceJson := .obj (fragment0124037Acc01000.reverse)

theorem value_fragment0124037 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 566) (fragment0124037Chars ++ tail) =
      .ok (fragment0124037Value, tail) := by
  have hinput : fragment0124037Chars ++ tail = '{' :: (fragment0124037Field000Chars00 ++ (fragment0124037Field001Chars00 ++ (fragment0124037Field002Chars00 ++ (fragment0124037Field003Chars00 ++ (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0124037Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 566) (fragment0124037Chars ++ tail) =
        SourceJson.value (fuel + 566) ('{' :: (fragment0124037Field000Chars00 ++ (fragment0124037Field001Chars00 ++ (fragment0124037Field002Chars00 ++ (fragment0124037Field003Chars00 ++ (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 566)) hinput
    _ = SourceJson.object (fuel + 565) (SourceJson.white (fragment0124037Field000Chars00 ++ (fragment0124037Field001Chars00 ++ (fragment0124037Field002Chars00 ++ (fragment0124037Field003Chars00 ++ (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))))))))))) fragment0124037Acc00000 := by rfl
    _ = SourceJson.object (fuel + 564) (SourceJson.white (fragment0124037Field001Chars00 ++ (fragment0124037Field002Chars00 ++ (fragment0124037Field003Chars00 ++ (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail))))))))))) fragment0124037Acc00100 := object_fragment0124037_field_000 fuel (fragment0124037Field001Chars00 ++ (fragment0124037Field002Chars00 ++ (fragment0124037Field003Chars00 ++ (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 563) (SourceJson.white (fragment0124037Field002Chars00 ++ (fragment0124037Field003Chars00 ++ (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))))))))) fragment0124037Acc00200 := object_fragment0124037_field_001 fuel (fragment0124037Field002Chars00 ++ (fragment0124037Field003Chars00 ++ (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 562) (SourceJson.white (fragment0124037Field003Chars00 ++ (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail))))))))) fragment0124037Acc00300 := object_fragment0124037_field_002 fuel (fragment0124037Field003Chars00 ++ (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 561) (SourceJson.white (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))))))) fragment0124037Acc00400 := object_fragment0124037_field_003 fuel (fragment0124037Field004Chars00 ++ (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 560) (SourceJson.white (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail))))))) fragment0124037Acc00500 := object_fragment0124037_field_004 fuel (fragment0124037Field005Chars00 ++ (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 559) (SourceJson.white (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))))) fragment0124037Acc00600 := object_fragment0124037_field_005 fuel (fragment0124037Field006Chars00 ++ (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 558) (SourceJson.white (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail))))) fragment0124037Acc00700 := object_fragment0124037_field_006 fuel (fragment0124037Field007Chars00 ++ (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 557) (SourceJson.white (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))) fragment0124037Acc00800 := object_fragment0124037_field_007 fuel (fragment0124037Field008Chars00 ++ (fragment0124037Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 556) (SourceJson.white (fragment0124037Field009Chars00 ++ (tail))) fragment0124037Acc00900 := object_fragment0124037_field_008 fuel (fragment0124037Field009Chars00 ++ (tail))
    _ = .ok (fragment0124037Value, tail) := object_fragment0124037_field_009 fuel (tail)

noncomputable def fragment0126332Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0126332Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0126332Field000Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0126332Acc00100 : List (String × SourceJson) := (fragment0126332Field000Key00, fragment0126332Field000Value00) :: fragment0126332Acc00000
noncomputable def fragment0126332Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', ',']

theorem object_fragment0126332_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 498) (SourceJson.white (fragment0126332Field000Chars00 ++ tail)) fragment0126332Acc00000 =
      SourceJson.object (fuel + 497) (SourceJson.white tail) fragment0126332Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_000"
  err.flush

noncomputable def fragment0126332Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0126332Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0126332Acc00200 : List (String × SourceJson) := (fragment0126332Field001Key00, fragment0126332Field001Value00) :: fragment0126332Acc00100
noncomputable def fragment0126332Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0126332_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 497) (SourceJson.white (fragment0126332Field001Chars00 ++ tail)) fragment0126332Acc00100 =
      SourceJson.object (fuel + 496) (SourceJson.white tail) fragment0126332Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_001"
  err.flush

noncomputable def fragment0126332Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0126332Field002Value00 : SourceJson := .str (String.ofList ['8', '5', '8', '8', '8', '6', '0', '8', '0', '5', '5', '3', '7', '0', '6', '1', '3', '3', '1', '4', '9', '6', '4', '9', '9', '8', '4', '4', '4', '3', '3', '2', '6', '6', '8', '3', '5', '2', '5', '6', '6', '1', '0', '6', '9', '3', '/', '1', '8', '4', '5', '9', '3', '1', '1', '3', '0', '1', '8', '0', '5', '4', '7', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0126332Acc00300 : List (String × SourceJson) := (fragment0126332Field002Key00, fragment0126332Field002Value00) :: fragment0126332Acc00200
noncomputable def fragment0126332Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '5', '8', '8', '8', '6', '0', '8', '0', '5', '5', '3', '7', '0', '6', '1', '3', '3', '1', '4', '9', '6', '4', '9', '9', '8', '4', '4', '4', '3', '3', '2', '6', '6', '8', '3', '5', '2', '5', '6', '6', '1', '0', '6', '9', '3', '/', '1', '8', '4', '5', '9', '3', '1', '1', '3', '0', '1', '8', '0', '5', '4', '7', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0126332_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 496) (SourceJson.white (fragment0126332Field002Chars00 ++ tail)) fragment0126332Acc00200 =
      SourceJson.object (fuel + 495) (SourceJson.white tail) fragment0126332Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_002"
  err.flush

noncomputable def fragment0126332Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0126332Field003Value00 : SourceJson := .str (String.ofList ['1', '7', '1', '4', '9', '2', '6', '3', '6', '4', '2', '1', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0126332Acc00400 : List (String × SourceJson) := (fragment0126332Field003Key00, fragment0126332Field003Value00) :: fragment0126332Acc00300
noncomputable def fragment0126332Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '7', '1', '4', '9', '2', '6', '3', '6', '4', '2', '1', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0126332_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 495) (SourceJson.white (fragment0126332Field003Chars00 ++ tail)) fragment0126332Acc00300 =
      SourceJson.object (fuel + 494) (SourceJson.white tail) fragment0126332Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_003"
  err.flush

noncomputable def fragment0126332Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0126332Field004Value00 : SourceJson := .arr [.str (String.ofList ['5', '3', '9', '0', '5', '9', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '5', '/', '5', '5', '0', '4']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0126332Acc00500 : List (String × SourceJson) := (fragment0126332Field004Key00, fragment0126332Field004Value00) :: fragment0126332Acc00400
noncomputable def fragment0126332Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '9', '0', '5', '9', '7', '/', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '5', '/', '5', '5', '0', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0126332_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 494) (SourceJson.white (fragment0126332Field004Chars00 ++ tail)) fragment0126332Acc00400 =
      SourceJson.object (fuel + 493) (SourceJson.white tail) fragment0126332Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_004"
  err.flush

noncomputable def fragment0126332Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0126332Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '5', '2', '7', '9', '1', '0', '4', '0', '7', '3', '9', '7', '3', '2', '6', '0', '0', '2', '9', '8', '7', '9', '9', '5', '3', '/', '3', '2', '9', '1', '0', '3', '9', '0', '4', '2', '8', '4', '2', '1', '1', '1', '5', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '4', '7', '9', '9', '8', '0', '1', '4', '1', '4', '4', '6', '5', '0', '0', '0', '2', '4', '7', '0', '0', '4', '7', '3', '/', '2', '3', '5', '0', '7', '4', '2', '1', '7', '3', '4', '5', '8', '6', '5', '1', '1', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '0', '8', '6', '9', '4', '4', '3', '8', '6', '4', '9', '6', '0', '7', '6', '5', '7', '6', '3', '8', '3', '9', '3', '9', '9', '/', '3', '2', '9', '1', '0', '3', '9', '0', '4', '2', '8', '4', '2', '1', '1', '1', '5', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '3', '9', '5', '1', '6', '1', '0', '7', '0', '2', '7', '0', '0', '4', '5', '6', '5', '1', '6', '7', '2', '8', '3', '/', '1', '3', '1', '6', '4', '1', '5', '6', '1', '7', '1', '3', '6', '8', '4', '4', '6', '3', '0', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '6', '6', '2', '8', '5', '2', '5', '2', '1', '6', '5', '8', '4', '0', '5', '9', '6', '9', '2', '2', '1', '2', '9', '9', '/', '1', '0', '9', '7', '0', '1', '3', '0', '1', '4', '2', '8', '0', '7', '0', '3', '8', '5', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '8', '9', '2', '2', '8', '5', '4', '6', '0', '2', '2', '0', '4', '1', '2', '8', '2', '9', '1', '6', '7', '1', '9', '3', '/', '2', '9', '9', '1', '8', '5', '3', '6', '7', '5', '3', '1', '1', '0', '1', '0', '5', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '7', '9', '8', '9', '2', '8', '4', '3', '1', '0', '7', '4', '7', '3', '8', '0', '9', '0', '0', '2', '9', '9', '7', '/', '1', '4', '9', '5', '9', '2', '6', '8', '3', '7', '6', '5', '5', '5', '0', '5', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '2', '5', '3', '3', '2', '2', '4', '0', '6', '3', '8', '9', '9', '1', '8', '1', '9', '5', '4', '2', '3', '4', '1', '/', '7', '4', '7', '9', '6', '3', '4', '1', '8', '8', '2', '7', '7', '5', '2', '6', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '1', '7', '2', '7', '4', '7', '6', '9', '3', '7', '8', '7', '5', '7', '3', '7', '9', '2', '4', '2', '8', '3', '7', '/', '1', '4', '9', '5', '9', '2', '6', '8', '3', '7', '6', '5', '5', '5', '0', '5', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '1', '8', '3', '1', '8', '0', '7', '3', '3', '3', '1', '5', '9', '0', '8', '6', '8', '8', '0', '1', '5', '1', '1', '/', '7', '8', '3', '5', '8', '0', '7', '2', '4', '4', '8', '6', '2', '1', '7', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0126332Acc00600 : List (String × SourceJson) := (fragment0126332Field005Key00, fragment0126332Field005Value00) :: fragment0126332Acc00500
noncomputable def fragment0126332Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '2', '7', '9', '1', '0', '4', '0', '7', '3', '9', '7', '3', '2', '6', '0', '0', '2', '9', '8', '7', '9', '9', '5', '3', '/', '3', '2', '9', '1', '0', '3', '9', '0', '4', '2', '8', '4', '2', '1', '1', '1', '5', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '4', '7', '9', '9', '8', '0', '1', '4', '1', '4', '4', '6', '5', '0', '0', '0', '2', '4', '7', '0', '0', '4', '7', '3', '/', '2', '3', '5', '0', '7', '4', '2', '1', '7', '3', '4', '5', '8', '6', '5', '1', '1', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '0', '8', '6', '9', '4', '4', '3', '8', '6', '4', '9', '6', '0', '7', '6', '5', '7', '6', '3', '8', '3', '9', '3', '9', '9', '/', '3', '2', '9', '1', '0', '3', '9', '0', '4', '2', '8', '4', '2', '1', '1', '1', '5', '7', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '3', '9', '5', '1', '6', '1', '0', '7', '0', '2', '7', '0', '0', '4', '5', '6', '5', '1', '6', '7', '2', '8', '3', '/', '1', '3', '1', '6', '4', '1', '5', '6', '1', '7', '1', '3', '6', '8', '4', '4', '6', '3', '0', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '6', '6', '2', '8', '5', '2', '5', '2', '1', '6', '5', '8', '4', '0', '5', '9', '6', '9', '2', '2', '1', '2', '9', '9', '/', '1', '0', '9', '7', '0', '1', '3', '0', '1', '4', '2', '8', '0', '7', '0', '3', '8', '5', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '9', '2', '2', '8', '5', '4', '6', '0', '2', '2', '0', '4', '1', '2', '8', '2', '9', '1', '6', '7', '1', '9', '3', '/', '2', '9', '9', '1', '8', '5', '3', '6', '7', '5', '3', '1', '1', '0', '1', '0', '5', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '7', '9', '8', '9', '2', '8', '4', '3', '1', '0', '7', '4', '7', '3', '8', '0', '9', '0', '0', '2', '9', '9', '7', '/', '1', '4', '9', '5', '9', '2', '6', '8', '3', '7', '6', '5', '5', '5', '0', '5', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '5', '3', '3', '2', '2', '4', '0', '6', '3', '8', '9', '9', '1', '8', '1', '9', '5', '4', '2', '3', '4', '1', '/', '7', '4', '7', '9', '6', '3', '4', '1', '8', '8', '2', '7', '7', '5', '2', '6', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '1', '7', '2', '7', '4', '7', '6', '9', '3', '7', '8', '7', '5', '7', '3', '7', '9', '2', '4', '2', '8', '3', '7', '/', '1', '4', '9', '5', '9', '2', '6', '8', '3', '7', '6', '5', '5', '5', '0', '5', '2', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '1', '8', '3', '1', '8', '0', '7', '3', '3', '3', '1', '5', '9', '0', '8', '6', '8', '8', '0', '1', '5', '1', '1', '/', '7', '8', '3', '5', '8', '0', '7', '2', '4', '4', '8', '6', '2', '1', '7', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0126332_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 493) (SourceJson.white (fragment0126332Field005Chars00 ++ tail)) fragment0126332Acc00500 =
      SourceJson.object (fuel + 492) (SourceJson.white tail) fragment0126332Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_005"
  err.flush

noncomputable def fragment0126332Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0126332Field006Value00 : SourceJson := .str (String.ofList ['1', '4', '7', '2', '9', '2', '6', '3', '8', '3', '4', '0', '2', '2', '7', '4', '4', '1', '7', '2', '8', '8', '0', '9', '0', '7', '5', '8', '8', '5', '3', '8', '2', '4', '1', '4', '0', '0', '3', '5', '9', '2', '9', '1', '8', '1', '9', '6', '3', '1', '2', '0', '7', '9', '9', '3', '7', '6', '7', '/', '3', '4', '2', '8', '1', '4', '8', '8', '0', '7', '3', '6', '7', '6', '0', '4', '1', '0', '4', '3', '4', '6', '2', '4', '2', '7', '9', '7', '6', '0', '5', '4', '4', '8', '7', '1', '4', '2', '0', '1', '6', '2', '2', '0', '0', '1', '5', '3', '6', '2', '2', '8', '7', '4', '6', '6', '4', '1', '3', '7', '6', '7', '5', '7', '9', '6', '4', '5', '1', '8', '2', '7', '2', '0'])
noncomputable def fragment0126332Acc00700 : List (String × SourceJson) := (fragment0126332Field006Key00, fragment0126332Field006Value00) :: fragment0126332Acc00600
noncomputable def fragment0126332Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '7', '2', '9', '2', '6', '3', '8', '3', '4', '0', '2', '2', '7', '4', '4', '1', '7', '2', '8', '8', '0', '9', '0', '7', '5', '8', '8', '5', '3', '8', '2', '4', '1', '4', '0', '0', '3', '5', '9', '2', '9', '1', '8', '1', '9', '6', '3', '1', '2', '0', '7', '9', '9', '3', '7', '6', '7', '/', '3', '4', '2', '8', '1', '4', '8', '8', '0', '7', '3', '6', '7', '6', '0', '4', '1', '0', '4', '3', '4', '6', '2', '4', '2', '7', '9', '7', '6', '0', '5', '4', '4', '8', '7', '1', '4', '2', '0', '1', '6', '2', '2', '0', '0', '1', '5', '3', '6', '2', '2', '8', '7', '4', '6', '6', '4', '1', '3', '7', '6', '7', '5', '7', '9', '6', '4', '5', '1', '8', '2', '7', '2', '0', '"', ',']

theorem object_fragment0126332_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 492) (SourceJson.white (fragment0126332Field006Chars00 ++ tail)) fragment0126332Acc00600 =
      SourceJson.object (fuel + 491) (SourceJson.white tail) fragment0126332Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_006"
  err.flush

noncomputable def fragment0126332Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0126332Field007Value00 : SourceJson := .str (String.ofList ['7', '0', '9', '9', '4', '1', '0', '9', '0', '8', '0', '7', '1', '6', '4', '1', '6', '5', '2', '3', '3', '8', '4', '3', '6', '8', '7', '6', '8', '3', '6', '2', '3', '5', '4', '9', '6', '7', '1', '6', '2', '2', '2', '9', '0', '1', '8', '6', '7', '9', '8', '4', '0', '3', '5', '5', '0', '6', '0', '6', '9', '0', '3', '7', '3', '0', '1', '9', '8', '5', '5', '2', '9', '8', '9', '9', '0', '6', '5', '8', '5', '7', '0', '0', '6', '1', '1', '3', '0', '9', '4', '0', '3', '2', '9', '1', '9', '0', '4', '1', '1', '7', '6', '6', '3', '3', '4', '5', '0', '1', '9', '2', '5', '5', '4', '8', '0', '6', '2', '2', '2', '6', '8', '7', '8', '1', '3', '6', '3', '6', '9', '6', '7', '0', '9', '9', '6', '1', '0', '0', '3', '8', '6', '2', '3', '1', '4', '6', '2', '9', '4', '0', '6', '5', '8', '8', '9', '0', '9', '5', '1', '4', '6', '6', '0', '3', '7', '9', '8', '7', '6', '5', '0', '8', '1', '1', '4', '5', '0', '8', '8', '9', '9', '7', '4', '6', '3', '5', '2', '5', '5', '8', '3', '4', '5', '0', '1', '2', '2', '0', '3', '4', '6', '0', '3', '9', '3', '8', '3', '2', '7', '9', '1', '4', '4', '3', '1', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '9', '3', '5', '4', '6', '5', '4', '4', '5', '2', '5', '1', '6', '7', '8', '5', '6', '8', '0', '9', '1', '4', '8', '0', '0', '2', '8', '7', '7', '3', '1', '1', '8', '1', '2', '1', '3', '2', '2', '1', '9', '2', '3', '0', '1', '3', '5', '6', '3', '1', '2', '2', '5', '5', '1', '5', '1', '7', '3', '1', '2', '1', '7', '4', '3', '3', '0', '0', '8', '6', '7', '2', '1', '2', '6', '4', '3', '1', '8', '2', '2', '5', '7', '0', '9', '3', '1', '6', '6', '1', '7', '8', '7', '2', '6', '5', '5', '4', '9', '6', '7', '5', '1', '5', '0', '4', '5', '6', '3', '8', '8', '7', '5', '4', '4', '1', '3', '8', '6', '4', '6', '6', '5', '3', '2', '4', '0', '0', '8', '9', '7', '4', '6', '1', '5', '1', '8', '5', '7', '3', '5', '8', '1', '0', '0', '8', '2', '2', '0', '9', '0', '0', '5', '8', '7', '6', '8', '6', '9', '8', '9', '8', '1', '6', '7', '8', '6', '1', '0', '9', '3', '0', '6', '3', '8', '2', '9', '0', '8', '1', '2', '1', '9', '7', '8', '6', '9', '4', '7', '7', '6', '9', '9', '8', '0', '8', '1', '0', '5', '3', '4', '3', '3', '3', '6', '2', '0', '0', '8', '1', '2', '4', '5', '9', '6', '8', '7', '2', '7', '6', '5', '5', '0', '7', '8', '2', '2', '6', '2', '3', '7', '9', '6', '9', '6', '3', '9', '7', '0', '8', '8', '8', '0', '9', '4', '3', '2', '1', '4', '1'])
noncomputable def fragment0126332Acc00800 : List (String × SourceJson) := (fragment0126332Field007Key00, fragment0126332Field007Value00) :: fragment0126332Acc00700
noncomputable def fragment0126332Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '0', '9', '9', '4', '1', '0', '9', '0', '8', '0', '7', '1', '6', '4', '1', '6', '5', '2', '3', '3', '8', '4', '3', '6', '8', '7', '6', '8', '3', '6', '2', '3', '5', '4', '9', '6', '7', '1', '6', '2', '2', '2', '9', '0', '1', '8', '6', '7', '9', '8', '4', '0', '3', '5', '5', '0', '6', '0', '6', '9', '0', '3', '7', '3', '0', '1', '9', '8', '5', '5', '2', '9', '8', '9', '9', '0', '6', '5', '8', '5', '7', '0', '0', '6', '1', '1', '3', '0', '9', '4', '0', '3', '2', '9', '1', '9', '0', '4', '1', '1', '7', '6', '6', '3', '3', '4', '5', '0', '1', '9', '2', '5', '5', '4', '8', '0', '6', '2', '2', '2', '6', '8', '7', '8', '1', '3', '6', '3', '6', '9', '6', '7', '0', '9', '9', '6', '1', '0', '0', '3', '8', '6', '2', '3', '1', '4', '6', '2', '9', '4', '0', '6', '5', '8', '8', '9', '0', '9', '5', '1', '4', '6', '6', '0', '3', '7', '9', '8', '7', '6', '5', '0', '8', '1', '1', '4', '5', '0', '8', '8', '9', '9', '7', '4', '6', '3', '5', '2', '5', '5', '8', '3', '4', '5', '0', '1', '2', '2', '0', '3', '4', '6', '0', '3', '9', '3', '8', '3', '2', '7', '9', '1', '4', '4', '3', '1', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '9', '3', '5', '4', '6', '5', '4', '4', '5', '2', '5', '1', '6', '7', '8', '5', '6', '8', '0', '9', '1', '4', '8', '0', '0', '2', '8', '7', '7', '3', '1', '1', '8', '1', '2', '1', '3', '2', '2', '1', '9', '2', '3', '0', '1', '3', '5', '6', '3', '1', '2', '2', '5', '5', '1', '5', '1', '7', '3', '1', '2', '1', '7', '4', '3', '3', '0', '0', '8', '6', '7', '2', '1', '2', '6', '4', '3', '1', '8', '2', '2', '5', '7', '0', '9', '3', '1', '6', '6', '1', '7', '8', '7', '2', '6', '5', '5', '4', '9', '6', '7', '5', '1', '5', '0', '4', '5', '6', '3', '8', '8', '7', '5', '4', '4', '1', '3', '8', '6', '4', '6', '6', '5', '3', '2', '4', '0', '0', '8', '9', '7', '4', '6', '1', '5', '1', '8', '5', '7', '3', '5', '8', '1', '0', '0', '8', '2', '2', '0', '9', '0', '0', '5', '8', '7', '6', '8', '6', '9', '8', '9', '8', '1', '6', '7', '8', '6', '1', '0', '9', '3', '0', '6', '3', '8', '2', '9', '0', '8', '1', '2', '1', '9', '7', '8', '6', '9', '4', '7', '7', '6', '9', '9', '8', '0', '8', '1', '0', '5', '3', '4', '3', '3', '3', '6', '2', '0', '0', '8', '1', '2', '4', '5', '9', '6', '8', '7', '2', '7', '6', '5', '5', '0', '7', '8', '2', '2', '6', '2', '3', '7', '9', '6', '9', '6', '3', '9', '7', '0', '8', '8', '8', '0', '9', '4', '3', '2', '1', '4', '1', '"', ',']

theorem object_fragment0126332_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 491) (SourceJson.white (fragment0126332Field007Chars00 ++ tail)) fragment0126332Acc00700 =
      SourceJson.object (fuel + 490) (SourceJson.white tail) fragment0126332Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_007"
  err.flush

noncomputable def fragment0126332Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0126332Field008Value00 : SourceJson := .str (String.ofList ['3', '4', '0', '4', '0', '8', '9', '4', '2', '0', '6', '5', '0', '0'])
noncomputable def fragment0126332Acc00900 : List (String × SourceJson) := (fragment0126332Field008Key00, fragment0126332Field008Value00) :: fragment0126332Acc00800
noncomputable def fragment0126332Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '0', '4', '0', '8', '9', '4', '2', '0', '6', '5', '0', '0', '"', ',']

theorem object_fragment0126332_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 490) (SourceJson.white (fragment0126332Field008Chars00 ++ tail)) fragment0126332Acc00800 =
      SourceJson.object (fuel + 489) (SourceJson.white tail) fragment0126332Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_008"
  err.flush

noncomputable def fragment0126332Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0126332Field009Value00 : SourceJson := .str (String.ofList ['8', '1', '1', '0', '1', '0', '1', '4', '1', '4', '5', '3', '9', '3'])
noncomputable def fragment0126332Acc01000 : List (String × SourceJson) := (fragment0126332Field009Key00, fragment0126332Field009Value00) :: fragment0126332Acc00900
noncomputable def fragment0126332Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '1', '1', '0', '1', '0', '1', '4', '1', '4', '5', '3', '9', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0126332_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 489) (SourceJson.white (fragment0126332Field009Chars00 ++ tail)) fragment0126332Acc00900 =
      .ok (.obj (fragment0126332Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0126332_object_field_009"
  err.flush

noncomputable def fragment0126332Chars : List Char := '{' :: (fragment0126332Field000Chars00 ++ fragment0126332Field001Chars00 ++ fragment0126332Field002Chars00 ++ fragment0126332Field003Chars00 ++ fragment0126332Field004Chars00 ++ fragment0126332Field005Chars00 ++ fragment0126332Field006Chars00 ++ fragment0126332Field007Chars00 ++ fragment0126332Field008Chars00 ++ fragment0126332Field009Chars00)
noncomputable def fragment0126332Value : SourceJson := .obj (fragment0126332Acc01000.reverse)

theorem value_fragment0126332 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 499) (fragment0126332Chars ++ tail) =
      .ok (fragment0126332Value, tail) := by
  have hinput : fragment0126332Chars ++ tail = '{' :: (fragment0126332Field000Chars00 ++ (fragment0126332Field001Chars00 ++ (fragment0126332Field002Chars00 ++ (fragment0126332Field003Chars00 ++ (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0126332Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 499) (fragment0126332Chars ++ tail) =
        SourceJson.value (fuel + 499) ('{' :: (fragment0126332Field000Chars00 ++ (fragment0126332Field001Chars00 ++ (fragment0126332Field002Chars00 ++ (fragment0126332Field003Chars00 ++ (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 499)) hinput
    _ = SourceJson.object (fuel + 498) (SourceJson.white (fragment0126332Field000Chars00 ++ (fragment0126332Field001Chars00 ++ (fragment0126332Field002Chars00 ++ (fragment0126332Field003Chars00 ++ (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))))))))))) fragment0126332Acc00000 := by rfl
    _ = SourceJson.object (fuel + 497) (SourceJson.white (fragment0126332Field001Chars00 ++ (fragment0126332Field002Chars00 ++ (fragment0126332Field003Chars00 ++ (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail))))))))))) fragment0126332Acc00100 := object_fragment0126332_field_000 fuel (fragment0126332Field001Chars00 ++ (fragment0126332Field002Chars00 ++ (fragment0126332Field003Chars00 ++ (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 496) (SourceJson.white (fragment0126332Field002Chars00 ++ (fragment0126332Field003Chars00 ++ (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))))))))) fragment0126332Acc00200 := object_fragment0126332_field_001 fuel (fragment0126332Field002Chars00 ++ (fragment0126332Field003Chars00 ++ (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 495) (SourceJson.white (fragment0126332Field003Chars00 ++ (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail))))))))) fragment0126332Acc00300 := object_fragment0126332_field_002 fuel (fragment0126332Field003Chars00 ++ (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 494) (SourceJson.white (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))))))) fragment0126332Acc00400 := object_fragment0126332_field_003 fuel (fragment0126332Field004Chars00 ++ (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 493) (SourceJson.white (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail))))))) fragment0126332Acc00500 := object_fragment0126332_field_004 fuel (fragment0126332Field005Chars00 ++ (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 492) (SourceJson.white (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))))) fragment0126332Acc00600 := object_fragment0126332_field_005 fuel (fragment0126332Field006Chars00 ++ (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 491) (SourceJson.white (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail))))) fragment0126332Acc00700 := object_fragment0126332_field_006 fuel (fragment0126332Field007Chars00 ++ (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 490) (SourceJson.white (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))) fragment0126332Acc00800 := object_fragment0126332_field_007 fuel (fragment0126332Field008Chars00 ++ (fragment0126332Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 489) (SourceJson.white (fragment0126332Field009Chars00 ++ (tail))) fragment0126332Acc00900 := object_fragment0126332_field_008 fuel (fragment0126332Field009Chars00 ++ (tail))
    _ = .ok (fragment0126332Value, tail) := object_fragment0126332_field_009 fuel (tail)

noncomputable def fragment0128490Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0128490Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0128490Field000Value00 : SourceJson := .number (String.ofList ['2'])
noncomputable def fragment0128490Acc00100 : List (String × SourceJson) := (fragment0128490Field000Key00, fragment0128490Field000Value00) :: fragment0128490Acc00000
noncomputable def fragment0128490Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', ',']

theorem object_fragment0128490_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 489) (SourceJson.white (fragment0128490Field000Chars00 ++ tail)) fragment0128490Acc00000 =
      SourceJson.object (fuel + 488) (SourceJson.white tail) fragment0128490Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_000"
  err.flush

noncomputable def fragment0128490Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0128490Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0128490Acc00200 : List (String × SourceJson) := (fragment0128490Field001Key00, fragment0128490Field001Value00) :: fragment0128490Acc00100
noncomputable def fragment0128490Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0128490_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 488) (SourceJson.white (fragment0128490Field001Chars00 ++ tail)) fragment0128490Acc00100 =
      SourceJson.object (fuel + 487) (SourceJson.white tail) fragment0128490Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_001"
  err.flush

noncomputable def fragment0128490Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0128490Field002Value00 : SourceJson := .str (String.ofList ['3', '0', '3', '2', '8', '2', '8', '6', '8', '9', '7', '0', '9', '6', '8', '1', '5', '9', '9', '4', '5', '1', '3', '6', '2', '1', '1', '3', '5', '6', '0', '3', '7', '7', '0', '8', '0', '4', '6', '5', '7', '2', '2', '5', '1', '0', '3', '/', '5', '1', '5', '1', '4', '3', '5', '7', '1', '2', '1', '3', '1', '7', '6', '0', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0128490Acc00300 : List (String × SourceJson) := (fragment0128490Field002Key00, fragment0128490Field002Value00) :: fragment0128490Acc00200
noncomputable def fragment0128490Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '0', '3', '2', '8', '2', '8', '6', '8', '9', '7', '0', '9', '6', '8', '1', '5', '9', '9', '4', '5', '1', '3', '6', '2', '1', '1', '3', '5', '6', '0', '3', '7', '7', '0', '8', '0', '4', '6', '5', '7', '2', '2', '5', '1', '0', '3', '/', '5', '1', '5', '1', '4', '3', '5', '7', '1', '2', '1', '3', '1', '7', '6', '0', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0128490_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 487) (SourceJson.white (fragment0128490Field002Chars00 ++ tail)) fragment0128490Acc00200 =
      SourceJson.object (fuel + 486) (SourceJson.white tail) fragment0128490Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_002"
  err.flush

noncomputable def fragment0128490Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0128490Field003Value00 : SourceJson := .str (String.ofList ['4', '7', '4', '8', '0', '4', '7', '7', '4', '1', '3', '3', '/', '1', '2', '7', '9', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0128490Acc00400 : List (String × SourceJson) := (fragment0128490Field003Key00, fragment0128490Field003Value00) :: fragment0128490Acc00300
noncomputable def fragment0128490Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '7', '4', '8', '0', '4', '7', '7', '4', '1', '3', '3', '/', '1', '2', '7', '9', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0128490_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 486) (SourceJson.white (fragment0128490Field003Chars00 ++ tail)) fragment0128490Acc00300 =
      SourceJson.object (fuel + 485) (SourceJson.white tail) fragment0128490Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_003"
  err.flush

noncomputable def fragment0128490Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0128490Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0128490Acc00500 : List (String × SourceJson) := (fragment0128490Field004Key00, fragment0128490Field004Value00) :: fragment0128490Acc00400
noncomputable def fragment0128490Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0128490_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 485) (SourceJson.white (fragment0128490Field004Chars00 ++ tail)) fragment0128490Acc00400 =
      SourceJson.object (fuel + 484) (SourceJson.white tail) fragment0128490Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_004"
  err.flush

noncomputable def fragment0128490Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0128490Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '5', '8', '2', '6', '9', '6', '5', '2', '7', '3', '3', '9', '3', '8', '0', '0', '5', '5', '3', '3', '8', '9', '9', '/', '1', '4', '2', '3', '7', '1', '3', '6', '8', '8', '6', '0', '4', '1', '6', '9', '9', '9', '1', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '2', '5', '9', '3', '0', '0', '1', '8', '7', '8', '2', '4', '7', '3', '3', '9', '3', '4', '1', '3', '7', '1', '7', '/', '1', '3', '0', '1', '6', '8', '1', '0', '8', '6', '7', '2', '3', '8', '1', '2', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '4', '3', '2', '8', '1', '1', '9', '2', '3', '2', '8', '7', '1', '8', '7', '5', '5', '9', '6', '3', '5', '4', '3', '1', '/', '1', '8', '2', '2', '3', '5', '3', '5', '2', '1', '4', '1', '3', '3', '3', '7', '5', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '3', '9', '9', '6', '4', '2', '1', '4', '9', '5', '7', '5', '2', '1', '9', '4', '9', '2', '9', '0', '2', '8', '0', '1', '/', '3', '6', '4', '4', '7', '0', '7', '0', '4', '2', '8', '2', '6', '6', '7', '5', '1', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '1', '5', '2', '6', '4', '1', '6', '4', '5', '7', '3', '1', '9', '3', '2', '2', '4', '7', '2', '5', '4', '5', '7', '/', '2', '0', '2', '4', '8', '3', '7', '2', '4', '6', '0', '1', '4', '8', '1', '9', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '5', '1', '2', '8', '3', '4', '1', '2', '2', '7', '7', '2', '5', '3', '6', '6', '8', '1', '9', '0', '6', '0', '7', '/', '1', '6', '5', '6', '6', '8', '5', '0', '1', '9', '4', '6', '6', '6', '7', '0', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '1', '9', '5', '2', '5', '5', '9', '1', '2', '4', '1', '2', '2', '1', '8', '9', '7', '3', '3', '9', '0', '9', '3', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '0', '2', '8', '6', '9', '7', '7', '0', '1', '4', '5', '5', '3', '8', '0', '5', '1', '3', '4', '8', '6', '8', '3', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '3', '8', '2', '9', '0', '4', '2', '7', '0', '6', '2', '5', '6', '5', '1', '8', '6', '0', '9', '7', '3', '3', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '5', '8', '8', '7', '0', '3', '1', '1', '5', '4', '1', '6', '7', '6', '7', '5', '4', '5', '7', '2', '9', '9', '/', '4', '3', '3', '8', '9', '3', '6', '9', '5', '5', '7', '4', '6', '0', '4', '1', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0128490Acc00600 : List (String × SourceJson) := (fragment0128490Field005Key00, fragment0128490Field005Value00) :: fragment0128490Acc00500
noncomputable def fragment0128490Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '8', '2', '6', '9', '6', '5', '2', '7', '3', '3', '9', '3', '8', '0', '0', '5', '5', '3', '3', '8', '9', '9', '/', '1', '4', '2', '3', '7', '1', '3', '6', '8', '8', '6', '0', '4', '1', '6', '9', '9', '9', '1', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '2', '5', '9', '3', '0', '0', '1', '8', '7', '8', '2', '4', '7', '3', '3', '9', '3', '4', '1', '3', '7', '1', '7', '/', '1', '3', '0', '1', '6', '8', '1', '0', '8', '6', '7', '2', '3', '8', '1', '2', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '4', '3', '2', '8', '1', '1', '9', '2', '3', '2', '8', '7', '1', '8', '7', '5', '5', '9', '6', '3', '5', '4', '3', '1', '/', '1', '8', '2', '2', '3', '5', '3', '5', '2', '1', '4', '1', '3', '3', '3', '7', '5', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '3', '9', '9', '6', '4', '2', '1', '4', '9', '5', '7', '5', '2', '1', '9', '4', '9', '2', '9', '0', '2', '8', '0', '1', '/', '3', '6', '4', '4', '7', '0', '7', '0', '4', '2', '8', '2', '6', '6', '7', '5', '1', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '1', '5', '2', '6', '4', '1', '6', '4', '5', '7', '3', '1', '9', '3', '2', '2', '4', '7', '2', '5', '4', '5', '7', '/', '2', '0', '2', '4', '8', '3', '7', '2', '4', '6', '0', '1', '4', '8', '1', '9', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '5', '1', '2', '8', '3', '4', '1', '2', '2', '7', '7', '2', '5', '3', '6', '6', '8', '1', '9', '0', '6', '0', '7', '/', '1', '6', '5', '6', '6', '8', '5', '0', '1', '9', '4', '6', '6', '6', '7', '0', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '1', '9', '5', '2', '5', '5', '9', '1', '2', '4', '1', '2', '2', '1', '8', '9', '7', '3', '3', '9', '0', '9', '3', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '0', '2', '8', '6', '9', '7', '7', '0', '1', '4', '5', '5', '3', '8', '0', '5', '1', '3', '4', '8', '6', '8', '3', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '8', '3', '8', '2', '9', '0', '4', '2', '7', '0', '6', '2', '5', '6', '5', '1', '8', '6', '0', '9', '7', '3', '3', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '5', '8', '8', '7', '0', '3', '1', '1', '5', '4', '1', '6', '7', '6', '7', '5', '4', '5', '7', '2', '9', '9', '/', '4', '3', '3', '8', '9', '3', '6', '9', '5', '5', '7', '4', '6', '0', '4', '1', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0128490_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 484) (SourceJson.white (fragment0128490Field005Chars00 ++ tail)) fragment0128490Acc00500 =
      SourceJson.object (fuel + 483) (SourceJson.white tail) fragment0128490Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_005"
  err.flush

noncomputable def fragment0128490Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0128490Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '1', '8', '6', '4', '2', '9', '7', '8', '2', '6', '0', '2', '1', '9', '0', '4', '3', '1', '5', '3', '4', '6', '8', '6', '8', '7', '3', '5', '1', '0', '6', '7', '0', '0', '5', '9', '3', '1', '6', '4', '6', '5', '4', '5', '4', '4', '0', '8', '5', '6', '0', '9', '9', '0', '6', '2', '5', '/', '5', '1', '9', '1', '8', '4', '0', '1', '7', '0', '7', '8', '5', '6', '4', '4', '6', '9', '8', '1', '4', '1', '3', '5', '8', '0', '8', '4', '7', '4', '9', '7', '9', '7', '9', '5', '6', '0', '6', '3', '9', '1', '4', '6', '7', '8', '8', '8', '6', '6', '2', '1', '5', '4', '6', '7', '4', '9', '8', '7', '5', '9', '6', '3', '7', '3', '8', '5', '8', '7', '9', '4', '1', '6'])
noncomputable def fragment0128490Acc00700 : List (String × SourceJson) := (fragment0128490Field006Key00, fragment0128490Field006Value00) :: fragment0128490Acc00600
noncomputable def fragment0128490Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '2', '1', '8', '6', '4', '2', '9', '7', '8', '2', '6', '0', '2', '1', '9', '0', '4', '3', '1', '5', '3', '4', '6', '8', '6', '8', '7', '3', '5', '1', '0', '6', '7', '0', '0', '5', '9', '3', '1', '6', '4', '6', '5', '4', '5', '4', '4', '0', '8', '5', '6', '0', '9', '9', '0', '6', '2', '5', '/', '5', '1', '9', '1', '8', '4', '0', '1', '7', '0', '7', '8', '5', '6', '4', '4', '6', '9', '8', '1', '4', '1', '3', '5', '8', '0', '8', '4', '7', '4', '9', '7', '9', '7', '9', '5', '6', '0', '6', '3', '9', '1', '4', '6', '7', '8', '8', '8', '6', '6', '2', '1', '5', '4', '6', '7', '4', '9', '8', '7', '5', '9', '6', '3', '7', '3', '8', '5', '8', '7', '9', '4', '1', '6', '"', ',']

theorem object_fragment0128490_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 483) (SourceJson.white (fragment0128490Field006Chars00 ++ tail)) fragment0128490Acc00600 =
      SourceJson.object (fuel + 482) (SourceJson.white tail) fragment0128490Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_006"
  err.flush

noncomputable def fragment0128490Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0128490Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '2', '3', '3', '9', '5', '4', '4', '9', '4', '2', '2', '6', '8', '8', '7', '7', '3', '9', '0', '9', '2', '5', '3', '9', '3', '1', '0', '3', '4', '2', '1', '3', '4', '4', '5', '5', '8', '8', '6', '2', '7', '6', '6', '3', '0', '9', '7', '5', '1', '6', '6', '4', '0', '3', '4', '4', '2', '4', '6', '2', '5', '8', '8', '0', '0', '8', '9', '4', '3', '9', '5', '4', '7', '7', '2', '1', '1', '9', '6', '5', '4', '9', '9', '2', '6', '2', '8', '0', '0', '6', '2', '6', '8', '0', '5', '5', '3', '9', '5', '4', '0', '8', '9', '4', '7', '9', '8', '0', '0', '3', '4', '0', '4', '5', '7', '4', '2', '0', '0', '8', '9', '3', '5', '7', '3', '5', '2', '8', '8', '7', '5', '4', '4', '2', '0', '7', '5', '4', '9', '2', '3', '3', '2', '0', '8', '8', '0', '8', '9', '9', '2', '0', '5', '7', '7', '2', '7', '3', '4', '0', '5', '7', '6', '3', '3', '8', '9', '3', '3', '7', '4', '1', '7', '7', '3', '3', '2', '2', '8', '9', '9', '2', '2', '9', '5', '3', '4', '1', '1', '4', '0', '4', '4', '7', '6', '3', '2', '0', '5', '1', '0', '4', '5', '4', '9', '0', '2', '5', '1', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '1', '6', '2', '5', '3', '5', '3', '5', '9', '7', '1', '2', '5', '1', '7', '9', '2', '1', '0', '5', '3', '9', '7', '3', '6', '8', '2', '1', '5', '7', '1', '5', '3', '3', '7', '7', '1', '4', '5', '4', '3', '3', '6', '0', '1', '0', '7', '8', '2', '1', '2', '1', '1', '7', '0', '6', '0', '8', '9', '5', '9', '4', '6', '6', '0', '4', '8', '3', '8', '7', '0', '3', '8', '9', '4', '0', '4', '0', '5', '0', '1', '9', '9', '8', '9', '3', '2', '3', '3', '8', '0', '5', '9', '1', '4', '3', '6', '3', '5', '6', '3', '6', '3', '1', '5', '4', '0', '3', '2', '3', '6', '6', '3', '2', '4', '5', '4', '7', '5', '5', '0', '8', '5', '6', '9', '5', '4', '0', '0', '2', '5', '8', '4', '3', '8', '0', '1', '5', '4', '3', '1', '5', '2', '5', '3', '4', '0', '3', '9', '4', '7', '2', '1', '1', '8', '7', '6', '7', '4', '2', '5', '6', '5', '0', '7', '1', '3', '9', '6', '1', '8', '6', '3', '5', '9', '2', '1', '7', '0', '6', '0', '9', '6', '6', '7', '9', '1', '9', '5', '8', '8', '8', '6', '3', '5', '2', '9', '2', '6', '1', '7', '6', '7', '2', '2', '1', '5', '3', '9', '0', '5', '1', '7', '7', '8', '7', '8', '0', '7', '0', '1', '5', '9', '9', '4', '7', '9', '4', '6', '5', '0', '7', '4', '5', '4', '4', '2', '0', '5', '2', '8', '6', '7', '3'])
noncomputable def fragment0128490Acc00800 : List (String × SourceJson) := (fragment0128490Field007Key00, fragment0128490Field007Value00) :: fragment0128490Acc00700
noncomputable def fragment0128490Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '8', '2', '3', '3', '9', '5', '4', '4', '9', '4', '2', '2', '6', '8', '8', '7', '7', '3', '9', '0', '9', '2', '5', '3', '9', '3', '1', '0', '3', '4', '2', '1', '3', '4', '4', '5', '5', '8', '8', '6', '2', '7', '6', '6', '3', '0', '9', '7', '5', '1', '6', '6', '4', '0', '3', '4', '4', '2', '4', '6', '2', '5', '8', '8', '0', '0', '8', '9', '4', '3', '9', '5', '4', '7', '7', '2', '1', '1', '9', '6', '5', '4', '9', '9', '2', '6', '2', '8', '0', '0', '6', '2', '6', '8', '0', '5', '5', '3', '9', '5', '4', '0', '8', '9', '4', '7', '9', '8', '0', '0', '3', '4', '0', '4', '5', '7', '4', '2', '0', '0', '8', '9', '3', '5', '7', '3', '5', '2', '8', '8', '7', '5', '4', '4', '2', '0', '7', '5', '4', '9', '2', '3', '3', '2', '0', '8', '8', '0', '8', '9', '9', '2', '0', '5', '7', '7', '2', '7', '3', '4', '0', '5', '7', '6', '3', '3', '8', '9', '3', '3', '7', '4', '1', '7', '7', '3', '3', '2', '2', '8', '9', '9', '2', '2', '9', '5', '3', '4', '1', '1', '4', '0', '4', '4', '7', '6', '3', '2', '0', '5', '1', '0', '4', '5', '4', '9', '0', '2', '5', '1', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '1', '6', '2', '5', '3', '5', '3', '5', '9', '7', '1', '2', '5', '1', '7', '9', '2', '1', '0', '5', '3', '9', '7', '3', '6', '8', '2', '1', '5', '7', '1', '5', '3', '3', '7', '7', '1', '4', '5', '4', '3', '3', '6', '0', '1', '0', '7', '8', '2', '1', '2', '1', '1', '7', '0', '6', '0', '8', '9', '5', '9', '4', '6', '6', '0', '4', '8', '3', '8', '7', '0', '3', '8', '9', '4', '0', '4', '0', '5', '0', '1', '9', '9', '8', '9', '3', '2', '3', '3', '8', '0', '5', '9', '1', '4', '3', '6', '3', '5', '6', '3', '6', '3', '1', '5', '4', '0', '3', '2', '3', '6', '6', '3', '2', '4', '5', '4', '7', '5', '5', '0', '8', '5', '6', '9', '5', '4', '0', '0', '2', '5', '8', '4', '3', '8', '0', '1', '5', '4', '3', '1', '5', '2', '5', '3', '4', '0', '3', '9', '4', '7', '2', '1', '1', '8', '7', '6', '7', '4', '2', '5', '6', '5', '0', '7', '1', '3', '9', '6', '1', '8', '6', '3', '5', '9', '2', '1', '7', '0', '6', '0', '9', '6', '6', '7', '9', '1', '9', '5', '8', '8', '8', '6', '3', '5', '2', '9', '2', '6', '1', '7', '6', '7', '2', '2', '1', '5', '3', '9', '0', '5', '1', '7', '7', '8', '7', '8', '0', '7', '0', '1', '5', '9', '9', '4', '7', '9', '4', '6', '5', '0', '7', '4', '5', '4', '4', '2', '0', '5', '2', '8', '6', '7', '3', '"', ',']

theorem object_fragment0128490_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 482) (SourceJson.white (fragment0128490Field007Chars00 ++ tail)) fragment0128490Acc00700 =
      SourceJson.object (fuel + 481) (SourceJson.white tail) fragment0128490Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_007"
  err.flush

noncomputable def fragment0128490Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0128490Field008Value00 : SourceJson := .str (String.ofList ['2', '7', '8', '0', '1', '8', '8', '8', '3', '3', '2', '2', '5', '4', '6'])
noncomputable def fragment0128490Acc00900 : List (String × SourceJson) := (fragment0128490Field008Key00, fragment0128490Field008Value00) :: fragment0128490Acc00800
noncomputable def fragment0128490Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '8', '0', '1', '8', '8', '8', '3', '3', '2', '2', '5', '4', '6', '"', ',']

theorem object_fragment0128490_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 481) (SourceJson.white (fragment0128490Field008Chars00 ++ tail)) fragment0128490Acc00800 =
      SourceJson.object (fuel + 480) (SourceJson.white tail) fragment0128490Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_008"
  err.flush

noncomputable def fragment0128490Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0128490Field009Value00 : SourceJson := .str (String.ofList ['8', '3', '9', '1', '8', '7', '3', '9', '4', '2', '1', '7', '0', '4', '2'])
noncomputable def fragment0128490Acc01000 : List (String × SourceJson) := (fragment0128490Field009Key00, fragment0128490Field009Value00) :: fragment0128490Acc00900
noncomputable def fragment0128490Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '3', '9', '1', '8', '7', '3', '9', '4', '2', '1', '7', '0', '4', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0128490_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 480) (SourceJson.white (fragment0128490Field009Chars00 ++ tail)) fragment0128490Acc00900 =
      .ok (.obj (fragment0128490Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0128490_object_field_009"
  err.flush

noncomputable def fragment0128490Chars : List Char := '{' :: (fragment0128490Field000Chars00 ++ fragment0128490Field001Chars00 ++ fragment0128490Field002Chars00 ++ fragment0128490Field003Chars00 ++ fragment0128490Field004Chars00 ++ fragment0128490Field005Chars00 ++ fragment0128490Field006Chars00 ++ fragment0128490Field007Chars00 ++ fragment0128490Field008Chars00 ++ fragment0128490Field009Chars00)
noncomputable def fragment0128490Value : SourceJson := .obj (fragment0128490Acc01000.reverse)

theorem value_fragment0128490 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 490) (fragment0128490Chars ++ tail) =
      .ok (fragment0128490Value, tail) := by
  have hinput : fragment0128490Chars ++ tail = '{' :: (fragment0128490Field000Chars00 ++ (fragment0128490Field001Chars00 ++ (fragment0128490Field002Chars00 ++ (fragment0128490Field003Chars00 ++ (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0128490Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 490) (fragment0128490Chars ++ tail) =
        SourceJson.value (fuel + 490) ('{' :: (fragment0128490Field000Chars00 ++ (fragment0128490Field001Chars00 ++ (fragment0128490Field002Chars00 ++ (fragment0128490Field003Chars00 ++ (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 490)) hinput
    _ = SourceJson.object (fuel + 489) (SourceJson.white (fragment0128490Field000Chars00 ++ (fragment0128490Field001Chars00 ++ (fragment0128490Field002Chars00 ++ (fragment0128490Field003Chars00 ++ (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))))))))))) fragment0128490Acc00000 := by rfl
    _ = SourceJson.object (fuel + 488) (SourceJson.white (fragment0128490Field001Chars00 ++ (fragment0128490Field002Chars00 ++ (fragment0128490Field003Chars00 ++ (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail))))))))))) fragment0128490Acc00100 := object_fragment0128490_field_000 fuel (fragment0128490Field001Chars00 ++ (fragment0128490Field002Chars00 ++ (fragment0128490Field003Chars00 ++ (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 487) (SourceJson.white (fragment0128490Field002Chars00 ++ (fragment0128490Field003Chars00 ++ (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))))))))) fragment0128490Acc00200 := object_fragment0128490_field_001 fuel (fragment0128490Field002Chars00 ++ (fragment0128490Field003Chars00 ++ (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 486) (SourceJson.white (fragment0128490Field003Chars00 ++ (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail))))))))) fragment0128490Acc00300 := object_fragment0128490_field_002 fuel (fragment0128490Field003Chars00 ++ (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 485) (SourceJson.white (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))))))) fragment0128490Acc00400 := object_fragment0128490_field_003 fuel (fragment0128490Field004Chars00 ++ (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 484) (SourceJson.white (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail))))))) fragment0128490Acc00500 := object_fragment0128490_field_004 fuel (fragment0128490Field005Chars00 ++ (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 483) (SourceJson.white (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))))) fragment0128490Acc00600 := object_fragment0128490_field_005 fuel (fragment0128490Field006Chars00 ++ (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 482) (SourceJson.white (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail))))) fragment0128490Acc00700 := object_fragment0128490_field_006 fuel (fragment0128490Field007Chars00 ++ (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 481) (SourceJson.white (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))) fragment0128490Acc00800 := object_fragment0128490_field_007 fuel (fragment0128490Field008Chars00 ++ (fragment0128490Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 480) (SourceJson.white (fragment0128490Field009Chars00 ++ (tail))) fragment0128490Acc00900 := object_fragment0128490_field_008 fuel (fragment0128490Field009Chars00 ++ (tail))
    _ = .ok (fragment0128490Value, tail) := object_fragment0128490_field_009 fuel (tail)

noncomputable def fragment0130641Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0130641Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0130641Field000Value00 : SourceJson := .number (String.ofList ['3'])
noncomputable def fragment0130641Acc00100 : List (String × SourceJson) := (fragment0130641Field000Key00, fragment0130641Field000Value00) :: fragment0130641Acc00000
noncomputable def fragment0130641Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', ',']

theorem object_fragment0130641_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 488) (SourceJson.white (fragment0130641Field000Chars00 ++ tail)) fragment0130641Acc00000 =
      SourceJson.object (fuel + 487) (SourceJson.white tail) fragment0130641Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_000"
  err.flush

noncomputable def fragment0130641Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0130641Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0130641Acc00200 : List (String × SourceJson) := (fragment0130641Field001Key00, fragment0130641Field001Value00) :: fragment0130641Acc00100
noncomputable def fragment0130641Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0130641_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 487) (SourceJson.white (fragment0130641Field001Chars00 ++ tail)) fragment0130641Acc00100 =
      SourceJson.object (fuel + 486) (SourceJson.white tail) fragment0130641Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_001"
  err.flush

noncomputable def fragment0130641Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0130641Field002Value00 : SourceJson := .str (String.ofList ['5', '5', '4', '2', '8', '2', '0', '5', '3', '5', '3', '5', '1', '6', '9', '6', '9', '5', '8', '0', '7', '0', '5', '7', '8', '9', '6', '8', '0', '5', '5', '2', '2', '4', '2', '7', '3', '3', '0', '0', '1', '/', '2', '6', '9', '5', '5', '1', '8', '6', '8', '6', '5', '8', '0', '5', '7', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0130641Acc00300 : List (String × SourceJson) := (fragment0130641Field002Key00, fragment0130641Field002Value00) :: fragment0130641Acc00200
noncomputable def fragment0130641Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '5', '4', '2', '8', '2', '0', '5', '3', '5', '3', '5', '1', '6', '9', '6', '9', '5', '8', '0', '7', '0', '5', '7', '8', '9', '6', '8', '0', '5', '5', '2', '2', '4', '2', '7', '3', '3', '0', '0', '1', '/', '2', '6', '9', '5', '5', '1', '8', '6', '8', '6', '5', '8', '0', '5', '7', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0130641_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 486) (SourceJson.white (fragment0130641Field002Chars00 ++ tail)) fragment0130641Acc00200 =
      SourceJson.object (fuel + 485) (SourceJson.white tail) fragment0130641Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_002"
  err.flush

noncomputable def fragment0130641Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0130641Field003Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0130641Acc00400 : List (String × SourceJson) := (fragment0130641Field003Key00, fragment0130641Field003Value00) :: fragment0130641Acc00300
noncomputable def fragment0130641Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0130641_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 485) (SourceJson.white (fragment0130641Field003Chars00 ++ tail)) fragment0130641Acc00300 =
      SourceJson.object (fuel + 484) (SourceJson.white tail) fragment0130641Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_003"
  err.flush

noncomputable def fragment0130641Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0130641Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0130641Acc00500 : List (String × SourceJson) := (fragment0130641Field004Key00, fragment0130641Field004Value00) :: fragment0130641Acc00400
noncomputable def fragment0130641Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0130641_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 484) (SourceJson.white (fragment0130641Field004Chars00 ++ tail)) fragment0130641Acc00400 =
      SourceJson.object (fuel + 483) (SourceJson.white tail) fragment0130641Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_004"
  err.flush

noncomputable def fragment0130641Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0130641Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '9', '5', '4', '9', '5', '8', '2', '8', '9', '2', '9', '1', '2', '2', '4', '2', '2', '7', '7', '0', '9', '6', '4', '5', '9', '3', '/', '2', '1', '7', '6', '0', '2', '1', '5', '2', '1', '3', '9', '7', '9', '0', '1', '1', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '6', '7', '5', '7', '9', '7', '4', '0', '5', '2', '9', '2', '0', '5', '9', '7', '5', '3', '0', '9', '1', '1', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '2', '9', '5', '2', '5', '5', '1', '6', '0', '8', '4', '7', '3', '8', '2', '2', '5', '8', '3', '9', '2', '0', '6', '9', '/', '3', '6', '2', '6', '7', '0', '2', '5', '3', '5', '6', '6', '3', '1', '6', '8', '6', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '5', '8', '5', '2', '8', '6', '9', '9', '3', '2', '1', '2', '1', '1', '7', '1', '0', '1', '2', '7', '4', '4', '1', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '5', '9', '3', '7', '0', '9', '6', '4', '8', '4', '8', '6', '0', '2', '7', '5', '4', '9', '0', '5', '6', '1', '6', '1', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '1', '9', '3', '5', '7', '8', '0', '6', '5', '5', '8', '9', '1', '4', '8', '1', '6', '1', '9', '2', '5', '9', '/', '1', '6', '4', '8', '5', '0', '1', '1', '5', '2', '5', '7', '4', '1', '6', '7', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '9', '3', '9', '8', '3', '5', '2', '3', '4', '0', '6', '5', '1', '9', '8', '2', '7', '6', '6', '6', '1', '0', '1', '/', '4', '9', '4', '5', '5', '0', '3', '4', '5', '7', '7', '2', '2', '5', '0', '2', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '6', '7', '2', '2', '7', '9', '4', '5', '3', '5', '5', '4', '7', '8', '2', '8', '7', '2', '7', '9', '2', '8', '7', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '6', '7', '2', '2', '1', '3', '5', '1', '3', '5', '0', '8', '6', '7', '9', '9', '0', '6', '0', '9', '0', '0', '7', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '0', '2', '8', '4', '4', '8', '4', '4', '1', '1', '7', '4', '7', '5', '8', '3', '3', '5', '1', '1', '3', '/', '1', '8', '0', '7', '3', '2', '6', '8', '4', '5', '0', '1', '4', '8', '6', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0130641Acc00600 : List (String × SourceJson) := (fragment0130641Field005Key00, fragment0130641Field005Value00) :: fragment0130641Acc00500
noncomputable def fragment0130641Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '5', '4', '9', '5', '8', '2', '8', '9', '2', '9', '1', '2', '2', '4', '2', '2', '7', '7', '0', '9', '6', '4', '5', '9', '3', '/', '2', '1', '7', '6', '0', '2', '1', '5', '2', '1', '3', '9', '7', '9', '0', '1', '1', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '7', '5', '7', '9', '7', '4', '0', '5', '2', '9', '2', '0', '5', '9', '7', '5', '3', '0', '9', '1', '1', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '9', '5', '2', '5', '5', '1', '6', '0', '8', '4', '7', '3', '8', '2', '2', '5', '8', '3', '9', '2', '0', '6', '9', '/', '3', '6', '2', '6', '7', '0', '2', '5', '3', '5', '6', '6', '3', '1', '6', '8', '6', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '5', '8', '5', '2', '8', '6', '9', '9', '3', '2', '1', '2', '1', '1', '7', '1', '0', '1', '2', '7', '4', '4', '1', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '5', '9', '3', '7', '0', '9', '6', '4', '8', '4', '8', '6', '0', '2', '7', '5', '4', '9', '0', '5', '6', '1', '6', '1', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '1', '9', '3', '5', '7', '8', '0', '6', '5', '5', '8', '9', '1', '4', '8', '1', '6', '1', '9', '2', '5', '9', '/', '1', '6', '4', '8', '5', '0', '1', '1', '5', '2', '5', '7', '4', '1', '6', '7', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '3', '9', '8', '3', '5', '2', '3', '4', '0', '6', '5', '1', '9', '8', '2', '7', '6', '6', '6', '1', '0', '1', '/', '4', '9', '4', '5', '5', '0', '3', '4', '5', '7', '7', '2', '2', '5', '0', '2', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '6', '7', '2', '2', '7', '9', '4', '5', '3', '5', '5', '4', '7', '8', '2', '8', '7', '2', '7', '9', '2', '8', '7', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '6', '7', '2', '2', '1', '3', '5', '1', '3', '5', '0', '8', '6', '7', '9', '9', '0', '6', '0', '9', '0', '0', '7', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '0', '2', '8', '4', '4', '8', '4', '4', '1', '1', '7', '4', '7', '5', '8', '3', '3', '5', '1', '1', '3', '/', '1', '8', '0', '7', '3', '2', '6', '8', '4', '5', '0', '1', '4', '8', '6', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0130641_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 483) (SourceJson.white (fragment0130641Field005Chars00 ++ tail)) fragment0130641Acc00500 =
      SourceJson.object (fuel + 482) (SourceJson.white tail) fragment0130641Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_005"
  err.flush

noncomputable def fragment0130641Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0130641Field006Value00 : SourceJson := .str (String.ofList ['7', '5', '5', '4', '1', '0', '6', '7', '8', '5', '9', '0', '7', '9', '3', '6', '1', '4', '4', '9', '4', '4', '6', '2', '3', '1', '1', '4', '8', '0', '8', '5', '7', '1', '1', '4', '4', '1', '2', '2', '9', '5', '8', '3', '7', '5', '5', '6', '3', '4', '1', '0', '9', '3', '7', '5', '/', '7', '7', '4', '2', '4', '8', '7', '9', '3', '0', '0', '7', '4', '0', '8', '7', '7', '0', '7', '9', '1', '3', '8', '3', '9', '7', '3', '6', '8', '2', '2', '3', '2', '2', '1', '4', '8', '5', '5', '9', '1', '9', '4', '7', '5', '5', '6', '8', '5', '4', '4', '4', '8', '1', '3', '1', '2', '7', '5', '4', '3', '3', '8', '5', '0', '1', '4', '7', '3', '2', '4', '9', '8', '1'])
noncomputable def fragment0130641Acc00700 : List (String × SourceJson) := (fragment0130641Field006Key00, fragment0130641Field006Value00) :: fragment0130641Acc00600
noncomputable def fragment0130641Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '5', '5', '4', '1', '0', '6', '7', '8', '5', '9', '0', '7', '9', '3', '6', '1', '4', '4', '9', '4', '4', '6', '2', '3', '1', '1', '4', '8', '0', '8', '5', '7', '1', '1', '4', '4', '1', '2', '2', '9', '5', '8', '3', '7', '5', '5', '6', '3', '4', '1', '0', '9', '3', '7', '5', '/', '7', '7', '4', '2', '4', '8', '7', '9', '3', '0', '0', '7', '4', '0', '8', '7', '7', '0', '7', '9', '1', '3', '8', '3', '9', '7', '3', '6', '8', '2', '2', '3', '2', '2', '1', '4', '8', '5', '5', '9', '1', '9', '4', '7', '5', '5', '6', '8', '5', '4', '4', '4', '8', '1', '3', '1', '2', '7', '5', '4', '3', '3', '8', '5', '0', '1', '4', '7', '3', '2', '4', '9', '8', '1', '"', ',']

theorem object_fragment0130641_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 482) (SourceJson.white (fragment0130641Field006Chars00 ++ tail)) fragment0130641Acc00600 =
      SourceJson.object (fuel + 481) (SourceJson.white tail) fragment0130641Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_006"
  err.flush

noncomputable def fragment0130641Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0130641Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '2', '8', '5', '6', '9', '1', '0', '1', '7', '3', '1', '3', '7', '4', '4', '8', '7', '1', '2', '5', '9', '0', '9', '1', '0', '4', '0', '5', '4', '5', '4', '8', '6', '1', '0', '0', '7', '3', '6', '2', '1', '1', '0', '6', '2', '8', '2', '2', '4', '3', '5', '0', '5', '4', '8', '5', '8', '8', '9', '1', '5', '2', '3', '0', '6', '5', '3', '5', '5', '6', '8', '9', '8', '8', '5', '0', '7', '4', '5', '4', '5', '9', '4', '0', '1', '5', '9', '2', '2', '8', '2', '0', '1', '3', '5', '7', '1', '0', '5', '0', '6', '1', '8', '3', '4', '2', '6', '5', '1', '2', '3', '6', '7', '9', '2', '6', '2', '6', '7', '7', '6', '9', '6', '9', '8', '7', '4', '0', '4', '3', '0', '0', '6', '9', '2', '9', '2', '9', '9', '7', '4', '5', '6', '1', '8', '2', '0', '4', '4', '9', '7', '9', '2', '6', '4', '8', '8', '8', '6', '7', '9', '1', '9', '5', '4', '0', '3', '2', '6', '2', '3', '9', '4', '7', '1', '3', '1', '7', '7', '0', '5', '1', '8', '5', '3', '7', '8', '3', '5', '0', '9', '0', '7', '4', '2', '1', '2', '5', '0', '3', '8', '6', '7', '7', '9', '9', '1', '7', '4', '0', '7', '2', '2', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '0', '8', '0', '7', '2', '8', '0', '3', '0', '5', '5', '8', '7', '3', '0', '1', '3', '2', '6', '6', '2', '4', '4', '6', '6', '2', '2', '1', '2', '2', '2', '3', '3', '2', '3', '0', '5', '0', '3', '1', '2', '8', '2', '2', '9', '1', '1', '1', '0', '6', '2', '5', '0', '6', '6', '9', '0', '9', '9', '0', '2', '6', '9', '0', '5', '8', '1', '7', '2', '0', '6', '6', '4', '1', '7', '1', '3', '0', '1', '1', '7', '4', '4', '2', '9', '4', '8', '7', '1', '5', '3', '4', '9', '3', '4', '9', '0', '3', '5', '1', '8', '7', '1', '6', '3', '9', '2', '0', '3', '7', '3', '9', '1', '7', '7', '7', '1', '4', '5', '4', '8', '8', '7', '0', '8', '5', '4', '5', '1', '8', '0', '6', '6', '1', '0', '6', '9', '3', '9', '8', '3', '1', '9', '1', '4', '2', '7', '9', '6', '5', '6', '3', '0', '9', '2', '7', '8', '3', '7', '9', '8', '8', '9', '9', '4', '5', '9', '0', '4', '2', '4', '5', '5', '6', '7', '8', '2', '2', '3', '0', '7', '8', '7', '2', '5', '0', '4', '2', '7', '8', '2', '3', '3', '5', '1', '3', '3', '1', '8', '3', '7', '2', '0', '7', '9', '1', '6', '9', '6', '9', '7', '0', '0', '2', '5', '8', '9', '5', '3', '6', '2', '7', '3', '5', '3', '3', '7', '0', '0', '9', '3', '0', '5', '8', '2', '6', '1', '0', '4', '4', '4', '4', '2', '0', '6', '1'])
noncomputable def fragment0130641Acc00800 : List (String × SourceJson) := (fragment0130641Field007Key00, fragment0130641Field007Value00) :: fragment0130641Acc00700
noncomputable def fragment0130641Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '8', '2', '8', '5', '6', '9', '1', '0', '1', '7', '3', '1', '3', '7', '4', '4', '8', '7', '1', '2', '5', '9', '0', '9', '1', '0', '4', '0', '5', '4', '5', '4', '8', '6', '1', '0', '0', '7', '3', '6', '2', '1', '1', '0', '6', '2', '8', '2', '2', '4', '3', '5', '0', '5', '4', '8', '5', '8', '8', '9', '1', '5', '2', '3', '0', '6', '5', '3', '5', '5', '6', '8', '9', '8', '8', '5', '0', '7', '4', '5', '4', '5', '9', '4', '0', '1', '5', '9', '2', '2', '8', '2', '0', '1', '3', '5', '7', '1', '0', '5', '0', '6', '1', '8', '3', '4', '2', '6', '5', '1', '2', '3', '6', '7', '9', '2', '6', '2', '6', '7', '7', '6', '9', '6', '9', '8', '7', '4', '0', '4', '3', '0', '0', '6', '9', '2', '9', '2', '9', '9', '7', '4', '5', '6', '1', '8', '2', '0', '4', '4', '9', '7', '9', '2', '6', '4', '8', '8', '8', '6', '7', '9', '1', '9', '5', '4', '0', '3', '2', '6', '2', '3', '9', '4', '7', '1', '3', '1', '7', '7', '0', '5', '1', '8', '5', '3', '7', '8', '3', '5', '0', '9', '0', '7', '4', '2', '1', '2', '5', '0', '3', '8', '6', '7', '7', '9', '9', '1', '7', '4', '0', '7', '2', '2', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '0', '8', '0', '7', '2', '8', '0', '3', '0', '5', '5', '8', '7', '3', '0', '1', '3', '2', '6', '6', '2', '4', '4', '6', '6', '2', '2', '1', '2', '2', '2', '3', '3', '2', '3', '0', '5', '0', '3', '1', '2', '8', '2', '2', '9', '1', '1', '1', '0', '6', '2', '5', '0', '6', '6', '9', '0', '9', '9', '0', '2', '6', '9', '0', '5', '8', '1', '7', '2', '0', '6', '6', '4', '1', '7', '1', '3', '0', '1', '1', '7', '4', '4', '2', '9', '4', '8', '7', '1', '5', '3', '4', '9', '3', '4', '9', '0', '3', '5', '1', '8', '7', '1', '6', '3', '9', '2', '0', '3', '7', '3', '9', '1', '7', '7', '7', '1', '4', '5', '4', '8', '8', '7', '0', '8', '5', '4', '5', '1', '8', '0', '6', '6', '1', '0', '6', '9', '3', '9', '8', '3', '1', '9', '1', '4', '2', '7', '9', '6', '5', '6', '3', '0', '9', '2', '7', '8', '3', '7', '9', '8', '8', '9', '9', '4', '5', '9', '0', '4', '2', '4', '5', '5', '6', '7', '8', '2', '2', '3', '0', '7', '8', '7', '2', '5', '0', '4', '2', '7', '8', '2', '3', '3', '5', '1', '3', '3', '1', '8', '3', '7', '2', '0', '7', '9', '1', '6', '9', '6', '9', '7', '0', '0', '2', '5', '8', '9', '5', '3', '6', '2', '7', '3', '5', '3', '3', '7', '0', '0', '9', '3', '0', '5', '8', '2', '6', '1', '0', '4', '4', '4', '4', '2', '0', '6', '1', '"', ',']

theorem object_fragment0130641_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 481) (SourceJson.white (fragment0130641Field007Chars00 ++ tail)) fragment0130641Acc00700 =
      SourceJson.object (fuel + 480) (SourceJson.white tail) fragment0130641Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_007"
  err.flush

noncomputable def fragment0130641Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0130641Field008Value00 : SourceJson := .str (String.ofList ['7', '7', '3', '0', '0', '4', '7', '5', '6', '9', '8'])
noncomputable def fragment0130641Acc00900 : List (String × SourceJson) := (fragment0130641Field008Key00, fragment0130641Field008Value00) :: fragment0130641Acc00800
noncomputable def fragment0130641Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '7', '3', '0', '0', '4', '7', '5', '6', '9', '8', '"', ',']

theorem object_fragment0130641_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 480) (SourceJson.white (fragment0130641Field008Chars00 ++ tail)) fragment0130641Acc00800 =
      SourceJson.object (fuel + 479) (SourceJson.white tail) fragment0130641Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_008"
  err.flush

noncomputable def fragment0130641Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0130641Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '9', '6', '5', '4', '0', '6', '8', '6', '0', '8'])
noncomputable def fragment0130641Acc01000 : List (String × SourceJson) := (fragment0130641Field009Key00, fragment0130641Field009Value00) :: fragment0130641Acc00900
noncomputable def fragment0130641Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '9', '6', '5', '4', '0', '6', '8', '6', '0', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0130641_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 479) (SourceJson.white (fragment0130641Field009Chars00 ++ tail)) fragment0130641Acc00900 =
      .ok (.obj (fragment0130641Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0130641_object_field_009"
  err.flush

noncomputable def fragment0130641Chars : List Char := '{' :: (fragment0130641Field000Chars00 ++ fragment0130641Field001Chars00 ++ fragment0130641Field002Chars00 ++ fragment0130641Field003Chars00 ++ fragment0130641Field004Chars00 ++ fragment0130641Field005Chars00 ++ fragment0130641Field006Chars00 ++ fragment0130641Field007Chars00 ++ fragment0130641Field008Chars00 ++ fragment0130641Field009Chars00)
noncomputable def fragment0130641Value : SourceJson := .obj (fragment0130641Acc01000.reverse)

theorem value_fragment0130641 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 489) (fragment0130641Chars ++ tail) =
      .ok (fragment0130641Value, tail) := by
  have hinput : fragment0130641Chars ++ tail = '{' :: (fragment0130641Field000Chars00 ++ (fragment0130641Field001Chars00 ++ (fragment0130641Field002Chars00 ++ (fragment0130641Field003Chars00 ++ (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0130641Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 489) (fragment0130641Chars ++ tail) =
        SourceJson.value (fuel + 489) ('{' :: (fragment0130641Field000Chars00 ++ (fragment0130641Field001Chars00 ++ (fragment0130641Field002Chars00 ++ (fragment0130641Field003Chars00 ++ (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 489)) hinput
    _ = SourceJson.object (fuel + 488) (SourceJson.white (fragment0130641Field000Chars00 ++ (fragment0130641Field001Chars00 ++ (fragment0130641Field002Chars00 ++ (fragment0130641Field003Chars00 ++ (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))))))))))) fragment0130641Acc00000 := by rfl
    _ = SourceJson.object (fuel + 487) (SourceJson.white (fragment0130641Field001Chars00 ++ (fragment0130641Field002Chars00 ++ (fragment0130641Field003Chars00 ++ (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail))))))))))) fragment0130641Acc00100 := object_fragment0130641_field_000 fuel (fragment0130641Field001Chars00 ++ (fragment0130641Field002Chars00 ++ (fragment0130641Field003Chars00 ++ (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 486) (SourceJson.white (fragment0130641Field002Chars00 ++ (fragment0130641Field003Chars00 ++ (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))))))))) fragment0130641Acc00200 := object_fragment0130641_field_001 fuel (fragment0130641Field002Chars00 ++ (fragment0130641Field003Chars00 ++ (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 485) (SourceJson.white (fragment0130641Field003Chars00 ++ (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail))))))))) fragment0130641Acc00300 := object_fragment0130641_field_002 fuel (fragment0130641Field003Chars00 ++ (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 484) (SourceJson.white (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))))))) fragment0130641Acc00400 := object_fragment0130641_field_003 fuel (fragment0130641Field004Chars00 ++ (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 483) (SourceJson.white (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail))))))) fragment0130641Acc00500 := object_fragment0130641_field_004 fuel (fragment0130641Field005Chars00 ++ (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 482) (SourceJson.white (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))))) fragment0130641Acc00600 := object_fragment0130641_field_005 fuel (fragment0130641Field006Chars00 ++ (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 481) (SourceJson.white (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail))))) fragment0130641Acc00700 := object_fragment0130641_field_006 fuel (fragment0130641Field007Chars00 ++ (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 480) (SourceJson.white (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))) fragment0130641Acc00800 := object_fragment0130641_field_007 fuel (fragment0130641Field008Chars00 ++ (fragment0130641Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 479) (SourceJson.white (fragment0130641Field009Chars00 ++ (tail))) fragment0130641Acc00900 := object_fragment0130641_field_008 fuel (fragment0130641Field009Chars00 ++ (tail))
    _ = .ok (fragment0130641Value, tail) := object_fragment0130641_field_009 fuel (tail)

noncomputable def fragment0132769Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0132769Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0132769Field000Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0132769Acc00100 : List (String × SourceJson) := (fragment0132769Field000Key00, fragment0132769Field000Value00) :: fragment0132769Acc00000
noncomputable def fragment0132769Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', ',']

theorem object_fragment0132769_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0132769Field000Chars00 ++ tail)) fragment0132769Acc00000 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0132769Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_000"
  err.flush

noncomputable def fragment0132769Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0132769Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0132769Acc00200 : List (String × SourceJson) := (fragment0132769Field001Key00, fragment0132769Field001Value00) :: fragment0132769Acc00100
noncomputable def fragment0132769Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0132769_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0132769Field001Chars00 ++ tail)) fragment0132769Acc00100 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0132769Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_001"
  err.flush

noncomputable def fragment0132769Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0132769Field002Value00 : SourceJson := .str (String.ofList ['4', '9', '8', '8', '1', '6', '8', '3', '1', '6', '6', '0', '9', '5', '5', '2', '7', '9', '2', '0', '0', '3', '4', '5', '4', '1', '5', '0', '1', '1', '1', '9', '1', '2', '3', '3', '2', '3', '2', '5', '1', '/', '2', '6', '8', '0', '2', '0', '3', '2', '3', '9', '4', '9', '7', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0132769Acc00300 : List (String × SourceJson) := (fragment0132769Field002Key00, fragment0132769Field002Value00) :: fragment0132769Acc00200
noncomputable def fragment0132769Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '9', '8', '8', '1', '6', '8', '3', '1', '6', '6', '0', '9', '5', '5', '2', '7', '9', '2', '0', '0', '3', '4', '5', '4', '1', '5', '0', '1', '1', '1', '9', '1', '2', '3', '3', '2', '3', '2', '5', '1', '/', '2', '6', '8', '0', '2', '0', '3', '2', '3', '9', '4', '9', '7', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0132769_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0132769Field002Chars00 ++ tail)) fragment0132769Acc00200 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0132769Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_002"
  err.flush

noncomputable def fragment0132769Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0132769Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0132769Acc00400 : List (String × SourceJson) := (fragment0132769Field003Key00, fragment0132769Field003Value00) :: fragment0132769Acc00300
noncomputable def fragment0132769Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0132769_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0132769Field003Chars00 ++ tail)) fragment0132769Acc00300 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0132769Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_003"
  err.flush

noncomputable def fragment0132769Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0132769Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0132769Acc00500 : List (String × SourceJson) := (fragment0132769Field004Key00, fragment0132769Field004Value00) :: fragment0132769Acc00400
noncomputable def fragment0132769Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0132769_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0132769Field004Chars00 ++ tail)) fragment0132769Acc00400 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0132769Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_004"
  err.flush

noncomputable def fragment0132769Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0132769Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '7', '3', '4', '3', '4', '1', '6', '1', '0', '7', '8', '8', '4', '2', '2', '2', '1', '6', '6', '1', '1', '7', '/', '1', '9', '1', '8', '2', '4', '9', '6', '1', '4', '7', '9', '5', '5', '9', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '6', '5', '2', '5', '6', '0', '5', '9', '0', '2', '2', '7', '4', '8', '4', '2', '8', '9', '/', '3', '1', '8', '6', '4', '6', '1', '1', '5', '4', '1', '4', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '2', '8', '8', '2', '9', '0', '1', '0', '7', '5', '7', '5', '4', '8', '1', '6', '5', '6', '8', '3', '7', '9', '/', '5', '8', '8', '2', '6', '3', '2', '1', '5', '2', '0', '3', '9', '8', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '7', '2', '5', '7', '2', '6', '1', '8', '3', '2', '9', '3', '0', '8', '7', '0', '6', '4', '2', '5', '0', '7', '/', '3', '5', '2', '9', '5', '7', '9', '2', '9', '1', '2', '2', '3', '8', '8', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '2', '0', '2', '0', '2', '5', '9', '4', '7', '9', '3', '3', '7', '5', '3', '8', '2', '0', '6', '3', '3', '4', '1', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '1', '3', '7', '3', '9', '2', '5', '0', '1', '9', '7', '4', '6', '6', '5', '9', '1', '5', '2', '2', '3', '/', '5', '3', '4', '7', '8', '4', '7', '4', '1', '0', '9', '4', '5', '2', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '2', '7', '9', '0', '6', '2', '7', '4', '4', '0', '5', '5', '0', '8', '7', '1', '3', '0', '4', '3', '1', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '7', '4', '8', '3', '8', '3', '6', '9', '1', '7', '1', '5', '9', '8', '1', '1', '1', '1', '0', '9', '/', '2', '0', '0', '5', '4', '4', '2', '7', '7', '9', '1', '0', '4', '4', '8', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '7', '4', '8', '2', '4', '9', '9', '9', '5', '5', '3', '0', '7', '0', '7', '4', '7', '8', '9', '9', '/', '2', '0', '0', '5', '4', '4', '2', '7', '7', '9', '1', '0', '4', '4', '8', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '5', '8', '3', '4', '1', '4', '5', '2', '1', '3', '8', '8', '3', '7', '4', '7', '3', '1', '/', '1', '2', '7', '4', '5', '8', '4', '4', '6', '1', '6', '5', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0132769Acc00600 : List (String × SourceJson) := (fragment0132769Field005Key00, fragment0132769Field005Value00) :: fragment0132769Acc00500
noncomputable def fragment0132769Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '4', '3', '4', '1', '6', '1', '0', '7', '8', '8', '4', '2', '2', '2', '1', '6', '6', '1', '1', '7', '/', '1', '9', '1', '8', '2', '4', '9', '6', '1', '4', '7', '9', '5', '5', '9', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '6', '5', '2', '5', '6', '0', '5', '9', '0', '2', '2', '7', '4', '8', '4', '2', '8', '9', '/', '3', '1', '8', '6', '4', '6', '1', '1', '5', '4', '1', '4', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '2', '8', '8', '2', '9', '0', '1', '0', '7', '5', '7', '5', '4', '8', '1', '6', '5', '6', '8', '3', '7', '9', '/', '5', '8', '8', '2', '6', '3', '2', '1', '5', '2', '0', '3', '9', '8', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '2', '5', '7', '2', '6', '1', '8', '3', '2', '9', '3', '0', '8', '7', '0', '6', '4', '2', '5', '0', '7', '/', '3', '5', '2', '9', '5', '7', '9', '2', '9', '1', '2', '2', '3', '8', '8', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '0', '2', '0', '2', '5', '9', '4', '7', '9', '3', '3', '7', '5', '3', '8', '2', '0', '6', '3', '3', '4', '1', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '1', '3', '7', '3', '9', '2', '5', '0', '1', '9', '7', '4', '6', '6', '5', '9', '1', '5', '2', '2', '3', '/', '5', '3', '4', '7', '8', '4', '7', '4', '1', '0', '9', '4', '5', '2', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '2', '7', '9', '0', '6', '2', '7', '4', '4', '0', '5', '5', '0', '8', '7', '1', '3', '0', '4', '3', '1', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '7', '4', '8', '3', '8', '3', '6', '9', '1', '7', '1', '5', '9', '8', '1', '1', '1', '1', '0', '9', '/', '2', '0', '0', '5', '4', '4', '2', '7', '7', '9', '1', '0', '4', '4', '8', '1', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '2', '7', '4', '8', '2', '4', '9', '9', '9', '5', '5', '3', '0', '7', '0', '7', '4', '7', '8', '9', '9', '/', '2', '0', '0', '5', '4', '4', '2', '7', '7', '9', '1', '0', '4', '4', '8', '1', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '5', '8', '3', '4', '1', '4', '5', '2', '1', '3', '8', '8', '3', '7', '4', '7', '3', '1', '/', '1', '2', '7', '4', '5', '8', '4', '4', '6', '1', '6', '5', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0132769_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0132769Field005Chars00 ++ tail)) fragment0132769Acc00500 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0132769Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_005"
  err.flush

noncomputable def fragment0132769Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0132769Field006Value00 : SourceJson := .str (String.ofList ['1', '4', '1', '1', '4', '4', '2', '2', '9', '7', '3', '6', '6', '2', '5', '0', '7', '6', '6', '7', '5', '3', '0', '6', '3', '6', '8', '4', '2', '6', '1', '3', '5', '6', '0', '6', '4', '2', '4', '2', '3', '1', '3', '4', '9', '9', '2', '5', '7', '9', '6', '0', '0', '0', '0', '0', '/', '2', '1', '4', '2', '1', '9', '0', '3', '3', '6', '3', '8', '4', '1', '3', '4', '9', '3', '8', '9', '4', '8', '4', '9', '3', '2', '0', '7', '8', '1', '6', '4', '5', '2', '7', '6', '8', '3', '7', '6', '0', '6', '1', '7', '9', '0', '1', '1', '0', '5', '9', '7', '3', '7', '9', '1', '2', '6', '1', '9', '7', '7', '7', '4', '5', '1', '0', '0', '0', '5', '0', '3', '9'])
noncomputable def fragment0132769Acc00700 : List (String × SourceJson) := (fragment0132769Field006Key00, fragment0132769Field006Value00) :: fragment0132769Acc00600
noncomputable def fragment0132769Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '1', '1', '4', '4', '2', '2', '9', '7', '3', '6', '6', '2', '5', '0', '7', '6', '6', '7', '5', '3', '0', '6', '3', '6', '8', '4', '2', '6', '1', '3', '5', '6', '0', '6', '4', '2', '4', '2', '3', '1', '3', '4', '9', '9', '2', '5', '7', '9', '6', '0', '0', '0', '0', '0', '/', '2', '1', '4', '2', '1', '9', '0', '3', '3', '6', '3', '8', '4', '1', '3', '4', '9', '3', '8', '9', '4', '8', '4', '9', '3', '2', '0', '7', '8', '1', '6', '4', '5', '2', '7', '6', '8', '3', '7', '6', '0', '6', '1', '7', '9', '0', '1', '1', '0', '5', '9', '7', '3', '7', '9', '1', '2', '6', '1', '9', '7', '7', '7', '4', '5', '1', '0', '0', '0', '5', '0', '3', '9', '"', ',']

theorem object_fragment0132769_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0132769Field006Chars00 ++ tail)) fragment0132769Acc00600 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0132769Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_006"
  err.flush

noncomputable def fragment0132769Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0132769Field007Value00 : SourceJson := .str (String.ofList ['7', '3', '4', '7', '7', '7', '9', '4', '8', '7', '1', '8', '1', '0', '5', '7', '5', '7', '7', '2', '0', '0', '9', '0', '9', '4', '4', '2', '5', '1', '7', '3', '0', '5', '9', '7', '7', '2', '4', '5', '2', '6', '4', '0', '9', '8', '2', '6', '7', '0', '6', '3', '8', '7', '1', '3', '9', '1', '3', '6', '2', '3', '5', '4', '5', '1', '1', '6', '2', '8', '0', '5', '8', '1', '3', '5', '4', '5', '6', '8', '6', '2', '1', '2', '3', '9', '0', '9', '0', '5', '1', '5', '4', '1', '2', '8', '5', '2', '4', '4', '4', '0', '3', '1', '3', '6', '9', '8', '9', '4', '4', '4', '0', '5', '6', '5', '3', '1', '2', '6', '6', '2', '4', '1', '0', '0', '3', '5', '0', '6', '4', '3', '5', '3', '6', '8', '4', '2', '9', '4', '0', '2', '3', '3', '0', '4', '6', '4', '4', '1', '3', '5', '0', '8', '8', '0', '2', '0', '7', '5', '7', '2', '7', '0', '9', '4', '1', '6', '7', '7', '5', '0', '8', '6', '4', '2', '3', '5', '2', '1', '2', '2', '8', '9', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '8', '0', '0', '3', '1', '5', '4', '8', '3', '7', '4', '6', '5', '7', '2', '8', '6', '3', '8', '9', '3', '0', '9', '0', '1', '1', '0', '8', '4', '4', '9', '5', '7', '2', '9', '1', '8', '3', '1', '1', '3', '9', '6', '8', '8', '2', '1', '5', '8', '2', '3', '8', '2', '0', '5', '2', '3', '6', '0', '9', '0', '7', '7', '5', '1', '7', '8', '4', '2', '8', '3', '2', '5', '1', '5', '2', '4', '6', '0', '0', '6', '2', '3', '4', '7', '4', '0', '1', '7', '5', '9', '5', '5', '0', '4', '4', '8', '9', '5', '5', '8', '6', '0', '8', '3', '9', '1', '2', '7', '0', '8', '9', '8', '8', '3', '5', '0', '2', '8', '3', '8', '8', '2', '1', '0', '9', '9', '2', '6', '9', '5', '0', '1', '9', '9', '0', '5', '5', '7', '2', '8', '1', '5', '2', '9', '0', '9', '4', '4', '9', '0', '4', '0', '9', '4', '1', '7', '7', '3', '3', '1', '6', '5', '9', '8', '4', '8', '8', '6', '8', '3', '9', '2', '4', '3', '3', '5', '8', '3', '0', '6', '1', '9', '4', '8', '2', '2', '2', '6', '9', '1', '0', '3', '7', '3', '4', '3', '7', '1', '9', '9', '0', '9', '2', '4', '2', '2', '8', '2', '1', '7', '1', '2', '5', '5', '6', '2', '8', '0', '7'])
noncomputable def fragment0132769Acc00800 : List (String × SourceJson) := (fragment0132769Field007Key00, fragment0132769Field007Value00) :: fragment0132769Acc00700
noncomputable def fragment0132769Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '3', '4', '7', '7', '7', '9', '4', '8', '7', '1', '8', '1', '0', '5', '7', '5', '7', '7', '2', '0', '0', '9', '0', '9', '4', '4', '2', '5', '1', '7', '3', '0', '5', '9', '7', '7', '2', '4', '5', '2', '6', '4', '0', '9', '8', '2', '6', '7', '0', '6', '3', '8', '7', '1', '3', '9', '1', '3', '6', '2', '3', '5', '4', '5', '1', '1', '6', '2', '8', '0', '5', '8', '1', '3', '5', '4', '5', '6', '8', '6', '2', '1', '2', '3', '9', '0', '9', '0', '5', '1', '5', '4', '1', '2', '8', '5', '2', '4', '4', '4', '0', '3', '1', '3', '6', '9', '8', '9', '4', '4', '4', '0', '5', '6', '5', '3', '1', '2', '6', '6', '2', '4', '1', '0', '0', '3', '5', '0', '6', '4', '3', '5', '3', '6', '8', '4', '2', '9', '4', '0', '2', '3', '3', '0', '4', '6', '4', '4', '1', '3', '5', '0', '8', '8', '0', '2', '0', '7', '5', '7', '2', '7', '0', '9', '4', '1', '6', '7', '7', '5', '0', '8', '6', '4', '2', '3', '5', '2', '1', '2', '2', '8', '9', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '8', '0', '0', '3', '1', '5', '4', '8', '3', '7', '4', '6', '5', '7', '2', '8', '6', '3', '8', '9', '3', '0', '9', '0', '1', '1', '0', '8', '4', '4', '9', '5', '7', '2', '9', '1', '8', '3', '1', '1', '3', '9', '6', '8', '8', '2', '1', '5', '8', '2', '3', '8', '2', '0', '5', '2', '3', '6', '0', '9', '0', '7', '7', '5', '1', '7', '8', '4', '2', '8', '3', '2', '5', '1', '5', '2', '4', '6', '0', '0', '6', '2', '3', '4', '7', '4', '0', '1', '7', '5', '9', '5', '5', '0', '4', '4', '8', '9', '5', '5', '8', '6', '0', '8', '3', '9', '1', '2', '7', '0', '8', '9', '8', '8', '3', '5', '0', '2', '8', '3', '8', '8', '2', '1', '0', '9', '9', '2', '6', '9', '5', '0', '1', '9', '9', '0', '5', '5', '7', '2', '8', '1', '5', '2', '9', '0', '9', '4', '4', '9', '0', '4', '0', '9', '4', '1', '7', '7', '3', '3', '1', '6', '5', '9', '8', '4', '8', '8', '6', '8', '3', '9', '2', '4', '3', '3', '5', '8', '3', '0', '6', '1', '9', '4', '8', '2', '2', '2', '6', '9', '1', '0', '3', '7', '3', '4', '3', '7', '1', '9', '9', '0', '9', '2', '4', '2', '2', '8', '2', '1', '7', '1', '2', '5', '5', '6', '2', '8', '0', '7', '"', ',']

theorem object_fragment0132769_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0132769Field007Chars00 ++ tail)) fragment0132769Acc00700 =
      SourceJson.object (fuel + 428) (SourceJson.white tail) fragment0132769Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_007"
  err.flush

noncomputable def fragment0132769Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0132769Field008Value00 : SourceJson := .str (String.ofList ['5', '2', '2', '0', '1', '7', '0', '1', '1', '3', '5', '4'])
noncomputable def fragment0132769Acc00900 : List (String × SourceJson) := (fragment0132769Field008Key00, fragment0132769Field008Value00) :: fragment0132769Acc00800
noncomputable def fragment0132769Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '2', '2', '0', '1', '7', '0', '1', '1', '3', '5', '4', '"', ',']

theorem object_fragment0132769_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 428) (SourceJson.white (fragment0132769Field008Chars00 ++ tail)) fragment0132769Acc00800 =
      SourceJson.object (fuel + 427) (SourceJson.white tail) fragment0132769Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_008"
  err.flush

noncomputable def fragment0132769Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0132769Field009Value00 : SourceJson := .str (String.ofList ['1', '5', '3', '1', '8', '4', '9', '3', '1', '5', '7', '1', '9'])
noncomputable def fragment0132769Acc01000 : List (String × SourceJson) := (fragment0132769Field009Key00, fragment0132769Field009Value00) :: fragment0132769Acc00900
noncomputable def fragment0132769Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '3', '1', '8', '4', '9', '3', '1', '5', '7', '1', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0132769_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 427) (SourceJson.white (fragment0132769Field009Chars00 ++ tail)) fragment0132769Acc00900 =
      .ok (.obj (fragment0132769Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0132769_object_field_009"
  err.flush

noncomputable def fragment0132769Chars : List Char := '{' :: (fragment0132769Field000Chars00 ++ fragment0132769Field001Chars00 ++ fragment0132769Field002Chars00 ++ fragment0132769Field003Chars00 ++ fragment0132769Field004Chars00 ++ fragment0132769Field005Chars00 ++ fragment0132769Field006Chars00 ++ fragment0132769Field007Chars00 ++ fragment0132769Field008Chars00 ++ fragment0132769Field009Chars00)
noncomputable def fragment0132769Value : SourceJson := .obj (fragment0132769Acc01000.reverse)

theorem value_fragment0132769 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 437) (fragment0132769Chars ++ tail) =
      .ok (fragment0132769Value, tail) := by
  have hinput : fragment0132769Chars ++ tail = '{' :: (fragment0132769Field000Chars00 ++ (fragment0132769Field001Chars00 ++ (fragment0132769Field002Chars00 ++ (fragment0132769Field003Chars00 ++ (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0132769Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 437) (fragment0132769Chars ++ tail) =
        SourceJson.value (fuel + 437) ('{' :: (fragment0132769Field000Chars00 ++ (fragment0132769Field001Chars00 ++ (fragment0132769Field002Chars00 ++ (fragment0132769Field003Chars00 ++ (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 437)) hinput
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0132769Field000Chars00 ++ (fragment0132769Field001Chars00 ++ (fragment0132769Field002Chars00 ++ (fragment0132769Field003Chars00 ++ (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))))))))))) fragment0132769Acc00000 := by rfl
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0132769Field001Chars00 ++ (fragment0132769Field002Chars00 ++ (fragment0132769Field003Chars00 ++ (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail))))))))))) fragment0132769Acc00100 := object_fragment0132769_field_000 fuel (fragment0132769Field001Chars00 ++ (fragment0132769Field002Chars00 ++ (fragment0132769Field003Chars00 ++ (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0132769Field002Chars00 ++ (fragment0132769Field003Chars00 ++ (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))))))))) fragment0132769Acc00200 := object_fragment0132769_field_001 fuel (fragment0132769Field002Chars00 ++ (fragment0132769Field003Chars00 ++ (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0132769Field003Chars00 ++ (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail))))))))) fragment0132769Acc00300 := object_fragment0132769_field_002 fuel (fragment0132769Field003Chars00 ++ (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))))))) fragment0132769Acc00400 := object_fragment0132769_field_003 fuel (fragment0132769Field004Chars00 ++ (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail))))))) fragment0132769Acc00500 := object_fragment0132769_field_004 fuel (fragment0132769Field005Chars00 ++ (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))))) fragment0132769Acc00600 := object_fragment0132769_field_005 fuel (fragment0132769Field006Chars00 ++ (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail))))) fragment0132769Acc00700 := object_fragment0132769_field_006 fuel (fragment0132769Field007Chars00 ++ (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 428) (SourceJson.white (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))) fragment0132769Acc00800 := object_fragment0132769_field_007 fuel (fragment0132769Field008Chars00 ++ (fragment0132769Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 427) (SourceJson.white (fragment0132769Field009Chars00 ++ (tail))) fragment0132769Acc00900 := object_fragment0132769_field_008 fuel (fragment0132769Field009Chars00 ++ (tail))
    _ = .ok (fragment0132769Value, tail) := object_fragment0132769_field_009 fuel (tail)

noncomputable def fragment0134791Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0134791Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0134791Field000Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0134791Acc00100 : List (String × SourceJson) := (fragment0134791Field000Key00, fragment0134791Field000Value00) :: fragment0134791Acc00000
noncomputable def fragment0134791Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', ',']

theorem object_fragment0134791_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment0134791Field000Chars00 ++ tail)) fragment0134791Acc00000 =
      SourceJson.object (fuel + 368) (SourceJson.white tail) fragment0134791Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_000"
  err.flush

noncomputable def fragment0134791Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0134791Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0134791Acc00200 : List (String × SourceJson) := (fragment0134791Field001Key00, fragment0134791Field001Value00) :: fragment0134791Acc00100
noncomputable def fragment0134791Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0134791_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0134791Field001Chars00 ++ tail)) fragment0134791Acc00100 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment0134791Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_001"
  err.flush

noncomputable def fragment0134791Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0134791Field002Value00 : SourceJson := .str (String.ofList ['9', '1', '3', '9', '4', '1', '8', '9', '5', '4', '8', '5', '1', '7', '6', '8', '3', '9', '1', '5', '1', '0', '0', '1', '5', '9', '5', '8', '7', '6', '7', '6', '5', '3', '2', '5', '2', '8', '4', '6', '6', '3', '/', '4', '1', '1', '3', '8', '0', '0', '3', '2', '1', '0', '8', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0134791Acc00300 : List (String × SourceJson) := (fragment0134791Field002Key00, fragment0134791Field002Value00) :: fragment0134791Acc00200
noncomputable def fragment0134791Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '1', '3', '9', '4', '1', '8', '9', '5', '4', '8', '5', '1', '7', '6', '8', '3', '9', '1', '5', '1', '0', '0', '1', '5', '9', '5', '8', '7', '6', '7', '6', '5', '3', '2', '5', '2', '8', '4', '6', '6', '3', '/', '4', '1', '1', '3', '8', '0', '0', '3', '2', '1', '0', '8', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0134791_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0134791Field002Chars00 ++ tail)) fragment0134791Acc00200 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0134791Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_002"
  err.flush

noncomputable def fragment0134791Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0134791Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0134791Acc00400 : List (String × SourceJson) := (fragment0134791Field003Key00, fragment0134791Field003Value00) :: fragment0134791Acc00300
noncomputable def fragment0134791Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0134791_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0134791Field003Chars00 ++ tail)) fragment0134791Acc00300 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0134791Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_003"
  err.flush

noncomputable def fragment0134791Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0134791Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0134791Acc00500 : List (String × SourceJson) := (fragment0134791Field004Key00, fragment0134791Field004Value00) :: fragment0134791Acc00400
noncomputable def fragment0134791Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0134791_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0134791Field004Chars00 ++ tail)) fragment0134791Acc00400 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0134791Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_004"
  err.flush

noncomputable def fragment0134791Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0134791Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '3', '3', '1', '7', '4', '4', '9', '7', '4', '6', '2', '4', '1', '4', '1', '5', '3', '3', '/', '6', '9', '5', '4', '7', '4', '4', '2', '7', '8', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '2', '1', '7', '7', '6', '9', '6', '6', '4', '4', '1', '0', '4', '3', '0', '3', '/', '4', '9', '6', '7', '6', '7', '4', '4', '8', '4', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '6', '1', '6', '5', '6', '8', '4', '0', '2', '2', '9', '4', '6', '5', '1', '4', '2', '7', '/', '7', '1', '0', '9', '2', '9', '4', '1', '5', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '2', '7', '7', '6', '2', '0', '5', '8', '0', '5', '7', '5', '1', '3', '8', '0', '9', '3', '/', '1', '2', '7', '9', '6', '7', '2', '9', '4', '7', '2', '9', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '5', '5', '5', '6', '8', '4', '3', '0', '0', '6', '2', '1', '9', '0', '9', '4', '6', '7', '9', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '1', '2', '4', '2', '7', '4', '5', '9', '7', '9', '1', '3', '7', '4', '1', '3', '9', '/', '6', '4', '6', '2', '9', '9', '4', '6', '8', '3', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '2', '1', '1', '2', '6', '8', '0', '7', '6', '1', '8', '2', '3', '0', '2', '2', '7', '/', '1', '4', '5', '4', '1', '7', '3', '8', '0', '3', '7', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '0', '0', '2', '5', '8', '7', '1', '5', '6', '2', '3', '3', '6', '6', '0', '4', '1', '/', '7', '2', '7', '0', '8', '6', '9', '0', '1', '8', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '0', '0', '2', '5', '3', '8', '6', '8', '3', '7', '7', '3', '5', '3', '5', '5', '1', '/', '7', '2', '7', '0', '8', '6', '9', '0', '1', '8', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '8', '1', '4', '4', '3', '4', '9', '9', '1', '1', '8', '6', '2', '6', '9', '7', '/', '1', '9', '8', '7', '0', '6', '9', '7', '9', '3', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0134791Acc00600 : List (String × SourceJson) := (fragment0134791Field005Key00, fragment0134791Field005Value00) :: fragment0134791Acc00500
noncomputable def fragment0134791Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '3', '1', '7', '4', '4', '9', '7', '4', '6', '2', '4', '1', '4', '1', '5', '3', '3', '/', '6', '9', '5', '4', '7', '4', '4', '2', '7', '8', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '2', '1', '7', '7', '6', '9', '6', '6', '4', '4', '1', '0', '4', '3', '0', '3', '/', '4', '9', '6', '7', '6', '7', '4', '4', '8', '4', '8', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '6', '1', '6', '5', '6', '8', '4', '0', '2', '2', '9', '4', '6', '5', '1', '4', '2', '7', '/', '7', '1', '0', '9', '2', '9', '4', '1', '5', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '2', '7', '7', '6', '2', '0', '5', '8', '0', '5', '7', '5', '1', '3', '8', '0', '9', '3', '/', '1', '2', '7', '9', '6', '7', '2', '9', '4', '7', '2', '9', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '5', '5', '5', '6', '8', '4', '3', '0', '0', '6', '2', '1', '9', '0', '9', '4', '6', '7', '9', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '1', '2', '4', '2', '7', '4', '5', '9', '7', '9', '1', '3', '7', '4', '1', '3', '9', '/', '6', '4', '6', '2', '9', '9', '4', '6', '8', '3', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '2', '1', '1', '2', '6', '8', '0', '7', '6', '1', '8', '2', '3', '0', '2', '2', '7', '/', '1', '4', '5', '4', '1', '7', '3', '8', '0', '3', '7', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '0', '0', '2', '5', '8', '7', '1', '5', '6', '2', '3', '3', '6', '6', '0', '4', '1', '/', '7', '2', '7', '0', '8', '6', '9', '0', '1', '8', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '0', '0', '2', '5', '3', '8', '6', '8', '3', '7', '7', '3', '5', '3', '5', '5', '1', '/', '7', '2', '7', '0', '8', '6', '9', '0', '1', '8', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '8', '1', '4', '4', '3', '4', '9', '9', '1', '1', '8', '6', '2', '6', '9', '7', '/', '1', '9', '8', '7', '0', '6', '9', '7', '9', '3', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0134791_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0134791Field005Chars00 ++ tail)) fragment0134791Acc00500 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0134791Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_005"
  err.flush

noncomputable def fragment0134791Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0134791Field006Value00 : SourceJson := .str (String.ofList ['7', '0', '9', '3', '2', '0', '4', '9', '4', '5', '6', '0', '3', '2', '2', '6', '0', '9', '0', '8', '7', '7', '3', '4', '0', '6', '6', '3', '6', '1', '7', '3', '4', '3', '3', '4', '5', '6', '5', '1', '8', '5', '8', '1', '6', '0', '0', '/', '1', '7', '8', '4', '2', '6', '6', '2', '8', '1', '5', '4', '4', '3', '5', '0', '4', '6', '0', '5', '8', '4', '2', '7', '0', '6', '3', '0', '4', '6', '6', '7', '2', '0', '4', '2', '9', '4', '2', '7', '7', '3', '6', '0', '6', '8', '0', '0', '1', '5', '8', '3', '7', '9', '9', '0', '8', '4', '6', '1', '8', '0', '7', '9'])
noncomputable def fragment0134791Acc00700 : List (String × SourceJson) := (fragment0134791Field006Key00, fragment0134791Field006Value00) :: fragment0134791Acc00600
noncomputable def fragment0134791Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '0', '9', '3', '2', '0', '4', '9', '4', '5', '6', '0', '3', '2', '2', '6', '0', '9', '0', '8', '7', '7', '3', '4', '0', '6', '6', '3', '6', '1', '7', '3', '4', '3', '3', '4', '5', '6', '5', '1', '8', '5', '8', '1', '6', '0', '0', '/', '1', '7', '8', '4', '2', '6', '6', '2', '8', '1', '5', '4', '4', '3', '5', '0', '4', '6', '0', '5', '8', '4', '2', '7', '0', '6', '3', '0', '4', '6', '6', '7', '2', '0', '4', '2', '9', '4', '2', '7', '7', '3', '6', '0', '6', '8', '0', '0', '1', '5', '8', '3', '7', '9', '9', '0', '8', '4', '6', '1', '8', '0', '7', '9', '"', ',']

theorem object_fragment0134791_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0134791Field006Chars00 ++ tail)) fragment0134791Acc00600 =
      SourceJson.object (fuel + 362) (SourceJson.white tail) fragment0134791Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_006"
  err.flush

noncomputable def fragment0134791Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0134791Field007Value00 : SourceJson := .str (String.ofList ['6', '0', '7', '7', '5', '8', '9', '1', '7', '3', '4', '3', '1', '4', '6', '3', '8', '4', '9', '8', '7', '0', '2', '9', '6', '4', '6', '8', '8', '8', '0', '2', '0', '9', '8', '7', '1', '8', '2', '8', '6', '8', '9', '7', '6', '9', '7', '3', '9', '0', '7', '4', '5', '0', '2', '7', '1', '6', '4', '6', '9', '9', '3', '0', '9', '2', '8', '7', '7', '7', '2', '8', '6', '8', '4', '9', '2', '7', '7', '4', '9', '9', '3', '4', '2', '2', '0', '1', '2', '2', '7', '0', '8', '9', '2', '9', '0', '0', '0', '9', '9', '7', '8', '8', '2', '5', '8', '7', '7', '4', '3', '6', '9', '8', '5', '6', '5', '1', '5', '5', '8', '2', '5', '5', '4', '8', '7', '4', '7', '4', '3', '3', '3', '9', '2', '6', '9', '3', '7', '0', '2', '8', '7', '8', '8', '6', '9', '5', '2', '1', '4', '3', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '9', '8', '1', '1', '5', '1', '9', '6', '1', '1', '8', '5', '0', '1', '6', '4', '6', '7', '1', '0', '8', '8', '5', '7', '4', '4', '6', '5', '1', '1', '7', '2', '5', '3', '3', '5', '7', '9', '5', '3', '4', '4', '1', '4', '1', '5', '9', '9', '5', '8', '3', '5', '6', '8', '3', '2', '4', '0', '6', '2', '5', '3', '0', '9', '7', '1', '5', '4', '9', '8', '5', '1', '3', '5', '0', '3', '5', '3', '7', '7', '3', '3', '4', '5', '1', '0', '6', '5', '8', '8', '0', '0', '7', '5', '6', '9', '8', '6', '8', '1', '7', '3', '1', '9', '1', '3', '3', '8', '6', '6', '7', '4', '9', '2', '8', '3', '4', '2', '3', '9', '4', '4', '5', '9', '0', '2', '2', '5', '9', '6', '5', '8', '4', '2', '2', '2', '2', '3', '6', '0', '1', '4', '7', '7', '1', '1', '1', '7', '0', '3', '3', '2', '8', '9', '2', '1', '2', '2', '3', '6', '6', '7', '4', '6', '0', '0', '0', '4', '0', '2', '7', '5', '3', '3', '8', '4', '2', '2', '7', '6', '3', '2', '6', '6', '0', '9'])
noncomputable def fragment0134791Acc00800 : List (String × SourceJson) := (fragment0134791Field007Key00, fragment0134791Field007Value00) :: fragment0134791Acc00700
noncomputable def fragment0134791Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '0', '7', '7', '5', '8', '9', '1', '7', '3', '4', '3', '1', '4', '6', '3', '8', '4', '9', '8', '7', '0', '2', '9', '6', '4', '6', '8', '8', '8', '0', '2', '0', '9', '8', '7', '1', '8', '2', '8', '6', '8', '9', '7', '6', '9', '7', '3', '9', '0', '7', '4', '5', '0', '2', '7', '1', '6', '4', '6', '9', '9', '3', '0', '9', '2', '8', '7', '7', '7', '2', '8', '6', '8', '4', '9', '2', '7', '7', '4', '9', '9', '3', '4', '2', '2', '0', '1', '2', '2', '7', '0', '8', '9', '2', '9', '0', '0', '0', '9', '9', '7', '8', '8', '2', '5', '8', '7', '7', '4', '3', '6', '9', '8', '5', '6', '5', '1', '5', '5', '8', '2', '5', '5', '4', '8', '7', '4', '7', '4', '3', '3', '3', '9', '2', '6', '9', '3', '7', '0', '2', '8', '7', '8', '8', '6', '9', '5', '2', '1', '4', '3', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '9', '8', '1', '1', '5', '1', '9', '6', '1', '1', '8', '5', '0', '1', '6', '4', '6', '7', '1', '0', '8', '8', '5', '7', '4', '4', '6', '5', '1', '1', '7', '2', '5', '3', '3', '5', '7', '9', '5', '3', '4', '4', '1', '4', '1', '5', '9', '9', '5', '8', '3', '5', '6', '8', '3', '2', '4', '0', '6', '2', '5', '3', '0', '9', '7', '1', '5', '4', '9', '8', '5', '1', '3', '5', '0', '3', '5', '3', '7', '7', '3', '3', '4', '5', '1', '0', '6', '5', '8', '8', '0', '0', '7', '5', '6', '9', '8', '6', '8', '1', '7', '3', '1', '9', '1', '3', '3', '8', '6', '6', '7', '4', '9', '2', '8', '3', '4', '2', '3', '9', '4', '4', '5', '9', '0', '2', '2', '5', '9', '6', '5', '8', '4', '2', '2', '2', '2', '3', '6', '0', '1', '4', '7', '7', '1', '1', '1', '7', '0', '3', '3', '2', '8', '9', '2', '1', '2', '2', '3', '6', '6', '7', '4', '6', '0', '0', '0', '4', '0', '2', '7', '5', '3', '3', '8', '4', '2', '2', '7', '6', '3', '2', '6', '6', '0', '9', '"', ',']

theorem object_fragment0134791_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 362) (SourceJson.white (fragment0134791Field007Chars00 ++ tail)) fragment0134791Acc00700 =
      SourceJson.object (fuel + 361) (SourceJson.white tail) fragment0134791Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_007"
  err.flush

noncomputable def fragment0134791Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0134791Field008Value00 : SourceJson := .str (String.ofList ['3', '1', '4', '9', '6', '5', '0', '9', '2', '3', '6', '8', '8'])
noncomputable def fragment0134791Acc00900 : List (String × SourceJson) := (fragment0134791Field008Key00, fragment0134791Field008Value00) :: fragment0134791Acc00800
noncomputable def fragment0134791Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '4', '9', '6', '5', '0', '9', '2', '3', '6', '8', '8', '"', ',']

theorem object_fragment0134791_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 361) (SourceJson.white (fragment0134791Field008Chars00 ++ tail)) fragment0134791Acc00800 =
      SourceJson.object (fuel + 360) (SourceJson.white tail) fragment0134791Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_008"
  err.flush

noncomputable def fragment0134791Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0134791Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '0', '9', '4', '8', '9', '6', '8', '3', '9', '4', '6', '2'])
noncomputable def fragment0134791Acc01000 : List (String × SourceJson) := (fragment0134791Field009Key00, fragment0134791Field009Value00) :: fragment0134791Acc00900
noncomputable def fragment0134791Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '0', '9', '4', '8', '9', '6', '8', '3', '9', '4', '6', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0134791_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 360) (SourceJson.white (fragment0134791Field009Chars00 ++ tail)) fragment0134791Acc00900 =
      .ok (.obj (fragment0134791Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0134791_object_field_009"
  err.flush

noncomputable def fragment0134791Chars : List Char := '{' :: (fragment0134791Field000Chars00 ++ fragment0134791Field001Chars00 ++ fragment0134791Field002Chars00 ++ fragment0134791Field003Chars00 ++ fragment0134791Field004Chars00 ++ fragment0134791Field005Chars00 ++ fragment0134791Field006Chars00 ++ fragment0134791Field007Chars00 ++ fragment0134791Field008Chars00 ++ fragment0134791Field009Chars00)
noncomputable def fragment0134791Value : SourceJson := .obj (fragment0134791Acc01000.reverse)

theorem value_fragment0134791 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 370) (fragment0134791Chars ++ tail) =
      .ok (fragment0134791Value, tail) := by
  have hinput : fragment0134791Chars ++ tail = '{' :: (fragment0134791Field000Chars00 ++ (fragment0134791Field001Chars00 ++ (fragment0134791Field002Chars00 ++ (fragment0134791Field003Chars00 ++ (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0134791Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 370) (fragment0134791Chars ++ tail) =
        SourceJson.value (fuel + 370) ('{' :: (fragment0134791Field000Chars00 ++ (fragment0134791Field001Chars00 ++ (fragment0134791Field002Chars00 ++ (fragment0134791Field003Chars00 ++ (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 370)) hinput
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment0134791Field000Chars00 ++ (fragment0134791Field001Chars00 ++ (fragment0134791Field002Chars00 ++ (fragment0134791Field003Chars00 ++ (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))))))))))) fragment0134791Acc00000 := by rfl
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0134791Field001Chars00 ++ (fragment0134791Field002Chars00 ++ (fragment0134791Field003Chars00 ++ (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail))))))))))) fragment0134791Acc00100 := object_fragment0134791_field_000 fuel (fragment0134791Field001Chars00 ++ (fragment0134791Field002Chars00 ++ (fragment0134791Field003Chars00 ++ (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0134791Field002Chars00 ++ (fragment0134791Field003Chars00 ++ (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))))))))) fragment0134791Acc00200 := object_fragment0134791_field_001 fuel (fragment0134791Field002Chars00 ++ (fragment0134791Field003Chars00 ++ (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0134791Field003Chars00 ++ (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail))))))))) fragment0134791Acc00300 := object_fragment0134791_field_002 fuel (fragment0134791Field003Chars00 ++ (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))))))) fragment0134791Acc00400 := object_fragment0134791_field_003 fuel (fragment0134791Field004Chars00 ++ (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail))))))) fragment0134791Acc00500 := object_fragment0134791_field_004 fuel (fragment0134791Field005Chars00 ++ (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))))) fragment0134791Acc00600 := object_fragment0134791_field_005 fuel (fragment0134791Field006Chars00 ++ (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 362) (SourceJson.white (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail))))) fragment0134791Acc00700 := object_fragment0134791_field_006 fuel (fragment0134791Field007Chars00 ++ (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 361) (SourceJson.white (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))) fragment0134791Acc00800 := object_fragment0134791_field_007 fuel (fragment0134791Field008Chars00 ++ (fragment0134791Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 360) (SourceJson.white (fragment0134791Field009Chars00 ++ (tail))) fragment0134791Acc00900 := object_fragment0134791_field_008 fuel (fragment0134791Field009Chars00 ++ (tail))
    _ = .ok (fragment0134791Value, tail) := object_fragment0134791_field_009 fuel (tail)

noncomputable def fragment0136659Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0136659Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0136659Field000Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0136659Acc00100 : List (String × SourceJson) := (fragment0136659Field000Key00, fragment0136659Field000Value00) :: fragment0136659Acc00000
noncomputable def fragment0136659Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', ',']

theorem object_fragment0136659_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0136659Field000Chars00 ++ tail)) fragment0136659Acc00000 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0136659Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_000"
  err.flush

noncomputable def fragment0136659Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0136659Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0136659Acc00200 : List (String × SourceJson) := (fragment0136659Field001Key00, fragment0136659Field001Value00) :: fragment0136659Acc00100
noncomputable def fragment0136659Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0136659_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0136659Field001Chars00 ++ tail)) fragment0136659Acc00100 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0136659Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_001"
  err.flush

noncomputable def fragment0136659Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0136659Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '2', '2', '4', '4', '6', '9', '3', '9', '0', '4', '3', '9', '1', '9', '3', '8', '3', '7', '3', '5', '4', '0', '2', '9', '9', '1', '6', '1', '4', '9', '5', '9', '6', '2', '7', '3', '6', '8', '3', '2', '4', '3', '/', '9', '0', '6', '7', '1', '5', '1', '7', '2', '8', '1', '1', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0136659Acc00300 : List (String × SourceJson) := (fragment0136659Field002Key00, fragment0136659Field002Value00) :: fragment0136659Acc00200
noncomputable def fragment0136659Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '2', '2', '4', '4', '6', '9', '3', '9', '0', '4', '3', '9', '1', '9', '3', '8', '3', '7', '3', '5', '4', '0', '2', '9', '9', '1', '6', '1', '4', '9', '5', '9', '6', '2', '7', '3', '6', '8', '3', '2', '4', '3', '/', '9', '0', '6', '7', '1', '5', '1', '7', '2', '8', '1', '1', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0136659_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0136659Field002Chars00 ++ tail)) fragment0136659Acc00200 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0136659Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_002"
  err.flush

noncomputable def fragment0136659Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0136659Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0136659Acc00400 : List (String × SourceJson) := (fragment0136659Field003Key00, fragment0136659Field003Value00) :: fragment0136659Acc00300
noncomputable def fragment0136659Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0136659_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0136659Field003Chars00 ++ tail)) fragment0136659Acc00300 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0136659Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_003"
  err.flush

noncomputable def fragment0136659Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0136659Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0136659Acc00500 : List (String × SourceJson) := (fragment0136659Field004Key00, fragment0136659Field004Value00) :: fragment0136659Acc00400
noncomputable def fragment0136659Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0136659_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0136659Field004Chars00 ++ tail)) fragment0136659Acc00400 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0136659Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_004"
  err.flush

noncomputable def fragment0136659Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0136659Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '8', '2', '6', '5', '5', '8', '8', '7', '/', '8', '6', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '5', '2', '7', '7', '8', '5', '9', '9', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '0', '0', '4', '7', '3', '9', '8', '7', '5', '3', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '7', '0', '8', '8', '5', '0', '1', '1', '5', '1', '/', '3', '8', '2', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '1', '8', '0', '1', '0', '9', '6', '7', '1', '6', '9', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '1', '2', '2', '5', '2', '2', '2', '4', '1', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '8', '4', '9', '3', '9', '4', '9', '1', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '6', '9', '1', '2', '7', '5', '7', '3', '9', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '6', '9', '1', '2', '1', '7', '7', '7', '9', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '3', '7', '3', '2', '2', '9', '0', '4', '9', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0136659Acc00600 : List (String × SourceJson) := (fragment0136659Field005Key00, fragment0136659Field005Value00) :: fragment0136659Acc00500
noncomputable def fragment0136659Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '2', '6', '5', '5', '8', '8', '7', '/', '8', '6', '6', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '5', '2', '7', '7', '8', '5', '9', '9', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '0', '0', '0', '4', '7', '3', '9', '8', '7', '5', '3', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '7', '0', '8', '8', '5', '0', '1', '1', '5', '1', '/', '3', '8', '2', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '8', '0', '1', '0', '9', '6', '7', '1', '6', '9', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '1', '2', '2', '5', '2', '2', '2', '4', '1', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '8', '4', '9', '3', '9', '4', '9', '1', '/', '6', '2', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '6', '9', '1', '2', '7', '5', '7', '3', '9', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '6', '9', '1', '2', '1', '7', '7', '7', '9', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '3', '7', '3', '2', '2', '9', '0', '4', '9', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0136659_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0136659Field005Chars00 ++ tail)) fragment0136659Acc00500 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0136659Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_005"
  err.flush

noncomputable def fragment0136659Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0136659Field006Value00 : SourceJson := .str (String.ofList ['4', '6', '8', '4', '5', '3', '5', '2', '4', '3', '1', '1', '6', '8', '8', '9', '0', '2', '0', '5', '8', '3', '3', '0', '1', '7', '6', '7', '8', '1', '2', '7', '2', '8', '8', '2', '9', '6', '0', '6', '2', '4', '6', '9', '1', '4', '8', '0', '0', '/', '2', '8', '1', '8', '1', '7', '7', '5', '9', '5', '3', '4', '0', '7', '8', '5', '3', '0', '3', '8', '3', '8', '1', '3', '1', '2', '7', '5', '7', '6', '6', '6', '4', '0', '7', '0', '9', '2', '9', '7', '8', '7', '7', '6', '4', '2', '5', '6', '7', '7', '5', '1', '2', '4', '9', '9', '4', '8', '9', '8', '8', '6', '2', '2', '1'])
noncomputable def fragment0136659Acc00700 : List (String × SourceJson) := (fragment0136659Field006Key00, fragment0136659Field006Value00) :: fragment0136659Acc00600
noncomputable def fragment0136659Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '6', '8', '4', '5', '3', '5', '2', '4', '3', '1', '1', '6', '8', '8', '9', '0', '2', '0', '5', '8', '3', '3', '0', '1', '7', '6', '7', '8', '1', '2', '7', '2', '8', '8', '2', '9', '6', '0', '6', '2', '4', '6', '9', '1', '4', '8', '0', '0', '/', '2', '8', '1', '8', '1', '7', '7', '5', '9', '5', '3', '4', '0', '7', '8', '5', '3', '0', '3', '8', '3', '8', '1', '3', '1', '2', '7', '5', '7', '6', '6', '6', '4', '0', '7', '0', '9', '2', '9', '7', '8', '7', '7', '6', '4', '2', '5', '6', '7', '7', '5', '1', '2', '4', '9', '9', '4', '8', '9', '8', '8', '6', '2', '2', '1', '"', ',']

theorem object_fragment0136659_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0136659Field006Chars00 ++ tail)) fragment0136659Acc00600 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0136659Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_006"
  err.flush

noncomputable def fragment0136659Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0136659Field007Value00 : SourceJson := .str (String.ofList ['1', '3', '0', '5', '2', '4', '9', '3', '2', '5', '1', '4', '4', '6', '9', '6', '4', '4', '2', '7', '9', '6', '3', '3', '8', '2', '3', '1', '6', '9', '0', '7', '6', '1', '9', '4', '3', '1', '1', '0', '3', '2', '1', '7', '7', '1', '8', '4', '9', '1', '8', '9', '8', '7', '1', '9', '8', '2', '0', '1', '9', '5', '6', '1', '9', '7', '8', '6', '5', '0', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '3', '9', '2', '8', '7', '2', '9', '2', '5', '8', '4', '7', '4', '7', '3', '8', '3', '6', '2', '1', '3', '1', '2', '2', '2', '9', '8', '0', '0', '1', '1', '5', '4', '8', '7', '3', '4', '6', '7', '4', '7', '8', '0', '6', '7', '5', '6', '5', '1', '6', '0', '5', '1', '8', '6', '8', '3', '3', '9', '6', '7', '9', '2', '8', '2', '3', '5', '0', '5', '4', '0', '7', '3', '3', '1', '9', '8', '3', '3', '7', '3', '3', '7', '9', '1', '1', '6', '8', '7', '0', '2', '8', '0', '2', '2', '4', '5', '1', '8', '9', '0', '4', '3'])
noncomputable def fragment0136659Acc00800 : List (String × SourceJson) := (fragment0136659Field007Key00, fragment0136659Field007Value00) :: fragment0136659Acc00700
noncomputable def fragment0136659Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '0', '5', '2', '4', '9', '3', '2', '5', '1', '4', '4', '6', '9', '6', '4', '4', '2', '7', '9', '6', '3', '3', '8', '2', '3', '1', '6', '9', '0', '7', '6', '1', '9', '4', '3', '1', '1', '0', '3', '2', '1', '7', '7', '1', '8', '4', '9', '1', '8', '9', '8', '7', '1', '9', '8', '2', '0', '1', '9', '5', '6', '1', '9', '7', '8', '6', '5', '0', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '7', '3', '9', '2', '8', '7', '2', '9', '2', '5', '8', '4', '7', '4', '7', '3', '8', '3', '6', '2', '1', '3', '1', '2', '2', '2', '9', '8', '0', '0', '1', '1', '5', '4', '8', '7', '3', '4', '6', '7', '4', '7', '8', '0', '6', '7', '5', '6', '5', '1', '6', '0', '5', '1', '8', '6', '8', '3', '3', '9', '6', '7', '9', '2', '8', '2', '3', '5', '0', '5', '4', '0', '7', '3', '3', '1', '9', '8', '3', '3', '7', '3', '3', '7', '9', '1', '1', '6', '8', '7', '0', '2', '8', '0', '2', '2', '4', '5', '1', '8', '9', '0', '4', '3', '"', ',']

theorem object_fragment0136659_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0136659Field007Chars00 ++ tail)) fragment0136659Acc00700 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0136659Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_007"
  err.flush

noncomputable def fragment0136659Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0136659Field008Value00 : SourceJson := .str (String.ofList ['1', '3', '1', '6', '9', '7', '5', '6', '2', '3', '3', '9', '2', '4'])
noncomputable def fragment0136659Acc00900 : List (String × SourceJson) := (fragment0136659Field008Key00, fragment0136659Field008Value00) :: fragment0136659Acc00800
noncomputable def fragment0136659Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '1', '6', '9', '7', '5', '6', '2', '3', '3', '9', '2', '4', '"', ',']

theorem object_fragment0136659_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0136659Field008Chars00 ++ tail)) fragment0136659Acc00800 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0136659Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_008"
  err.flush

noncomputable def fragment0136659Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0136659Field009Value00 : SourceJson := .str (String.ofList ['5', '9', '4', '5', '6', '8', '2', '8', '1', '4', '7', '4', '1', '7'])
noncomputable def fragment0136659Acc01000 : List (String × SourceJson) := (fragment0136659Field009Key00, fragment0136659Field009Value00) :: fragment0136659Acc00900
noncomputable def fragment0136659Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '4', '5', '6', '8', '2', '8', '1', '4', '7', '4', '1', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0136659_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0136659Field009Chars00 ++ tail)) fragment0136659Acc00900 =
      .ok (.obj (fragment0136659Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0136659_object_field_009"
  err.flush

noncomputable def fragment0136659Chars : List Char := '{' :: (fragment0136659Field000Chars00 ++ fragment0136659Field001Chars00 ++ fragment0136659Field002Chars00 ++ fragment0136659Field003Chars00 ++ fragment0136659Field004Chars00 ++ fragment0136659Field005Chars00 ++ fragment0136659Field006Chars00 ++ fragment0136659Field007Chars00 ++ fragment0136659Field008Chars00 ++ fragment0136659Field009Chars00)
noncomputable def fragment0136659Value : SourceJson := .obj (fragment0136659Acc01000.reverse)

theorem value_fragment0136659 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 207) (fragment0136659Chars ++ tail) =
      .ok (fragment0136659Value, tail) := by
  have hinput : fragment0136659Chars ++ tail = '{' :: (fragment0136659Field000Chars00 ++ (fragment0136659Field001Chars00 ++ (fragment0136659Field002Chars00 ++ (fragment0136659Field003Chars00 ++ (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0136659Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 207) (fragment0136659Chars ++ tail) =
        SourceJson.value (fuel + 207) ('{' :: (fragment0136659Field000Chars00 ++ (fragment0136659Field001Chars00 ++ (fragment0136659Field002Chars00 ++ (fragment0136659Field003Chars00 ++ (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 207)) hinput
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0136659Field000Chars00 ++ (fragment0136659Field001Chars00 ++ (fragment0136659Field002Chars00 ++ (fragment0136659Field003Chars00 ++ (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))))))))))) fragment0136659Acc00000 := by rfl
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0136659Field001Chars00 ++ (fragment0136659Field002Chars00 ++ (fragment0136659Field003Chars00 ++ (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail))))))))))) fragment0136659Acc00100 := object_fragment0136659_field_000 fuel (fragment0136659Field001Chars00 ++ (fragment0136659Field002Chars00 ++ (fragment0136659Field003Chars00 ++ (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0136659Field002Chars00 ++ (fragment0136659Field003Chars00 ++ (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))))))))) fragment0136659Acc00200 := object_fragment0136659_field_001 fuel (fragment0136659Field002Chars00 ++ (fragment0136659Field003Chars00 ++ (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0136659Field003Chars00 ++ (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail))))))))) fragment0136659Acc00300 := object_fragment0136659_field_002 fuel (fragment0136659Field003Chars00 ++ (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))))))) fragment0136659Acc00400 := object_fragment0136659_field_003 fuel (fragment0136659Field004Chars00 ++ (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail))))))) fragment0136659Acc00500 := object_fragment0136659_field_004 fuel (fragment0136659Field005Chars00 ++ (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))))) fragment0136659Acc00600 := object_fragment0136659_field_005 fuel (fragment0136659Field006Chars00 ++ (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail))))) fragment0136659Acc00700 := object_fragment0136659_field_006 fuel (fragment0136659Field007Chars00 ++ (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))) fragment0136659Acc00800 := object_fragment0136659_field_007 fuel (fragment0136659Field008Chars00 ++ (fragment0136659Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0136659Field009Chars00 ++ (tail))) fragment0136659Acc00900 := object_fragment0136659_field_008 fuel (fragment0136659Field009Chars00 ++ (tail))
    _ = .ok (fragment0136659Value, tail) := object_fragment0136659_field_009 fuel (tail)

noncomputable def fragment0138209Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0138209Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0138209Field000Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0138209Acc00100 : List (String × SourceJson) := (fragment0138209Field000Key00, fragment0138209Field000Value00) :: fragment0138209Acc00000
noncomputable def fragment0138209Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '7', ',']

theorem object_fragment0138209_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 454) (SourceJson.white (fragment0138209Field000Chars00 ++ tail)) fragment0138209Acc00000 =
      SourceJson.object (fuel + 453) (SourceJson.white tail) fragment0138209Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_000"
  err.flush

noncomputable def fragment0138209Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0138209Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0138209Acc00200 : List (String × SourceJson) := (fragment0138209Field001Key00, fragment0138209Field001Value00) :: fragment0138209Acc00100
noncomputable def fragment0138209Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0138209_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 453) (SourceJson.white (fragment0138209Field001Chars00 ++ tail)) fragment0138209Acc00100 =
      SourceJson.object (fuel + 452) (SourceJson.white tail) fragment0138209Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_001"
  err.flush

noncomputable def fragment0138209Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0138209Field002Value00 : SourceJson := .str (String.ofList ['5', '5', '9', '1', '4', '9', '1', '8', '4', '5', '1', '1', '5', '2', '3', '3', '3', '1', '8', '5', '1', '3', '7', '8', '8', '7', '5', '7', '1', '6', '2', '0', '5', '0', '1', '7', '3', '4', '9', '7', '6', '3', '9', '1', '6', '7', '/', '9', '3', '7', '8', '9', '7', '2', '6', '2', '8', '0', '6', '5', '9', '7', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0138209Acc00300 : List (String × SourceJson) := (fragment0138209Field002Key00, fragment0138209Field002Value00) :: fragment0138209Acc00200
noncomputable def fragment0138209Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '5', '9', '1', '4', '9', '1', '8', '4', '5', '1', '1', '5', '2', '3', '3', '3', '1', '8', '5', '1', '3', '7', '8', '8', '7', '5', '7', '1', '6', '2', '0', '5', '0', '1', '7', '3', '4', '9', '7', '6', '3', '9', '1', '6', '7', '/', '9', '3', '7', '8', '9', '7', '2', '6', '2', '8', '0', '6', '5', '9', '7', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0138209_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 452) (SourceJson.white (fragment0138209Field002Chars00 ++ tail)) fragment0138209Acc00200 =
      SourceJson.object (fuel + 451) (SourceJson.white tail) fragment0138209Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_002"
  err.flush

noncomputable def fragment0138209Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0138209Field003Value00 : SourceJson := .str (String.ofList ['1', '5', '4', '4', '2', '3', '4', '4', '5', '9', '/', '5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0'])
noncomputable def fragment0138209Acc00400 : List (String × SourceJson) := (fragment0138209Field003Key00, fragment0138209Field003Value00) :: fragment0138209Acc00300
noncomputable def fragment0138209Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '5', '4', '4', '2', '3', '4', '4', '5', '9', '/', '5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0138209_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 451) (SourceJson.white (fragment0138209Field003Chars00 ++ tail)) fragment0138209Acc00300 =
      SourceJson.object (fuel + 450) (SourceJson.white tail) fragment0138209Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_003"
  err.flush

noncomputable def fragment0138209Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0138209Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0138209Acc00500 : List (String × SourceJson) := (fragment0138209Field004Key00, fragment0138209Field004Value00) :: fragment0138209Acc00400
noncomputable def fragment0138209Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0138209_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 450) (SourceJson.white (fragment0138209Field004Chars00 ++ tail)) fragment0138209Acc00400 =
      SourceJson.object (fuel + 449) (SourceJson.white tail) fragment0138209Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_004"
  err.flush

noncomputable def fragment0138209Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0138209Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '5', '4', '4', '0', '9', '4', '8', '6', '4', '8', '2', '4', '6', '8', '5', '6', '1', '3', '7', '3', '4', '6', '8', '9', '/', '1', '7', '2', '6', '5', '4', '4', '4', '3', '1', '9', '9', '3', '1', '6', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '6', '0', '0', '2', '7', '8', '3', '7', '0', '5', '7', '1', '0', '1', '3', '1', '1', '1', '0', '3', '1', '/', '3', '0', '8', '3', '1', '1', '5', '0', '5', '7', '1', '3', '0', '6', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '5', '7', '3', '1', '5', '3', '3', '4', '4', '7', '4', '1', '6', '4', '8', '9', '8', '0', '6', '7', '6', '9', '/', '2', '1', '5', '8', '1', '8', '0', '5', '3', '9', '9', '9', '1', '4', '5', '2', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '9', '3', '3', '2', '3', '5', '4', '6', '2', '3', '5', '3', '9', '6', '9', '2', '6', '5', '7', '1', '3', '/', '1', '7', '2', '6', '5', '4', '4', '4', '3', '1', '9', '9', '3', '1', '6', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '0', '5', '9', '9', '5', '3', '2', '4', '3', '2', '2', '0', '8', '5', '2', '7', '4', '3', '1', '1', '6', '1', '/', '2', '8', '7', '7', '5', '7', '4', '0', '5', '3', '3', '2', '1', '9', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '3', '1', '8', '6', '7', '4', '0', '1', '8', '1', '5', '7', '8', '7', '0', '2', '9', '8', '8', '6', '7', '/', '7', '8', '4', '7', '9', '2', '9', '2', '3', '6', '3', '3', '2', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '1', '7', '8', '2', '5', '5', '6', '8', '1', '5', '3', '8', '1', '8', '7', '9', '1', '5', '9', '6', '9', '/', '3', '1', '3', '9', '1', '7', '1', '6', '9', '4', '5', '3', '3', '0', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '7', '7', '3', '8', '2', '8', '6', '6', '4', '9', '4', '2', '7', '1', '2', '5', '6', '6', '4', '9', '/', '5', '1', '4', '6', '1', '8', '3', '1', '0', '5', '7', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '0', '2', '9', '8', '1', '3', '4', '7', '9', '8', '7', '5', '4', '7', '5', '1', '2', '3', '0', '4', '7', '/', '1', '5', '6', '9', '5', '8', '5', '8', '4', '7', '2', '6', '6', '5', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '8', '5', '6', '6', '5', '3', '7', '7', '3', '6', '9', '2', '1', '8', '2', '1', '4', '3', '9', '9', '/', '2', '0', '5', '5', '4', '1', '0', '0', '3', '8', '0', '8', '7', '0', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0138209Acc00600 : List (String × SourceJson) := (fragment0138209Field005Key00, fragment0138209Field005Value00) :: fragment0138209Acc00500
noncomputable def fragment0138209Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '4', '0', '9', '4', '8', '6', '4', '8', '2', '4', '6', '8', '5', '6', '1', '3', '7', '3', '4', '6', '8', '9', '/', '1', '7', '2', '6', '5', '4', '4', '4', '3', '1', '9', '9', '3', '1', '6', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '0', '0', '2', '7', '8', '3', '7', '0', '5', '7', '1', '0', '1', '3', '1', '1', '1', '0', '3', '1', '/', '3', '0', '8', '3', '1', '1', '5', '0', '5', '7', '1', '3', '0', '6', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '5', '7', '3', '1', '5', '3', '3', '4', '4', '7', '4', '1', '6', '4', '8', '9', '8', '0', '6', '7', '6', '9', '/', '2', '1', '5', '8', '1', '8', '0', '5', '3', '9', '9', '9', '1', '4', '5', '2', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '9', '3', '3', '2', '3', '5', '4', '6', '2', '3', '5', '3', '9', '6', '9', '2', '6', '5', '7', '1', '3', '/', '1', '7', '2', '6', '5', '4', '4', '4', '3', '1', '9', '9', '3', '1', '6', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '0', '5', '9', '9', '5', '3', '2', '4', '3', '2', '2', '0', '8', '5', '2', '7', '4', '3', '1', '1', '6', '1', '/', '2', '8', '7', '7', '5', '7', '4', '0', '5', '3', '3', '2', '1', '9', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '3', '1', '8', '6', '7', '4', '0', '1', '8', '1', '5', '7', '8', '7', '0', '2', '9', '8', '8', '6', '7', '/', '7', '8', '4', '7', '9', '2', '9', '2', '3', '6', '3', '3', '2', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '1', '7', '8', '2', '5', '5', '6', '8', '1', '5', '3', '8', '1', '8', '7', '9', '1', '5', '9', '6', '9', '/', '3', '1', '3', '9', '1', '7', '1', '6', '9', '4', '5', '3', '3', '0', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '7', '3', '8', '2', '8', '6', '6', '4', '9', '4', '2', '7', '1', '2', '5', '6', '6', '4', '9', '/', '5', '1', '4', '6', '1', '8', '3', '1', '0', '5', '7', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '0', '2', '9', '8', '1', '3', '4', '7', '9', '8', '7', '5', '4', '7', '5', '1', '2', '3', '0', '4', '7', '/', '1', '5', '6', '9', '5', '8', '5', '8', '4', '7', '2', '6', '6', '5', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '8', '5', '6', '6', '5', '3', '7', '7', '3', '6', '9', '2', '1', '8', '2', '1', '4', '3', '9', '9', '/', '2', '0', '5', '5', '4', '1', '0', '0', '3', '8', '0', '8', '7', '0', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0138209_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 449) (SourceJson.white (fragment0138209Field005Chars00 ++ tail)) fragment0138209Acc00500 =
      SourceJson.object (fuel + 448) (SourceJson.white tail) fragment0138209Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_005"
  err.flush

noncomputable def fragment0138209Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0138209Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '2', '8', '3', '9', '6', '0', '5', '9', '1', '4', '5', '2', '9', '7', '5', '5', '6', '3', '4', '9', '8', '3', '3', '1', '1', '7', '7', '6', '2', '5', '2', '6', '2', '9', '6', '1', '5', '4', '1', '5', '1', '2', '2', '4', '1', '2', '7', '6', '0', '8', '5', '6', '2', '0', '0', '0', '0', '0', '0', '/', '4', '6', '8', '5', '1', '6', '9', '5', '6', '8', '1', '0', '7', '3', '6', '6', '9', '9', '0', '1', '2', '3', '3', '0', '9', '6', '7', '0', '5', '2', '4', '4', '5', '1', '4', '1', '6', '4', '0', '0', '7', '7', '7', '4', '4', '7', '7', '0', '0', '3', '7', '9', '8', '8', '8', '2', '4', '1', '4', '4', '0', '5', '2', '5', '8', '7', '8', '4', '6', '5', '8', '1', '9', '7'])
noncomputable def fragment0138209Acc00700 : List (String × SourceJson) := (fragment0138209Field006Key00, fragment0138209Field006Value00) :: fragment0138209Acc00600
noncomputable def fragment0138209Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '2', '8', '3', '9', '6', '0', '5', '9', '1', '4', '5', '2', '9', '7', '5', '5', '6', '3', '4', '9', '8', '3', '3', '1', '1', '7', '7', '6', '2', '5', '2', '6', '2', '9', '6', '1', '5', '4', '1', '5', '1', '2', '2', '4', '1', '2', '7', '6', '0', '8', '5', '6', '2', '0', '0', '0', '0', '0', '0', '/', '4', '6', '8', '5', '1', '6', '9', '5', '6', '8', '1', '0', '7', '3', '6', '6', '9', '9', '0', '1', '2', '3', '3', '0', '9', '6', '7', '0', '5', '2', '4', '4', '5', '1', '4', '1', '6', '4', '0', '0', '7', '7', '7', '4', '4', '7', '7', '0', '0', '3', '7', '9', '8', '8', '8', '2', '4', '1', '4', '4', '0', '5', '2', '5', '8', '7', '8', '4', '6', '5', '8', '1', '9', '7', '"', ',']

theorem object_fragment0138209_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 448) (SourceJson.white (fragment0138209Field006Chars00 ++ tail)) fragment0138209Acc00600 =
      SourceJson.object (fuel + 447) (SourceJson.white tail) fragment0138209Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_006"
  err.flush

noncomputable def fragment0138209Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0138209Field007Value00 : SourceJson := .str (String.ofList ['1', '2', '6', '8', '1', '2', '1', '9', '7', '6', '4', '4', '4', '4', '8', '5', '8', '1', '6', '8', '4', '3', '5', '9', '3', '6', '2', '8', '8', '4', '0', '5', '4', '2', '5', '6', '2', '0', '9', '3', '7', '3', '1', '6', '0', '7', '5', '0', '3', '7', '7', '9', '1', '1', '3', '0', '0', '6', '6', '6', '9', '6', '2', '8', '1', '4', '0', '0', '1', '4', '3', '9', '2', '3', '3', '5', '2', '8', '8', '7', '3', '4', '8', '9', '2', '6', '4', '5', '6', '2', '3', '7', '1', '8', '5', '8', '1', '0', '2', '1', '0', '2', '4', '7', '7', '1', '5', '8', '5', '3', '7', '0', '6', '2', '4', '2', '2', '4', '7', '8', '6', '8', '2', '9', '9', '1', '4', '7', '3', '3', '0', '6', '0', '8', '3', '9', '9', '7', '9', '3', '9', '1', '5', '6', '8', '3', '6', '7', '5', '4', '4', '4', '6', '1', '5', '9', '6', '9', '4', '2', '1', '1', '1', '5', '8', '5', '3', '8', '8', '2', '7', '3', '9', '6', '6', '6', '8', '5', '4', '3', '0', '2', '4', '6', '2', '8', '4', '4', '4', '8', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '0', '1', '3', '7', '6', '5', '2', '4', '2', '3', '9', '7', '0', '4', '6', '9', '7', '3', '6', '2', '1', '0', '5', '2', '5', '9', '1', '6', '2', '3', '7', '5', '9', '2', '7', '3', '2', '5', '8', '7', '1', '8', '8', '6', '3', '5', '0', '4', '5', '0', '3', '6', '4', '8', '5', '9', '9', '8', '9', '5', '3', '7', '8', '9', '5', '2', '2', '5', '7', '8', '4', '7', '2', '2', '3', '9', '7', '8', '3', '0', '1', '4', '6', '4', '4', '5', '1', '7', '3', '7', '4', '8', '3', '8', '0', '4', '4', '0', '0', '3', '2', '0', '3', '5', '1', '9', '9', '0', '8', '4', '1', '7', '2', '7', '6', '9', '0', '9', '7', '3', '9', '0', '0', '6', '8', '8', '9', '6', '5', '7', '9', '8', '9', '4', '6', '8', '8', '0', '2', '5', '4', '2', '1', '4', '6', '3', '7', '4', '0', '6', '5', '3', '2', '0', '4', '2', '0', '2', '1', '1', '0', '4', '2', '0', '6', '7', '0', '8', '3', '0', '9', '0', '1', '9', '5', '6', '0', '1', '7', '4', '5', '9', '6', '2', '5', '6', '1', '1', '9', '8', '0', '9', '2', '1', '0', '3', '7', '1', '1', '2', '7', '3', '7', '0', '6', '5', '9', '0', '9', '7', '6', '6', '6', '2', '0', '4', '8', '8', '8', '2', '7', '4', '8', '9', '6', '1'])
noncomputable def fragment0138209Acc00800 : List (String × SourceJson) := (fragment0138209Field007Key00, fragment0138209Field007Value00) :: fragment0138209Acc00700
noncomputable def fragment0138209Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '6', '8', '1', '2', '1', '9', '7', '6', '4', '4', '4', '4', '8', '5', '8', '1', '6', '8', '4', '3', '5', '9', '3', '6', '2', '8', '8', '4', '0', '5', '4', '2', '5', '6', '2', '0', '9', '3', '7', '3', '1', '6', '0', '7', '5', '0', '3', '7', '7', '9', '1', '1', '3', '0', '0', '6', '6', '6', '9', '6', '2', '8', '1', '4', '0', '0', '1', '4', '3', '9', '2', '3', '3', '5', '2', '8', '8', '7', '3', '4', '8', '9', '2', '6', '4', '5', '6', '2', '3', '7', '1', '8', '5', '8', '1', '0', '2', '1', '0', '2', '4', '7', '7', '1', '5', '8', '5', '3', '7', '0', '6', '2', '4', '2', '2', '4', '7', '8', '6', '8', '2', '9', '9', '1', '4', '7', '3', '3', '0', '6', '0', '8', '3', '9', '9', '7', '9', '3', '9', '1', '5', '6', '8', '3', '6', '7', '5', '4', '4', '4', '6', '1', '5', '9', '6', '9', '4', '2', '1', '1', '1', '5', '8', '5', '3', '8', '8', '2', '7', '3', '9', '6', '6', '6', '8', '5', '4', '3', '0', '2', '4', '6', '2', '8', '4', '4', '4', '8', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '0', '1', '3', '7', '6', '5', '2', '4', '2', '3', '9', '7', '0', '4', '6', '9', '7', '3', '6', '2', '1', '0', '5', '2', '5', '9', '1', '6', '2', '3', '7', '5', '9', '2', '7', '3', '2', '5', '8', '7', '1', '8', '8', '6', '3', '5', '0', '4', '5', '0', '3', '6', '4', '8', '5', '9', '9', '8', '9', '5', '3', '7', '8', '9', '5', '2', '2', '5', '7', '8', '4', '7', '2', '2', '3', '9', '7', '8', '3', '0', '1', '4', '6', '4', '4', '5', '1', '7', '3', '7', '4', '8', '3', '8', '0', '4', '4', '0', '0', '3', '2', '0', '3', '5', '1', '9', '9', '0', '8', '4', '1', '7', '2', '7', '6', '9', '0', '9', '7', '3', '9', '0', '0', '6', '8', '8', '9', '6', '5', '7', '9', '8', '9', '4', '6', '8', '8', '0', '2', '5', '4', '2', '1', '4', '6', '3', '7', '4', '0', '6', '5', '3', '2', '0', '4', '2', '0', '2', '1', '1', '0', '4', '2', '0', '6', '7', '0', '8', '3', '0', '9', '0', '1', '9', '5', '6', '0', '1', '7', '4', '5', '9', '6', '2', '5', '6', '1', '1', '9', '8', '0', '9', '2', '1', '0', '3', '7', '1', '1', '2', '7', '3', '7', '0', '6', '5', '9', '0', '9', '7', '6', '6', '6', '2', '0', '4', '8', '8', '8', '2', '7', '4', '8', '9', '6', '1', '"', ',']

theorem object_fragment0138209_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 447) (SourceJson.white (fragment0138209Field007Chars00 ++ tail)) fragment0138209Acc00700 =
      SourceJson.object (fuel + 446) (SourceJson.white tail) fragment0138209Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_007"
  err.flush

noncomputable def fragment0138209Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0138209Field008Value00 : SourceJson := .str (String.ofList ['2', '2', '4', '6', '3', '7', '2', '8', '8', '6', '3', '4', '5', '4', '4', '6'])
noncomputable def fragment0138209Acc00900 : List (String × SourceJson) := (fragment0138209Field008Key00, fragment0138209Field008Value00) :: fragment0138209Acc00800
noncomputable def fragment0138209Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '4', '6', '3', '7', '2', '8', '8', '6', '3', '4', '5', '4', '4', '6', '"', ',']

theorem object_fragment0138209_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 446) (SourceJson.white (fragment0138209Field008Chars00 ++ tail)) fragment0138209Acc00800 =
      SourceJson.object (fuel + 445) (SourceJson.white tail) fragment0138209Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_008"
  err.flush

noncomputable def fragment0138209Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0138209Field009Value00 : SourceJson := .str (String.ofList ['6', '6', '9', '1', '9', '2', '3', '8', '7', '2', '2', '2', '9', '9', '9', '8'])
noncomputable def fragment0138209Acc01000 : List (String × SourceJson) := (fragment0138209Field009Key00, fragment0138209Field009Value00) :: fragment0138209Acc00900
noncomputable def fragment0138209Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '6', '9', '1', '9', '2', '3', '8', '7', '2', '2', '2', '9', '9', '9', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0138209_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 445) (SourceJson.white (fragment0138209Field009Chars00 ++ tail)) fragment0138209Acc00900 =
      .ok (.obj (fragment0138209Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0138209_object_field_009"
  err.flush

noncomputable def fragment0138209Chars : List Char := '{' :: (fragment0138209Field000Chars00 ++ fragment0138209Field001Chars00 ++ fragment0138209Field002Chars00 ++ fragment0138209Field003Chars00 ++ fragment0138209Field004Chars00 ++ fragment0138209Field005Chars00 ++ fragment0138209Field006Chars00 ++ fragment0138209Field007Chars00 ++ fragment0138209Field008Chars00 ++ fragment0138209Field009Chars00)
noncomputable def fragment0138209Value : SourceJson := .obj (fragment0138209Acc01000.reverse)

theorem value_fragment0138209 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 455) (fragment0138209Chars ++ tail) =
      .ok (fragment0138209Value, tail) := by
  have hinput : fragment0138209Chars ++ tail = '{' :: (fragment0138209Field000Chars00 ++ (fragment0138209Field001Chars00 ++ (fragment0138209Field002Chars00 ++ (fragment0138209Field003Chars00 ++ (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0138209Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 455) (fragment0138209Chars ++ tail) =
        SourceJson.value (fuel + 455) ('{' :: (fragment0138209Field000Chars00 ++ (fragment0138209Field001Chars00 ++ (fragment0138209Field002Chars00 ++ (fragment0138209Field003Chars00 ++ (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 455)) hinput
    _ = SourceJson.object (fuel + 454) (SourceJson.white (fragment0138209Field000Chars00 ++ (fragment0138209Field001Chars00 ++ (fragment0138209Field002Chars00 ++ (fragment0138209Field003Chars00 ++ (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))))))))))) fragment0138209Acc00000 := by rfl
    _ = SourceJson.object (fuel + 453) (SourceJson.white (fragment0138209Field001Chars00 ++ (fragment0138209Field002Chars00 ++ (fragment0138209Field003Chars00 ++ (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail))))))))))) fragment0138209Acc00100 := object_fragment0138209_field_000 fuel (fragment0138209Field001Chars00 ++ (fragment0138209Field002Chars00 ++ (fragment0138209Field003Chars00 ++ (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 452) (SourceJson.white (fragment0138209Field002Chars00 ++ (fragment0138209Field003Chars00 ++ (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))))))))) fragment0138209Acc00200 := object_fragment0138209_field_001 fuel (fragment0138209Field002Chars00 ++ (fragment0138209Field003Chars00 ++ (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 451) (SourceJson.white (fragment0138209Field003Chars00 ++ (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail))))))))) fragment0138209Acc00300 := object_fragment0138209_field_002 fuel (fragment0138209Field003Chars00 ++ (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 450) (SourceJson.white (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))))))) fragment0138209Acc00400 := object_fragment0138209_field_003 fuel (fragment0138209Field004Chars00 ++ (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 449) (SourceJson.white (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail))))))) fragment0138209Acc00500 := object_fragment0138209_field_004 fuel (fragment0138209Field005Chars00 ++ (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 448) (SourceJson.white (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))))) fragment0138209Acc00600 := object_fragment0138209_field_005 fuel (fragment0138209Field006Chars00 ++ (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 447) (SourceJson.white (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail))))) fragment0138209Acc00700 := object_fragment0138209_field_006 fuel (fragment0138209Field007Chars00 ++ (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 446) (SourceJson.white (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))) fragment0138209Acc00800 := object_fragment0138209_field_007 fuel (fragment0138209Field008Chars00 ++ (fragment0138209Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 445) (SourceJson.white (fragment0138209Field009Chars00 ++ (tail))) fragment0138209Acc00900 := object_fragment0138209_field_008 fuel (fragment0138209Field009Chars00 ++ (tail))
    _ = .ok (fragment0138209Value, tail) := object_fragment0138209_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_before_reader"
  err.flush

noncomputable def chunk0000LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0000SuffixChars00 : List Char := [',']
noncomputable def chunk0000Chars00 : List Char := chunk0000LeadChars00 ++ fragment0124037Chars ++ chunk0000SuffixChars00
noncomputable def chunk0000Push00 (acc : List SourceJson) : List SourceJson := fragment0124037Value :: acc

noncomputable def chunk0000AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0000_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 657)
      (SourceJson.white (chunk0000LeadChars00 ++ (fragment0124037Chars ++ rest))) acc =
      (SourceJson.value (fuel + 656) (fragment0124037Chars ++ rest)).bind
        (chunk0000AfterValue00 (fuel + 656) acc) := by rfl

theorem array_chunk0000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 657) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 656) (SourceJson.white tail) (chunk0000Push00 acc) := by
  have hinput : chunk0000Chars00 ++ tail = chunk0000LeadChars00 ++ (fragment0124037Chars ++ (chunk0000SuffixChars00 ++ tail)) := by
    simp only [chunk0000Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 657) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 657)
          (SourceJson.white (chunk0000LeadChars00 ++ (fragment0124037Chars ++ (chunk0000SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 657) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 656) (fragment0124037Chars ++ (chunk0000SuffixChars00 ++ tail))).bind
        (chunk0000AfterValue00 (fuel + 656) acc) := array_chunk0000_head fuel (chunk0000SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0124037Value, chunk0000SuffixChars00 ++ tail)).bind
        (chunk0000AfterValue00 (fuel + 656) acc) :=
      congrArg (fun result => result.bind (chunk0000AfterValue00 (fuel + 656) acc))
        (value_fragment0124037 (fuel + 90) (chunk0000SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 656) (SourceJson.white tail) (chunk0000Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_before_reader"
  err.flush

noncomputable def chunk0001LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0001SuffixChars00 : List Char := [',']
noncomputable def chunk0001Chars00 : List Char := chunk0001LeadChars00 ++ fragment0126332Chars ++ chunk0001SuffixChars00
noncomputable def chunk0001Push00 (acc : List SourceJson) : List SourceJson := fragment0126332Value :: acc

noncomputable def chunk0001AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0001_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 656)
      (SourceJson.white (chunk0001LeadChars00 ++ (fragment0126332Chars ++ rest))) acc =
      (SourceJson.value (fuel + 655) (fragment0126332Chars ++ rest)).bind
        (chunk0001AfterValue00 (fuel + 655) acc) := by rfl

theorem array_chunk0001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 656) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 655) (SourceJson.white tail) (chunk0001Push00 acc) := by
  have hinput : chunk0001Chars00 ++ tail = chunk0001LeadChars00 ++ (fragment0126332Chars ++ (chunk0001SuffixChars00 ++ tail)) := by
    simp only [chunk0001Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 656) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 656)
          (SourceJson.white (chunk0001LeadChars00 ++ (fragment0126332Chars ++ (chunk0001SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 656) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 655) (fragment0126332Chars ++ (chunk0001SuffixChars00 ++ tail))).bind
        (chunk0001AfterValue00 (fuel + 655) acc) := array_chunk0001_head fuel (chunk0001SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0126332Value, chunk0001SuffixChars00 ++ tail)).bind
        (chunk0001AfterValue00 (fuel + 655) acc) :=
      congrArg (fun result => result.bind (chunk0001AfterValue00 (fuel + 655) acc))
        (value_fragment0126332 (fuel + 156) (chunk0001SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 655) (SourceJson.white tail) (chunk0001Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_before_reader"
  err.flush

noncomputable def chunk0002LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0002SuffixChars00 : List Char := [',']
noncomputable def chunk0002Chars00 : List Char := chunk0002LeadChars00 ++ fragment0128490Chars ++ chunk0002SuffixChars00
noncomputable def chunk0002Push00 (acc : List SourceJson) : List SourceJson := fragment0128490Value :: acc

noncomputable def chunk0002AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0002_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 655)
      (SourceJson.white (chunk0002LeadChars00 ++ (fragment0128490Chars ++ rest))) acc =
      (SourceJson.value (fuel + 654) (fragment0128490Chars ++ rest)).bind
        (chunk0002AfterValue00 (fuel + 654) acc) := by rfl

theorem array_chunk0002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 655) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 654) (SourceJson.white tail) (chunk0002Push00 acc) := by
  have hinput : chunk0002Chars00 ++ tail = chunk0002LeadChars00 ++ (fragment0128490Chars ++ (chunk0002SuffixChars00 ++ tail)) := by
    simp only [chunk0002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 655) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 655)
          (SourceJson.white (chunk0002LeadChars00 ++ (fragment0128490Chars ++ (chunk0002SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 655) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 654) (fragment0128490Chars ++ (chunk0002SuffixChars00 ++ tail))).bind
        (chunk0002AfterValue00 (fuel + 654) acc) := array_chunk0002_head fuel (chunk0002SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0128490Value, chunk0002SuffixChars00 ++ tail)).bind
        (chunk0002AfterValue00 (fuel + 654) acc) :=
      congrArg (fun result => result.bind (chunk0002AfterValue00 (fuel + 654) acc))
        (value_fragment0128490 (fuel + 164) (chunk0002SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 654) (SourceJson.white tail) (chunk0002Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_before_reader"
  err.flush

noncomputable def chunk0003LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0003SuffixChars00 : List Char := [',']
noncomputable def chunk0003Chars00 : List Char := chunk0003LeadChars00 ++ fragment0130641Chars ++ chunk0003SuffixChars00
noncomputable def chunk0003Push00 (acc : List SourceJson) : List SourceJson := fragment0130641Value :: acc

noncomputable def chunk0003AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0003_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 654)
      (SourceJson.white (chunk0003LeadChars00 ++ (fragment0130641Chars ++ rest))) acc =
      (SourceJson.value (fuel + 653) (fragment0130641Chars ++ rest)).bind
        (chunk0003AfterValue00 (fuel + 653) acc) := by rfl

theorem array_chunk0003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 654) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 653) (SourceJson.white tail) (chunk0003Push00 acc) := by
  have hinput : chunk0003Chars00 ++ tail = chunk0003LeadChars00 ++ (fragment0130641Chars ++ (chunk0003SuffixChars00 ++ tail)) := by
    simp only [chunk0003Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 654) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 654)
          (SourceJson.white (chunk0003LeadChars00 ++ (fragment0130641Chars ++ (chunk0003SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 654) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 653) (fragment0130641Chars ++ (chunk0003SuffixChars00 ++ tail))).bind
        (chunk0003AfterValue00 (fuel + 653) acc) := array_chunk0003_head fuel (chunk0003SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0130641Value, chunk0003SuffixChars00 ++ tail)).bind
        (chunk0003AfterValue00 (fuel + 653) acc) :=
      congrArg (fun result => result.bind (chunk0003AfterValue00 (fuel + 653) acc))
        (value_fragment0130641 (fuel + 164) (chunk0003SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 653) (SourceJson.white tail) (chunk0003Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_before_reader"
  err.flush

noncomputable def chunk0004LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0004SuffixChars00 : List Char := [',']
noncomputable def chunk0004Chars00 : List Char := chunk0004LeadChars00 ++ fragment0132769Chars ++ chunk0004SuffixChars00
noncomputable def chunk0004Push00 (acc : List SourceJson) : List SourceJson := fragment0132769Value :: acc

noncomputable def chunk0004AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0004_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 653)
      (SourceJson.white (chunk0004LeadChars00 ++ (fragment0132769Chars ++ rest))) acc =
      (SourceJson.value (fuel + 652) (fragment0132769Chars ++ rest)).bind
        (chunk0004AfterValue00 (fuel + 652) acc) := by rfl

theorem array_chunk0004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 653) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 652) (SourceJson.white tail) (chunk0004Push00 acc) := by
  have hinput : chunk0004Chars00 ++ tail = chunk0004LeadChars00 ++ (fragment0132769Chars ++ (chunk0004SuffixChars00 ++ tail)) := by
    simp only [chunk0004Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 653) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 653)
          (SourceJson.white (chunk0004LeadChars00 ++ (fragment0132769Chars ++ (chunk0004SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 653) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 652) (fragment0132769Chars ++ (chunk0004SuffixChars00 ++ tail))).bind
        (chunk0004AfterValue00 (fuel + 652) acc) := array_chunk0004_head fuel (chunk0004SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0132769Value, chunk0004SuffixChars00 ++ tail)).bind
        (chunk0004AfterValue00 (fuel + 652) acc) :=
      congrArg (fun result => result.bind (chunk0004AfterValue00 (fuel + 652) acc))
        (value_fragment0132769 (fuel + 215) (chunk0004SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 652) (SourceJson.white tail) (chunk0004Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_before_reader"
  err.flush

noncomputable def chunk0005LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0005SuffixChars00 : List Char := [',']
noncomputable def chunk0005Chars00 : List Char := chunk0005LeadChars00 ++ fragment0134791Chars ++ chunk0005SuffixChars00
noncomputable def chunk0005Push00 (acc : List SourceJson) : List SourceJson := fragment0134791Value :: acc

noncomputable def chunk0005AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0005_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 652)
      (SourceJson.white (chunk0005LeadChars00 ++ (fragment0134791Chars ++ rest))) acc =
      (SourceJson.value (fuel + 651) (fragment0134791Chars ++ rest)).bind
        (chunk0005AfterValue00 (fuel + 651) acc) := by rfl

theorem array_chunk0005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 652) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 651) (SourceJson.white tail) (chunk0005Push00 acc) := by
  have hinput : chunk0005Chars00 ++ tail = chunk0005LeadChars00 ++ (fragment0134791Chars ++ (chunk0005SuffixChars00 ++ tail)) := by
    simp only [chunk0005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 652) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 652)
          (SourceJson.white (chunk0005LeadChars00 ++ (fragment0134791Chars ++ (chunk0005SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 652) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 651) (fragment0134791Chars ++ (chunk0005SuffixChars00 ++ tail))).bind
        (chunk0005AfterValue00 (fuel + 651) acc) := array_chunk0005_head fuel (chunk0005SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0134791Value, chunk0005SuffixChars00 ++ tail)).bind
        (chunk0005AfterValue00 (fuel + 651) acc) :=
      congrArg (fun result => result.bind (chunk0005AfterValue00 (fuel + 651) acc))
        (value_fragment0134791 (fuel + 281) (chunk0005SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 651) (SourceJson.white tail) (chunk0005Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_before_reader"
  err.flush

noncomputable def chunk0006LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0006SuffixChars00 : List Char := [',']
noncomputable def chunk0006Chars00 : List Char := chunk0006LeadChars00 ++ fragment0136659Chars ++ chunk0006SuffixChars00
noncomputable def chunk0006Push00 (acc : List SourceJson) : List SourceJson := fragment0136659Value :: acc

noncomputable def chunk0006AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0006_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 651)
      (SourceJson.white (chunk0006LeadChars00 ++ (fragment0136659Chars ++ rest))) acc =
      (SourceJson.value (fuel + 650) (fragment0136659Chars ++ rest)).bind
        (chunk0006AfterValue00 (fuel + 650) acc) := by rfl

theorem array_chunk0006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 651) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 650) (SourceJson.white tail) (chunk0006Push00 acc) := by
  have hinput : chunk0006Chars00 ++ tail = chunk0006LeadChars00 ++ (fragment0136659Chars ++ (chunk0006SuffixChars00 ++ tail)) := by
    simp only [chunk0006Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 651) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 651)
          (SourceJson.white (chunk0006LeadChars00 ++ (fragment0136659Chars ++ (chunk0006SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 651) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 650) (fragment0136659Chars ++ (chunk0006SuffixChars00 ++ tail))).bind
        (chunk0006AfterValue00 (fuel + 650) acc) := array_chunk0006_head fuel (chunk0006SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0136659Value, chunk0006SuffixChars00 ++ tail)).bind
        (chunk0006AfterValue00 (fuel + 650) acc) :=
      congrArg (fun result => result.bind (chunk0006AfterValue00 (fuel + 650) acc))
        (value_fragment0136659 (fuel + 443) (chunk0006SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 650) (SourceJson.white tail) (chunk0006Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_before_reader"
  err.flush

noncomputable def chunk0007LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0007SuffixChars00 : List Char := [',']
noncomputable def chunk0007Chars00 : List Char := chunk0007LeadChars00 ++ fragment0138209Chars ++ chunk0007SuffixChars00
noncomputable def chunk0007Push00 (acc : List SourceJson) : List SourceJson := fragment0138209Value :: acc

noncomputable def chunk0007AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0007_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 650)
      (SourceJson.white (chunk0007LeadChars00 ++ (fragment0138209Chars ++ rest))) acc =
      (SourceJson.value (fuel + 649) (fragment0138209Chars ++ rest)).bind
        (chunk0007AfterValue00 (fuel + 649) acc) := by rfl

theorem array_chunk0007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 650) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 649) (SourceJson.white tail) (chunk0007Push00 acc) := by
  have hinput : chunk0007Chars00 ++ tail = chunk0007LeadChars00 ++ (fragment0138209Chars ++ (chunk0007SuffixChars00 ++ tail)) := by
    simp only [chunk0007Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 650) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 650)
          (SourceJson.white (chunk0007LeadChars00 ++ (fragment0138209Chars ++ (chunk0007SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 650) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 649) (fragment0138209Chars ++ (chunk0007SuffixChars00 ++ tail))).bind
        (chunk0007AfterValue00 (fuel + 649) acc) := array_chunk0007_head fuel (chunk0007SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0138209Value, chunk0007SuffixChars00 ++ tail)).bind
        (chunk0007AfterValue00 (fuel + 649) acc) :=
      congrArg (fun result => result.bind (chunk0007AfterValue00 (fuel + 649) acc))
        (value_fragment0138209 (fuel + 194) (chunk0007SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 649) (SourceJson.white tail) (chunk0007Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0000Chars00 ++ chunk0001Chars00 ++ chunk0002Chars00 ++ chunk0003Chars00 ++ chunk0004Chars00 ++ chunk0005Chars00 ++ chunk0006Chars00 ++ chunk0007Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0007Push00 (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 657) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 649) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 657) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 657) (SourceJson.white (chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 657) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 656) (SourceJson.white (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))))) (chunk0000Push00 (acc)) := array_chunk0000 fuel (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 655) (SourceJson.white (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (chunk0001Push00 (chunk0000Push00 (acc))) := array_chunk0001 fuel (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0000Push00 (acc))
    _ = SourceJson.array (fuel + 654) (SourceJson.white (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))) := array_chunk0002 fuel (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0001Push00 (chunk0000Push00 (acc)))
    _ = SourceJson.array (fuel + 653) (SourceJson.white (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))) := array_chunk0003 fuel (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))
    _ = SourceJson.array (fuel + 652) (SourceJson.white (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))) := array_chunk0004 fuel (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))
    _ = SourceJson.array (fuel + 651) (SourceJson.white (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))) := array_chunk0005 fuel (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))
    _ = SourceJson.array (fuel + 650) (SourceJson.white (chunk0007Chars00 ++ (tail))) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))) := array_chunk0006 fuel (chunk0007Chars00 ++ (tail)) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))
    _ = SourceJson.array (fuel + 649) (SourceJson.white tail) (blockPush acc) := array_chunk0007 fuel (tail) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 124031).take 16242 = blockChars := by rfl

theorem block_original_split : sourceRest 124031 = blockChars ++ sourceRest 140273 := by
  calc
    sourceRest 124031 = (sourceRest 124031).take 16242 ++ (sourceRest 124031).drop 16242 :=
      (List.take_append_drop 16242 (sourceRest 124031)).symm
    _ = blockChars ++ (sourceRest 124031).drop 16242 :=
      congrArg (fun part => part ++ (sourceRest 124031).drop 16242) block_original_prefix
    _ = blockChars ++ sourceRest 140273 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 124031 16242)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 657) (SourceJson.white (sourceRest 124031)) acc =
      SourceJson.array (fuel + 649) (SourceJson.white (sourceRest 140273)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 657) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 140273) acc)

#print axioms object_fragment0124037_field_000
#print axioms object_fragment0124037_field_001
#print axioms object_fragment0124037_field_002
#print axioms object_fragment0124037_field_003
#print axioms object_fragment0124037_field_004
#print axioms object_fragment0124037_field_005
#print axioms object_fragment0124037_field_006
#print axioms object_fragment0124037_field_007
#print axioms object_fragment0124037_field_008
#print axioms object_fragment0124037_field_009
#print axioms value_fragment0124037
#print axioms object_fragment0126332_field_000
#print axioms object_fragment0126332_field_001
#print axioms object_fragment0126332_field_002
#print axioms object_fragment0126332_field_003
#print axioms object_fragment0126332_field_004
#print axioms object_fragment0126332_field_005
#print axioms object_fragment0126332_field_006
#print axioms object_fragment0126332_field_007
#print axioms object_fragment0126332_field_008
#print axioms object_fragment0126332_field_009
#print axioms value_fragment0126332
#print axioms object_fragment0128490_field_000
#print axioms object_fragment0128490_field_001
#print axioms object_fragment0128490_field_002
#print axioms object_fragment0128490_field_003
#print axioms object_fragment0128490_field_004
#print axioms object_fragment0128490_field_005
#print axioms object_fragment0128490_field_006
#print axioms object_fragment0128490_field_007
#print axioms object_fragment0128490_field_008
#print axioms object_fragment0128490_field_009
#print axioms value_fragment0128490
#print axioms object_fragment0130641_field_000
#print axioms object_fragment0130641_field_001
#print axioms object_fragment0130641_field_002
#print axioms object_fragment0130641_field_003
#print axioms object_fragment0130641_field_004
#print axioms object_fragment0130641_field_005
#print axioms object_fragment0130641_field_006
#print axioms object_fragment0130641_field_007
#print axioms object_fragment0130641_field_008
#print axioms object_fragment0130641_field_009
#print axioms value_fragment0130641
#print axioms object_fragment0132769_field_000
#print axioms object_fragment0132769_field_001
#print axioms object_fragment0132769_field_002
#print axioms object_fragment0132769_field_003
#print axioms object_fragment0132769_field_004
#print axioms object_fragment0132769_field_005
#print axioms object_fragment0132769_field_006
#print axioms object_fragment0132769_field_007
#print axioms object_fragment0132769_field_008
#print axioms object_fragment0132769_field_009
#print axioms value_fragment0132769
#print axioms object_fragment0134791_field_000
#print axioms object_fragment0134791_field_001
#print axioms object_fragment0134791_field_002
#print axioms object_fragment0134791_field_003
#print axioms object_fragment0134791_field_004
#print axioms object_fragment0134791_field_005
#print axioms object_fragment0134791_field_006
#print axioms object_fragment0134791_field_007
#print axioms object_fragment0134791_field_008
#print axioms object_fragment0134791_field_009
#print axioms value_fragment0134791
#print axioms object_fragment0136659_field_000
#print axioms object_fragment0136659_field_001
#print axioms object_fragment0136659_field_002
#print axioms object_fragment0136659_field_003
#print axioms object_fragment0136659_field_004
#print axioms object_fragment0136659_field_005
#print axioms object_fragment0136659_field_006
#print axioms object_fragment0136659_field_007
#print axioms object_fragment0136659_field_008
#print axioms object_fragment0136659_field_009
#print axioms value_fragment0136659
#print axioms object_fragment0138209_field_000
#print axioms object_fragment0138209_field_001
#print axioms object_fragment0138209_field_002
#print axioms object_fragment0138209_field_003
#print axioms object_fragment0138209_field_004
#print axioms object_fragment0138209_field_005
#print axioms object_fragment0138209_field_006
#print axioms object_fragment0138209_field_007
#print axioms object_fragment0138209_field_008
#print axioms object_fragment0138209_field_009
#print axioms value_fragment0138209
#print axioms array_chunk0000_head
#print axioms array_chunk0000
#print axioms array_chunk0001_head
#print axioms array_chunk0001
#print axioms array_chunk0002_head
#print axioms array_chunk0002
#print axioms array_chunk0003_head
#print axioms array_chunk0003
#print axioms array_chunk0004_head
#print axioms array_chunk0004
#print axioms array_chunk0005_head
#print axioms array_chunk0005
#print axioms array_chunk0006_head
#print axioms array_chunk0006
#print axioms array_chunk0007_head
#print axioms array_chunk0007
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock000

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
