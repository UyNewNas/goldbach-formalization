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

namespace SimplicesBlock012

noncomputable def fragment0305254Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0305254Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0305254Field000Value00 : SourceJson := .number (String.ofList ['9', '6'])
noncomputable def fragment0305254Acc00100 : List (String × SourceJson) := (fragment0305254Field000Key00, fragment0305254Field000Value00) :: fragment0305254Acc00000
noncomputable def fragment0305254Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '6', ',']

theorem object_fragment0305254_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 525) (SourceJson.white (fragment0305254Field000Chars00 ++ tail)) fragment0305254Acc00000 =
      SourceJson.object (fuel + 524) (SourceJson.white tail) fragment0305254Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_000"
  err.flush

noncomputable def fragment0305254Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0305254Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0305254Acc00200 : List (String × SourceJson) := (fragment0305254Field001Key00, fragment0305254Field001Value00) :: fragment0305254Acc00100
noncomputable def fragment0305254Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0305254_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 524) (SourceJson.white (fragment0305254Field001Chars00 ++ tail)) fragment0305254Acc00100 =
      SourceJson.object (fuel + 523) (SourceJson.white tail) fragment0305254Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_001"
  err.flush

noncomputable def fragment0305254Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0305254Field002Value00 : SourceJson := .str (String.ofList ['3', '2', '7', '0', '2', '5', '4', '1', '8', '5', '9', '0', '5', '8', '1', '5', '4', '3', '5', '7', '7', '1', '7', '6', '7', '9', '5', '6', '9', '9', '2', '2', '6', '7', '1', '6', '8', '6', '4', '8', '6', '3', '/', '3', '4', '9', '3', '1', '9', '8', '2', '2', '2', '1', '4', '5', '3', '7', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0305254Acc00300 : List (String × SourceJson) := (fragment0305254Field002Key00, fragment0305254Field002Value00) :: fragment0305254Acc00200
noncomputable def fragment0305254Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '2', '7', '0', '2', '5', '4', '1', '8', '5', '9', '0', '5', '8', '1', '5', '4', '3', '5', '7', '7', '1', '7', '6', '7', '9', '5', '6', '9', '9', '2', '2', '6', '7', '1', '6', '8', '6', '4', '8', '6', '3', '/', '3', '4', '9', '3', '1', '9', '8', '2', '2', '2', '1', '4', '5', '3', '7', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0305254_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 523) (SourceJson.white (fragment0305254Field002Chars00 ++ tail)) fragment0305254Acc00200 =
      SourceJson.object (fuel + 522) (SourceJson.white tail) fragment0305254Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_002"
  err.flush

noncomputable def fragment0305254Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0305254Field003Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0305254Acc00400 : List (String × SourceJson) := (fragment0305254Field003Key00, fragment0305254Field003Value00) :: fragment0305254Acc00300
noncomputable def fragment0305254Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0305254_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 522) (SourceJson.white (fragment0305254Field003Chars00 ++ tail)) fragment0305254Acc00300 =
      SourceJson.object (fuel + 521) (SourceJson.white tail) fragment0305254Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_003"
  err.flush

noncomputable def fragment0305254Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0305254Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '2', '8', '2', '3', '3', '/', '1', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0305254Acc00500 : List (String × SourceJson) := (fragment0305254Field004Key00, fragment0305254Field004Value00) :: fragment0305254Acc00400
noncomputable def fragment0305254Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '2', '8', '2', '3', '3', '/', '1', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0305254_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 521) (SourceJson.white (fragment0305254Field004Chars00 ++ tail)) fragment0305254Acc00400 =
      SourceJson.object (fuel + 520) (SourceJson.white tail) fragment0305254Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_004"
  err.flush

noncomputable def fragment0305254Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0305254Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '0', '4', '1', '4', '1', '6', '6', '6', '2', '7', '3', '8', '4', '1', '1', '7', '1', '2', '1', '5', '6', '9', '7', '3', '1', '7', '/', '1', '8', '4', '9', '6', '1', '8', '2', '9', '3', '1', '8', '8', '2', '1', '6', '0', '1', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '6', '7', '2', '2', '7', '0', '6', '7', '1', '4', '3', '4', '9', '0', '2', '0', '0', '8', '5', '1', '6', '2', '7', '/', '1', '2', '2', '8', '9', '8', '2', '2', '5', '4', '6', '1', '0', '1', '1', '0', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '8', '4', '3', '3', '2', '0', '5', '7', '9', '0', '2', '6', '4', '2', '0', '5', '7', '3', '1', '1', '9', '6', '0', '5', '9', '/', '4', '9', '3', '2', '3', '1', '5', '4', '4', '8', '5', '0', '1', '9', '0', '9', '3', '6', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '9', '6', '2', '5', '6', '6', '4', '8', '5', '1', '9', '1', '6', '1', '0', '5', '4', '1', '4', '3', '4', '6', '1', '9', '1', '9', '/', '7', '3', '9', '8', '4', '7', '3', '1', '7', '2', '7', '5', '2', '8', '6', '4', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '0', '1', '6', '5', '6', '3', '7', '7', '2', '0', '0', '2', '3', '1', '3', '0', '5', '1', '5', '6', '1', '2', '7', '1', '9', '9', '/', '7', '3', '9', '8', '4', '7', '3', '1', '7', '2', '7', '5', '2', '8', '6', '4', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '9', '8', '9', '8', '8', '4', '0', '8', '9', '5', '2', '2', '8', '6', '0', '1', '9', '4', '7', '0', '0', '8', '3', '5', '1', '/', '2', '2', '4', '1', '9', '6', '1', '5', '6', '7', '5', '0', '0', '8', '6', '7', '8', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '6', '7', '1', '8', '7', '5', '6', '3', '4', '2', '7', '5', '8', '7', '8', '8', '9', '2', '0', '0', '6', '2', '5', '7', '/', '3', '3', '6', '2', '9', '4', '2', '3', '5', '1', '2', '5', '1', '3', '0', '1', '8', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '9', '6', '6', '7', '4', '6', '1', '8', '4', '7', '1', '8', '7', '9', '2', '3', '7', '8', '2', '0', '7', '1', '4', '7', '/', '3', '3', '6', '2', '9', '4', '2', '3', '5', '1', '2', '5', '1', '3', '0', '1', '8', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '1', '3', '9', '0', '5', '0', '3', '7', '6', '5', '9', '7', '1', '3', '9', '1', '9', '8', '9', '9', '8', '9', '0', '7', '/', '3', '3', '6', '2', '9', '4', '2', '3', '5', '1', '2', '5', '1', '3', '0', '1', '8', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '4', '4', '1', '4', '3', '9', '6', '0', '9', '3', '5', '0', '4', '8', '5', '2', '5', '0', '0', '5', '6', '9', '/', '1', '2', '2', '8', '9', '8', '2', '2', '5', '4', '6', '1', '0', '1', '1', '0', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0305254Acc00600 : List (String × SourceJson) := (fragment0305254Field005Key00, fragment0305254Field005Value00) :: fragment0305254Acc00500
noncomputable def fragment0305254Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '4', '1', '4', '1', '6', '6', '6', '2', '7', '3', '8', '4', '1', '1', '7', '1', '2', '1', '5', '6', '9', '7', '3', '1', '7', '/', '1', '8', '4', '9', '6', '1', '8', '2', '9', '3', '1', '8', '8', '2', '1', '6', '0', '1', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '6', '7', '2', '2', '7', '0', '6', '7', '1', '4', '3', '4', '9', '0', '2', '0', '0', '8', '5', '1', '6', '2', '7', '/', '1', '2', '2', '8', '9', '8', '2', '2', '5', '4', '6', '1', '0', '1', '1', '0', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '8', '4', '3', '3', '2', '0', '5', '7', '9', '0', '2', '6', '4', '2', '0', '5', '7', '3', '1', '1', '9', '6', '0', '5', '9', '/', '4', '9', '3', '2', '3', '1', '5', '4', '4', '8', '5', '0', '1', '9', '0', '9', '3', '6', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '9', '6', '2', '5', '6', '6', '4', '8', '5', '1', '9', '1', '6', '1', '0', '5', '4', '1', '4', '3', '4', '6', '1', '9', '1', '9', '/', '7', '3', '9', '8', '4', '7', '3', '1', '7', '2', '7', '5', '2', '8', '6', '4', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '0', '1', '6', '5', '6', '3', '7', '7', '2', '0', '0', '2', '3', '1', '3', '0', '5', '1', '5', '6', '1', '2', '7', '1', '9', '9', '/', '7', '3', '9', '8', '4', '7', '3', '1', '7', '2', '7', '5', '2', '8', '6', '4', '0', '5', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '8', '9', '8', '8', '4', '0', '8', '9', '5', '2', '2', '8', '6', '0', '1', '9', '4', '7', '0', '0', '8', '3', '5', '1', '/', '2', '2', '4', '1', '9', '6', '1', '5', '6', '7', '5', '0', '0', '8', '6', '7', '8', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '6', '7', '1', '8', '7', '5', '6', '3', '4', '2', '7', '5', '8', '7', '8', '8', '9', '2', '0', '0', '6', '2', '5', '7', '/', '3', '3', '6', '2', '9', '4', '2', '3', '5', '1', '2', '5', '1', '3', '0', '1', '8', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '9', '6', '6', '7', '4', '6', '1', '8', '4', '7', '1', '8', '7', '9', '2', '3', '7', '8', '2', '0', '7', '1', '4', '7', '/', '3', '3', '6', '2', '9', '4', '2', '3', '5', '1', '2', '5', '1', '3', '0', '1', '8', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '1', '3', '9', '0', '5', '0', '3', '7', '6', '5', '9', '7', '1', '3', '9', '1', '9', '8', '9', '9', '8', '9', '0', '7', '/', '3', '3', '6', '2', '9', '4', '2', '3', '5', '1', '2', '5', '1', '3', '0', '1', '8', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '7', '4', '4', '1', '4', '3', '9', '6', '0', '9', '3', '5', '0', '4', '8', '5', '2', '5', '0', '0', '5', '6', '9', '/', '1', '2', '2', '8', '9', '8', '2', '2', '5', '4', '6', '1', '0', '1', '1', '0', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0305254_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 520) (SourceJson.white (fragment0305254Field005Chars00 ++ tail)) fragment0305254Acc00500 =
      SourceJson.object (fuel + 519) (SourceJson.white tail) fragment0305254Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_005"
  err.flush

noncomputable def fragment0305254Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0305254Field006Value00 : SourceJson := .str (String.ofList ['4', '3', '1', '4', '9', '3', '6', '6', '4', '5', '2', '0', '3', '3', '4', '5', '6', '4', '2', '4', '9', '6', '3', '1', '2', '3', '0', '0', '6', '5', '6', '0', '8', '9', '9', '8', '6', '3', '2', '5', '3', '5', '1', '2', '9', '1', '9', '5', '5', '1', '4', '9', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '/', '7', '5', '3', '0', '6', '6', '6', '9', '3', '7', '3', '6', '9', '5', '7', '9', '3', '1', '1', '8', '9', '2', '1', '0', '5', '2', '3', '4', '5', '5', '1', '5', '4', '8', '7', '2', '5', '1', '7', '2', '0', '1', '7', '8', '6', '2', '0', '5', '3', '9', '7', '1', '3', '4', '4', '9', '6', '8', '3', '2', '3', '7', '3', '1', '0', '5', '3', '2', '2', '7', '2', '7', '7', '0', '7', '7'])
noncomputable def fragment0305254Acc00700 : List (String × SourceJson) := (fragment0305254Field006Key00, fragment0305254Field006Value00) :: fragment0305254Acc00600
noncomputable def fragment0305254Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '3', '1', '4', '9', '3', '6', '6', '4', '5', '2', '0', '3', '3', '4', '5', '6', '4', '2', '4', '9', '6', '3', '1', '2', '3', '0', '0', '6', '5', '6', '0', '8', '9', '9', '8', '6', '3', '2', '5', '3', '5', '1', '2', '9', '1', '9', '5', '5', '1', '4', '9', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '/', '7', '5', '3', '0', '6', '6', '6', '9', '3', '7', '3', '6', '9', '5', '7', '9', '3', '1', '1', '8', '9', '2', '1', '0', '5', '2', '3', '4', '5', '5', '1', '5', '4', '8', '7', '2', '5', '1', '7', '2', '0', '1', '7', '8', '6', '2', '0', '5', '3', '9', '7', '1', '3', '4', '4', '9', '6', '8', '3', '2', '3', '7', '3', '1', '0', '5', '3', '2', '2', '7', '2', '7', '7', '0', '7', '7', '"', ',']

theorem object_fragment0305254_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 519) (SourceJson.white (fragment0305254Field006Chars00 ++ tail)) fragment0305254Acc00600 =
      SourceJson.object (fuel + 518) (SourceJson.white tail) fragment0305254Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_006"
  err.flush

noncomputable def fragment0305254Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0305254Field007Value00 : SourceJson := .str (String.ofList ['7', '1', '1', '4', '9', '3', '8', '7', '3', '9', '8', '5', '9', '8', '1', '4', '6', '8', '5', '7', '4', '4', '3', '0', '3', '8', '5', '3', '6', '7', '5', '1', '5', '5', '7', '0', '9', '4', '2', '0', '9', '6', '8', '4', '0', '4', '0', '7', '7', '0', '3', '8', '3', '2', '0', '3', '5', '4', '9', '1', '9', '8', '7', '5', '7', '4', '6', '0', '5', '6', '2', '4', '1', '8', '9', '3', '7', '7', '0', '6', '1', '4', '4', '1', '4', '7', '0', '3', '8', '5', '6', '3', '8', '6', '5', '4', '0', '3', '7', '9', '9', '0', '4', '5', '2', '4', '9', '8', '1', '1', '1', '6', '2', '9', '0', '5', '0', '9', '6', '9', '3', '0', '4', '4', '6', '7', '0', '0', '5', '3', '8', '2', '3', '9', '5', '7', '6', '7', '0', '6', '5', '7', '1', '6', '2', '9', '6', '1', '2', '6', '0', '4', '8', '1', '7', '4', '8', '0', '6', '9', '2', '0', '9', '9', '8', '3', '1', '3', '7', '2', '8', '2', '1', '2', '2', '7', '7', '1', '3', '9', '9', '9', '2', '3', '6', '1', '0', '4', '2', '0', '4', '6', '0', '1', '3', '4', '6', '0', '6', '8', '2', '7', '8', '9', '6', '3', '5', '6', '8', '5', '0', '4', '4', '8', '7', '5', '0', '8', '8', '9', '4', '8', '3', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '4', '8', '9', '4', '3', '4', '7', '2', '3', '5', '7', '9', '8', '7', '1', '0', '0', '3', '7', '4', '3', '8', '4', '5', '2', '9', '1', '2', '6', '9', '7', '7', '9', '6', '2', '1', '9', '1', '9', '6', '0', '4', '8', '7', '9', '5', '0', '5', '0', '0', '4', '3', '4', '7', '9', '3', '5', '7', '4', '1', '2', '2', '7', '4', '9', '7', '6', '5', '7', '7', '0', '7', '8', '1', '8', '8', '1', '7', '1', '3', '0', '1', '0', '2', '0', '6', '8', '2', '9', '4', '3', '0', '6', '4', '9', '4', '7', '9', '7', '2', '3', '6', '0', '0', '3', '9', '8', '9', '4', '9', '7', '5', '2', '1', '0', '8', '9', '8', '1', '0', '3', '4', '9', '0', '1', '1', '3', '6', '5', '8', '6', '5', '2', '0', '6', '3', '0', '0', '7', '8', '4', '9', '1', '4', '7', '4', '2', '3', '2', '6', '2', '4', '9', '6', '5', '8', '0', '2', '0', '9', '6', '9', '5', '1', '6', '6', '8', '6', '9', '0', '9', '1', '4', '0', '0', '2', '2', '9', '9', '3', '5', '3', '6', '3', '1', '4', '9', '2', '1', '9', '4', '6', '0', '5', '8', '4', '6', '6', '7', '1', '2', '4', '7', '7', '3', '8', '7', '7', '6', '7', '7', '4', '7', '0', '5', '2', '3', '7', '9', '7', '2', '4', '9', '5', '3', '7', '7', '4', '3', '7', '7', '2', '6', '2', '6', '8', '2', '8', '5', '3', '3', '0', '1', '7', '6', '0', '4', '0', '4', '3', '1', '2', '0', '0', '3', '4', '0', '4', '8', '5', '0', '2', '7'])
noncomputable def fragment0305254Acc00800 : List (String × SourceJson) := (fragment0305254Field007Key00, fragment0305254Field007Value00) :: fragment0305254Acc00700
noncomputable def fragment0305254Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '1', '1', '4', '9', '3', '8', '7', '3', '9', '8', '5', '9', '8', '1', '4', '6', '8', '5', '7', '4', '4', '3', '0', '3', '8', '5', '3', '6', '7', '5', '1', '5', '5', '7', '0', '9', '4', '2', '0', '9', '6', '8', '4', '0', '4', '0', '7', '7', '0', '3', '8', '3', '2', '0', '3', '5', '4', '9', '1', '9', '8', '7', '5', '7', '4', '6', '0', '5', '6', '2', '4', '1', '8', '9', '3', '7', '7', '0', '6', '1', '4', '4', '1', '4', '7', '0', '3', '8', '5', '6', '3', '8', '6', '5', '4', '0', '3', '7', '9', '9', '0', '4', '5', '2', '4', '9', '8', '1', '1', '1', '6', '2', '9', '0', '5', '0', '9', '6', '9', '3', '0', '4', '4', '6', '7', '0', '0', '5', '3', '8', '2', '3', '9', '5', '7', '6', '7', '0', '6', '5', '7', '1', '6', '2', '9', '6', '1', '2', '6', '0', '4', '8', '1', '7', '4', '8', '0', '6', '9', '2', '0', '9', '9', '8', '3', '1', '3', '7', '2', '8', '2', '1', '2', '2', '7', '7', '1', '3', '9', '9', '9', '2', '3', '6', '1', '0', '4', '2', '0', '4', '6', '0', '1', '3', '4', '6', '0', '6', '8', '2', '7', '8', '9', '6', '3', '5', '6', '8', '5', '0', '4', '4', '8', '7', '5', '0', '8', '8', '9', '4', '8', '3', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '4', '8', '9', '4', '3', '4', '7', '2', '3', '5', '7', '9', '8', '7', '1', '0', '0', '3', '7', '4', '3', '8', '4', '5', '2', '9', '1', '2', '6', '9', '7', '7', '9', '6', '2', '1', '9', '1', '9', '6', '0', '4', '8', '7', '9', '5', '0', '5', '0', '0', '4', '3', '4', '7', '9', '3', '5', '7', '4', '1', '2', '2', '7', '4', '9', '7', '6', '5', '7', '7', '0', '7', '8', '1', '8', '8', '1', '7', '1', '3', '0', '1', '0', '2', '0', '6', '8', '2', '9', '4', '3', '0', '6', '4', '9', '4', '7', '9', '7', '2', '3', '6', '0', '0', '3', '9', '8', '9', '4', '9', '7', '5', '2', '1', '0', '8', '9', '8', '1', '0', '3', '4', '9', '0', '1', '1', '3', '6', '5', '8', '6', '5', '2', '0', '6', '3', '0', '0', '7', '8', '4', '9', '1', '4', '7', '4', '2', '3', '2', '6', '2', '4', '9', '6', '5', '8', '0', '2', '0', '9', '6', '9', '5', '1', '6', '6', '8', '6', '9', '0', '9', '1', '4', '0', '0', '2', '2', '9', '9', '3', '5', '3', '6', '3', '1', '4', '9', '2', '1', '9', '4', '6', '0', '5', '8', '4', '6', '6', '7', '1', '2', '4', '7', '7', '3', '8', '7', '7', '6', '7', '7', '4', '7', '0', '5', '2', '3', '7', '9', '7', '2', '4', '9', '5', '3', '7', '7', '4', '3', '7', '7', '2', '6', '2', '6', '8', '2', '8', '5', '3', '3', '0', '1', '7', '6', '0', '4', '0', '4', '3', '1', '2', '0', '0', '3', '4', '0', '4', '8', '5', '0', '2', '7', '"', ',']

theorem object_fragment0305254_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 518) (SourceJson.white (fragment0305254Field007Chars00 ++ tail)) fragment0305254Acc00700 =
      SourceJson.object (fuel + 517) (SourceJson.white tail) fragment0305254Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_007"
  err.flush

noncomputable def fragment0305254Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0305254Field008Value00 : SourceJson := .str (String.ofList ['4', '5', '3', '9', '6', '3', '1', '1', '4', '5', '6', '6', '2', '3', '3'])
noncomputable def fragment0305254Acc00900 : List (String × SourceJson) := (fragment0305254Field008Key00, fragment0305254Field008Value00) :: fragment0305254Acc00800
noncomputable def fragment0305254Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '3', '9', '6', '3', '1', '1', '4', '5', '6', '6', '2', '3', '3', '"', ',']

theorem object_fragment0305254_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 517) (SourceJson.white (fragment0305254Field008Chars00 ++ tail)) fragment0305254Acc00800 =
      SourceJson.object (fuel + 516) (SourceJson.white tail) fragment0305254Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_008"
  err.flush

noncomputable def fragment0305254Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0305254Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '5', '5', '6', '2', '2', '4', '9', '4', '7', '4', '2', '8', '3', '8'])
noncomputable def fragment0305254Acc01000 : List (String × SourceJson) := (fragment0305254Field009Key00, fragment0305254Field009Value00) :: fragment0305254Acc00900
noncomputable def fragment0305254Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '5', '6', '2', '2', '4', '9', '4', '7', '4', '2', '8', '3', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0305254_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 516) (SourceJson.white (fragment0305254Field009Chars00 ++ tail)) fragment0305254Acc00900 =
      .ok (.obj (fragment0305254Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0305254_object_field_009"
  err.flush

noncomputable def fragment0305254Chars : List Char := '{' :: (fragment0305254Field000Chars00 ++ fragment0305254Field001Chars00 ++ fragment0305254Field002Chars00 ++ fragment0305254Field003Chars00 ++ fragment0305254Field004Chars00 ++ fragment0305254Field005Chars00 ++ fragment0305254Field006Chars00 ++ fragment0305254Field007Chars00 ++ fragment0305254Field008Chars00 ++ fragment0305254Field009Chars00)
noncomputable def fragment0305254Value : SourceJson := .obj (fragment0305254Acc01000.reverse)

theorem value_fragment0305254 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 526) (fragment0305254Chars ++ tail) =
      .ok (fragment0305254Value, tail) := by
  have hinput : fragment0305254Chars ++ tail = '{' :: (fragment0305254Field000Chars00 ++ (fragment0305254Field001Chars00 ++ (fragment0305254Field002Chars00 ++ (fragment0305254Field003Chars00 ++ (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0305254Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 526) (fragment0305254Chars ++ tail) =
        SourceJson.value (fuel + 526) ('{' :: (fragment0305254Field000Chars00 ++ (fragment0305254Field001Chars00 ++ (fragment0305254Field002Chars00 ++ (fragment0305254Field003Chars00 ++ (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 526)) hinput
    _ = SourceJson.object (fuel + 525) (SourceJson.white (fragment0305254Field000Chars00 ++ (fragment0305254Field001Chars00 ++ (fragment0305254Field002Chars00 ++ (fragment0305254Field003Chars00 ++ (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))))))))))) fragment0305254Acc00000 := by rfl
    _ = SourceJson.object (fuel + 524) (SourceJson.white (fragment0305254Field001Chars00 ++ (fragment0305254Field002Chars00 ++ (fragment0305254Field003Chars00 ++ (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail))))))))))) fragment0305254Acc00100 := object_fragment0305254_field_000 fuel (fragment0305254Field001Chars00 ++ (fragment0305254Field002Chars00 ++ (fragment0305254Field003Chars00 ++ (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 523) (SourceJson.white (fragment0305254Field002Chars00 ++ (fragment0305254Field003Chars00 ++ (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))))))))) fragment0305254Acc00200 := object_fragment0305254_field_001 fuel (fragment0305254Field002Chars00 ++ (fragment0305254Field003Chars00 ++ (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 522) (SourceJson.white (fragment0305254Field003Chars00 ++ (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail))))))))) fragment0305254Acc00300 := object_fragment0305254_field_002 fuel (fragment0305254Field003Chars00 ++ (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 521) (SourceJson.white (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))))))) fragment0305254Acc00400 := object_fragment0305254_field_003 fuel (fragment0305254Field004Chars00 ++ (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 520) (SourceJson.white (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail))))))) fragment0305254Acc00500 := object_fragment0305254_field_004 fuel (fragment0305254Field005Chars00 ++ (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 519) (SourceJson.white (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))))) fragment0305254Acc00600 := object_fragment0305254_field_005 fuel (fragment0305254Field006Chars00 ++ (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 518) (SourceJson.white (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail))))) fragment0305254Acc00700 := object_fragment0305254_field_006 fuel (fragment0305254Field007Chars00 ++ (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 517) (SourceJson.white (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))) fragment0305254Acc00800 := object_fragment0305254_field_007 fuel (fragment0305254Field008Chars00 ++ (fragment0305254Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 516) (SourceJson.white (fragment0305254Field009Chars00 ++ (tail))) fragment0305254Acc00900 := object_fragment0305254_field_008 fuel (fragment0305254Field009Chars00 ++ (tail))
    _ = .ok (fragment0305254Value, tail) := object_fragment0305254_field_009 fuel (tail)

noncomputable def fragment0307480Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0307480Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0307480Field000Value00 : SourceJson := .number (String.ofList ['9', '7'])
noncomputable def fragment0307480Acc00100 : List (String × SourceJson) := (fragment0307480Field000Key00, fragment0307480Field000Value00) :: fragment0307480Acc00000
noncomputable def fragment0307480Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '7', ',']

theorem object_fragment0307480_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment0307480Field000Chars00 ++ tail)) fragment0307480Acc00000 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment0307480Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_000"
  err.flush

noncomputable def fragment0307480Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0307480Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0307480Acc00200 : List (String × SourceJson) := (fragment0307480Field001Key00, fragment0307480Field001Value00) :: fragment0307480Acc00100
noncomputable def fragment0307480Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0307480_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment0307480Field001Chars00 ++ tail)) fragment0307480Acc00100 =
      SourceJson.object (fuel + 474) (SourceJson.white tail) fragment0307480Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_001"
  err.flush

noncomputable def fragment0307480Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0307480Field002Value00 : SourceJson := .str (String.ofList ['3', '2', '3', '7', '3', '1', '1', '4', '0', '7', '5', '5', '6', '8', '9', '6', '0', '8', '4', '9', '8', '5', '6', '2', '5', '0', '9', '1', '4', '0', '1', '3', '7', '7', '5', '1', '2', '5', '0', '6', '7', '4', '3', '/', '3', '8', '2', '0', '6', '8', '5', '5', '5', '5', '4', '7', '1', '5', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0307480Acc00300 : List (String × SourceJson) := (fragment0307480Field002Key00, fragment0307480Field002Value00) :: fragment0307480Acc00200
noncomputable def fragment0307480Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '2', '3', '7', '3', '1', '1', '4', '0', '7', '5', '5', '6', '8', '9', '6', '0', '8', '4', '9', '8', '5', '6', '2', '5', '0', '9', '1', '4', '0', '1', '3', '7', '7', '5', '1', '2', '5', '0', '6', '7', '4', '3', '/', '3', '8', '2', '0', '6', '8', '5', '5', '5', '5', '4', '7', '1', '5', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0307480_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 474) (SourceJson.white (fragment0307480Field002Chars00 ++ tail)) fragment0307480Acc00200 =
      SourceJson.object (fuel + 473) (SourceJson.white tail) fragment0307480Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_002"
  err.flush

noncomputable def fragment0307480Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0307480Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0307480Acc00400 : List (String × SourceJson) := (fragment0307480Field003Key00, fragment0307480Field003Value00) :: fragment0307480Acc00300
noncomputable def fragment0307480Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0307480_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 473) (SourceJson.white (fragment0307480Field003Chars00 ++ tail)) fragment0307480Acc00300 =
      SourceJson.object (fuel + 472) (SourceJson.white tail) fragment0307480Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_003"
  err.flush

noncomputable def fragment0307480Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0307480Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0307480Acc00500 : List (String × SourceJson) := (fragment0307480Field004Key00, fragment0307480Field004Value00) :: fragment0307480Acc00400
noncomputable def fragment0307480Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0307480_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment0307480Field004Chars00 ++ tail)) fragment0307480Acc00400 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment0307480Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_004"
  err.flush

noncomputable def fragment0307480Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0307480Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '6', '1', '9', '1', '2', '5', '1', '5', '3', '4', '1', '0', '2', '7', '8', '2', '6', '0', '3', '9', '8', '2', '0', '9', '7', '/', '3', '0', '0', '0', '1', '4', '2', '3', '9', '7', '5', '4', '0', '3', '0', '4', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '6', '5', '0', '7', '1', '3', '6', '5', '0', '3', '9', '0', '5', '7', '1', '3', '0', '8', '4', '0', '1', '/', '9', '9', '6', '7', '2', '5', '0', '4', '9', '0', '1', '6', '7', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '8', '6', '9', '4', '9', '3', '9', '2', '1', '3', '9', '7', '6', '3', '1', '5', '5', '2', '6', '2', '3', '/', '1', '7', '3', '9', '2', '1', '2', '9', '8', '4', '0', '8', '1', '3', '3', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '4', '4', '9', '0', '6', '7', '7', '9', '9', '1', '2', '9', '0', '1', '8', '5', '3', '3', '1', '9', '5', '6', '5', '7', '/', '6', '0', '0', '0', '2', '8', '4', '7', '9', '5', '0', '8', '0', '6', '0', '8', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '6', '8', '1', '8', '4', '3', '8', '6', '4', '7', '4', '2', '2', '0', '4', '9', '7', '7', '3', '8', '3', '4', '9', '7', '/', '6', '0', '0', '0', '2', '8', '4', '7', '9', '5', '0', '8', '0', '6', '0', '8', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '2', '6', '7', '3', '7', '8', '4', '6', '6', '8', '4', '9', '6', '4', '7', '1', '5', '5', '1', '5', '1', '3', '/', '1', '8', '1', '8', '2', '6', '8', '1', '1', '9', '7', '2', '1', '3', '9', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '2', '3', '5', '0', '1', '2', '6', '5', '4', '2', '7', '7', '0', '6', '7', '1', '9', '0', '9', '6', '7', '1', '/', '2', '7', '2', '7', '4', '0', '2', '1', '7', '9', '5', '8', '2', '0', '9', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '6', '2', '4', '0', '0', '1', '1', '4', '5', '2', '2', '3', '5', '0', '5', '2', '5', '8', '5', '8', '4', '1', '/', '2', '7', '2', '7', '4', '0', '2', '1', '7', '9', '5', '8', '2', '0', '9', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '1', '4', '1', '7', '0', '9', '4', '4', '6', '4', '5', '8', '8', '0', '2', '7', '5', '2', '5', '1', '2', '1', '/', '2', '7', '2', '7', '4', '0', '2', '1', '7', '9', '5', '8', '2', '0', '9', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '5', '7', '5', '6', '8', '2', '3', '2', '4', '5', '3', '7', '0', '3', '9', '7', '2', '3', '5', '4', '7', '/', '9', '9', '6', '7', '2', '5', '0', '4', '9', '0', '1', '6', '7', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0307480Acc00600 : List (String × SourceJson) := (fragment0307480Field005Key00, fragment0307480Field005Value00) :: fragment0307480Acc00500
noncomputable def fragment0307480Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '9', '1', '2', '5', '1', '5', '3', '4', '1', '0', '2', '7', '8', '2', '6', '0', '3', '9', '8', '2', '0', '9', '7', '/', '3', '0', '0', '0', '1', '4', '2', '3', '9', '7', '5', '4', '0', '3', '0', '4', '3', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '6', '5', '0', '7', '1', '3', '6', '5', '0', '3', '9', '0', '5', '7', '1', '3', '0', '8', '4', '0', '1', '/', '9', '9', '6', '7', '2', '5', '0', '4', '9', '0', '1', '6', '7', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '4', '8', '6', '9', '4', '9', '3', '9', '2', '1', '3', '9', '7', '6', '3', '1', '5', '5', '2', '6', '2', '3', '/', '1', '7', '3', '9', '2', '1', '2', '9', '8', '4', '0', '8', '1', '3', '3', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '4', '4', '9', '0', '6', '7', '7', '9', '9', '1', '2', '9', '0', '1', '8', '5', '3', '3', '1', '9', '5', '6', '5', '7', '/', '6', '0', '0', '0', '2', '8', '4', '7', '9', '5', '0', '8', '0', '6', '0', '8', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '6', '8', '1', '8', '4', '3', '8', '6', '4', '7', '4', '2', '2', '0', '4', '9', '7', '7', '3', '8', '3', '4', '9', '7', '/', '6', '0', '0', '0', '2', '8', '4', '7', '9', '5', '0', '8', '0', '6', '0', '8', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '2', '6', '7', '3', '7', '8', '4', '6', '6', '8', '4', '9', '6', '4', '7', '1', '5', '5', '1', '5', '1', '3', '/', '1', '8', '1', '8', '2', '6', '8', '1', '1', '9', '7', '2', '1', '3', '9', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '2', '3', '5', '0', '1', '2', '6', '5', '4', '2', '7', '7', '0', '6', '7', '1', '9', '0', '9', '6', '7', '1', '/', '2', '7', '2', '7', '4', '0', '2', '1', '7', '9', '5', '8', '2', '0', '9', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '6', '2', '4', '0', '0', '1', '1', '4', '5', '2', '2', '3', '5', '0', '5', '2', '5', '8', '5', '8', '4', '1', '/', '2', '7', '2', '7', '4', '0', '2', '1', '7', '9', '5', '8', '2', '0', '9', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '1', '4', '1', '7', '0', '9', '4', '4', '6', '4', '5', '8', '8', '0', '2', '7', '5', '2', '5', '1', '2', '1', '/', '2', '7', '2', '7', '4', '0', '2', '1', '7', '9', '5', '8', '2', '0', '9', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '5', '7', '5', '6', '8', '2', '3', '2', '4', '5', '3', '7', '0', '3', '9', '7', '2', '3', '5', '4', '7', '/', '9', '9', '6', '7', '2', '5', '0', '4', '9', '0', '1', '6', '7', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0307480_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment0307480Field005Chars00 ++ tail)) fragment0307480Acc00500 =
      SourceJson.object (fuel + 470) (SourceJson.white tail) fragment0307480Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_005"
  err.flush

noncomputable def fragment0307480Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0307480Field006Value00 : SourceJson := .str (String.ofList ['2', '2', '6', '3', '5', '6', '1', '6', '3', '2', '9', '8', '3', '4', '2', '7', '9', '0', '6', '2', '3', '2', '8', '6', '7', '7', '4', '5', '2', '0', '2', '1', '2', '9', '8', '0', '6', '0', '1', '0', '8', '8', '1', '7', '2', '5', '8', '2', '5', '1', '1', '3', '2', '0', '0', '0', '0', '/', '6', '3', '8', '9', '3', '3', '3', '9', '3', '1', '7', '1', '7', '6', '8', '0', '6', '3', '1', '3', '4', '5', '4', '7', '5', '9', '1', '8', '1', '5', '1', '1', '4', '9', '8', '3', '4', '8', '0', '1', '6', '4', '4', '7', '1', '0', '9', '7', '0', '9', '6', '8', '2', '8', '0', '0', '4', '0', '4', '0', '4', '6', '5', '3', '2', '8', '5', '7', '6', '3'])
noncomputable def fragment0307480Acc00700 : List (String × SourceJson) := (fragment0307480Field006Key00, fragment0307480Field006Value00) :: fragment0307480Acc00600
noncomputable def fragment0307480Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '6', '3', '5', '6', '1', '6', '3', '2', '9', '8', '3', '4', '2', '7', '9', '0', '6', '2', '3', '2', '8', '6', '7', '7', '4', '5', '2', '0', '2', '1', '2', '9', '8', '0', '6', '0', '1', '0', '8', '8', '1', '7', '2', '5', '8', '2', '5', '1', '1', '3', '2', '0', '0', '0', '0', '/', '6', '3', '8', '9', '3', '3', '3', '9', '3', '1', '7', '1', '7', '6', '8', '0', '6', '3', '1', '3', '4', '5', '4', '7', '5', '9', '1', '8', '1', '5', '1', '1', '4', '9', '8', '3', '4', '8', '0', '1', '6', '4', '4', '7', '1', '0', '9', '7', '0', '9', '6', '8', '2', '8', '0', '0', '4', '0', '4', '0', '4', '6', '5', '3', '2', '8', '5', '7', '6', '3', '"', ',']

theorem object_fragment0307480_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment0307480Field006Chars00 ++ tail)) fragment0307480Acc00600 =
      SourceJson.object (fuel + 469) (SourceJson.white tail) fragment0307480Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_006"
  err.flush

noncomputable def fragment0307480Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0307480Field007Value00 : SourceJson := .str (String.ofList ['1', '3', '5', '3', '9', '5', '4', '6', '7', '8', '8', '8', '6', '7', '8', '4', '5', '3', '1', '5', '5', '1', '2', '3', '6', '3', '7', '0', '9', '3', '4', '4', '1', '1', '3', '6', '2', '8', '7', '4', '2', '0', '6', '6', '6', '7', '8', '5', '7', '4', '6', '0', '1', '1', '8', '7', '7', '5', '5', '2', '4', '4', '3', '2', '2', '2', '3', '1', '1', '8', '7', '4', '5', '2', '7', '0', '2', '0', '3', '2', '5', '1', '4', '4', '9', '8', '3', '3', '0', '6', '4', '0', '2', '0', '7', '6', '3', '5', '2', '6', '8', '6', '1', '6', '0', '9', '7', '2', '9', '4', '4', '1', '3', '3', '7', '5', '6', '1', '7', '9', '4', '1', '4', '9', '7', '7', '0', '1', '9', '4', '4', '5', '6', '8', '3', '5', '3', '9', '6', '8', '0', '9', '3', '2', '2', '6', '0', '3', '1', '0', '1', '7', '4', '5', '1', '0', '0', '6', '0', '1', '2', '5', '8', '5', '6', '2', '9', '4', '8', '3', '4', '7', '2', '5', '9', '7', '4', '0', '6', '1', '5', '1', '4', '0', '6', '9', '9', '3', '6', '0', '1', '0', '0', '6', '0', '6', '7', '5', '1', '5', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '8', '3', '5', '3', '9', '9', '4', '9', '7', '2', '2', '5', '0', '8', '1', '3', '6', '1', '2', '3', '3', '1', '1', '1', '7', '5', '6', '3', '1', '1', '3', '6', '4', '9', '8', '9', '8', '3', '0', '5', '4', '4', '9', '3', '3', '3', '1', '1', '4', '9', '5', '5', '4', '0', '2', '9', '2', '0', '4', '6', '3', '8', '7', '0', '5', '6', '7', '7', '2', '2', '9', '1', '4', '0', '2', '7', '8', '9', '8', '5', '7', '0', '1', '5', '8', '6', '9', '5', '6', '7', '4', '1', '9', '0', '9', '5', '6', '9', '3', '2', '6', '3', '2', '3', '7', '7', '7', '2', '4', '2', '5', '3', '7', '3', '0', '2', '5', '0', '2', '8', '8', '8', '3', '9', '9', '4', '7', '5', '6', '7', '8', '7', '9', '8', '2', '6', '5', '4', '9', '1', '4', '5', '6', '1', '8', '8', '6', '4', '5', '5', '5', '7', '1', '6', '2', '4', '6', '7', '2', '6', '1', '1', '1', '7', '2', '8', '4', '7', '3', '8', '8', '0', '4', '1', '0', '9', '2', '0', '6', '6', '9', '3', '9', '1', '1', '4', '8', '1', '3', '5', '2', '7', '0', '5', '9', '5', '1', '8', '1', '2', '3', '4', '9', '6', '8', '1', '2', '5', '9', '2', '8', '2', '5', '5', '7', '4', '5', '7', '0', '1', '0', '7', '8', '3', '1', '5', '4', '8', '4', '9', '3', '9', '7', '1', '7', '4', '1'])
noncomputable def fragment0307480Acc00800 : List (String × SourceJson) := (fragment0307480Field007Key00, fragment0307480Field007Value00) :: fragment0307480Acc00700
noncomputable def fragment0307480Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '5', '3', '9', '5', '4', '6', '7', '8', '8', '8', '6', '7', '8', '4', '5', '3', '1', '5', '5', '1', '2', '3', '6', '3', '7', '0', '9', '3', '4', '4', '1', '1', '3', '6', '2', '8', '7', '4', '2', '0', '6', '6', '6', '7', '8', '5', '7', '4', '6', '0', '1', '1', '8', '7', '7', '5', '5', '2', '4', '4', '3', '2', '2', '2', '3', '1', '1', '8', '7', '4', '5', '2', '7', '0', '2', '0', '3', '2', '5', '1', '4', '4', '9', '8', '3', '3', '0', '6', '4', '0', '2', '0', '7', '6', '3', '5', '2', '6', '8', '6', '1', '6', '0', '9', '7', '2', '9', '4', '4', '1', '3', '3', '7', '5', '6', '1', '7', '9', '4', '1', '4', '9', '7', '7', '0', '1', '9', '4', '4', '5', '6', '8', '3', '5', '3', '9', '6', '8', '0', '9', '3', '2', '2', '6', '0', '3', '1', '0', '1', '7', '4', '5', '1', '0', '0', '6', '0', '1', '2', '5', '8', '5', '6', '2', '9', '4', '8', '3', '4', '7', '2', '5', '9', '7', '4', '0', '6', '1', '5', '1', '4', '0', '6', '9', '9', '3', '6', '0', '1', '0', '0', '6', '0', '6', '7', '5', '1', '5', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '8', '3', '5', '3', '9', '9', '4', '9', '7', '2', '2', '5', '0', '8', '1', '3', '6', '1', '2', '3', '3', '1', '1', '1', '7', '5', '6', '3', '1', '1', '3', '6', '4', '9', '8', '9', '8', '3', '0', '5', '4', '4', '9', '3', '3', '3', '1', '1', '4', '9', '5', '5', '4', '0', '2', '9', '2', '0', '4', '6', '3', '8', '7', '0', '5', '6', '7', '7', '2', '2', '9', '1', '4', '0', '2', '7', '8', '9', '8', '5', '7', '0', '1', '5', '8', '6', '9', '5', '6', '7', '4', '1', '9', '0', '9', '5', '6', '9', '3', '2', '6', '3', '2', '3', '7', '7', '7', '2', '4', '2', '5', '3', '7', '3', '0', '2', '5', '0', '2', '8', '8', '8', '3', '9', '9', '4', '7', '5', '6', '7', '8', '7', '9', '8', '2', '6', '5', '4', '9', '1', '4', '5', '6', '1', '8', '8', '6', '4', '5', '5', '5', '7', '1', '6', '2', '4', '6', '7', '2', '6', '1', '1', '1', '7', '2', '8', '4', '7', '3', '8', '8', '0', '4', '1', '0', '9', '2', '0', '6', '6', '9', '3', '9', '1', '1', '4', '8', '1', '3', '5', '2', '7', '0', '5', '9', '5', '1', '8', '1', '2', '3', '4', '9', '6', '8', '1', '2', '5', '9', '2', '8', '2', '5', '5', '7', '4', '5', '7', '0', '1', '0', '7', '8', '3', '1', '5', '4', '8', '4', '9', '3', '9', '7', '1', '7', '4', '1', '"', ',']

theorem object_fragment0307480_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 469) (SourceJson.white (fragment0307480Field007Chars00 ++ tail)) fragment0307480Acc00700 =
      SourceJson.object (fuel + 468) (SourceJson.white tail) fragment0307480Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_007"
  err.flush

noncomputable def fragment0307480Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0307480Field008Value00 : SourceJson := .str (String.ofList ['2', '8', '0', '6', '8', '3', '1', '3', '6', '6', '7', '0', '6', '3', '6', '0'])
noncomputable def fragment0307480Acc00900 : List (String × SourceJson) := (fragment0307480Field008Key00, fragment0307480Field008Value00) :: fragment0307480Acc00800
noncomputable def fragment0307480Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '8', '0', '6', '8', '3', '1', '3', '6', '6', '7', '0', '6', '3', '6', '0', '"', ',']

theorem object_fragment0307480_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 468) (SourceJson.white (fragment0307480Field008Chars00 ++ tail)) fragment0307480Acc00800 =
      SourceJson.object (fuel + 467) (SourceJson.white tail) fragment0307480Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_008"
  err.flush

noncomputable def fragment0307480Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0307480Field009Value00 : SourceJson := .str (String.ofList ['8', '3', '5', '7', '4', '6', '0', '2', '6', '9', '0', '7', '7', '0', '9', '5'])
noncomputable def fragment0307480Acc01000 : List (String × SourceJson) := (fragment0307480Field009Key00, fragment0307480Field009Value00) :: fragment0307480Acc00900
noncomputable def fragment0307480Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '3', '5', '7', '4', '6', '0', '2', '6', '9', '0', '7', '7', '0', '9', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0307480_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 467) (SourceJson.white (fragment0307480Field009Chars00 ++ tail)) fragment0307480Acc00900 =
      .ok (.obj (fragment0307480Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0307480_object_field_009"
  err.flush

noncomputable def fragment0307480Chars : List Char := '{' :: (fragment0307480Field000Chars00 ++ fragment0307480Field001Chars00 ++ fragment0307480Field002Chars00 ++ fragment0307480Field003Chars00 ++ fragment0307480Field004Chars00 ++ fragment0307480Field005Chars00 ++ fragment0307480Field006Chars00 ++ fragment0307480Field007Chars00 ++ fragment0307480Field008Chars00 ++ fragment0307480Field009Chars00)
noncomputable def fragment0307480Value : SourceJson := .obj (fragment0307480Acc01000.reverse)

theorem value_fragment0307480 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 477) (fragment0307480Chars ++ tail) =
      .ok (fragment0307480Value, tail) := by
  have hinput : fragment0307480Chars ++ tail = '{' :: (fragment0307480Field000Chars00 ++ (fragment0307480Field001Chars00 ++ (fragment0307480Field002Chars00 ++ (fragment0307480Field003Chars00 ++ (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0307480Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 477) (fragment0307480Chars ++ tail) =
        SourceJson.value (fuel + 477) ('{' :: (fragment0307480Field000Chars00 ++ (fragment0307480Field001Chars00 ++ (fragment0307480Field002Chars00 ++ (fragment0307480Field003Chars00 ++ (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 477)) hinput
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment0307480Field000Chars00 ++ (fragment0307480Field001Chars00 ++ (fragment0307480Field002Chars00 ++ (fragment0307480Field003Chars00 ++ (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))))))))))) fragment0307480Acc00000 := by rfl
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment0307480Field001Chars00 ++ (fragment0307480Field002Chars00 ++ (fragment0307480Field003Chars00 ++ (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail))))))))))) fragment0307480Acc00100 := object_fragment0307480_field_000 fuel (fragment0307480Field001Chars00 ++ (fragment0307480Field002Chars00 ++ (fragment0307480Field003Chars00 ++ (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 474) (SourceJson.white (fragment0307480Field002Chars00 ++ (fragment0307480Field003Chars00 ++ (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))))))))) fragment0307480Acc00200 := object_fragment0307480_field_001 fuel (fragment0307480Field002Chars00 ++ (fragment0307480Field003Chars00 ++ (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 473) (SourceJson.white (fragment0307480Field003Chars00 ++ (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail))))))))) fragment0307480Acc00300 := object_fragment0307480_field_002 fuel (fragment0307480Field003Chars00 ++ (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))))))) fragment0307480Acc00400 := object_fragment0307480_field_003 fuel (fragment0307480Field004Chars00 ++ (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail))))))) fragment0307480Acc00500 := object_fragment0307480_field_004 fuel (fragment0307480Field005Chars00 ++ (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))))) fragment0307480Acc00600 := object_fragment0307480_field_005 fuel (fragment0307480Field006Chars00 ++ (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 469) (SourceJson.white (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail))))) fragment0307480Acc00700 := object_fragment0307480_field_006 fuel (fragment0307480Field007Chars00 ++ (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 468) (SourceJson.white (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))) fragment0307480Acc00800 := object_fragment0307480_field_007 fuel (fragment0307480Field008Chars00 ++ (fragment0307480Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 467) (SourceJson.white (fragment0307480Field009Chars00 ++ (tail))) fragment0307480Acc00900 := object_fragment0307480_field_008 fuel (fragment0307480Field009Chars00 ++ (tail))
    _ = .ok (fragment0307480Value, tail) := object_fragment0307480_field_009 fuel (tail)

noncomputable def fragment0309594Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0309594Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0309594Field000Value00 : SourceJson := .number (String.ofList ['9', '8'])
noncomputable def fragment0309594Acc00100 : List (String × SourceJson) := (fragment0309594Field000Key00, fragment0309594Field000Value00) :: fragment0309594Acc00000
noncomputable def fragment0309594Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '8', ',']

theorem object_fragment0309594_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0309594Field000Chars00 ++ tail)) fragment0309594Acc00000 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0309594Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_000"
  err.flush

noncomputable def fragment0309594Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0309594Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0309594Acc00200 : List (String × SourceJson) := (fragment0309594Field001Key00, fragment0309594Field001Value00) :: fragment0309594Acc00100
noncomputable def fragment0309594Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0309594_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0309594Field001Chars00 ++ tail)) fragment0309594Acc00100 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0309594Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_001"
  err.flush

noncomputable def fragment0309594Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0309594Field002Value00 : SourceJson := .str (String.ofList ['5', '3', '9', '2', '2', '4', '0', '8', '1', '0', '1', '1', '2', '1', '2', '3', '4', '8', '5', '9', '1', '3', '2', '4', '0', '1', '1', '5', '1', '6', '7', '2', '7', '3', '6', '2', '8', '6', '1', '9', '1', '6', '9', '/', '5', '3', '3', '1', '1', '8', '9', '1', '4', '7', '1', '6', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0309594Acc00300 : List (String × SourceJson) := (fragment0309594Field002Key00, fragment0309594Field002Value00) :: fragment0309594Acc00200
noncomputable def fragment0309594Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '3', '9', '2', '2', '4', '0', '8', '1', '0', '1', '1', '2', '1', '2', '3', '4', '8', '5', '9', '1', '3', '2', '4', '0', '1', '1', '5', '1', '6', '7', '2', '7', '3', '6', '2', '8', '6', '1', '9', '1', '6', '9', '/', '5', '3', '3', '1', '1', '8', '9', '1', '4', '7', '1', '6', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0309594_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0309594Field002Chars00 ++ tail)) fragment0309594Acc00200 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0309594Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_002"
  err.flush

noncomputable def fragment0309594Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0309594Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0309594Acc00400 : List (String × SourceJson) := (fragment0309594Field003Key00, fragment0309594Field003Value00) :: fragment0309594Acc00300
noncomputable def fragment0309594Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0309594_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0309594Field003Chars00 ++ tail)) fragment0309594Acc00300 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0309594Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_003"
  err.flush

noncomputable def fragment0309594Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0309594Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0309594Acc00500 : List (String × SourceJson) := (fragment0309594Field004Key00, fragment0309594Field004Value00) :: fragment0309594Acc00400
noncomputable def fragment0309594Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0309594_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0309594Field004Chars00 ++ tail)) fragment0309594Acc00400 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0309594Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_004"
  err.flush

noncomputable def fragment0309594Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0309594Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '5', '6', '4', '2', '7', '5', '0', '2', '3', '1', '5', '3', '9', '4', '9', '0', '7', '8', '0', '3', '3', '/', '1', '0', '8', '7', '7', '2', '2', '0', '0', '5', '2', '0', '2', '7', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '7', '3', '2', '4', '1', '0', '4', '0', '8', '0', '1', '5', '7', '0', '7', '6', '9', '8', '7', '/', '1', '5', '5', '3', '8', '8', '8', '5', '7', '8', '8', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '9', '3', '5', '8', '8', '2', '9', '1', '0', '1', '3', '8', '5', '9', '9', '7', '/', '4', '2', '0', '3', '7', '5', '6', '5', '4', '1', '8', '4', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '9', '1', '2', '9', '3', '6', '4', '2', '2', '7', '8', '7', '0', '7', '9', '1', '1', '6', '7', '3', '3', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '6', '3', '4', '7', '7', '4', '1', '7', '3', '8', '7', '6', '8', '3', '8', '3', '8', '1', '6', '9', '3', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '9', '5', '2', '9', '9', '8', '8', '0', '8', '2', '4', '2', '6', '8', '2', '9', '8', '3', '9', '/', '2', '1', '9', '7', '4', '1', '8', '1', '9', '2', '3', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '9', '7', '9', '6', '6', '4', '5', '5', '4', '6', '7', '7', '2', '3', '8', '4', '3', '0', '9', '/', '9', '8', '8', '8', '3', '8', '1', '8', '6', '5', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '7', '9', '9', '5', '2', '0', '7', '9', '5', '3', '5', '1', '0', '5', '1', '0', '4', '4', '9', '/', '9', '8', '8', '8', '3', '8', '1', '8', '6', '5', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '6', '2', '1', '0', '5', '8', '7', '1', '2', '4', '6', '9', '0', '8', '8', '7', '6', '9', '/', '9', '8', '8', '8', '3', '8', '1', '8', '6', '5', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '6', '5', '6', '4', '6', '7', '3', '4', '4', '5', '9', '4', '8', '3', '1', '1', '6', '8', '9', '/', '1', '5', '5', '3', '8', '8', '8', '5', '7', '8', '8', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0309594Acc00600 : List (String × SourceJson) := (fragment0309594Field005Key00, fragment0309594Field005Value00) :: fragment0309594Acc00500
noncomputable def fragment0309594Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '6', '4', '2', '7', '5', '0', '2', '3', '1', '5', '3', '9', '4', '9', '0', '7', '8', '0', '3', '3', '/', '1', '0', '8', '7', '7', '2', '2', '0', '0', '5', '2', '0', '2', '7', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '7', '3', '2', '4', '1', '0', '4', '0', '8', '0', '1', '5', '7', '0', '7', '6', '9', '8', '7', '/', '1', '5', '5', '3', '8', '8', '8', '5', '7', '8', '8', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '9', '3', '5', '8', '8', '2', '9', '1', '0', '1', '3', '8', '5', '9', '9', '7', '/', '4', '2', '0', '3', '7', '5', '6', '5', '4', '1', '8', '4', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '1', '2', '9', '3', '6', '4', '2', '2', '7', '8', '7', '0', '7', '9', '1', '1', '6', '7', '3', '3', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '6', '3', '4', '7', '7', '4', '1', '7', '3', '8', '7', '6', '8', '3', '8', '3', '8', '1', '6', '9', '3', '/', '2', '1', '7', '5', '4', '4', '4', '0', '1', '0', '4', '0', '5', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '5', '2', '9', '9', '8', '8', '0', '8', '2', '4', '2', '6', '8', '2', '9', '8', '3', '9', '/', '2', '1', '9', '7', '4', '1', '8', '1', '9', '2', '3', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '9', '7', '9', '6', '6', '4', '5', '5', '4', '6', '7', '7', '2', '3', '8', '4', '3', '0', '9', '/', '9', '8', '8', '8', '3', '8', '1', '8', '6', '5', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '7', '9', '9', '5', '2', '0', '7', '9', '5', '3', '5', '1', '0', '5', '1', '0', '4', '4', '9', '/', '9', '8', '8', '8', '3', '8', '1', '8', '6', '5', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '6', '2', '1', '0', '5', '8', '7', '1', '2', '4', '6', '9', '0', '8', '8', '7', '6', '9', '/', '9', '8', '8', '8', '3', '8', '1', '8', '6', '5', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '6', '5', '6', '4', '6', '7', '3', '4', '4', '5', '9', '4', '8', '3', '1', '1', '6', '8', '9', '/', '1', '5', '5', '3', '8', '8', '8', '5', '7', '8', '8', '6', '1', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0309594_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0309594Field005Chars00 ++ tail)) fragment0309594Acc00500 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0309594Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_005"
  err.flush

noncomputable def fragment0309594Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0309594Field006Value00 : SourceJson := .str (String.ofList ['7', '6', '3', '6', '4', '4', '3', '8', '7', '6', '3', '6', '6', '0', '1', '0', '2', '9', '5', '2', '3', '0', '2', '6', '9', '0', '6', '3', '4', '7', '9', '4', '0', '5', '0', '1', '0', '5', '9', '9', '4', '6', '6', '3', '9', '4', '8', '1', '6', '0', '0', '/', '3', '6', '6', '8', '2', '2', '0', '4', '9', '6', '2', '7', '0', '8', '5', '0', '4', '3', '1', '3', '6', '1', '8', '4', '0', '8', '0', '8', '9', '2', '2', '7', '2', '9', '0', '5', '4', '4', '2', '1', '3', '9', '2', '3', '0', '7', '9', '7', '5', '6', '7', '7', '8', '3', '7', '9', '2', '0', '1', '5', '5', '7', '8', '7'])
noncomputable def fragment0309594Acc00700 : List (String × SourceJson) := (fragment0309594Field006Key00, fragment0309594Field006Value00) :: fragment0309594Acc00600
noncomputable def fragment0309594Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '6', '3', '6', '4', '4', '3', '8', '7', '6', '3', '6', '6', '0', '1', '0', '2', '9', '5', '2', '3', '0', '2', '6', '9', '0', '6', '3', '4', '7', '9', '4', '0', '5', '0', '1', '0', '5', '9', '9', '4', '6', '6', '3', '9', '4', '8', '1', '6', '0', '0', '/', '3', '6', '6', '8', '2', '2', '0', '4', '9', '6', '2', '7', '0', '8', '5', '0', '4', '3', '1', '3', '6', '1', '8', '4', '0', '8', '0', '8', '9', '2', '2', '7', '2', '9', '0', '5', '4', '4', '2', '1', '3', '9', '2', '3', '0', '7', '9', '7', '5', '6', '7', '7', '8', '3', '7', '9', '2', '0', '1', '5', '5', '7', '8', '7', '"', ',']

theorem object_fragment0309594_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0309594Field006Chars00 ++ tail)) fragment0309594Acc00600 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0309594Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_006"
  err.flush

noncomputable def fragment0309594Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0309594Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '6', '6', '8', '5', '1', '8', '4', '8', '5', '3', '5', '9', '2', '7', '8', '1', '7', '2', '5', '9', '7', '4', '4', '2', '4', '7', '0', '8', '7', '6', '8', '0', '0', '1', '7', '4', '0', '3', '6', '3', '7', '6', '4', '6', '7', '0', '0', '6', '1', '5', '0', '1', '1', '7', '6', '5', '8', '2', '3', '5', '5', '0', '0', '8', '6', '0', '9', '2', '1', '2', '7', '4', '3', '9', '7', '2', '3', '5', '6', '8', '2', '6', '6', '6', '8', '3', '7', '7', '6', '1', '6', '7', '6', '7', '1', '2', '0', '7', '1', '1', '6', '5', '7', '3', '8', '8', '5', '8', '5', '5', '7', '9', '1', '5', '7', '4', '7', '1', '8', '0', '9', '7', '0', '0', '5', '5', '5', '4', '8', '7', '8', '6', '1', '9', '7', '1', '0', '2', '9', '8', '5', '5', '7', '4', '7', '5', '1', '7', '1', '9', '3', '2', '5', '0', '9', '4', '6', '7', '6', '4', '2', '9', '5', '3', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '0', '3', '8', '9', '5', '6', '5', '2', '4', '9', '9', '5', '6', '7', '4', '9', '3', '7', '9', '5', '6', '0', '7', '8', '1', '7', '1', '9', '1', '7', '9', '4', '9', '1', '5', '5', '6', '4', '2', '2', '6', '0', '2', '5', '4', '6', '2', '6', '3', '1', '2', '6', '9', '9', '8', '2', '4', '8', '4', '1', '0', '7', '7', '6', '7', '9', '8', '5', '3', '2', '5', '7', '0', '2', '5', '2', '5', '5', '8', '5', '0', '9', '2', '8', '8', '9', '8', '6', '0', '5', '7', '6', '8', '9', '6', '1', '4', '6', '3', '7', '7', '0', '7', '7', '1', '4', '1', '5', '6', '8', '5', '9', '8', '1', '4', '5', '9', '1', '2', '7', '4', '9', '0', '3', '9', '7', '3', '9', '4', '2', '6', '1', '7', '6', '6', '1', '1', '3', '5', '0', '9', '3', '5', '0', '6', '9', '7', '9', '1', '5', '5', '6', '6', '9', '5', '8', '9', '8', '0', '7', '2', '8', '5', '6', '6', '5', '3', '9', '7', '9', '4', '9', '5', '5', '2', '5', '3', '0', '5', '2', '7', '5', '0', '3', '9', '0', '6', '0', '0', '2', '4', '8', '2', '7', '9', '8', '4', '5', '6', '4', '9'])
noncomputable def fragment0309594Acc00800 : List (String × SourceJson) := (fragment0309594Field007Key00, fragment0309594Field007Value00) :: fragment0309594Acc00700
noncomputable def fragment0309594Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '6', '6', '8', '5', '1', '8', '4', '8', '5', '3', '5', '9', '2', '7', '8', '1', '7', '2', '5', '9', '7', '4', '4', '2', '4', '7', '0', '8', '7', '6', '8', '0', '0', '1', '7', '4', '0', '3', '6', '3', '7', '6', '4', '6', '7', '0', '0', '6', '1', '5', '0', '1', '1', '7', '6', '5', '8', '2', '3', '5', '5', '0', '0', '8', '6', '0', '9', '2', '1', '2', '7', '4', '3', '9', '7', '2', '3', '5', '6', '8', '2', '6', '6', '6', '8', '3', '7', '7', '6', '1', '6', '7', '6', '7', '1', '2', '0', '7', '1', '1', '6', '5', '7', '3', '8', '8', '5', '8', '5', '5', '7', '9', '1', '5', '7', '4', '7', '1', '8', '0', '9', '7', '0', '0', '5', '5', '5', '4', '8', '7', '8', '6', '1', '9', '7', '1', '0', '2', '9', '8', '5', '5', '7', '4', '7', '5', '1', '7', '1', '9', '3', '2', '5', '0', '9', '4', '6', '7', '6', '4', '2', '9', '5', '3', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '0', '3', '8', '9', '5', '6', '5', '2', '4', '9', '9', '5', '6', '7', '4', '9', '3', '7', '9', '5', '6', '0', '7', '8', '1', '7', '1', '9', '1', '7', '9', '4', '9', '1', '5', '5', '6', '4', '2', '2', '6', '0', '2', '5', '4', '6', '2', '6', '3', '1', '2', '6', '9', '9', '8', '2', '4', '8', '4', '1', '0', '7', '7', '6', '7', '9', '8', '5', '3', '2', '5', '7', '0', '2', '5', '2', '5', '5', '8', '5', '0', '9', '2', '8', '8', '9', '8', '6', '0', '5', '7', '6', '8', '9', '6', '1', '4', '6', '3', '7', '7', '0', '7', '7', '1', '4', '1', '5', '6', '8', '5', '9', '8', '1', '4', '5', '9', '1', '2', '7', '4', '9', '0', '3', '9', '7', '3', '9', '4', '2', '6', '1', '7', '6', '6', '1', '1', '3', '5', '0', '9', '3', '5', '0', '6', '9', '7', '9', '1', '5', '5', '6', '6', '9', '5', '8', '9', '8', '0', '7', '2', '8', '5', '6', '6', '5', '3', '9', '7', '9', '4', '9', '5', '5', '2', '5', '3', '0', '5', '2', '7', '5', '0', '3', '9', '0', '6', '0', '0', '2', '4', '8', '2', '7', '9', '8', '4', '5', '6', '4', '9', '"', ',']

theorem object_fragment0309594_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0309594Field007Chars00 ++ tail)) fragment0309594Acc00700 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0309594Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_007"
  err.flush

noncomputable def fragment0309594Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0309594Field008Value00 : SourceJson := .str (String.ofList ['1', '6', '4', '9', '3', '5', '9', '4', '5', '6', '6', '7', '0', '7', '6', '3', '9'])
noncomputable def fragment0309594Acc00900 : List (String × SourceJson) := (fragment0309594Field008Key00, fragment0309594Field008Value00) :: fragment0309594Acc00800
noncomputable def fragment0309594Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '4', '9', '3', '5', '9', '4', '5', '6', '6', '7', '0', '7', '6', '3', '9', '"', ',']

theorem object_fragment0309594_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0309594Field008Chars00 ++ tail)) fragment0309594Acc00800 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0309594Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_008"
  err.flush

noncomputable def fragment0309594Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0309594Field009Value00 : SourceJson := .str (String.ofList ['6', '5', '8', '5', '0', '7', '1', '1', '7', '1', '1', '5', '6', '9', '1', '2', '2'])
noncomputable def fragment0309594Acc01000 : List (String × SourceJson) := (fragment0309594Field009Key00, fragment0309594Field009Value00) :: fragment0309594Acc00900
noncomputable def fragment0309594Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '5', '8', '5', '0', '7', '1', '1', '7', '1', '1', '5', '6', '9', '1', '2', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0309594_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0309594Field009Chars00 ++ tail)) fragment0309594Acc00900 =
      .ok (.obj (fragment0309594Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0309594_object_field_009"
  err.flush

noncomputable def fragment0309594Chars : List Char := '{' :: (fragment0309594Field000Chars00 ++ fragment0309594Field001Chars00 ++ fragment0309594Field002Chars00 ++ fragment0309594Field003Chars00 ++ fragment0309594Field004Chars00 ++ fragment0309594Field005Chars00 ++ fragment0309594Field006Chars00 ++ fragment0309594Field007Chars00 ++ fragment0309594Field008Chars00 ++ fragment0309594Field009Chars00)
noncomputable def fragment0309594Value : SourceJson := .obj (fragment0309594Acc01000.reverse)

theorem value_fragment0309594 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 406) (fragment0309594Chars ++ tail) =
      .ok (fragment0309594Value, tail) := by
  have hinput : fragment0309594Chars ++ tail = '{' :: (fragment0309594Field000Chars00 ++ (fragment0309594Field001Chars00 ++ (fragment0309594Field002Chars00 ++ (fragment0309594Field003Chars00 ++ (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0309594Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 406) (fragment0309594Chars ++ tail) =
        SourceJson.value (fuel + 406) ('{' :: (fragment0309594Field000Chars00 ++ (fragment0309594Field001Chars00 ++ (fragment0309594Field002Chars00 ++ (fragment0309594Field003Chars00 ++ (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 406)) hinput
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0309594Field000Chars00 ++ (fragment0309594Field001Chars00 ++ (fragment0309594Field002Chars00 ++ (fragment0309594Field003Chars00 ++ (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))))))))))) fragment0309594Acc00000 := by rfl
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0309594Field001Chars00 ++ (fragment0309594Field002Chars00 ++ (fragment0309594Field003Chars00 ++ (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail))))))))))) fragment0309594Acc00100 := object_fragment0309594_field_000 fuel (fragment0309594Field001Chars00 ++ (fragment0309594Field002Chars00 ++ (fragment0309594Field003Chars00 ++ (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0309594Field002Chars00 ++ (fragment0309594Field003Chars00 ++ (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))))))))) fragment0309594Acc00200 := object_fragment0309594_field_001 fuel (fragment0309594Field002Chars00 ++ (fragment0309594Field003Chars00 ++ (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0309594Field003Chars00 ++ (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail))))))))) fragment0309594Acc00300 := object_fragment0309594_field_002 fuel (fragment0309594Field003Chars00 ++ (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))))))) fragment0309594Acc00400 := object_fragment0309594_field_003 fuel (fragment0309594Field004Chars00 ++ (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail))))))) fragment0309594Acc00500 := object_fragment0309594_field_004 fuel (fragment0309594Field005Chars00 ++ (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))))) fragment0309594Acc00600 := object_fragment0309594_field_005 fuel (fragment0309594Field006Chars00 ++ (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail))))) fragment0309594Acc00700 := object_fragment0309594_field_006 fuel (fragment0309594Field007Chars00 ++ (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))) fragment0309594Acc00800 := object_fragment0309594_field_007 fuel (fragment0309594Field008Chars00 ++ (fragment0309594Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0309594Field009Chars00 ++ (tail))) fragment0309594Acc00900 := object_fragment0309594_field_008 fuel (fragment0309594Field009Chars00 ++ (tail))
    _ = .ok (fragment0309594Value, tail) := object_fragment0309594_field_009 fuel (tail)

noncomputable def fragment0311558Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0311558Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0311558Field000Value00 : SourceJson := .number (String.ofList ['9', '9'])
noncomputable def fragment0311558Acc00100 : List (String × SourceJson) := (fragment0311558Field000Key00, fragment0311558Field000Value00) :: fragment0311558Acc00000
noncomputable def fragment0311558Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '9', ',']

theorem object_fragment0311558_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0311558Field000Chars00 ++ tail)) fragment0311558Acc00000 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0311558Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_000"
  err.flush

noncomputable def fragment0311558Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0311558Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0311558Acc00200 : List (String × SourceJson) := (fragment0311558Field001Key00, fragment0311558Field001Value00) :: fragment0311558Acc00100
noncomputable def fragment0311558Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0311558_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0311558Field001Chars00 ++ tail)) fragment0311558Acc00100 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0311558Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_001"
  err.flush

noncomputable def fragment0311558Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0311558Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '9', '3', '2', '4', '0', '0', '7', '0', '8', '2', '6', '3', '4', '5', '4', '5', '6', '5', '7', '7', '3', '9', '2', '2', '7', '7', '5', '5', '2', '4', '7', '7', '4', '2', '8', '3', '1', '8', '9', '3', '7', '0', '9', '/', '1', '1', '7', '5', '0', '3', '7', '6', '0', '7', '9', '4', '7', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0311558Acc00300 : List (String × SourceJson) := (fragment0311558Field002Key00, fragment0311558Field002Value00) :: fragment0311558Acc00200
noncomputable def fragment0311558Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '9', '3', '2', '4', '0', '0', '7', '0', '8', '2', '6', '3', '4', '5', '4', '5', '6', '5', '7', '7', '3', '9', '2', '2', '7', '7', '5', '5', '2', '4', '7', '7', '4', '2', '8', '3', '1', '8', '9', '3', '7', '0', '9', '/', '1', '1', '7', '5', '0', '3', '7', '6', '0', '7', '9', '4', '7', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0311558_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0311558Field002Chars00 ++ tail)) fragment0311558Acc00200 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0311558Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_002"
  err.flush

noncomputable def fragment0311558Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0311558Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0311558Acc00400 : List (String × SourceJson) := (fragment0311558Field003Key00, fragment0311558Field003Value00) :: fragment0311558Acc00300
noncomputable def fragment0311558Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0311558_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0311558Field003Chars00 ++ tail)) fragment0311558Acc00300 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0311558Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_003"
  err.flush

noncomputable def fragment0311558Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0311558Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0311558Acc00500 : List (String × SourceJson) := (fragment0311558Field004Key00, fragment0311558Field004Value00) :: fragment0311558Acc00400
noncomputable def fragment0311558Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0311558_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0311558Field004Chars00 ++ tail)) fragment0311558Acc00400 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0311558Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_004"
  err.flush

noncomputable def fragment0311558Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0311558Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '4', '5', '5', '2', '2', '0', '9', '5', '3', '5', '5', '1', '/', '1', '0', '8', '3', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '9', '8', '3', '7', '6', '2', '2', '4', '2', '4', '3', '/', '1', '0', '8', '3', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '9', '7', '3', '0', '2', '6', '2', '9', '8', '1', '/', '5', '6', '5', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '0', '8', '9', '8', '2', '5', '2', '0', '1', '9', '9', '3', '/', '6', '5', '0', '3', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '2', '5', '8', '3', '0', '7', '4', '7', '4', '9', '5', '3', '/', '6', '5', '0', '3', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '2', '6', '5', '5', '2', '5', '4', '9', '7', '3', '/', '8', '4', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '8', '4', '7', '8', '2', '0', '1', '9', '8', '9', '/', '2', '9', '5', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '0', '7', '5', '0', '3', '7', '9', '3', '9', '9', '/', '2', '9', '5', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '4', '6', '8', '5', '2', '9', '3', '7', '1', '9', '/', '2', '9', '5', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '2', '4', '1', '5', '9', '4', '5', '5', '7', '6', '3', '/', '3', '2', '5', '1', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0311558Acc00600 : List (String × SourceJson) := (fragment0311558Field005Key00, fragment0311558Field005Value00) :: fragment0311558Acc00500
noncomputable def fragment0311558Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '5', '5', '2', '2', '0', '9', '5', '3', '5', '5', '1', '/', '1', '0', '8', '3', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '9', '8', '3', '7', '6', '2', '2', '4', '2', '4', '3', '/', '1', '0', '8', '3', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '9', '7', '3', '0', '2', '6', '2', '9', '8', '1', '/', '5', '6', '5', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '0', '8', '9', '8', '2', '5', '2', '0', '1', '9', '9', '3', '/', '6', '5', '0', '3', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '2', '5', '8', '3', '0', '7', '4', '7', '4', '9', '5', '3', '/', '6', '5', '0', '3', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '2', '6', '5', '5', '2', '5', '4', '9', '7', '3', '/', '8', '4', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '8', '4', '7', '8', '2', '0', '1', '9', '8', '9', '/', '2', '9', '5', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '0', '7', '5', '0', '3', '7', '9', '3', '9', '9', '/', '2', '9', '5', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '4', '6', '8', '5', '2', '9', '3', '7', '1', '9', '/', '2', '9', '5', '5', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '2', '4', '1', '5', '9', '4', '5', '5', '7', '6', '3', '/', '3', '2', '5', '1', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0311558_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0311558Field005Chars00 ++ tail)) fragment0311558Acc00500 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0311558Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_005"
  err.flush

noncomputable def fragment0311558Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0311558Field006Value00 : SourceJson := .str (String.ofList ['9', '6', '8', '3', '1', '4', '4', '1', '1', '1', '9', '9', '1', '6', '3', '0', '8', '2', '9', '1', '8', '2', '3', '3', '3', '3', '1', '6', '7', '6', '2', '8', '3', '4', '1', '5', '3', '8', '4', '4', '9', '9', '0', '9', '1', '0', '4', '0', '6', '0', '4', '1', '6', '0', '0', '0', '0', '/', '1', '1', '7', '2', '7', '9', '7', '1', '4', '2', '8', '4', '6', '4', '1', '2', '8', '9', '3', '4', '4', '5', '4', '3', '7', '1', '3', '4', '6', '1', '5', '0', '2', '2', '3', '3', '4', '5', '0', '4', '4', '1', '2', '5', '9', '0', '0', '6', '5', '2', '1', '9', '5', '8', '7', '7', '8', '9', '4', '6', '9', '7', '2', '8', '1', '4', '9', '1', '3', '9'])
noncomputable def fragment0311558Acc00700 : List (String × SourceJson) := (fragment0311558Field006Key00, fragment0311558Field006Value00) :: fragment0311558Acc00600
noncomputable def fragment0311558Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '6', '8', '3', '1', '4', '4', '1', '1', '1', '9', '9', '1', '6', '3', '0', '8', '2', '9', '1', '8', '2', '3', '3', '3', '3', '1', '6', '7', '6', '2', '8', '3', '4', '1', '5', '3', '8', '4', '4', '9', '9', '0', '9', '1', '0', '4', '0', '6', '0', '4', '1', '6', '0', '0', '0', '0', '/', '1', '1', '7', '2', '7', '9', '7', '1', '4', '2', '8', '4', '6', '4', '1', '2', '8', '9', '3', '4', '4', '5', '4', '3', '7', '1', '3', '4', '6', '1', '5', '0', '2', '2', '3', '3', '4', '5', '0', '4', '4', '1', '2', '5', '9', '0', '0', '6', '5', '2', '1', '9', '5', '8', '7', '7', '8', '9', '4', '6', '9', '7', '2', '8', '1', '4', '9', '1', '3', '9', '"', ',']

theorem object_fragment0311558_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0311558Field006Chars00 ++ tail)) fragment0311558Acc00600 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0311558Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_006"
  err.flush

noncomputable def fragment0311558Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0311558Field007Value00 : SourceJson := .str (String.ofList ['2', '0', '4', '7', '9', '8', '2', '0', '3', '5', '2', '9', '5', '2', '8', '1', '1', '5', '6', '4', '2', '6', '5', '4', '1', '9', '3', '5', '7', '6', '8', '4', '0', '5', '1', '5', '8', '8', '2', '3', '4', '4', '0', '5', '1', '3', '1', '7', '2', '5', '5', '6', '8', '2', '4', '3', '1', '3', '6', '8', '3', '3', '1', '3', '3', '0', '0', '0', '3', '2', '5', '6', '8', '7', '7', '7', '6', '7', '3', '5', '2', '0', '3', '7', '8', '4', '7', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '0', '2', '4', '4', '6', '2', '5', '2', '6', '3', '9', '3', '5', '5', '1', '1', '1', '3', '4', '8', '4', '3', '1', '3', '9', '7', '5', '4', '1', '9', '2', '1', '0', '8', '7', '8', '5', '9', '9', '9', '0', '1', '5', '4', '4', '4', '7', '1', '0', '1', '0', '0', '6', '2', '1', '5', '9', '8', '1', '7', '4', '8', '9', '2', '1', '7', '2', '6', '0', '7', '3', '1', '5', '6', '6', '1', '1', '7', '1', '5', '0', '5', '1', '5', '5', '8', '3', '7', '7', '6', '3', '4', '1', '9', '2', '2', '6', '1', '6', '9', '7', '4', '3', '0', '8', '0', '9', '0', '3', '2', '4', '2', '5', '9', '0', '3', '2', '5', '9', '2', '4', '7', '0', '3'])
noncomputable def fragment0311558Acc00800 : List (String × SourceJson) := (fragment0311558Field007Key00, fragment0311558Field007Value00) :: fragment0311558Acc00700
noncomputable def fragment0311558Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '0', '4', '7', '9', '8', '2', '0', '3', '5', '2', '9', '5', '2', '8', '1', '1', '5', '6', '4', '2', '6', '5', '4', '1', '9', '3', '5', '7', '6', '8', '4', '0', '5', '1', '5', '8', '8', '2', '3', '4', '4', '0', '5', '1', '3', '1', '7', '2', '5', '5', '6', '8', '2', '4', '3', '1', '3', '6', '8', '3', '3', '1', '3', '3', '0', '0', '0', '3', '2', '5', '6', '8', '7', '7', '7', '6', '7', '3', '5', '2', '0', '3', '7', '8', '4', '7', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '0', '2', '4', '4', '6', '2', '5', '2', '6', '3', '9', '3', '5', '5', '1', '1', '1', '3', '4', '8', '4', '3', '1', '3', '9', '7', '5', '4', '1', '9', '2', '1', '0', '8', '7', '8', '5', '9', '9', '9', '0', '1', '5', '4', '4', '4', '7', '1', '0', '1', '0', '0', '6', '2', '1', '5', '9', '8', '1', '7', '4', '8', '9', '2', '1', '7', '2', '6', '0', '7', '3', '1', '5', '6', '6', '1', '1', '7', '1', '5', '0', '5', '1', '5', '5', '8', '3', '7', '7', '6', '3', '4', '1', '9', '2', '2', '6', '1', '6', '9', '7', '4', '3', '0', '8', '0', '9', '0', '3', '2', '4', '2', '5', '9', '0', '3', '2', '5', '9', '2', '4', '7', '0', '3', '"', ',']

theorem object_fragment0311558_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0311558Field007Chars00 ++ tail)) fragment0311558Acc00700 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0311558Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_007"
  err.flush

noncomputable def fragment0311558Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0311558Field008Value00 : SourceJson := .str (String.ofList ['6', '5', '4', '1', '4', '3', '5', '7', '4', '6', '4', '4', '0', '7', '8', '7', '3'])
noncomputable def fragment0311558Acc00900 : List (String × SourceJson) := (fragment0311558Field008Key00, fragment0311558Field008Value00) :: fragment0311558Acc00800
noncomputable def fragment0311558Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '5', '4', '1', '4', '3', '5', '7', '4', '6', '4', '4', '0', '7', '8', '7', '3', '"', ',']

theorem object_fragment0311558_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0311558Field008Chars00 ++ tail)) fragment0311558Acc00800 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0311558Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_008"
  err.flush

noncomputable def fragment0311558Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0311558Field009Value00 : SourceJson := .str (String.ofList ['3', '2', '2', '9', '3', '5', '7', '4', '2', '2', '1', '3', '8', '7', '1', '1', '8', '7'])
noncomputable def fragment0311558Acc01000 : List (String × SourceJson) := (fragment0311558Field009Key00, fragment0311558Field009Value00) :: fragment0311558Acc00900
noncomputable def fragment0311558Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '2', '9', '3', '5', '7', '4', '2', '2', '1', '3', '8', '7', '1', '1', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0311558_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0311558Field009Chars00 ++ tail)) fragment0311558Acc00900 =
      .ok (.obj (fragment0311558Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0311558_object_field_009"
  err.flush

noncomputable def fragment0311558Chars : List Char := '{' :: (fragment0311558Field000Chars00 ++ fragment0311558Field001Chars00 ++ fragment0311558Field002Chars00 ++ fragment0311558Field003Chars00 ++ fragment0311558Field004Chars00 ++ fragment0311558Field005Chars00 ++ fragment0311558Field006Chars00 ++ fragment0311558Field007Chars00 ++ fragment0311558Field008Chars00 ++ fragment0311558Field009Chars00)
noncomputable def fragment0311558Value : SourceJson := .obj (fragment0311558Acc01000.reverse)

theorem value_fragment0311558 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 251) (fragment0311558Chars ++ tail) =
      .ok (fragment0311558Value, tail) := by
  have hinput : fragment0311558Chars ++ tail = '{' :: (fragment0311558Field000Chars00 ++ (fragment0311558Field001Chars00 ++ (fragment0311558Field002Chars00 ++ (fragment0311558Field003Chars00 ++ (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0311558Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 251) (fragment0311558Chars ++ tail) =
        SourceJson.value (fuel + 251) ('{' :: (fragment0311558Field000Chars00 ++ (fragment0311558Field001Chars00 ++ (fragment0311558Field002Chars00 ++ (fragment0311558Field003Chars00 ++ (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 251)) hinput
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0311558Field000Chars00 ++ (fragment0311558Field001Chars00 ++ (fragment0311558Field002Chars00 ++ (fragment0311558Field003Chars00 ++ (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))))))))))) fragment0311558Acc00000 := by rfl
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0311558Field001Chars00 ++ (fragment0311558Field002Chars00 ++ (fragment0311558Field003Chars00 ++ (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail))))))))))) fragment0311558Acc00100 := object_fragment0311558_field_000 fuel (fragment0311558Field001Chars00 ++ (fragment0311558Field002Chars00 ++ (fragment0311558Field003Chars00 ++ (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0311558Field002Chars00 ++ (fragment0311558Field003Chars00 ++ (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))))))))) fragment0311558Acc00200 := object_fragment0311558_field_001 fuel (fragment0311558Field002Chars00 ++ (fragment0311558Field003Chars00 ++ (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0311558Field003Chars00 ++ (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail))))))))) fragment0311558Acc00300 := object_fragment0311558_field_002 fuel (fragment0311558Field003Chars00 ++ (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))))))) fragment0311558Acc00400 := object_fragment0311558_field_003 fuel (fragment0311558Field004Chars00 ++ (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail))))))) fragment0311558Acc00500 := object_fragment0311558_field_004 fuel (fragment0311558Field005Chars00 ++ (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))))) fragment0311558Acc00600 := object_fragment0311558_field_005 fuel (fragment0311558Field006Chars00 ++ (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail))))) fragment0311558Acc00700 := object_fragment0311558_field_006 fuel (fragment0311558Field007Chars00 ++ (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))) fragment0311558Acc00800 := object_fragment0311558_field_007 fuel (fragment0311558Field008Chars00 ++ (fragment0311558Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0311558Field009Chars00 ++ (tail))) fragment0311558Acc00900 := object_fragment0311558_field_008 fuel (fragment0311558Field009Chars00 ++ (tail))
    _ = .ok (fragment0311558Value, tail) := object_fragment0311558_field_009 fuel (tail)

noncomputable def fragment0313219Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0313219Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0313219Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '0'])
noncomputable def fragment0313219Acc00100 : List (String × SourceJson) := (fragment0313219Field000Key00, fragment0313219Field000Value00) :: fragment0313219Acc00000
noncomputable def fragment0313219Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '0', ',']

theorem object_fragment0313219_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment0313219Field000Chars00 ++ tail)) fragment0313219Acc00000 =
      SourceJson.object (fuel + 469) (SourceJson.white tail) fragment0313219Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_000"
  err.flush

noncomputable def fragment0313219Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0313219Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0313219Acc00200 : List (String × SourceJson) := (fragment0313219Field001Key00, fragment0313219Field001Value00) :: fragment0313219Acc00100
noncomputable def fragment0313219Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0313219_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 469) (SourceJson.white (fragment0313219Field001Chars00 ++ tail)) fragment0313219Acc00100 =
      SourceJson.object (fuel + 468) (SourceJson.white tail) fragment0313219Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_001"
  err.flush

noncomputable def fragment0313219Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0313219Field002Value00 : SourceJson := .str (String.ofList ['6', '1', '0', '8', '1', '9', '0', '3', '6', '9', '5', '8', '5', '0', '5', '4', '4', '4', '2', '7', '1', '1', '4', '3', '7', '1', '5', '8', '1', '9', '9', '5', '2', '5', '8', '2', '7', '5', '9', '7', '1', '/', '9', '9', '4', '9', '7', '0', '1', '9', '6', '7', '3', '7', '3', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0313219Acc00300 : List (String × SourceJson) := (fragment0313219Field002Key00, fragment0313219Field002Value00) :: fragment0313219Acc00200
noncomputable def fragment0313219Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '1', '0', '8', '1', '9', '0', '3', '6', '9', '5', '8', '5', '0', '5', '4', '4', '4', '2', '7', '1', '1', '4', '3', '7', '1', '5', '8', '1', '9', '9', '5', '2', '5', '8', '2', '7', '5', '9', '7', '1', '/', '9', '9', '4', '9', '7', '0', '1', '9', '6', '7', '3', '7', '3', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0313219_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 468) (SourceJson.white (fragment0313219Field002Chars00 ++ tail)) fragment0313219Acc00200 =
      SourceJson.object (fuel + 467) (SourceJson.white tail) fragment0313219Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_002"
  err.flush

noncomputable def fragment0313219Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0313219Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0313219Acc00400 : List (String × SourceJson) := (fragment0313219Field003Key00, fragment0313219Field003Value00) :: fragment0313219Acc00300
noncomputable def fragment0313219Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0313219_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 467) (SourceJson.white (fragment0313219Field003Chars00 ++ tail)) fragment0313219Acc00300 =
      SourceJson.object (fuel + 466) (SourceJson.white tail) fragment0313219Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_003"
  err.flush

noncomputable def fragment0313219Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0313219Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0313219Acc00500 : List (String × SourceJson) := (fragment0313219Field004Key00, fragment0313219Field004Value00) :: fragment0313219Acc00400
noncomputable def fragment0313219Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0313219_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 466) (SourceJson.white (fragment0313219Field004Chars00 ++ tail)) fragment0313219Acc00400 =
      SourceJson.object (fuel + 465) (SourceJson.white tail) fragment0313219Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_004"
  err.flush

noncomputable def fragment0313219Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0313219Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '2', '7', '7', '3', '3', '8', '7', '3', '4', '7', '4', '5', '7', '9', '1', '4', '9', '1', '1', '0', '8', '0', '9', '5', '1', '/', '1', '5', '0', '0', '0', '7', '1', '1', '9', '8', '7', '7', '0', '1', '5', '2', '1', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '7', '5', '4', '7', '9', '7', '2', '9', '1', '6', '6', '2', '1', '4', '1', '4', '9', '8', '3', '5', '3', '/', '4', '9', '8', '3', '6', '2', '5', '2', '4', '5', '0', '8', '3', '5', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '9', '6', '8', '1', '9', '8', '3', '0', '5', '3', '8', '4', '2', '0', '0', '3', '8', '1', '4', '2', '3', '/', '1', '3', '0', '4', '4', '0', '9', '7', '3', '8', '0', '6', '1', '0', '0', '1', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '3', '5', '0', '4', '7', '8', '5', '1', '1', '8', '6', '7', '5', '1', '2', '5', '4', '5', '3', '1', '4', '3', '/', '2', '5', '0', '0', '1', '1', '8', '6', '6', '4', '6', '1', '6', '9', '2', '0', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '1', '5', '3', '7', '1', '2', '1', '1', '8', '5', '8', '9', '1', '2', '2', '7', '2', '9', '4', '3', '0', '3', '/', '2', '5', '0', '0', '1', '1', '8', '6', '6', '4', '6', '1', '6', '9', '2', '0', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '3', '2', '4', '6', '3', '4', '2', '6', '4', '6', '9', '5', '0', '7', '7', '8', '8', '9', '5', '4', '6', '1', '/', '1', '3', '6', '3', '7', '0', '1', '0', '8', '9', '7', '9', '1', '0', '4', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '3', '8', '5', '8', '1', '3', '6', '9', '6', '8', '7', '5', '4', '5', '1', '0', '8', '4', '0', '1', '5', '9', '/', '6', '8', '1', '8', '5', '0', '5', '4', '4', '8', '9', '5', '5', '2', '3', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '3', '3', '5', '5', '2', '0', '5', '1', '3', '2', '3', '7', '5', '8', '1', '7', '4', '7', '7', '4', '6', '3', '/', '1', '3', '6', '3', '7', '0', '1', '0', '8', '9', '7', '9', '1', '0', '4', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '5', '9', '4', '3', '7', '4', '6', '6', '3', '8', '5', '5', '2', '3', '0', '4', '9', '4', '7', '1', '0', '3', '/', '1', '3', '6', '3', '7', '0', '1', '0', '8', '9', '7', '9', '1', '0', '4', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '3', '0', '9', '8', '7', '9', '8', '4', '4', '2', '4', '1', '3', '8', '4', '7', '6', '4', '9', '1', '/', '4', '9', '8', '3', '6', '2', '5', '2', '4', '5', '0', '8', '3', '5', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0313219Acc00600 : List (String × SourceJson) := (fragment0313219Field005Key00, fragment0313219Field005Value00) :: fragment0313219Acc00500
noncomputable def fragment0313219Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '7', '3', '3', '8', '7', '3', '4', '7', '4', '5', '7', '9', '1', '4', '9', '1', '1', '0', '8', '0', '9', '5', '1', '/', '1', '5', '0', '0', '0', '7', '1', '1', '9', '8', '7', '7', '0', '1', '5', '2', '1', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '7', '5', '4', '7', '9', '7', '2', '9', '1', '6', '6', '2', '1', '4', '1', '4', '9', '8', '3', '5', '3', '/', '4', '9', '8', '3', '6', '2', '5', '2', '4', '5', '0', '8', '3', '5', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '9', '6', '8', '1', '9', '8', '3', '0', '5', '3', '8', '4', '2', '0', '0', '3', '8', '1', '4', '2', '3', '/', '1', '3', '0', '4', '4', '0', '9', '7', '3', '8', '0', '6', '1', '0', '0', '1', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '3', '5', '0', '4', '7', '8', '5', '1', '1', '8', '6', '7', '5', '1', '2', '5', '4', '5', '3', '1', '4', '3', '/', '2', '5', '0', '0', '1', '1', '8', '6', '6', '4', '6', '1', '6', '9', '2', '0', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '1', '5', '3', '7', '1', '2', '1', '1', '8', '5', '8', '9', '1', '2', '2', '7', '2', '9', '4', '3', '0', '3', '/', '2', '5', '0', '0', '1', '1', '8', '6', '6', '4', '6', '1', '6', '9', '2', '0', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '3', '2', '4', '6', '3', '4', '2', '6', '4', '6', '9', '5', '0', '7', '7', '8', '8', '9', '5', '4', '6', '1', '/', '1', '3', '6', '3', '7', '0', '1', '0', '8', '9', '7', '9', '1', '0', '4', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '3', '8', '5', '8', '1', '3', '6', '9', '6', '8', '7', '5', '4', '5', '1', '0', '8', '4', '0', '1', '5', '9', '/', '6', '8', '1', '8', '5', '0', '5', '4', '4', '8', '9', '5', '5', '2', '3', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '3', '3', '5', '5', '2', '0', '5', '1', '3', '2', '3', '7', '5', '8', '1', '7', '4', '7', '7', '4', '6', '3', '/', '1', '3', '6', '3', '7', '0', '1', '0', '8', '9', '7', '9', '1', '0', '4', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '5', '9', '4', '3', '7', '4', '6', '6', '3', '8', '5', '5', '2', '3', '0', '4', '9', '4', '7', '1', '0', '3', '/', '1', '3', '6', '3', '7', '0', '1', '0', '8', '9', '7', '9', '1', '0', '4', '7', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '3', '0', '9', '8', '7', '9', '8', '4', '4', '2', '4', '1', '3', '8', '4', '7', '6', '4', '9', '1', '/', '4', '9', '8', '3', '6', '2', '5', '2', '4', '5', '0', '8', '3', '5', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0313219_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 465) (SourceJson.white (fragment0313219Field005Chars00 ++ tail)) fragment0313219Acc00500 =
      SourceJson.object (fuel + 464) (SourceJson.white tail) fragment0313219Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_005"
  err.flush

noncomputable def fragment0313219Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0313219Field006Value00 : SourceJson := .str (String.ofList ['6', '3', '8', '5', '9', '2', '9', '8', '8', '7', '1', '6', '5', '1', '7', '4', '0', '2', '1', '6', '0', '5', '2', '5', '0', '2', '6', '5', '4', '1', '9', '1', '6', '4', '0', '1', '6', '0', '6', '1', '5', '6', '4', '9', '6', '6', '7', '3', '7', '5', '/', '2', '0', '5', '7', '6', '7', '0', '2', '3', '5', '7', '0', '0', '1', '5', '0', '1', '8', '6', '6', '3', '7', '4', '8', '4', '4', '9', '1', '8', '1', '9', '5', '3', '9', '7', '2', '0', '8', '3', '4', '0', '1', '0', '6', '6', '1', '4', '1', '8', '7', '5', '9', '7', '2', '0', '8', '8', '9', '3', '5', '0', '6', '0', '4'])
noncomputable def fragment0313219Acc00700 : List (String × SourceJson) := (fragment0313219Field006Key00, fragment0313219Field006Value00) :: fragment0313219Acc00600
noncomputable def fragment0313219Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '3', '8', '5', '9', '2', '9', '8', '8', '7', '1', '6', '5', '1', '7', '4', '0', '2', '1', '6', '0', '5', '2', '5', '0', '2', '6', '5', '4', '1', '9', '1', '6', '4', '0', '1', '6', '0', '6', '1', '5', '6', '4', '9', '6', '6', '7', '3', '7', '5', '/', '2', '0', '5', '7', '6', '7', '0', '2', '3', '5', '7', '0', '0', '1', '5', '0', '1', '8', '6', '6', '3', '7', '4', '8', '4', '4', '9', '1', '8', '1', '9', '5', '3', '9', '7', '2', '0', '8', '3', '4', '0', '1', '0', '6', '6', '1', '4', '1', '8', '7', '5', '9', '7', '2', '0', '8', '8', '9', '3', '5', '0', '6', '0', '4', '"', ',']

theorem object_fragment0313219_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 464) (SourceJson.white (fragment0313219Field006Chars00 ++ tail)) fragment0313219Acc00600 =
      SourceJson.object (fuel + 463) (SourceJson.white tail) fragment0313219Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_006"
  err.flush

noncomputable def fragment0313219Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0313219Field007Value00 : SourceJson := .str (String.ofList ['1', '4', '9', '6', '4', '7', '4', '0', '9', '8', '7', '6', '9', '1', '6', '3', '6', '1', '0', '7', '8', '1', '4', '1', '4', '0', '1', '2', '0', '9', '7', '7', '8', '5', '5', '5', '5', '2', '3', '9', '2', '3', '6', '6', '7', '8', '2', '0', '1', '2', '6', '3', '6', '0', '0', '7', '5', '3', '5', '9', '1', '0', '9', '5', '4', '6', '6', '9', '2', '1', '2', '7', '0', '5', '2', '6', '1', '0', '8', '6', '2', '0', '6', '2', '5', '6', '8', '0', '0', '8', '4', '4', '4', '8', '1', '0', '0', '6', '9', '3', '4', '2', '5', '8', '0', '3', '9', '6', '6', '6', '2', '3', '7', '1', '0', '9', '9', '7', '9', '6', '9', '8', '6', '0', '0', '2', '6', '7', '6', '4', '1', '4', '4', '2', '5', '4', '9', '8', '6', '4', '4', '0', '6', '4', '2', '4', '6', '5', '0', '7', '3', '9', '6', '2', '6', '4', '9', '3', '3', '6', '2', '5', '2', '7', '7', '2', '8', '1', '5', '8', '5', '4', '7', '6', '8', '1', '0', '4', '4', '9', '0', '3', '4', '9', '7', '0', '2', '5', '0', '3', '2', '7', '0', '4', '9', '1', '3', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '4', '5', '4', '4', '0', '0', '2', '3', '3', '5', '7', '9', '8', '3', '7', '8', '1', '0', '5', '4', '0', '7', '7', '0', '5', '1', '6', '8', '3', '5', '7', '2', '1', '6', '0', '8', '4', '7', '1', '1', '8', '4', '3', '7', '3', '9', '3', '5', '3', '2', '8', '1', '4', '4', '3', '8', '6', '9', '6', '6', '4', '5', '7', '7', '1', '0', '4', '9', '6', '2', '2', '4', '8', '1', '5', '2', '8', '7', '8', '1', '9', '9', '5', '4', '6', '0', '5', '5', '7', '7', '4', '9', '7', '8', '5', '5', '0', '6', '4', '3', '5', '6', '4', '4', '9', '2', '3', '9', '0', '1', '0', '1', '1', '9', '1', '7', '0', '3', '6', '6', '1', '7', '6', '2', '4', '0', '9', '0', '9', '9', '1', '8', '8', '4', '8', '9', '5', '7', '5', '0', '7', '1', '1', '1', '3', '9', '4', '5', '4', '3', '1', '2', '3', '7', '5', '3', '8', '5', '7', '1', '6', '9', '7', '8', '1', '8', '8', '1', '5', '7', '8', '9', '2', '5', '0', '9', '8', '8', '7', '2', '9', '6', '7', '8', '7', '0', '1', '4', '8', '9', '0', '2', '3', '7', '8', '5', '2', '2', '8', '0', '8', '5', '4', '6', '3', '0', '4', '9', '5', '6', '3', '2', '3', '3', '4', '7', '3', '1', '2', '4', '8', '3', '6', '3', '3', '7', '8', '8', '4', '4', '6', '7', '7', '9'])
noncomputable def fragment0313219Acc00800 : List (String × SourceJson) := (fragment0313219Field007Key00, fragment0313219Field007Value00) :: fragment0313219Acc00700
noncomputable def fragment0313219Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '9', '6', '4', '7', '4', '0', '9', '8', '7', '6', '9', '1', '6', '3', '6', '1', '0', '7', '8', '1', '4', '1', '4', '0', '1', '2', '0', '9', '7', '7', '8', '5', '5', '5', '5', '2', '3', '9', '2', '3', '6', '6', '7', '8', '2', '0', '1', '2', '6', '3', '6', '0', '0', '7', '5', '3', '5', '9', '1', '0', '9', '5', '4', '6', '6', '9', '2', '1', '2', '7', '0', '5', '2', '6', '1', '0', '8', '6', '2', '0', '6', '2', '5', '6', '8', '0', '0', '8', '4', '4', '4', '8', '1', '0', '0', '6', '9', '3', '4', '2', '5', '8', '0', '3', '9', '6', '6', '6', '2', '3', '7', '1', '0', '9', '9', '7', '9', '6', '9', '8', '6', '0', '0', '2', '6', '7', '6', '4', '1', '4', '4', '2', '5', '4', '9', '8', '6', '4', '4', '0', '6', '4', '2', '4', '6', '5', '0', '7', '3', '9', '6', '2', '6', '4', '9', '3', '3', '6', '2', '5', '2', '7', '7', '2', '8', '1', '5', '8', '5', '4', '7', '6', '8', '1', '0', '4', '4', '9', '0', '3', '4', '9', '7', '0', '2', '5', '0', '3', '2', '7', '0', '4', '9', '1', '3', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '4', '5', '4', '4', '0', '0', '2', '3', '3', '5', '7', '9', '8', '3', '7', '8', '1', '0', '5', '4', '0', '7', '7', '0', '5', '1', '6', '8', '3', '5', '7', '2', '1', '6', '0', '8', '4', '7', '1', '1', '8', '4', '3', '7', '3', '9', '3', '5', '3', '2', '8', '1', '4', '4', '3', '8', '6', '9', '6', '6', '4', '5', '7', '7', '1', '0', '4', '9', '6', '2', '2', '4', '8', '1', '5', '2', '8', '7', '8', '1', '9', '9', '5', '4', '6', '0', '5', '5', '7', '7', '4', '9', '7', '8', '5', '5', '0', '6', '4', '3', '5', '6', '4', '4', '9', '2', '3', '9', '0', '1', '0', '1', '1', '9', '1', '7', '0', '3', '6', '6', '1', '7', '6', '2', '4', '0', '9', '0', '9', '9', '1', '8', '8', '4', '8', '9', '5', '7', '5', '0', '7', '1', '1', '1', '3', '9', '4', '5', '4', '3', '1', '2', '3', '7', '5', '3', '8', '5', '7', '1', '6', '9', '7', '8', '1', '8', '8', '1', '5', '7', '8', '9', '2', '5', '0', '9', '8', '8', '7', '2', '9', '6', '7', '8', '7', '0', '1', '4', '8', '9', '0', '2', '3', '7', '8', '5', '2', '2', '8', '0', '8', '5', '4', '6', '3', '0', '4', '9', '5', '6', '3', '2', '3', '3', '4', '7', '3', '1', '2', '4', '8', '3', '6', '3', '3', '7', '8', '8', '4', '4', '6', '7', '7', '9', '"', ',']

theorem object_fragment0313219_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 463) (SourceJson.white (fragment0313219Field007Chars00 ++ tail)) fragment0313219Acc00700 =
      SourceJson.object (fuel + 462) (SourceJson.white tail) fragment0313219Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_007"
  err.flush

noncomputable def fragment0313219Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0313219Field008Value00 : SourceJson := .str (String.ofList ['2', '4', '5', '8', '8', '2', '6', '8', '9', '1', '3', '4', '0', '3', '6', '7'])
noncomputable def fragment0313219Acc00900 : List (String × SourceJson) := (fragment0313219Field008Key00, fragment0313219Field008Value00) :: fragment0313219Acc00800
noncomputable def fragment0313219Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '5', '8', '8', '2', '6', '8', '9', '1', '3', '4', '0', '3', '6', '7', '"', ',']

theorem object_fragment0313219_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 462) (SourceJson.white (fragment0313219Field008Chars00 ++ tail)) fragment0313219Acc00800 =
      SourceJson.object (fuel + 461) (SourceJson.white tail) fragment0313219Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_008"
  err.flush

noncomputable def fragment0313219Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0313219Field009Value00 : SourceJson := .str (String.ofList ['6', '4', '2', '4', '6', '4', '0', '8', '2', '2', '5', '1', '4', '0', '8', '8'])
noncomputable def fragment0313219Acc01000 : List (String × SourceJson) := (fragment0313219Field009Key00, fragment0313219Field009Value00) :: fragment0313219Acc00900
noncomputable def fragment0313219Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '4', '2', '4', '6', '4', '0', '8', '2', '2', '5', '1', '4', '0', '8', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0313219_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 461) (SourceJson.white (fragment0313219Field009Chars00 ++ tail)) fragment0313219Acc00900 =
      .ok (.obj (fragment0313219Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0313219_object_field_009"
  err.flush

noncomputable def fragment0313219Chars : List Char := '{' :: (fragment0313219Field000Chars00 ++ fragment0313219Field001Chars00 ++ fragment0313219Field002Chars00 ++ fragment0313219Field003Chars00 ++ fragment0313219Field004Chars00 ++ fragment0313219Field005Chars00 ++ fragment0313219Field006Chars00 ++ fragment0313219Field007Chars00 ++ fragment0313219Field008Chars00 ++ fragment0313219Field009Chars00)
noncomputable def fragment0313219Value : SourceJson := .obj (fragment0313219Acc01000.reverse)

theorem value_fragment0313219 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 471) (fragment0313219Chars ++ tail) =
      .ok (fragment0313219Value, tail) := by
  have hinput : fragment0313219Chars ++ tail = '{' :: (fragment0313219Field000Chars00 ++ (fragment0313219Field001Chars00 ++ (fragment0313219Field002Chars00 ++ (fragment0313219Field003Chars00 ++ (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0313219Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 471) (fragment0313219Chars ++ tail) =
        SourceJson.value (fuel + 471) ('{' :: (fragment0313219Field000Chars00 ++ (fragment0313219Field001Chars00 ++ (fragment0313219Field002Chars00 ++ (fragment0313219Field003Chars00 ++ (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 471)) hinput
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment0313219Field000Chars00 ++ (fragment0313219Field001Chars00 ++ (fragment0313219Field002Chars00 ++ (fragment0313219Field003Chars00 ++ (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))))))))))) fragment0313219Acc00000 := by rfl
    _ = SourceJson.object (fuel + 469) (SourceJson.white (fragment0313219Field001Chars00 ++ (fragment0313219Field002Chars00 ++ (fragment0313219Field003Chars00 ++ (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail))))))))))) fragment0313219Acc00100 := object_fragment0313219_field_000 fuel (fragment0313219Field001Chars00 ++ (fragment0313219Field002Chars00 ++ (fragment0313219Field003Chars00 ++ (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 468) (SourceJson.white (fragment0313219Field002Chars00 ++ (fragment0313219Field003Chars00 ++ (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))))))))) fragment0313219Acc00200 := object_fragment0313219_field_001 fuel (fragment0313219Field002Chars00 ++ (fragment0313219Field003Chars00 ++ (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 467) (SourceJson.white (fragment0313219Field003Chars00 ++ (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail))))))))) fragment0313219Acc00300 := object_fragment0313219_field_002 fuel (fragment0313219Field003Chars00 ++ (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 466) (SourceJson.white (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))))))) fragment0313219Acc00400 := object_fragment0313219_field_003 fuel (fragment0313219Field004Chars00 ++ (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 465) (SourceJson.white (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail))))))) fragment0313219Acc00500 := object_fragment0313219_field_004 fuel (fragment0313219Field005Chars00 ++ (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 464) (SourceJson.white (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))))) fragment0313219Acc00600 := object_fragment0313219_field_005 fuel (fragment0313219Field006Chars00 ++ (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 463) (SourceJson.white (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail))))) fragment0313219Acc00700 := object_fragment0313219_field_006 fuel (fragment0313219Field007Chars00 ++ (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 462) (SourceJson.white (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))) fragment0313219Acc00800 := object_fragment0313219_field_007 fuel (fragment0313219Field008Chars00 ++ (fragment0313219Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 461) (SourceJson.white (fragment0313219Field009Chars00 ++ (tail))) fragment0313219Acc00900 := object_fragment0313219_field_008 fuel (fragment0313219Field009Chars00 ++ (tail))
    _ = .ok (fragment0313219Value, tail) := object_fragment0313219_field_009 fuel (tail)

noncomputable def fragment0315298Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0315298Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0315298Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '1'])
noncomputable def fragment0315298Acc00100 : List (String × SourceJson) := (fragment0315298Field000Key00, fragment0315298Field000Value00) :: fragment0315298Acc00000
noncomputable def fragment0315298Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '1', ',']

theorem object_fragment0315298_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0315298Field000Chars00 ++ tail)) fragment0315298Acc00000 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0315298Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_000"
  err.flush

noncomputable def fragment0315298Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0315298Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0315298Acc00200 : List (String × SourceJson) := (fragment0315298Field001Key00, fragment0315298Field001Value00) :: fragment0315298Acc00100
noncomputable def fragment0315298Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0315298_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0315298Field001Chars00 ++ tail)) fragment0315298Acc00100 =
      SourceJson.object (fuel + 405) (SourceJson.white tail) fragment0315298Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_001"
  err.flush

noncomputable def fragment0315298Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0315298Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '1', '7', '4', '1', '3', '1', '9', '3', '8', '5', '9', '7', '4', '1', '9', '7', '9', '5', '3', '2', '9', '5', '2', '1', '7', '3', '1', '2', '3', '3', '3', '4', '2', '2', '5', '2', '7', '0', '9', '3', '/', '1', '3', '8', '8', '3', '3', '0', '5', '0', '7', '0', '7', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0315298Acc00300 : List (String × SourceJson) := (fragment0315298Field002Key00, fragment0315298Field002Value00) :: fragment0315298Acc00200
noncomputable def fragment0315298Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '1', '7', '4', '1', '3', '1', '9', '3', '8', '5', '9', '7', '4', '1', '9', '7', '9', '5', '3', '2', '9', '5', '2', '1', '7', '3', '1', '2', '3', '3', '3', '4', '2', '2', '5', '2', '7', '0', '9', '3', '/', '1', '3', '8', '8', '3', '3', '0', '5', '0', '7', '0', '7', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0315298_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0315298Field002Chars00 ++ tail)) fragment0315298Acc00200 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0315298Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_002"
  err.flush

noncomputable def fragment0315298Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0315298Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0315298Acc00400 : List (String × SourceJson) := (fragment0315298Field003Key00, fragment0315298Field003Value00) :: fragment0315298Acc00300
noncomputable def fragment0315298Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0315298_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0315298Field003Chars00 ++ tail)) fragment0315298Acc00300 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0315298Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_003"
  err.flush

noncomputable def fragment0315298Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0315298Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0315298Acc00500 : List (String × SourceJson) := (fragment0315298Field004Key00, fragment0315298Field004Value00) :: fragment0315298Acc00400
noncomputable def fragment0315298Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0315298_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0315298Field004Chars00 ++ tail)) fragment0315298Acc00400 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0315298Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_004"
  err.flush

noncomputable def fragment0315298Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0315298Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '6', '6', '5', '3', '0', '7', '7', '8', '3', '6', '9', '4', '4', '0', '8', '4', '4', '0', '0', '3', '9', '/', '5', '4', '3', '8', '6', '1', '0', '0', '2', '6', '0', '1', '3', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '1', '9', '7', '2', '0', '9', '0', '9', '1', '3', '9', '9', '7', '6', '6', '7', '2', '1', '1', '/', '7', '7', '6', '9', '4', '4', '2', '8', '9', '4', '3', '0', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '1', '9', '1', '2', '1', '9', '8', '9', '8', '3', '9', '3', '5', '1', '2', '6', '1', '9', '/', '2', '3', '6', '4', '6', '1', '3', '0', '5', '4', '7', '8', '8', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '3', '5', '6', '1', '1', '0', '4', '4', '2', '2', '7', '6', '4', '6', '2', '0', '1', '0', '3', '/', '6', '0', '4', '2', '9', '0', '0', '0', '2', '8', '9', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '6', '7', '5', '0', '3', '1', '2', '5', '8', '5', '9', '1', '0', '7', '1', '3', '2', '3', '8', '9', '/', '1', '8', '1', '2', '8', '7', '0', '0', '0', '8', '6', '7', '1', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '4', '8', '8', '5', '1', '3', '9', '4', '4', '5', '3', '3', '5', '0', '6', '1', '3', '1', '/', '1', '2', '3', '6', '0', '4', '7', '7', '3', '3', '1', '8', '4', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '4', '0', '8', '2', '6', '6', '7', '0', '9', '6', '0', '1', '4', '2', '4', '6', '1', '9', '7', '/', '4', '9', '4', '4', '1', '9', '0', '9', '3', '2', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '4', '5', '7', '3', '0', '9', '1', '9', '2', '4', '3', '5', '0', '7', '0', '4', '0', '7', '/', '4', '9', '4', '4', '1', '9', '0', '9', '3', '2', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '2', '7', '7', '0', '2', '3', '4', '5', '7', '1', '9', '1', '4', '3', '5', '9', '5', '6', '7', '/', '4', '9', '4', '4', '1', '9', '0', '9', '3', '2', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '7', '1', '9', '0', '1', '6', '3', '4', '7', '6', '1', '3', '8', '6', '5', '4', '1', '7', '/', '7', '7', '6', '9', '4', '4', '2', '8', '9', '4', '3', '0', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0315298Acc00600 : List (String × SourceJson) := (fragment0315298Field005Key00, fragment0315298Field005Value00) :: fragment0315298Acc00500
noncomputable def fragment0315298Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '6', '5', '3', '0', '7', '7', '8', '3', '6', '9', '4', '4', '0', '8', '4', '4', '0', '0', '3', '9', '/', '5', '4', '3', '8', '6', '1', '0', '0', '2', '6', '0', '1', '3', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '1', '9', '7', '2', '0', '9', '0', '9', '1', '3', '9', '9', '7', '6', '6', '7', '2', '1', '1', '/', '7', '7', '6', '9', '4', '4', '2', '8', '9', '4', '3', '0', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '9', '1', '2', '1', '9', '8', '9', '8', '3', '9', '3', '5', '1', '2', '6', '1', '9', '/', '2', '3', '6', '4', '6', '1', '3', '0', '5', '4', '7', '8', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '3', '5', '6', '1', '1', '0', '4', '4', '2', '2', '7', '6', '4', '6', '2', '0', '1', '0', '3', '/', '6', '0', '4', '2', '9', '0', '0', '0', '2', '8', '9', '0', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '7', '5', '0', '3', '1', '2', '5', '8', '5', '9', '1', '0', '7', '1', '3', '2', '3', '8', '9', '/', '1', '8', '1', '2', '8', '7', '0', '0', '0', '8', '6', '7', '1', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '4', '8', '8', '5', '1', '3', '9', '4', '4', '5', '3', '3', '5', '0', '6', '1', '3', '1', '/', '1', '2', '3', '6', '0', '4', '7', '7', '3', '3', '1', '8', '4', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '0', '8', '2', '6', '6', '7', '0', '9', '6', '0', '1', '4', '2', '4', '6', '1', '9', '7', '/', '4', '9', '4', '4', '1', '9', '0', '9', '3', '2', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '4', '5', '7', '3', '0', '9', '1', '9', '2', '4', '3', '5', '0', '7', '0', '4', '0', '7', '/', '4', '9', '4', '4', '1', '9', '0', '9', '3', '2', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '2', '7', '7', '0', '2', '3', '4', '5', '7', '1', '9', '1', '4', '3', '5', '9', '5', '6', '7', '/', '4', '9', '4', '4', '1', '9', '0', '9', '3', '2', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '7', '1', '9', '0', '1', '6', '3', '4', '7', '6', '1', '3', '8', '6', '5', '4', '1', '7', '/', '7', '7', '6', '9', '4', '4', '2', '8', '9', '4', '3', '0', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0315298_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0315298Field005Chars00 ++ tail)) fragment0315298Acc00500 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0315298Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_005"
  err.flush

noncomputable def fragment0315298Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0315298Field006Value00 : SourceJson := .str (String.ofList ['8', '1', '8', '6', '6', '5', '6', '7', '7', '0', '9', '2', '2', '0', '5', '7', '1', '2', '2', '2', '0', '5', '3', '9', '4', '6', '1', '7', '5', '8', '8', '0', '5', '1', '0', '8', '0', '7', '1', '9', '8', '0', '8', '5', '2', '0', '/', '4', '2', '0', '0', '0', '0', '7', '4', '6', '8', '1', '3', '6', '4', '8', '5', '4', '3', '2', '8', '4', '3', '9', '4', '6', '1', '4', '7', '4', '7', '2', '3', '7', '6', '4', '1', '6', '0', '2', '2', '7', '8', '5', '9', '1', '5', '7', '8', '8', '8', '6', '3', '6', '4', '3', '9', '7', '9', '9'])
noncomputable def fragment0315298Acc00700 : List (String × SourceJson) := (fragment0315298Field006Key00, fragment0315298Field006Value00) :: fragment0315298Acc00600
noncomputable def fragment0315298Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '1', '8', '6', '6', '5', '6', '7', '7', '0', '9', '2', '2', '0', '5', '7', '1', '2', '2', '2', '0', '5', '3', '9', '4', '6', '1', '7', '5', '8', '8', '0', '5', '1', '0', '8', '0', '7', '1', '9', '8', '0', '8', '5', '2', '0', '/', '4', '2', '0', '0', '0', '0', '7', '4', '6', '8', '1', '3', '6', '4', '8', '5', '4', '3', '2', '8', '4', '3', '9', '4', '6', '1', '4', '7', '4', '7', '2', '3', '7', '6', '4', '1', '6', '0', '2', '2', '7', '8', '5', '9', '1', '5', '7', '8', '8', '8', '6', '3', '6', '4', '3', '9', '7', '9', '9', '"', ',']

theorem object_fragment0315298_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0315298Field006Chars00 ++ tail)) fragment0315298Acc00600 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0315298Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_006"
  err.flush

noncomputable def fragment0315298Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0315298Field007Value00 : SourceJson := .str (String.ofList ['5', '0', '0', '2', '8', '9', '2', '8', '6', '8', '6', '2', '6', '7', '8', '7', '4', '8', '7', '9', '6', '9', '7', '4', '1', '7', '4', '2', '8', '9', '6', '8', '7', '5', '1', '7', '0', '4', '0', '2', '4', '7', '8', '5', '6', '6', '8', '6', '3', '6', '9', '2', '2', '6', '0', '9', '2', '0', '4', '2', '4', '7', '2', '0', '4', '1', '0', '4', '7', '7', '9', '4', '6', '6', '2', '1', '8', '8', '9', '5', '1', '9', '6', '3', '8', '2', '5', '7', '6', '1', '7', '6', '4', '9', '1', '3', '5', '4', '0', '9', '2', '0', '0', '4', '7', '2', '5', '4', '8', '7', '6', '5', '6', '5', '0', '4', '9', '5', '2', '5', '1', '4', '3', '0', '5', '1', '6', '4', '1', '9', '5', '2', '3', '6', '2', '5', '7', '6', '3', '8', '4', '8', '8', '6', '5', '8', '2', '3', '2', '1', '7', '1', '9', '3', '0', '3', '6', '4', '1', '8', '1', '3', '7', '3', '1', '0', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '8', '2', '2', '9', '1', '0', '7', '1', '8', '2', '6', '7', '9', '0', '5', '6', '8', '0', '0', '6', '1', '2', '9', '1', '4', '0', '9', '5', '0', '0', '0', '5', '7', '3', '7', '8', '5', '0', '9', '2', '7', '1', '8', '2', '4', '0', '4', '3', '3', '3', '9', '6', '5', '1', '2', '4', '5', '2', '2', '3', '4', '6', '8', '7', '8', '8', '6', '7', '4', '9', '8', '3', '8', '3', '6', '5', '4', '8', '5', '6', '1', '3', '4', '9', '5', '7', '6', '0', '4', '5', '9', '5', '3', '2', '1', '5', '3', '6', '1', '7', '8', '6', '5', '5', '4', '9', '1', '9', '3', '6', '4', '2', '1', '3', '0', '9', '8', '5', '7', '0', '0', '0', '7', '8', '1', '0', '9', '6', '8', '6', '8', '1', '0', '8', '7', '7', '8', '6', '4', '1', '4', '5', '7', '5', '3', '2', '2', '7', '5', '0', '8', '0', '2', '9', '0', '2', '6', '6', '1', '2', '7', '5', '7', '4', '1', '7', '1', '9', '2', '0', '9', '3', '7', '9', '3', '9', '3', '5', '5', '8', '5', '1', '2', '7', '0', '6', '0', '6', '9', '1', '4', '2', '2', '0', '6', '5', '3', '1', '2', '5', '0', '1', '7'])
noncomputable def fragment0315298Acc00800 : List (String × SourceJson) := (fragment0315298Field007Key00, fragment0315298Field007Value00) :: fragment0315298Acc00700
noncomputable def fragment0315298Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '0', '0', '2', '8', '9', '2', '8', '6', '8', '6', '2', '6', '7', '8', '7', '4', '8', '7', '9', '6', '9', '7', '4', '1', '7', '4', '2', '8', '9', '6', '8', '7', '5', '1', '7', '0', '4', '0', '2', '4', '7', '8', '5', '6', '6', '8', '6', '3', '6', '9', '2', '2', '6', '0', '9', '2', '0', '4', '2', '4', '7', '2', '0', '4', '1', '0', '4', '7', '7', '9', '4', '6', '6', '2', '1', '8', '8', '9', '5', '1', '9', '6', '3', '8', '2', '5', '7', '6', '1', '7', '6', '4', '9', '1', '3', '5', '4', '0', '9', '2', '0', '0', '4', '7', '2', '5', '4', '8', '7', '6', '5', '6', '5', '0', '4', '9', '5', '2', '5', '1', '4', '3', '0', '5', '1', '6', '4', '1', '9', '5', '2', '3', '6', '2', '5', '7', '6', '3', '8', '4', '8', '8', '6', '5', '8', '2', '3', '2', '1', '7', '1', '9', '3', '0', '3', '6', '4', '1', '8', '1', '3', '7', '3', '1', '0', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '8', '2', '2', '9', '1', '0', '7', '1', '8', '2', '6', '7', '9', '0', '5', '6', '8', '0', '0', '6', '1', '2', '9', '1', '4', '0', '9', '5', '0', '0', '0', '5', '7', '3', '7', '8', '5', '0', '9', '2', '7', '1', '8', '2', '4', '0', '4', '3', '3', '3', '9', '6', '5', '1', '2', '4', '5', '2', '2', '3', '4', '6', '8', '7', '8', '8', '6', '7', '4', '9', '8', '3', '8', '3', '6', '5', '4', '8', '5', '6', '1', '3', '4', '9', '5', '7', '6', '0', '4', '5', '9', '5', '3', '2', '1', '5', '3', '6', '1', '7', '8', '6', '5', '5', '4', '9', '1', '9', '3', '6', '4', '2', '1', '3', '0', '9', '8', '5', '7', '0', '0', '0', '7', '8', '1', '0', '9', '6', '8', '6', '8', '1', '0', '8', '7', '7', '8', '6', '4', '1', '4', '5', '7', '5', '3', '2', '2', '7', '5', '0', '8', '0', '2', '9', '0', '2', '6', '6', '1', '2', '7', '5', '7', '4', '1', '7', '1', '9', '2', '0', '9', '3', '7', '9', '3', '9', '3', '5', '5', '8', '5', '1', '2', '7', '0', '6', '0', '6', '9', '1', '4', '2', '2', '0', '6', '5', '3', '1', '2', '5', '0', '1', '7', '"', ',']

theorem object_fragment0315298_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0315298Field007Chars00 ++ tail)) fragment0315298Acc00700 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0315298Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_007"
  err.flush

noncomputable def fragment0315298Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0315298Field008Value00 : SourceJson := .str (String.ofList ['1', '5', '4', '4', '3', '1', '5', '7', '6', '1', '3', '7', '8', '6', '3', '5', '7'])
noncomputable def fragment0315298Acc00900 : List (String × SourceJson) := (fragment0315298Field008Key00, fragment0315298Field008Value00) :: fragment0315298Acc00800
noncomputable def fragment0315298Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '4', '4', '3', '1', '5', '7', '6', '1', '3', '7', '8', '6', '3', '5', '7', '"', ',']

theorem object_fragment0315298_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0315298Field008Chars00 ++ tail)) fragment0315298Acc00800 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0315298Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_008"
  err.flush

noncomputable def fragment0315298Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0315298Field009Value00 : SourceJson := .str (String.ofList ['5', '0', '6', '6', '7', '8', '4', '2', '6', '3', '7', '0', '6', '6', '2', '5', '8'])
noncomputable def fragment0315298Acc01000 : List (String × SourceJson) := (fragment0315298Field009Key00, fragment0315298Field009Value00) :: fragment0315298Acc00900
noncomputable def fragment0315298Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '6', '6', '7', '8', '4', '2', '6', '3', '7', '0', '6', '6', '2', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0315298_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0315298Field009Chars00 ++ tail)) fragment0315298Acc00900 =
      .ok (.obj (fragment0315298Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0315298_object_field_009"
  err.flush

noncomputable def fragment0315298Chars : List Char := '{' :: (fragment0315298Field000Chars00 ++ fragment0315298Field001Chars00 ++ fragment0315298Field002Chars00 ++ fragment0315298Field003Chars00 ++ fragment0315298Field004Chars00 ++ fragment0315298Field005Chars00 ++ fragment0315298Field006Chars00 ++ fragment0315298Field007Chars00 ++ fragment0315298Field008Chars00 ++ fragment0315298Field009Chars00)
noncomputable def fragment0315298Value : SourceJson := .obj (fragment0315298Acc01000.reverse)

theorem value_fragment0315298 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 408) (fragment0315298Chars ++ tail) =
      .ok (fragment0315298Value, tail) := by
  have hinput : fragment0315298Chars ++ tail = '{' :: (fragment0315298Field000Chars00 ++ (fragment0315298Field001Chars00 ++ (fragment0315298Field002Chars00 ++ (fragment0315298Field003Chars00 ++ (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0315298Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 408) (fragment0315298Chars ++ tail) =
        SourceJson.value (fuel + 408) ('{' :: (fragment0315298Field000Chars00 ++ (fragment0315298Field001Chars00 ++ (fragment0315298Field002Chars00 ++ (fragment0315298Field003Chars00 ++ (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 408)) hinput
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0315298Field000Chars00 ++ (fragment0315298Field001Chars00 ++ (fragment0315298Field002Chars00 ++ (fragment0315298Field003Chars00 ++ (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))))))))))) fragment0315298Acc00000 := by rfl
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0315298Field001Chars00 ++ (fragment0315298Field002Chars00 ++ (fragment0315298Field003Chars00 ++ (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail))))))))))) fragment0315298Acc00100 := object_fragment0315298_field_000 fuel (fragment0315298Field001Chars00 ++ (fragment0315298Field002Chars00 ++ (fragment0315298Field003Chars00 ++ (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0315298Field002Chars00 ++ (fragment0315298Field003Chars00 ++ (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))))))))) fragment0315298Acc00200 := object_fragment0315298_field_001 fuel (fragment0315298Field002Chars00 ++ (fragment0315298Field003Chars00 ++ (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0315298Field003Chars00 ++ (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail))))))))) fragment0315298Acc00300 := object_fragment0315298_field_002 fuel (fragment0315298Field003Chars00 ++ (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))))))) fragment0315298Acc00400 := object_fragment0315298_field_003 fuel (fragment0315298Field004Chars00 ++ (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail))))))) fragment0315298Acc00500 := object_fragment0315298_field_004 fuel (fragment0315298Field005Chars00 ++ (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))))) fragment0315298Acc00600 := object_fragment0315298_field_005 fuel (fragment0315298Field006Chars00 ++ (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail))))) fragment0315298Acc00700 := object_fragment0315298_field_006 fuel (fragment0315298Field007Chars00 ++ (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))) fragment0315298Acc00800 := object_fragment0315298_field_007 fuel (fragment0315298Field008Chars00 ++ (fragment0315298Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0315298Field009Chars00 ++ (tail))) fragment0315298Acc00900 := object_fragment0315298_field_008 fuel (fragment0315298Field009Chars00 ++ (tail))
    _ = .ok (fragment0315298Value, tail) := object_fragment0315298_field_009 fuel (tail)

noncomputable def fragment0317240Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0317240Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0317240Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '2'])
noncomputable def fragment0317240Acc00100 : List (String × SourceJson) := (fragment0317240Field000Key00, fragment0317240Field000Value00) :: fragment0317240Acc00000
noncomputable def fragment0317240Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '2', ',']

theorem object_fragment0317240_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0317240Field000Chars00 ++ tail)) fragment0317240Acc00000 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0317240Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_000"
  err.flush

noncomputable def fragment0317240Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0317240Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0317240Acc00200 : List (String × SourceJson) := (fragment0317240Field001Key00, fragment0317240Field001Value00) :: fragment0317240Acc00100
noncomputable def fragment0317240Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0317240_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0317240Field001Chars00 ++ tail)) fragment0317240Acc00100 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0317240Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_001"
  err.flush

noncomputable def fragment0317240Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0317240Field002Value00 : SourceJson := .str (String.ofList ['2', '2', '5', '1', '4', '1', '6', '8', '6', '7', '7', '7', '8', '2', '2', '7', '4', '1', '4', '3', '3', '1', '3', '2', '2', '3', '0', '4', '6', '7', '7', '9', '8', '1', '1', '3', '4', '7', '3', '9', '4', '7', '3', '/', '3', '0', '5', '9', '9', '9', '3', '7', '7', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0317240Acc00300 : List (String × SourceJson) := (fragment0317240Field002Key00, fragment0317240Field002Value00) :: fragment0317240Acc00200
noncomputable def fragment0317240Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '2', '5', '1', '4', '1', '6', '8', '6', '7', '7', '7', '8', '2', '2', '7', '4', '1', '4', '3', '3', '1', '3', '2', '2', '3', '0', '4', '6', '7', '7', '9', '8', '1', '1', '3', '4', '7', '3', '9', '4', '7', '3', '/', '3', '0', '5', '9', '9', '9', '3', '7', '7', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0317240_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0317240Field002Chars00 ++ tail)) fragment0317240Acc00200 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0317240Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_002"
  err.flush

noncomputable def fragment0317240Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0317240Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0317240Acc00400 : List (String × SourceJson) := (fragment0317240Field003Key00, fragment0317240Field003Value00) :: fragment0317240Acc00300
noncomputable def fragment0317240Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0317240_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0317240Field003Chars00 ++ tail)) fragment0317240Acc00300 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0317240Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_003"
  err.flush

noncomputable def fragment0317240Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0317240Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0317240Acc00500 : List (String × SourceJson) := (fragment0317240Field004Key00, fragment0317240Field004Value00) :: fragment0317240Acc00400
noncomputable def fragment0317240Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0317240_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0317240Field004Chars00 ++ tail)) fragment0317240Acc00400 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0317240Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_004"
  err.flush

noncomputable def fragment0317240Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0317240Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '6', '1', '1', '1', '9', '6', '4', '1', '7', '2', '8', '3', '/', '5', '4', '1', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '8', '2', '7', '7', '4', '0', '5', '2', '6', '2', '9', '/', '5', '4', '1', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '8', '5', '8', '9', '3', '1', '6', '6', '7', '/', '1', '4', '1', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '0', '4', '0', '3', '2', '0', '1', '2', '8', '1', '/', '5', '0', '8', '0', '5', '5', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '7', '8', '1', '3', '9', '3', '8', '0', '7', '7', '/', '1', '0', '1', '6', '1', '1', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '3', '5', '3', '3', '5', '2', '6', '9', '7', '7', '/', '2', '1', '1', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '6', '7', '4', '7', '4', '7', '1', '5', '3', '7', '/', '1', '4', '7', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '2', '3', '9', '6', '0', '4', '6', '6', '9', '1', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '3', '7', '9', '7', '7', '5', '2', '7', '1', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '9', '5', '6', '6', '5', '6', '6', '8', '3', '8', '9', '/', '1', '6', '2', '5', '7', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0317240Acc00600 : List (String × SourceJson) := (fragment0317240Field005Key00, fragment0317240Field005Value00) :: fragment0317240Acc00500
noncomputable def fragment0317240Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '1', '1', '1', '9', '6', '4', '1', '7', '2', '8', '3', '/', '5', '4', '1', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '8', '2', '7', '7', '4', '0', '5', '2', '6', '2', '9', '/', '5', '4', '1', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '8', '5', '8', '9', '3', '1', '6', '6', '7', '/', '1', '4', '1', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '0', '4', '0', '3', '2', '0', '1', '2', '8', '1', '/', '5', '0', '8', '0', '5', '5', '6', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '7', '8', '1', '3', '9', '3', '8', '0', '7', '7', '/', '1', '0', '1', '6', '1', '1', '1', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '3', '5', '3', '3', '5', '2', '6', '9', '7', '7', '/', '2', '1', '1', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '6', '7', '4', '7', '4', '7', '1', '5', '3', '7', '/', '1', '4', '7', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '2', '3', '9', '6', '0', '4', '6', '6', '9', '1', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '3', '7', '9', '7', '7', '5', '2', '7', '1', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '7', '9', '5', '6', '6', '5', '6', '6', '8', '3', '8', '9', '/', '1', '6', '2', '5', '7', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0317240_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0317240Field005Chars00 ++ tail)) fragment0317240Acc00500 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0317240Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_005"
  err.flush

noncomputable def fragment0317240Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0317240Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '1', '1', '9', '7', '1', '3', '4', '2', '1', '1', '1', '1', '7', '2', '2', '2', '5', '6', '2', '0', '7', '7', '2', '1', '9', '7', '1', '2', '4', '1', '7', '5', '2', '2', '2', '0', '4', '1', '8', '3', '5', '3', '5', '3', '6', '0', '0', '0', '/', '2', '3', '5', '5', '8', '2', '3', '0', '8', '4', '4', '0', '3', '4', '1', '1', '6', '2', '8', '5', '9', '2', '5', '1', '0', '2', '1', '8', '7', '5', '6', '7', '1', '4', '9', '5', '1', '7', '8', '9', '1', '9', '7', '9', '7', '3', '3', '4', '8', '5', '0', '5', '0', '4', '7', '7', '1', '1', '9', '3', '8', '7', '9'])
noncomputable def fragment0317240Acc00700 : List (String × SourceJson) := (fragment0317240Field006Key00, fragment0317240Field006Value00) :: fragment0317240Acc00600
noncomputable def fragment0317240Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '2', '1', '1', '9', '7', '1', '3', '4', '2', '1', '1', '1', '1', '7', '2', '2', '2', '5', '6', '2', '0', '7', '7', '2', '1', '9', '7', '1', '2', '4', '1', '7', '5', '2', '2', '2', '0', '4', '1', '8', '3', '5', '3', '5', '3', '6', '0', '0', '0', '/', '2', '3', '5', '5', '8', '2', '3', '0', '8', '4', '4', '0', '3', '4', '1', '1', '6', '2', '8', '5', '9', '2', '5', '1', '0', '2', '1', '8', '7', '5', '6', '7', '1', '4', '9', '5', '1', '7', '8', '9', '1', '9', '7', '9', '7', '3', '3', '4', '8', '5', '0', '5', '0', '4', '7', '7', '1', '1', '9', '3', '8', '7', '9', '"', ',']

theorem object_fragment0317240_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0317240Field006Chars00 ++ tail)) fragment0317240Acc00600 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0317240Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_006"
  err.flush

noncomputable def fragment0317240Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0317240Field007Value00 : SourceJson := .str (String.ofList ['6', '7', '4', '9', '6', '2', '9', '8', '8', '1', '2', '7', '3', '3', '6', '5', '2', '0', '5', '4', '9', '4', '3', '2', '6', '1', '0', '2', '4', '1', '3', '1', '1', '5', '1', '2', '3', '8', '5', '0', '2', '0', '2', '4', '0', '5', '0', '2', '1', '2', '4', '4', '5', '5', '1', '3', '3', '4', '0', '0', '8', '0', '1', '6', '2', '7', '4', '8', '7', '5', '3', '2', '2', '7', '9', '7', '7', '5', '2', '6', '8', '6', '7', '6', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '5', '2', '4', '2', '2', '7', '7', '5', '6', '4', '4', '7', '4', '0', '9', '6', '6', '2', '6', '3', '4', '2', '1', '1', '4', '6', '1', '1', '5', '9', '3', '3', '6', '5', '6', '6', '5', '8', '4', '1', '4', '5', '2', '9', '6', '6', '6', '6', '4', '8', '6', '5', '8', '1', '9', '0', '3', '9', '4', '5', '9', '8', '7', '6', '2', '1', '3', '7', '5', '3', '9', '6', '0', '6', '8', '8', '3', '8', '2', '0', '3', '6', '8', '6', '6', '8', '9', '7', '9', '5', '5', '9', '3', '5', '5', '7', '9', '5', '4', '8', '0', '8', '1', '1', '6', '6', '3', '4', '8', '2', '2', '1', '2', '4', '2', '7'])
noncomputable def fragment0317240Acc00800 : List (String × SourceJson) := (fragment0317240Field007Key00, fragment0317240Field007Value00) :: fragment0317240Acc00700
noncomputable def fragment0317240Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '7', '4', '9', '6', '2', '9', '8', '8', '1', '2', '7', '3', '3', '6', '5', '2', '0', '5', '4', '9', '4', '3', '2', '6', '1', '0', '2', '4', '1', '3', '1', '1', '5', '1', '2', '3', '8', '5', '0', '2', '0', '2', '4', '0', '5', '0', '2', '1', '2', '4', '4', '5', '5', '1', '3', '3', '4', '0', '0', '8', '0', '1', '6', '2', '7', '4', '8', '7', '5', '3', '2', '2', '7', '9', '7', '7', '5', '2', '6', '8', '6', '7', '6', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '5', '2', '4', '2', '2', '7', '7', '5', '6', '4', '4', '7', '4', '0', '9', '6', '6', '2', '6', '3', '4', '2', '1', '1', '4', '6', '1', '1', '5', '9', '3', '3', '6', '5', '6', '6', '5', '8', '4', '1', '4', '5', '2', '9', '6', '6', '6', '6', '4', '8', '6', '5', '8', '1', '9', '0', '3', '9', '4', '5', '9', '8', '7', '6', '2', '1', '3', '7', '5', '3', '9', '6', '0', '6', '8', '8', '3', '8', '2', '0', '3', '6', '8', '6', '6', '8', '9', '7', '9', '5', '5', '9', '3', '5', '5', '7', '9', '5', '4', '8', '0', '8', '1', '1', '6', '6', '3', '4', '8', '2', '2', '1', '2', '4', '2', '7', '"', ',']

theorem object_fragment0317240_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0317240Field007Chars00 ++ tail)) fragment0317240Acc00700 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0317240Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_007"
  err.flush

noncomputable def fragment0317240Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0317240Field008Value00 : SourceJson := .str (String.ofList ['6', '1', '2', '4', '8', '2', '7', '6', '0', '1', '6', '5', '8', '8', '4', '3', '7'])
noncomputable def fragment0317240Acc00900 : List (String × SourceJson) := (fragment0317240Field008Key00, fragment0317240Field008Value00) :: fragment0317240Acc00800
noncomputable def fragment0317240Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '1', '2', '4', '8', '2', '7', '6', '0', '1', '6', '5', '8', '8', '4', '3', '7', '"', ',']

theorem object_fragment0317240_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0317240Field008Chars00 ++ tail)) fragment0317240Acc00800 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0317240Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_008"
  err.flush

noncomputable def fragment0317240Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0317240Field009Value00 : SourceJson := .str (String.ofList ['2', '4', '8', '4', '4', '5', '9', '7', '4', '0', '8', '8', '1', '8', '8', '8', '7', '2'])
noncomputable def fragment0317240Acc01000 : List (String × SourceJson) := (fragment0317240Field009Key00, fragment0317240Field009Value00) :: fragment0317240Acc00900
noncomputable def fragment0317240Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '8', '4', '4', '5', '9', '7', '4', '0', '8', '8', '1', '8', '8', '8', '7', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0317240_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0317240Field009Chars00 ++ tail)) fragment0317240Acc00900 =
      .ok (.obj (fragment0317240Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0317240_object_field_009"
  err.flush

noncomputable def fragment0317240Chars : List Char := '{' :: (fragment0317240Field000Chars00 ++ fragment0317240Field001Chars00 ++ fragment0317240Field002Chars00 ++ fragment0317240Field003Chars00 ++ fragment0317240Field004Chars00 ++ fragment0317240Field005Chars00 ++ fragment0317240Field006Chars00 ++ fragment0317240Field007Chars00 ++ fragment0317240Field008Chars00 ++ fragment0317240Field009Chars00)
noncomputable def fragment0317240Value : SourceJson := .obj (fragment0317240Acc01000.reverse)

theorem value_fragment0317240 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 236) (fragment0317240Chars ++ tail) =
      .ok (fragment0317240Value, tail) := by
  have hinput : fragment0317240Chars ++ tail = '{' :: (fragment0317240Field000Chars00 ++ (fragment0317240Field001Chars00 ++ (fragment0317240Field002Chars00 ++ (fragment0317240Field003Chars00 ++ (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0317240Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 236) (fragment0317240Chars ++ tail) =
        SourceJson.value (fuel + 236) ('{' :: (fragment0317240Field000Chars00 ++ (fragment0317240Field001Chars00 ++ (fragment0317240Field002Chars00 ++ (fragment0317240Field003Chars00 ++ (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 236)) hinput
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0317240Field000Chars00 ++ (fragment0317240Field001Chars00 ++ (fragment0317240Field002Chars00 ++ (fragment0317240Field003Chars00 ++ (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))))))))))) fragment0317240Acc00000 := by rfl
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0317240Field001Chars00 ++ (fragment0317240Field002Chars00 ++ (fragment0317240Field003Chars00 ++ (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail))))))))))) fragment0317240Acc00100 := object_fragment0317240_field_000 fuel (fragment0317240Field001Chars00 ++ (fragment0317240Field002Chars00 ++ (fragment0317240Field003Chars00 ++ (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0317240Field002Chars00 ++ (fragment0317240Field003Chars00 ++ (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))))))))) fragment0317240Acc00200 := object_fragment0317240_field_001 fuel (fragment0317240Field002Chars00 ++ (fragment0317240Field003Chars00 ++ (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0317240Field003Chars00 ++ (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail))))))))) fragment0317240Acc00300 := object_fragment0317240_field_002 fuel (fragment0317240Field003Chars00 ++ (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))))))) fragment0317240Acc00400 := object_fragment0317240_field_003 fuel (fragment0317240Field004Chars00 ++ (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail))))))) fragment0317240Acc00500 := object_fragment0317240_field_004 fuel (fragment0317240Field005Chars00 ++ (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))))) fragment0317240Acc00600 := object_fragment0317240_field_005 fuel (fragment0317240Field006Chars00 ++ (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail))))) fragment0317240Acc00700 := object_fragment0317240_field_006 fuel (fragment0317240Field007Chars00 ++ (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))) fragment0317240Acc00800 := object_fragment0317240_field_007 fuel (fragment0317240Field008Chars00 ++ (fragment0317240Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0317240Field009Chars00 ++ (tail))) fragment0317240Acc00900 := object_fragment0317240_field_008 fuel (fragment0317240Field009Chars00 ++ (tail))
    _ = .ok (fragment0317240Value, tail) := object_fragment0317240_field_009 fuel (tail)

noncomputable def fragment0318852Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0318852Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0318852Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '3'])
noncomputable def fragment0318852Acc00100 : List (String × SourceJson) := (fragment0318852Field000Key00, fragment0318852Field000Value00) :: fragment0318852Acc00000
noncomputable def fragment0318852Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '3', ',']

theorem object_fragment0318852_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 384) (SourceJson.white (fragment0318852Field000Chars00 ++ tail)) fragment0318852Acc00000 =
      SourceJson.object (fuel + 383) (SourceJson.white tail) fragment0318852Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_000"
  err.flush

noncomputable def fragment0318852Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0318852Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['0'])]
noncomputable def fragment0318852Acc00200 : List (String × SourceJson) := (fragment0318852Field001Key00, fragment0318852Field001Value00) :: fragment0318852Acc00100
noncomputable def fragment0318852Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0318852_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 383) (SourceJson.white (fragment0318852Field001Chars00 ++ tail)) fragment0318852Acc00100 =
      SourceJson.object (fuel + 382) (SourceJson.white tail) fragment0318852Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_001"
  err.flush

noncomputable def fragment0318852Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0318852Field002Value00 : SourceJson := .str (String.ofList ['2', '3', '7', '8', '3', '2', '5', '9', '7', '2', '1', '2', '8', '6', '8', '5', '2', '3', '2', '1', '6', '0', '3', '7', '7', '7', '9', '4', '7', '0', '9', '8', '5', '3', '1', '4', '6', '4', '5', '3', '/', '5', '0', '7', '6', '3', '7', '8', '5', '5', '4', '7', '8', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0318852Acc00300 : List (String × SourceJson) := (fragment0318852Field002Key00, fragment0318852Field002Value00) :: fragment0318852Acc00200
noncomputable def fragment0318852Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '3', '7', '8', '3', '2', '5', '9', '7', '2', '1', '2', '8', '6', '8', '5', '2', '3', '2', '1', '6', '0', '3', '7', '7', '7', '9', '4', '7', '0', '9', '8', '5', '3', '1', '4', '6', '4', '5', '3', '/', '5', '0', '7', '6', '3', '7', '8', '5', '5', '4', '7', '8', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0318852_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 382) (SourceJson.white (fragment0318852Field002Chars00 ++ tail)) fragment0318852Acc00200 =
      SourceJson.object (fuel + 381) (SourceJson.white tail) fragment0318852Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_002"
  err.flush

noncomputable def fragment0318852Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0318852Field003Value00 : SourceJson := .str (String.ofList ['9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0318852Acc00400 : List (String × SourceJson) := (fragment0318852Field003Key00, fragment0318852Field003Value00) :: fragment0318852Acc00300
noncomputable def fragment0318852Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '6', '7', '0', '7', '3', '8', '9', '/', '6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0318852_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 381) (SourceJson.white (fragment0318852Field003Chars00 ++ tail)) fragment0318852Acc00300 =
      SourceJson.object (fuel + 380) (SourceJson.white tail) fragment0318852Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_003"
  err.flush

noncomputable def fragment0318852Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0318852Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0318852Acc00500 : List (String × SourceJson) := (fragment0318852Field004Key00, fragment0318852Field004Value00) :: fragment0318852Acc00400
noncomputable def fragment0318852Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0318852_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 380) (SourceJson.white (fragment0318852Field004Chars00 ++ tail)) fragment0318852Acc00400 =
      SourceJson.object (fuel + 379) (SourceJson.white tail) fragment0318852Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_004"
  err.flush

noncomputable def fragment0318852Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0318852Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '5', '6', '0', '1', '7', '0', '2', '4', '5', '0', '2', '4', '2', '5', '6', '2', '5', '1', '2', '2', '3', '/', '1', '1', '2', '6', '7', '7', '7', '3', '4', '2', '5', '6', '1', '1', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '7', '4', '7', '9', '0', '6', '9', '6', '3', '5', '2', '3', '7', '5', '7', '4', '2', '9', '/', '1', '3', '1', '0', '2', '0', '6', '2', '1', '2', '2', '8', '0', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '1', '4', '9', '4', '8', '0', '1', '9', '1', '3', '5', '5', '3', '8', '0', '9', '/', '5', '8', '3', '2', '1', '8', '0', '8', '6', '2', '1', '1', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '2', '9', '5', '1', '9', '5', '8', '4', '8', '3', '8', '8', '5', '7', '8', '4', '7', '7', '/', '4', '4', '7', '1', '3', '3', '8', '6', '6', '0', '9', '5', '6', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '1', '7', '0', '4', '0', '9', '9', '3', '7', '8', '0', '5', '6', '7', '4', '3', '0', '1', '/', '1', '3', '4', '1', '4', '0', '1', '5', '9', '8', '2', '8', '7', '0', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '8', '4', '4', '3', '5', '9', '9', '1', '6', '9', '7', '9', '7', '5', '4', '1', '7', '/', '7', '1', '1', '3', '4', '9', '3', '3', '2', '4', '2', '4', '9', '3', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '2', '5', '6', '5', '3', '5', '4', '1', '4', '2', '7', '0', '5', '3', '7', '5', '7', '1', '/', '1', '1', '3', '8', '1', '5', '8', '9', '3', '1', '8', '7', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '4', '3', '4', '9', '4', '1', '5', '1', '3', '1', '9', '7', '3', '3', '3', '4', '2', '3', '/', '3', '4', '1', '4', '4', '7', '6', '7', '9', '5', '6', '3', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '5', '9', '7', '4', '5', '9', '0', '1', '8', '2', '9', '7', '9', '7', '7', '2', '1', '/', '1', '1', '3', '8', '1', '5', '8', '9', '3', '1', '8', '7', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '8', '2', '5', '7', '5', '6', '7', '7', '1', '1', '8', '6', '3', '2', '3', '3', '6', '3', '/', '1', '3', '1', '0', '2', '0', '6', '2', '1', '2', '2', '8', '0', '3', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0318852Acc00600 : List (String × SourceJson) := (fragment0318852Field005Key00, fragment0318852Field005Value00) :: fragment0318852Acc00500
noncomputable def fragment0318852Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '6', '0', '1', '7', '0', '2', '4', '5', '0', '2', '4', '2', '5', '6', '2', '5', '1', '2', '2', '3', '/', '1', '1', '2', '6', '7', '7', '7', '3', '4', '2', '5', '6', '1', '1', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '7', '4', '7', '9', '0', '6', '9', '6', '3', '5', '2', '3', '7', '5', '7', '4', '2', '9', '/', '1', '3', '1', '0', '2', '0', '6', '2', '1', '2', '2', '8', '0', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '1', '4', '9', '4', '8', '0', '1', '9', '1', '3', '5', '5', '3', '8', '0', '9', '/', '5', '8', '3', '2', '1', '8', '0', '8', '6', '2', '1', '1', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '2', '9', '5', '1', '9', '5', '8', '4', '8', '3', '8', '8', '5', '7', '8', '4', '7', '7', '/', '4', '4', '7', '1', '3', '3', '8', '6', '6', '0', '9', '5', '6', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '1', '7', '0', '4', '0', '9', '9', '3', '7', '8', '0', '5', '6', '7', '4', '3', '0', '1', '/', '1', '3', '4', '1', '4', '0', '1', '5', '9', '8', '2', '8', '7', '0', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '8', '4', '4', '3', '5', '9', '9', '1', '6', '9', '7', '9', '7', '5', '4', '1', '7', '/', '7', '1', '1', '3', '4', '9', '3', '3', '2', '4', '2', '4', '9', '3', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '2', '5', '6', '5', '3', '5', '4', '1', '4', '2', '7', '0', '5', '3', '7', '5', '7', '1', '/', '1', '1', '3', '8', '1', '5', '8', '9', '3', '1', '8', '7', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '4', '3', '4', '9', '4', '1', '5', '1', '3', '1', '9', '7', '3', '3', '3', '4', '2', '3', '/', '3', '4', '1', '4', '4', '7', '6', '7', '9', '5', '6', '3', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '5', '9', '7', '4', '5', '9', '0', '1', '8', '2', '9', '7', '9', '7', '7', '2', '1', '/', '1', '1', '3', '8', '1', '5', '8', '9', '3', '1', '8', '7', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '8', '2', '5', '7', '5', '6', '7', '7', '1', '1', '8', '6', '3', '2', '3', '3', '6', '3', '/', '1', '3', '1', '0', '2', '0', '6', '2', '1', '2', '2', '8', '0', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0318852_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 379) (SourceJson.white (fragment0318852Field005Chars00 ++ tail)) fragment0318852Acc00500 =
      SourceJson.object (fuel + 378) (SourceJson.white tail) fragment0318852Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_005"
  err.flush

noncomputable def fragment0318852Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0318852Field006Value00 : SourceJson := .str (String.ofList ['4', '9', '6', '8', '1', '0', '5', '7', '3', '2', '5', '0', '8', '8', '2', '2', '4', '8', '1', '7', '0', '2', '7', '1', '0', '5', '6', '8', '1', '2', '4', '7', '7', '6', '4', '2', '6', '0', '3', '1', '9', '2', '8', '5', '7', '6', '2', '5', '/', '3', '1', '6', '6', '1', '5', '9', '2', '5', '4', '8', '0', '2', '6', '2', '8', '2', '4', '3', '1', '2', '5', '3', '8', '1', '0', '6', '1', '2', '7', '0', '7', '5', '2', '7', '2', '8', '8', '5', '0', '5', '1', '8', '5', '1', '0', '4', '4', '3', '5', '0', '7', '8', '3', '0', '9', '7', '6', '4', '8', '7'])
noncomputable def fragment0318852Acc00700 : List (String × SourceJson) := (fragment0318852Field006Key00, fragment0318852Field006Value00) :: fragment0318852Acc00600
noncomputable def fragment0318852Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '9', '6', '8', '1', '0', '5', '7', '3', '2', '5', '0', '8', '8', '2', '2', '4', '8', '1', '7', '0', '2', '7', '1', '0', '5', '6', '8', '1', '2', '4', '7', '7', '6', '4', '2', '6', '0', '3', '1', '9', '2', '8', '5', '7', '6', '2', '5', '/', '3', '1', '6', '6', '1', '5', '9', '2', '5', '4', '8', '0', '2', '6', '2', '8', '2', '4', '3', '1', '2', '5', '3', '8', '1', '0', '6', '1', '2', '7', '0', '7', '5', '2', '7', '2', '8', '8', '5', '0', '5', '1', '8', '5', '1', '0', '4', '4', '3', '5', '0', '7', '8', '3', '0', '9', '7', '6', '4', '8', '7', '"', ',']

theorem object_fragment0318852_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 378) (SourceJson.white (fragment0318852Field006Chars00 ++ tail)) fragment0318852Acc00600 =
      SourceJson.object (fuel + 377) (SourceJson.white tail) fragment0318852Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_006"
  err.flush

noncomputable def fragment0318852Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0318852Field007Value00 : SourceJson := .str (String.ofList ['6', '9', '4', '8', '4', '3', '4', '1', '0', '5', '1', '7', '8', '9', '9', '3', '2', '2', '1', '9', '1', '6', '9', '6', '5', '1', '8', '1', '4', '7', '3', '4', '7', '4', '0', '0', '1', '1', '9', '6', '4', '0', '2', '3', '4', '5', '8', '3', '1', '7', '1', '3', '5', '4', '9', '9', '4', '2', '8', '2', '4', '6', '5', '2', '9', '5', '2', '4', '4', '3', '9', '0', '6', '9', '0', '3', '3', '1', '9', '9', '9', '7', '2', '5', '8', '1', '2', '7', '4', '1', '0', '8', '3', '1', '8', '9', '7', '0', '8', '1', '6', '1', '9', '7', '8', '4', '9', '5', '8', '6', '5', '5', '2', '6', '4', '5', '2', '3', '3', '4', '9', '6', '2', '1', '6', '2', '4', '2', '4', '6', '0', '5', '7', '8', '2', '8', '6', '5', '0', '6', '8', '4', '0', '7', '9', '8', '1', '7', '5', '9', '9', '6', '3', '7', '0', '3', '1', '7', '2', '0', '5', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '3', '9', '8', '1', '5', '3', '1', '4', '2', '1', '9', '3', '8', '7', '5', '8', '7', '0', '8', '1', '6', '7', '6', '2', '8', '3', '6', '7', '4', '7', '5', '3', '4', '1', '8', '4', '1', '7', '2', '9', '9', '2', '8', '2', '4', '9', '9', '9', '3', '1', '2', '1', '9', '3', '4', '1', '8', '3', '5', '4', '0', '7', '5', '1', '1', '0', '8', '2', '4', '4', '7', '8', '5', '0', '5', '1', '3', '0', '2', '8', '3', '9', '9', '0', '5', '1', '6', '4', '5', '8', '6', '5', '9', '1', '9', '2', '0', '1', '2', '7', '6', '4', '4', '2', '6', '9', '9', '8', '3', '0', '1', '1', '6', '4', '2', '9', '2', '6', '4', '8', '8', '1', '0', '8', '4', '3', '3', '9', '7', '8', '7', '4', '6', '2', '7', '0', '2', '1', '4', '4', '3', '8', '9', '9', '9', '2', '1', '5', '0', '2', '6', '9', '5', '1', '9', '1', '9', '4', '2', '3', '2', '2', '6', '3', '3', '2', '2', '4', '6', '8', '4', '0', '8', '4', '2', '9', '2', '7', '7', '5', '5', '2', '4', '1', '6', '3', '4', '2', '8', '8', '1'])
noncomputable def fragment0318852Acc00800 : List (String × SourceJson) := (fragment0318852Field007Key00, fragment0318852Field007Value00) :: fragment0318852Acc00700
noncomputable def fragment0318852Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '9', '4', '8', '4', '3', '4', '1', '0', '5', '1', '7', '8', '9', '9', '3', '2', '2', '1', '9', '1', '6', '9', '6', '5', '1', '8', '1', '4', '7', '3', '4', '7', '4', '0', '0', '1', '1', '9', '6', '4', '0', '2', '3', '4', '5', '8', '3', '1', '7', '1', '3', '5', '4', '9', '9', '4', '2', '8', '2', '4', '6', '5', '2', '9', '5', '2', '4', '4', '3', '9', '0', '6', '9', '0', '3', '3', '1', '9', '9', '9', '7', '2', '5', '8', '1', '2', '7', '4', '1', '0', '8', '3', '1', '8', '9', '7', '0', '8', '1', '6', '1', '9', '7', '8', '4', '9', '5', '8', '6', '5', '5', '2', '6', '4', '5', '2', '3', '3', '4', '9', '6', '2', '1', '6', '2', '4', '2', '4', '6', '0', '5', '7', '8', '2', '8', '6', '5', '0', '6', '8', '4', '0', '7', '9', '8', '1', '7', '5', '9', '9', '6', '3', '7', '0', '3', '1', '7', '2', '0', '5', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '3', '9', '8', '1', '5', '3', '1', '4', '2', '1', '9', '3', '8', '7', '5', '8', '7', '0', '8', '1', '6', '7', '6', '2', '8', '3', '6', '7', '4', '7', '5', '3', '4', '1', '8', '4', '1', '7', '2', '9', '9', '2', '8', '2', '4', '9', '9', '9', '3', '1', '2', '1', '9', '3', '4', '1', '8', '3', '5', '4', '0', '7', '5', '1', '1', '0', '8', '2', '4', '4', '7', '8', '5', '0', '5', '1', '3', '0', '2', '8', '3', '9', '9', '0', '5', '1', '6', '4', '5', '8', '6', '5', '9', '1', '9', '2', '0', '1', '2', '7', '6', '4', '4', '2', '6', '9', '9', '8', '3', '0', '1', '1', '6', '4', '2', '9', '2', '6', '4', '8', '8', '1', '0', '8', '4', '3', '3', '9', '7', '8', '7', '4', '6', '2', '7', '0', '2', '1', '4', '4', '3', '8', '9', '9', '9', '2', '1', '5', '0', '2', '6', '9', '5', '1', '9', '1', '9', '4', '2', '3', '2', '2', '6', '3', '3', '2', '2', '4', '6', '8', '4', '0', '8', '4', '2', '9', '2', '7', '7', '5', '5', '2', '4', '1', '6', '3', '4', '2', '8', '8', '1', '"', ',']

theorem object_fragment0318852_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 377) (SourceJson.white (fragment0318852Field007Chars00 ++ tail)) fragment0318852Acc00700 =
      SourceJson.object (fuel + 376) (SourceJson.white tail) fragment0318852Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_007"
  err.flush

noncomputable def fragment0318852Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0318852Field008Value00 : SourceJson := .str (String.ofList ['1', '2', '4', '3', '1', '9', '0', '4', '2', '9', '4', '3', '3', '3', '8', '7', '1'])
noncomputable def fragment0318852Acc00900 : List (String × SourceJson) := (fragment0318852Field008Key00, fragment0318852Field008Value00) :: fragment0318852Acc00800
noncomputable def fragment0318852Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '4', '3', '1', '9', '0', '4', '2', '9', '4', '3', '3', '3', '8', '7', '1', '"', ',']

theorem object_fragment0318852_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 376) (SourceJson.white (fragment0318852Field008Chars00 ++ tail)) fragment0318852Acc00800 =
      SourceJson.object (fuel + 375) (SourceJson.white tail) fragment0318852Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_008"
  err.flush

noncomputable def fragment0318852Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0318852Field009Value00 : SourceJson := .str (String.ofList ['3', '3', '5', '7', '1', '5', '6', '5', '1', '4', '7', '0', '6', '9', '1', '3', '6'])
noncomputable def fragment0318852Acc01000 : List (String × SourceJson) := (fragment0318852Field009Key00, fragment0318852Field009Value00) :: fragment0318852Acc00900
noncomputable def fragment0318852Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '5', '7', '1', '5', '6', '5', '1', '4', '7', '0', '6', '9', '1', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0318852_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 375) (SourceJson.white (fragment0318852Field009Chars00 ++ tail)) fragment0318852Acc00900 =
      .ok (.obj (fragment0318852Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0318852_object_field_009"
  err.flush

noncomputable def fragment0318852Chars : List Char := '{' :: (fragment0318852Field000Chars00 ++ fragment0318852Field001Chars00 ++ fragment0318852Field002Chars00 ++ fragment0318852Field003Chars00 ++ fragment0318852Field004Chars00 ++ fragment0318852Field005Chars00 ++ fragment0318852Field006Chars00 ++ fragment0318852Field007Chars00 ++ fragment0318852Field008Chars00 ++ fragment0318852Field009Chars00)
noncomputable def fragment0318852Value : SourceJson := .obj (fragment0318852Acc01000.reverse)

theorem value_fragment0318852 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 385) (fragment0318852Chars ++ tail) =
      .ok (fragment0318852Value, tail) := by
  have hinput : fragment0318852Chars ++ tail = '{' :: (fragment0318852Field000Chars00 ++ (fragment0318852Field001Chars00 ++ (fragment0318852Field002Chars00 ++ (fragment0318852Field003Chars00 ++ (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0318852Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 385) (fragment0318852Chars ++ tail) =
        SourceJson.value (fuel + 385) ('{' :: (fragment0318852Field000Chars00 ++ (fragment0318852Field001Chars00 ++ (fragment0318852Field002Chars00 ++ (fragment0318852Field003Chars00 ++ (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 385)) hinput
    _ = SourceJson.object (fuel + 384) (SourceJson.white (fragment0318852Field000Chars00 ++ (fragment0318852Field001Chars00 ++ (fragment0318852Field002Chars00 ++ (fragment0318852Field003Chars00 ++ (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))))))))))) fragment0318852Acc00000 := by rfl
    _ = SourceJson.object (fuel + 383) (SourceJson.white (fragment0318852Field001Chars00 ++ (fragment0318852Field002Chars00 ++ (fragment0318852Field003Chars00 ++ (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail))))))))))) fragment0318852Acc00100 := object_fragment0318852_field_000 fuel (fragment0318852Field001Chars00 ++ (fragment0318852Field002Chars00 ++ (fragment0318852Field003Chars00 ++ (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 382) (SourceJson.white (fragment0318852Field002Chars00 ++ (fragment0318852Field003Chars00 ++ (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))))))))) fragment0318852Acc00200 := object_fragment0318852_field_001 fuel (fragment0318852Field002Chars00 ++ (fragment0318852Field003Chars00 ++ (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 381) (SourceJson.white (fragment0318852Field003Chars00 ++ (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail))))))))) fragment0318852Acc00300 := object_fragment0318852_field_002 fuel (fragment0318852Field003Chars00 ++ (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 380) (SourceJson.white (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))))))) fragment0318852Acc00400 := object_fragment0318852_field_003 fuel (fragment0318852Field004Chars00 ++ (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 379) (SourceJson.white (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail))))))) fragment0318852Acc00500 := object_fragment0318852_field_004 fuel (fragment0318852Field005Chars00 ++ (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 378) (SourceJson.white (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))))) fragment0318852Acc00600 := object_fragment0318852_field_005 fuel (fragment0318852Field006Chars00 ++ (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 377) (SourceJson.white (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail))))) fragment0318852Acc00700 := object_fragment0318852_field_006 fuel (fragment0318852Field007Chars00 ++ (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 376) (SourceJson.white (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))) fragment0318852Acc00800 := object_fragment0318852_field_007 fuel (fragment0318852Field008Chars00 ++ (fragment0318852Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 375) (SourceJson.white (fragment0318852Field009Chars00 ++ (tail))) fragment0318852Acc00900 := object_fragment0318852_field_008 fuel (fragment0318852Field009Chars00 ++ (tail))
    _ = .ok (fragment0318852Value, tail) := object_fragment0318852_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0096_before_reader"
  err.flush

noncomputable def chunk0096LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0096SuffixChars00 : List Char := [',']
noncomputable def chunk0096Chars00 : List Char := chunk0096LeadChars00 ++ fragment0305254Chars ++ chunk0096SuffixChars00
noncomputable def chunk0096Push00 (acc : List SourceJson) : List SourceJson := fragment0305254Value :: acc

noncomputable def chunk0096AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0096_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 561)
      (SourceJson.white (chunk0096LeadChars00 ++ (fragment0305254Chars ++ rest))) acc =
      (SourceJson.value (fuel + 560) (fragment0305254Chars ++ rest)).bind
        (chunk0096AfterValue00 (fuel + 560) acc) := by rfl

theorem array_chunk0096 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 561) (SourceJson.white (chunk0096Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 560) (SourceJson.white tail) (chunk0096Push00 acc) := by
  have hinput : chunk0096Chars00 ++ tail = chunk0096LeadChars00 ++ (fragment0305254Chars ++ (chunk0096SuffixChars00 ++ tail)) := by
    simp only [chunk0096Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 561) (SourceJson.white (chunk0096Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 561)
          (SourceJson.white (chunk0096LeadChars00 ++ (fragment0305254Chars ++ (chunk0096SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 561) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 560) (fragment0305254Chars ++ (chunk0096SuffixChars00 ++ tail))).bind
        (chunk0096AfterValue00 (fuel + 560) acc) := array_chunk0096_head fuel (chunk0096SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0305254Value, chunk0096SuffixChars00 ++ tail)).bind
        (chunk0096AfterValue00 (fuel + 560) acc) :=
      congrArg (fun result => result.bind (chunk0096AfterValue00 (fuel + 560) acc))
        (value_fragment0305254 (fuel + 34) (chunk0096SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 560) (SourceJson.white tail) (chunk0096Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0096_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0097_before_reader"
  err.flush

noncomputable def chunk0097LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0097SuffixChars00 : List Char := [',']
noncomputable def chunk0097Chars00 : List Char := chunk0097LeadChars00 ++ fragment0307480Chars ++ chunk0097SuffixChars00
noncomputable def chunk0097Push00 (acc : List SourceJson) : List SourceJson := fragment0307480Value :: acc

noncomputable def chunk0097AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0097_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 560)
      (SourceJson.white (chunk0097LeadChars00 ++ (fragment0307480Chars ++ rest))) acc =
      (SourceJson.value (fuel + 559) (fragment0307480Chars ++ rest)).bind
        (chunk0097AfterValue00 (fuel + 559) acc) := by rfl

theorem array_chunk0097 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 560) (SourceJson.white (chunk0097Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 559) (SourceJson.white tail) (chunk0097Push00 acc) := by
  have hinput : chunk0097Chars00 ++ tail = chunk0097LeadChars00 ++ (fragment0307480Chars ++ (chunk0097SuffixChars00 ++ tail)) := by
    simp only [chunk0097Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 560) (SourceJson.white (chunk0097Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 560)
          (SourceJson.white (chunk0097LeadChars00 ++ (fragment0307480Chars ++ (chunk0097SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 560) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 559) (fragment0307480Chars ++ (chunk0097SuffixChars00 ++ tail))).bind
        (chunk0097AfterValue00 (fuel + 559) acc) := array_chunk0097_head fuel (chunk0097SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0307480Value, chunk0097SuffixChars00 ++ tail)).bind
        (chunk0097AfterValue00 (fuel + 559) acc) :=
      congrArg (fun result => result.bind (chunk0097AfterValue00 (fuel + 559) acc))
        (value_fragment0307480 (fuel + 82) (chunk0097SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 559) (SourceJson.white tail) (chunk0097Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0097_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0098_before_reader"
  err.flush

noncomputable def chunk0098LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0098SuffixChars00 : List Char := [',']
noncomputable def chunk0098Chars00 : List Char := chunk0098LeadChars00 ++ fragment0309594Chars ++ chunk0098SuffixChars00
noncomputable def chunk0098Push00 (acc : List SourceJson) : List SourceJson := fragment0309594Value :: acc

noncomputable def chunk0098AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0098_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 559)
      (SourceJson.white (chunk0098LeadChars00 ++ (fragment0309594Chars ++ rest))) acc =
      (SourceJson.value (fuel + 558) (fragment0309594Chars ++ rest)).bind
        (chunk0098AfterValue00 (fuel + 558) acc) := by rfl

theorem array_chunk0098 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 559) (SourceJson.white (chunk0098Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 558) (SourceJson.white tail) (chunk0098Push00 acc) := by
  have hinput : chunk0098Chars00 ++ tail = chunk0098LeadChars00 ++ (fragment0309594Chars ++ (chunk0098SuffixChars00 ++ tail)) := by
    simp only [chunk0098Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 559) (SourceJson.white (chunk0098Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 559)
          (SourceJson.white (chunk0098LeadChars00 ++ (fragment0309594Chars ++ (chunk0098SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 559) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 558) (fragment0309594Chars ++ (chunk0098SuffixChars00 ++ tail))).bind
        (chunk0098AfterValue00 (fuel + 558) acc) := array_chunk0098_head fuel (chunk0098SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0309594Value, chunk0098SuffixChars00 ++ tail)).bind
        (chunk0098AfterValue00 (fuel + 558) acc) :=
      congrArg (fun result => result.bind (chunk0098AfterValue00 (fuel + 558) acc))
        (value_fragment0309594 (fuel + 152) (chunk0098SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 558) (SourceJson.white tail) (chunk0098Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0098_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0099_before_reader"
  err.flush

noncomputable def chunk0099LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0099SuffixChars00 : List Char := [',']
noncomputable def chunk0099Chars00 : List Char := chunk0099LeadChars00 ++ fragment0311558Chars ++ chunk0099SuffixChars00
noncomputable def chunk0099Push00 (acc : List SourceJson) : List SourceJson := fragment0311558Value :: acc

noncomputable def chunk0099AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0099_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 558)
      (SourceJson.white (chunk0099LeadChars00 ++ (fragment0311558Chars ++ rest))) acc =
      (SourceJson.value (fuel + 557) (fragment0311558Chars ++ rest)).bind
        (chunk0099AfterValue00 (fuel + 557) acc) := by rfl

theorem array_chunk0099 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 558) (SourceJson.white (chunk0099Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 557) (SourceJson.white tail) (chunk0099Push00 acc) := by
  have hinput : chunk0099Chars00 ++ tail = chunk0099LeadChars00 ++ (fragment0311558Chars ++ (chunk0099SuffixChars00 ++ tail)) := by
    simp only [chunk0099Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 558) (SourceJson.white (chunk0099Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 558)
          (SourceJson.white (chunk0099LeadChars00 ++ (fragment0311558Chars ++ (chunk0099SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 558) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 557) (fragment0311558Chars ++ (chunk0099SuffixChars00 ++ tail))).bind
        (chunk0099AfterValue00 (fuel + 557) acc) := array_chunk0099_head fuel (chunk0099SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0311558Value, chunk0099SuffixChars00 ++ tail)).bind
        (chunk0099AfterValue00 (fuel + 557) acc) :=
      congrArg (fun result => result.bind (chunk0099AfterValue00 (fuel + 557) acc))
        (value_fragment0311558 (fuel + 306) (chunk0099SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 557) (SourceJson.white tail) (chunk0099Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0099_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0100_before_reader"
  err.flush

noncomputable def chunk0100LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0100SuffixChars00 : List Char := [',']
noncomputable def chunk0100Chars00 : List Char := chunk0100LeadChars00 ++ fragment0313219Chars ++ chunk0100SuffixChars00
noncomputable def chunk0100Push00 (acc : List SourceJson) : List SourceJson := fragment0313219Value :: acc

noncomputable def chunk0100AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0100_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 557)
      (SourceJson.white (chunk0100LeadChars00 ++ (fragment0313219Chars ++ rest))) acc =
      (SourceJson.value (fuel + 556) (fragment0313219Chars ++ rest)).bind
        (chunk0100AfterValue00 (fuel + 556) acc) := by rfl

theorem array_chunk0100 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 557) (SourceJson.white (chunk0100Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 556) (SourceJson.white tail) (chunk0100Push00 acc) := by
  have hinput : chunk0100Chars00 ++ tail = chunk0100LeadChars00 ++ (fragment0313219Chars ++ (chunk0100SuffixChars00 ++ tail)) := by
    simp only [chunk0100Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 557) (SourceJson.white (chunk0100Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 557)
          (SourceJson.white (chunk0100LeadChars00 ++ (fragment0313219Chars ++ (chunk0100SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 557) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 556) (fragment0313219Chars ++ (chunk0100SuffixChars00 ++ tail))).bind
        (chunk0100AfterValue00 (fuel + 556) acc) := array_chunk0100_head fuel (chunk0100SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0313219Value, chunk0100SuffixChars00 ++ tail)).bind
        (chunk0100AfterValue00 (fuel + 556) acc) :=
      congrArg (fun result => result.bind (chunk0100AfterValue00 (fuel + 556) acc))
        (value_fragment0313219 (fuel + 85) (chunk0100SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 556) (SourceJson.white tail) (chunk0100Push00 acc) := by rfl

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
noncomputable def chunk0101Chars00 : List Char := chunk0101LeadChars00 ++ fragment0315298Chars ++ chunk0101SuffixChars00
noncomputable def chunk0101Push00 (acc : List SourceJson) : List SourceJson := fragment0315298Value :: acc

noncomputable def chunk0101AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0101_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 556)
      (SourceJson.white (chunk0101LeadChars00 ++ (fragment0315298Chars ++ rest))) acc =
      (SourceJson.value (fuel + 555) (fragment0315298Chars ++ rest)).bind
        (chunk0101AfterValue00 (fuel + 555) acc) := by rfl

theorem array_chunk0101 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 556) (SourceJson.white (chunk0101Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 555) (SourceJson.white tail) (chunk0101Push00 acc) := by
  have hinput : chunk0101Chars00 ++ tail = chunk0101LeadChars00 ++ (fragment0315298Chars ++ (chunk0101SuffixChars00 ++ tail)) := by
    simp only [chunk0101Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 556) (SourceJson.white (chunk0101Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 556)
          (SourceJson.white (chunk0101LeadChars00 ++ (fragment0315298Chars ++ (chunk0101SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 556) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 555) (fragment0315298Chars ++ (chunk0101SuffixChars00 ++ tail))).bind
        (chunk0101AfterValue00 (fuel + 555) acc) := array_chunk0101_head fuel (chunk0101SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0315298Value, chunk0101SuffixChars00 ++ tail)).bind
        (chunk0101AfterValue00 (fuel + 555) acc) :=
      congrArg (fun result => result.bind (chunk0101AfterValue00 (fuel + 555) acc))
        (value_fragment0315298 (fuel + 147) (chunk0101SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 555) (SourceJson.white tail) (chunk0101Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0101_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0102_before_reader"
  err.flush

noncomputable def chunk0102LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0102SuffixChars00 : List Char := [',']
noncomputable def chunk0102Chars00 : List Char := chunk0102LeadChars00 ++ fragment0317240Chars ++ chunk0102SuffixChars00
noncomputable def chunk0102Push00 (acc : List SourceJson) : List SourceJson := fragment0317240Value :: acc

noncomputable def chunk0102AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0102_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 555)
      (SourceJson.white (chunk0102LeadChars00 ++ (fragment0317240Chars ++ rest))) acc =
      (SourceJson.value (fuel + 554) (fragment0317240Chars ++ rest)).bind
        (chunk0102AfterValue00 (fuel + 554) acc) := by rfl

theorem array_chunk0102 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 555) (SourceJson.white (chunk0102Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 554) (SourceJson.white tail) (chunk0102Push00 acc) := by
  have hinput : chunk0102Chars00 ++ tail = chunk0102LeadChars00 ++ (fragment0317240Chars ++ (chunk0102SuffixChars00 ++ tail)) := by
    simp only [chunk0102Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 555) (SourceJson.white (chunk0102Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 555)
          (SourceJson.white (chunk0102LeadChars00 ++ (fragment0317240Chars ++ (chunk0102SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 555) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 554) (fragment0317240Chars ++ (chunk0102SuffixChars00 ++ tail))).bind
        (chunk0102AfterValue00 (fuel + 554) acc) := array_chunk0102_head fuel (chunk0102SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0317240Value, chunk0102SuffixChars00 ++ tail)).bind
        (chunk0102AfterValue00 (fuel + 554) acc) :=
      congrArg (fun result => result.bind (chunk0102AfterValue00 (fuel + 554) acc))
        (value_fragment0317240 (fuel + 318) (chunk0102SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 554) (SourceJson.white tail) (chunk0102Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0102_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0103_before_reader"
  err.flush

noncomputable def chunk0103LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0103SuffixChars00 : List Char := [',']
noncomputable def chunk0103Chars00 : List Char := chunk0103LeadChars00 ++ fragment0318852Chars ++ chunk0103SuffixChars00
noncomputable def chunk0103Push00 (acc : List SourceJson) : List SourceJson := fragment0318852Value :: acc

noncomputable def chunk0103AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0103_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 554)
      (SourceJson.white (chunk0103LeadChars00 ++ (fragment0318852Chars ++ rest))) acc =
      (SourceJson.value (fuel + 553) (fragment0318852Chars ++ rest)).bind
        (chunk0103AfterValue00 (fuel + 553) acc) := by rfl

theorem array_chunk0103 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 554) (SourceJson.white (chunk0103Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 553) (SourceJson.white tail) (chunk0103Push00 acc) := by
  have hinput : chunk0103Chars00 ++ tail = chunk0103LeadChars00 ++ (fragment0318852Chars ++ (chunk0103SuffixChars00 ++ tail)) := by
    simp only [chunk0103Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 554) (SourceJson.white (chunk0103Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 554)
          (SourceJson.white (chunk0103LeadChars00 ++ (fragment0318852Chars ++ (chunk0103SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 554) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 553) (fragment0318852Chars ++ (chunk0103SuffixChars00 ++ tail))).bind
        (chunk0103AfterValue00 (fuel + 553) acc) := array_chunk0103_head fuel (chunk0103SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0318852Value, chunk0103SuffixChars00 ++ tail)).bind
        (chunk0103AfterValue00 (fuel + 553) acc) :=
      congrArg (fun result => result.bind (chunk0103AfterValue00 (fuel + 553) acc))
        (value_fragment0318852 (fuel + 168) (chunk0103SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 553) (SourceJson.white tail) (chunk0103Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0103_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0096Chars00 ++ chunk0097Chars00 ++ chunk0098Chars00 ++ chunk0099Chars00 ++ chunk0100Chars00 ++ chunk0101Chars00 ++ chunk0102Chars00 ++ chunk0103Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0103Push00 (chunk0102Push00 (chunk0101Push00 (chunk0100Push00 (chunk0099Push00 (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 561) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 553) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0096Chars00 ++ (chunk0097Chars00 ++ (chunk0098Chars00 ++ (chunk0099Chars00 ++ (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 561) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 561) (SourceJson.white (chunk0096Chars00 ++ (chunk0097Chars00 ++ (chunk0098Chars00 ++ (chunk0099Chars00 ++ (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 561) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 560) (SourceJson.white (chunk0097Chars00 ++ (chunk0098Chars00 ++ (chunk0099Chars00 ++ (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail))))))))) (chunk0096Push00 (acc)) := array_chunk0096 fuel (chunk0097Chars00 ++ (chunk0098Chars00 ++ (chunk0099Chars00 ++ (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 559) (SourceJson.white (chunk0098Chars00 ++ (chunk0099Chars00 ++ (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)))))))) (chunk0097Push00 (chunk0096Push00 (acc))) := array_chunk0097 fuel (chunk0098Chars00 ++ (chunk0099Chars00 ++ (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail))))))) (chunk0096Push00 (acc))
    _ = SourceJson.array (fuel + 558) (SourceJson.white (chunk0099Chars00 ++ (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail))))))) (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc)))) := array_chunk0098 fuel (chunk0099Chars00 ++ (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)))))) (chunk0097Push00 (chunk0096Push00 (acc)))
    _ = SourceJson.array (fuel + 557) (SourceJson.white (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)))))) (chunk0099Push00 (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc))))) := array_chunk0099 fuel (chunk0100Chars00 ++ (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail))))) (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc))))
    _ = SourceJson.array (fuel + 556) (SourceJson.white (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail))))) (chunk0100Push00 (chunk0099Push00 (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc)))))) := array_chunk0100 fuel (chunk0101Chars00 ++ (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)))) (chunk0099Push00 (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc)))))
    _ = SourceJson.array (fuel + 555) (SourceJson.white (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail)))) (chunk0101Push00 (chunk0100Push00 (chunk0099Push00 (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc))))))) := array_chunk0101 fuel (chunk0102Chars00 ++ (chunk0103Chars00 ++ (tail))) (chunk0100Push00 (chunk0099Push00 (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc))))))
    _ = SourceJson.array (fuel + 554) (SourceJson.white (chunk0103Chars00 ++ (tail))) (chunk0102Push00 (chunk0101Push00 (chunk0100Push00 (chunk0099Push00 (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc)))))))) := array_chunk0102 fuel (chunk0103Chars00 ++ (tail)) (chunk0101Push00 (chunk0100Push00 (chunk0099Push00 (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc)))))))
    _ = SourceJson.array (fuel + 553) (SourceJson.white tail) (blockPush acc) := array_chunk0103 fuel (tail) (chunk0102Push00 (chunk0101Push00 (chunk0100Push00 (chunk0099Push00 (chunk0098Push00 (chunk0097Push00 (chunk0096Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 305248).take 15503 = blockChars := by rfl

theorem block_original_split : sourceRest 305248 = blockChars ++ sourceRest 320751 := by
  calc
    sourceRest 305248 = (sourceRest 305248).take 15503 ++ (sourceRest 305248).drop 15503 :=
      (List.take_append_drop 15503 (sourceRest 305248)).symm
    _ = blockChars ++ (sourceRest 305248).drop 15503 :=
      congrArg (fun part => part ++ (sourceRest 305248).drop 15503) block_original_prefix
    _ = blockChars ++ sourceRest 320751 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 305248 15503)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 561) (SourceJson.white (sourceRest 305248)) acc =
      SourceJson.array (fuel + 553) (SourceJson.white (sourceRest 320751)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 561) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 320751) acc)

#print axioms object_fragment0305254_field_000
#print axioms object_fragment0305254_field_001
#print axioms object_fragment0305254_field_002
#print axioms object_fragment0305254_field_003
#print axioms object_fragment0305254_field_004
#print axioms object_fragment0305254_field_005
#print axioms object_fragment0305254_field_006
#print axioms object_fragment0305254_field_007
#print axioms object_fragment0305254_field_008
#print axioms object_fragment0305254_field_009
#print axioms value_fragment0305254
#print axioms object_fragment0307480_field_000
#print axioms object_fragment0307480_field_001
#print axioms object_fragment0307480_field_002
#print axioms object_fragment0307480_field_003
#print axioms object_fragment0307480_field_004
#print axioms object_fragment0307480_field_005
#print axioms object_fragment0307480_field_006
#print axioms object_fragment0307480_field_007
#print axioms object_fragment0307480_field_008
#print axioms object_fragment0307480_field_009
#print axioms value_fragment0307480
#print axioms object_fragment0309594_field_000
#print axioms object_fragment0309594_field_001
#print axioms object_fragment0309594_field_002
#print axioms object_fragment0309594_field_003
#print axioms object_fragment0309594_field_004
#print axioms object_fragment0309594_field_005
#print axioms object_fragment0309594_field_006
#print axioms object_fragment0309594_field_007
#print axioms object_fragment0309594_field_008
#print axioms object_fragment0309594_field_009
#print axioms value_fragment0309594
#print axioms object_fragment0311558_field_000
#print axioms object_fragment0311558_field_001
#print axioms object_fragment0311558_field_002
#print axioms object_fragment0311558_field_003
#print axioms object_fragment0311558_field_004
#print axioms object_fragment0311558_field_005
#print axioms object_fragment0311558_field_006
#print axioms object_fragment0311558_field_007
#print axioms object_fragment0311558_field_008
#print axioms object_fragment0311558_field_009
#print axioms value_fragment0311558
#print axioms object_fragment0313219_field_000
#print axioms object_fragment0313219_field_001
#print axioms object_fragment0313219_field_002
#print axioms object_fragment0313219_field_003
#print axioms object_fragment0313219_field_004
#print axioms object_fragment0313219_field_005
#print axioms object_fragment0313219_field_006
#print axioms object_fragment0313219_field_007
#print axioms object_fragment0313219_field_008
#print axioms object_fragment0313219_field_009
#print axioms value_fragment0313219
#print axioms object_fragment0315298_field_000
#print axioms object_fragment0315298_field_001
#print axioms object_fragment0315298_field_002
#print axioms object_fragment0315298_field_003
#print axioms object_fragment0315298_field_004
#print axioms object_fragment0315298_field_005
#print axioms object_fragment0315298_field_006
#print axioms object_fragment0315298_field_007
#print axioms object_fragment0315298_field_008
#print axioms object_fragment0315298_field_009
#print axioms value_fragment0315298
#print axioms object_fragment0317240_field_000
#print axioms object_fragment0317240_field_001
#print axioms object_fragment0317240_field_002
#print axioms object_fragment0317240_field_003
#print axioms object_fragment0317240_field_004
#print axioms object_fragment0317240_field_005
#print axioms object_fragment0317240_field_006
#print axioms object_fragment0317240_field_007
#print axioms object_fragment0317240_field_008
#print axioms object_fragment0317240_field_009
#print axioms value_fragment0317240
#print axioms object_fragment0318852_field_000
#print axioms object_fragment0318852_field_001
#print axioms object_fragment0318852_field_002
#print axioms object_fragment0318852_field_003
#print axioms object_fragment0318852_field_004
#print axioms object_fragment0318852_field_005
#print axioms object_fragment0318852_field_006
#print axioms object_fragment0318852_field_007
#print axioms object_fragment0318852_field_008
#print axioms object_fragment0318852_field_009
#print axioms value_fragment0318852
#print axioms array_chunk0096_head
#print axioms array_chunk0096
#print axioms array_chunk0097_head
#print axioms array_chunk0097
#print axioms array_chunk0098_head
#print axioms array_chunk0098
#print axioms array_chunk0099_head
#print axioms array_chunk0099
#print axioms array_chunk0100_head
#print axioms array_chunk0100
#print axioms array_chunk0101_head
#print axioms array_chunk0101
#print axioms array_chunk0102_head
#print axioms array_chunk0102
#print axioms array_chunk0103_head
#print axioms array_chunk0103
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock012

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
