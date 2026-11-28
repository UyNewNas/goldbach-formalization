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

namespace SimplicesBlock006

noncomputable def fragment0216586Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0216586Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0216586Field000Value00 : SourceJson := .number (String.ofList ['4', '8'])
noncomputable def fragment0216586Acc00100 : List (String × SourceJson) := (fragment0216586Field000Key00, fragment0216586Field000Value00) :: fragment0216586Acc00000
noncomputable def fragment0216586Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '8', ',']

theorem object_fragment0216586_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 490) (SourceJson.white (fragment0216586Field000Chars00 ++ tail)) fragment0216586Acc00000 =
      SourceJson.object (fuel + 489) (SourceJson.white tail) fragment0216586Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_000"
  err.flush

noncomputable def fragment0216586Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0216586Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0216586Acc00200 : List (String × SourceJson) := (fragment0216586Field001Key00, fragment0216586Field001Value00) :: fragment0216586Acc00100
noncomputable def fragment0216586Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0216586_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 489) (SourceJson.white (fragment0216586Field001Chars00 ++ tail)) fragment0216586Acc00100 =
      SourceJson.object (fuel + 488) (SourceJson.white tail) fragment0216586Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_001"
  err.flush

noncomputable def fragment0216586Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0216586Field002Value00 : SourceJson := .str (String.ofList ['4', '0', '6', '6', '1', '4', '4', '9', '8', '7', '3', '9', '2', '1', '8', '3', '8', '0', '7', '1', '2', '7', '5', '4', '4', '8', '8', '7', '8', '6', '1', '5', '0', '6', '7', '9', '8', '2', '1', '4', '3', '/', '6', '4', '8', '4', '9', '2', '5', '0', '7', '0', '0', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0216586Acc00300 : List (String × SourceJson) := (fragment0216586Field002Key00, fragment0216586Field002Value00) :: fragment0216586Acc00200
noncomputable def fragment0216586Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '0', '6', '6', '1', '4', '4', '9', '8', '7', '3', '9', '2', '1', '8', '3', '8', '0', '7', '1', '2', '7', '5', '4', '4', '8', '8', '7', '8', '6', '1', '5', '0', '6', '7', '9', '8', '2', '1', '4', '3', '/', '6', '4', '8', '4', '9', '2', '5', '0', '7', '0', '0', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0216586_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 488) (SourceJson.white (fragment0216586Field002Chars00 ++ tail)) fragment0216586Acc00200 =
      SourceJson.object (fuel + 487) (SourceJson.white tail) fragment0216586Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_002"
  err.flush

noncomputable def fragment0216586Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0216586Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0216586Acc00400 : List (String × SourceJson) := (fragment0216586Field003Key00, fragment0216586Field003Value00) :: fragment0216586Acc00300
noncomputable def fragment0216586Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0216586_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 487) (SourceJson.white (fragment0216586Field003Chars00 ++ tail)) fragment0216586Acc00300 =
      SourceJson.object (fuel + 486) (SourceJson.white tail) fragment0216586Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_003"
  err.flush

noncomputable def fragment0216586Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0216586Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0216586Acc00500 : List (String × SourceJson) := (fragment0216586Field004Key00, fragment0216586Field004Value00) :: fragment0216586Acc00400
noncomputable def fragment0216586Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0216586_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 486) (SourceJson.white (fragment0216586Field004Chars00 ++ tail)) fragment0216586Acc00400 =
      SourceJson.object (fuel + 485) (SourceJson.white tail) fragment0216586Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_004"
  err.flush

noncomputable def fragment0216586Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0216586Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '5', '4', '8', '7', '3', '3', '3', '3', '5', '3', '1', '9', '3', '5', '7', '9', '6', '0', '4', '5', '1', '9', '2', '3', '7', '/', '1', '1', '8', '2', '4', '0', '9', '0', '6', '2', '5', '6', '0', '0', '0', '2', '2', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '0', '8', '4', '7', '5', '1', '9', '3', '2', '9', '0', '6', '6', '0', '6', '8', '0', '8', '4', '1', '4', '1', '/', '3', '9', '2', '8', '2', '6', '9', '3', '1', '0', '8', '3', '0', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '5', '5', '1', '4', '0', '5', '7', '0', '5', '8', '7', '6', '3', '9', '1', '7', '7', '0', '5', '7', '4', '3', '/', '2', '0', '5', '6', '3', '6', '3', '5', '8', '7', '0', '6', '0', '8', '7', '3', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '3', '1', '5', '9', '2', '0', '8', '3', '5', '6', '6', '3', '1', '0', '7', '8', '7', '5', '0', '3', '1', '4', '6', '9', '/', '7', '8', '8', '2', '7', '2', '7', '0', '8', '3', '7', '3', '3', '3', '4', '8', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '2', '9', '1', '8', '7', '3', '4', '0', '5', '6', '3', '6', '2', '9', '1', '2', '4', '3', '5', '0', '5', '4', '3', '/', '2', '6', '2', '7', '5', '7', '5', '6', '9', '4', '5', '7', '7', '7', '8', '2', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '5', '9', '4', '3', '0', '5', '4', '5', '2', '9', '7', '0', '8', '5', '7', '1', '1', '7', '4', '3', '1', '0', '8', '9', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '0', '1', '4', '0', '8', '8', '5', '0', '5', '3', '1', '0', '2', '8', '3', '4', '9', '6', '8', '7', '1', '9', '1', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '7', '3', '2', '7', '8', '0', '8', '7', '0', '3', '6', '2', '3', '2', '6', '1', '7', '6', '3', '8', '6', '1', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '6', '0', '4', '0', '1', '7', '7', '0', '7', '1', '5', '0', '9', '9', '0', '0', '4', '7', '8', '9', '7', '0', '1', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '0', '1', '0', '2', '3', '8', '4', '5', '5', '8', '8', '0', '3', '8', '9', '4', '9', '4', '1', '2', '7', '/', '3', '9', '2', '8', '2', '6', '9', '3', '1', '0', '8', '3', '0', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0216586Acc00600 : List (String × SourceJson) := (fragment0216586Field005Key00, fragment0216586Field005Value00) :: fragment0216586Acc00500
noncomputable def fragment0216586Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '4', '8', '7', '3', '3', '3', '3', '5', '3', '1', '9', '3', '5', '7', '9', '6', '0', '4', '5', '1', '9', '2', '3', '7', '/', '1', '1', '8', '2', '4', '0', '9', '0', '6', '2', '5', '6', '0', '0', '0', '2', '2', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '0', '8', '4', '7', '5', '1', '9', '3', '2', '9', '0', '6', '6', '0', '6', '8', '0', '8', '4', '1', '4', '1', '/', '3', '9', '2', '8', '2', '6', '9', '3', '1', '0', '8', '3', '0', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '5', '5', '1', '4', '0', '5', '7', '0', '5', '8', '7', '6', '3', '9', '1', '7', '7', '0', '5', '7', '4', '3', '/', '2', '0', '5', '6', '3', '6', '3', '5', '8', '7', '0', '6', '0', '8', '7', '3', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '3', '1', '5', '9', '2', '0', '8', '3', '5', '6', '6', '3', '1', '0', '7', '8', '7', '5', '0', '3', '1', '4', '6', '9', '/', '7', '8', '8', '2', '7', '2', '7', '0', '8', '3', '7', '3', '3', '3', '4', '8', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '2', '9', '1', '8', '7', '3', '4', '0', '5', '6', '3', '6', '2', '9', '1', '2', '4', '3', '5', '0', '5', '4', '3', '/', '2', '6', '2', '7', '5', '7', '5', '6', '9', '4', '5', '7', '7', '7', '8', '2', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '5', '9', '4', '3', '0', '5', '4', '5', '2', '9', '7', '0', '8', '5', '7', '1', '1', '7', '4', '3', '1', '0', '8', '9', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '0', '1', '4', '0', '8', '8', '5', '0', '5', '3', '1', '0', '2', '8', '3', '4', '9', '6', '8', '7', '1', '9', '1', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '7', '7', '3', '2', '7', '8', '0', '8', '7', '0', '3', '6', '2', '3', '2', '6', '1', '7', '6', '3', '8', '6', '1', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '6', '0', '4', '0', '1', '7', '7', '0', '7', '1', '5', '0', '9', '9', '0', '0', '4', '7', '8', '9', '7', '0', '1', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '3', '0', '1', '0', '2', '3', '8', '4', '5', '5', '8', '8', '0', '3', '8', '9', '4', '9', '4', '1', '2', '7', '/', '3', '9', '2', '8', '2', '6', '9', '3', '1', '0', '8', '3', '0', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0216586_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 485) (SourceJson.white (fragment0216586Field005Chars00 ++ tail)) fragment0216586Acc00500 =
      SourceJson.object (fuel + 484) (SourceJson.white tail) fragment0216586Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_005"
  err.flush

noncomputable def fragment0216586Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0216586Field006Value00 : SourceJson := .str (String.ofList ['9', '5', '8', '9', '7', '3', '8', '2', '4', '9', '9', '0', '0', '8', '8', '1', '3', '1', '1', '1', '6', '1', '7', '1', '6', '5', '3', '5', '0', '5', '5', '9', '3', '5', '8', '9', '2', '7', '9', '2', '5', '0', '3', '5', '1', '4', '2', '3', '0', '6', '4', '0', '/', '3', '6', '6', '2', '0', '7', '1', '6', '0', '4', '3', '9', '2', '7', '5', '6', '4', '2', '2', '8', '4', '6', '7', '7', '5', '6', '8', '3', '9', '3', '1', '1', '7', '5', '0', '9', '7', '8', '1', '1', '9', '0', '5', '6', '2', '4', '8', '2', '8', '7', '7', '4', '0', '6', '5', '8', '7', '6', '9', '5', '5', '8', '0', '5', '1', '7'])
noncomputable def fragment0216586Acc00700 : List (String × SourceJson) := (fragment0216586Field006Key00, fragment0216586Field006Value00) :: fragment0216586Acc00600
noncomputable def fragment0216586Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '5', '8', '9', '7', '3', '8', '2', '4', '9', '9', '0', '0', '8', '8', '1', '3', '1', '1', '1', '6', '1', '7', '1', '6', '5', '3', '5', '0', '5', '5', '9', '3', '5', '8', '9', '2', '7', '9', '2', '5', '0', '3', '5', '1', '4', '2', '3', '0', '6', '4', '0', '/', '3', '6', '6', '2', '0', '7', '1', '6', '0', '4', '3', '9', '2', '7', '5', '6', '4', '2', '2', '8', '4', '6', '7', '7', '5', '6', '8', '3', '9', '3', '1', '1', '7', '5', '0', '9', '7', '8', '1', '1', '9', '0', '5', '6', '2', '4', '8', '2', '8', '7', '7', '4', '0', '6', '5', '8', '7', '6', '9', '5', '5', '8', '0', '5', '1', '7', '"', ',']

theorem object_fragment0216586_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 484) (SourceJson.white (fragment0216586Field006Chars00 ++ tail)) fragment0216586Acc00600 =
      SourceJson.object (fuel + 483) (SourceJson.white tail) fragment0216586Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_006"
  err.flush

noncomputable def fragment0216586Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0216586Field007Value00 : SourceJson := .str (String.ofList ['2', '6', '6', '7', '9', '4', '7', '2', '6', '2', '7', '8', '0', '4', '9', '6', '3', '6', '4', '6', '8', '6', '5', '9', '5', '8', '1', '5', '5', '5', '4', '9', '6', '6', '8', '6', '2', '8', '7', '6', '0', '7', '4', '9', '5', '2', '6', '0', '9', '1', '1', '7', '5', '0', '7', '4', '5', '6', '7', '5', '8', '1', '5', '4', '6', '2', '2', '5', '3', '7', '0', '2', '0', '6', '2', '0', '4', '3', '0', '2', '7', '9', '8', '0', '4', '4', '8', '8', '1', '9', '2', '0', '4', '6', '1', '0', '8', '3', '7', '3', '1', '2', '6', '5', '5', '6', '5', '4', '1', '8', '8', '4', '7', '8', '1', '3', '9', '7', '2', '1', '8', '5', '1', '3', '4', '5', '2', '6', '9', '6', '5', '7', '6', '3', '3', '1', '0', '9', '5', '0', '8', '9', '9', '9', '5', '9', '2', '1', '9', '4', '4', '3', '0', '6', '8', '0', '1', '6', '6', '9', '3', '2', '8', '9', '0', '8', '2', '3', '1', '2', '8', '9', '0', '6', '0', '0', '6', '5', '0', '8', '3', '8', '3', '6', '4', '7', '7', '0', '1', '5', '8', '8', '8', '6', '1', '0', '8', '1', '4', '5', '4', '6', '8', '5', '0', '8', '7', '3', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '0', '2', '9', '2', '2', '3', '0', '6', '0', '0', '8', '2', '7', '7', '4', '4', '5', '6', '4', '8', '4', '6', '5', '5', '4', '6', '4', '8', '6', '3', '8', '1', '7', '5', '2', '4', '0', '0', '2', '7', '4', '2', '2', '5', '8', '2', '0', '2', '9', '8', '2', '6', '3', '3', '7', '7', '5', '7', '5', '5', '3', '5', '3', '5', '9', '1', '1', '0', '4', '7', '0', '5', '4', '0', '4', '9', '4', '3', '7', '9', '2', '8', '8', '9', '5', '9', '4', '9', '7', '5', '7', '6', '0', '5', '9', '4', '1', '0', '4', '1', '6', '0', '9', '1', '3', '5', '0', '4', '4', '9', '7', '9', '9', '8', '2', '4', '2', '2', '9', '5', '9', '3', '2', '5', '0', '7', '0', '7', '8', '5', '2', '2', '3', '9', '2', '7', '8', '1', '0', '0', '1', '3', '2', '4', '1', '3', '5', '4', '3', '4', '6', '5', '9', '2', '6', '5', '0', '0', '4', '9', '1', '9', '1', '6', '9', '0', '7', '4', '0', '5', '6', '4', '6', '5', '7', '6', '4', '9', '2', '4', '7', '7', '8', '3', '9', '8', '5', '5', '5', '6', '6', '3', '8', '1', '4', '1', '2', '7', '7', '1', '0', '0', '1', '5', '9', '1', '4', '5', '0', '4', '6', '9', '3', '0', '3', '2', '0', '3', '1', '2', '3', '2', '8', '9', '5', '1', '1', '2', '2', '3', '4', '5', '2', '1', '5', '0', '2', '5', '2', '2', '2', '9', '6', '7'])
noncomputable def fragment0216586Acc00800 : List (String × SourceJson) := (fragment0216586Field007Key00, fragment0216586Field007Value00) :: fragment0216586Acc00700
noncomputable def fragment0216586Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '6', '7', '9', '4', '7', '2', '6', '2', '7', '8', '0', '4', '9', '6', '3', '6', '4', '6', '8', '6', '5', '9', '5', '8', '1', '5', '5', '5', '4', '9', '6', '6', '8', '6', '2', '8', '7', '6', '0', '7', '4', '9', '5', '2', '6', '0', '9', '1', '1', '7', '5', '0', '7', '4', '5', '6', '7', '5', '8', '1', '5', '4', '6', '2', '2', '5', '3', '7', '0', '2', '0', '6', '2', '0', '4', '3', '0', '2', '7', '9', '8', '0', '4', '4', '8', '8', '1', '9', '2', '0', '4', '6', '1', '0', '8', '3', '7', '3', '1', '2', '6', '5', '5', '6', '5', '4', '1', '8', '8', '4', '7', '8', '1', '3', '9', '7', '2', '1', '8', '5', '1', '3', '4', '5', '2', '6', '9', '6', '5', '7', '6', '3', '3', '1', '0', '9', '5', '0', '8', '9', '9', '9', '5', '9', '2', '1', '9', '4', '4', '3', '0', '6', '8', '0', '1', '6', '6', '9', '3', '2', '8', '9', '0', '8', '2', '3', '1', '2', '8', '9', '0', '6', '0', '0', '6', '5', '0', '8', '3', '8', '3', '6', '4', '7', '7', '0', '1', '5', '8', '8', '8', '6', '1', '0', '8', '1', '4', '5', '4', '6', '8', '5', '0', '8', '7', '3', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '0', '2', '9', '2', '2', '3', '0', '6', '0', '0', '8', '2', '7', '7', '4', '4', '5', '6', '4', '8', '4', '6', '5', '5', '4', '6', '4', '8', '6', '3', '8', '1', '7', '5', '2', '4', '0', '0', '2', '7', '4', '2', '2', '5', '8', '2', '0', '2', '9', '8', '2', '6', '3', '3', '7', '7', '5', '7', '5', '5', '3', '5', '3', '5', '9', '1', '1', '0', '4', '7', '0', '5', '4', '0', '4', '9', '4', '3', '7', '9', '2', '8', '8', '9', '5', '9', '4', '9', '7', '5', '7', '6', '0', '5', '9', '4', '1', '0', '4', '1', '6', '0', '9', '1', '3', '5', '0', '4', '4', '9', '7', '9', '9', '8', '2', '4', '2', '2', '9', '5', '9', '3', '2', '5', '0', '7', '0', '7', '8', '5', '2', '2', '3', '9', '2', '7', '8', '1', '0', '0', '1', '3', '2', '4', '1', '3', '5', '4', '3', '4', '6', '5', '9', '2', '6', '5', '0', '0', '4', '9', '1', '9', '1', '6', '9', '0', '7', '4', '0', '5', '6', '4', '6', '5', '7', '6', '4', '9', '2', '4', '7', '7', '8', '3', '9', '8', '5', '5', '5', '6', '6', '3', '8', '1', '4', '1', '2', '7', '7', '1', '0', '0', '1', '5', '9', '1', '4', '5', '0', '4', '6', '9', '3', '0', '3', '2', '0', '3', '1', '2', '3', '2', '8', '9', '5', '1', '1', '2', '2', '3', '4', '5', '2', '1', '5', '0', '2', '5', '2', '2', '2', '9', '6', '7', '"', ',']

theorem object_fragment0216586_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 483) (SourceJson.white (fragment0216586Field007Chars00 ++ tail)) fragment0216586Acc00700 =
      SourceJson.object (fuel + 482) (SourceJson.white tail) fragment0216586Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_007"
  err.flush

noncomputable def fragment0216586Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0216586Field008Value00 : SourceJson := .str (String.ofList ['2', '0', '7', '4', '7', '2', '0', '0', '5', '6', '3', '2', '2', '8', '4', '7'])
noncomputable def fragment0216586Acc00900 : List (String × SourceJson) := (fragment0216586Field008Key00, fragment0216586Field008Value00) :: fragment0216586Acc00800
noncomputable def fragment0216586Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '0', '7', '4', '7', '2', '0', '0', '5', '6', '3', '2', '2', '8', '4', '7', '"', ',']

theorem object_fragment0216586_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 482) (SourceJson.white (fragment0216586Field008Chars00 ++ tail)) fragment0216586Acc00800 =
      SourceJson.object (fuel + 481) (SourceJson.white tail) fragment0216586Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_008"
  err.flush

noncomputable def fragment0216586Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0216586Field009Value00 : SourceJson := .str (String.ofList ['5', '8', '6', '6', '8', '0', '8', '7', '0', '0', '3', '3', '0', '9', '9', '8'])
noncomputable def fragment0216586Acc01000 : List (String × SourceJson) := (fragment0216586Field009Key00, fragment0216586Field009Value00) :: fragment0216586Acc00900
noncomputable def fragment0216586Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '6', '6', '8', '0', '8', '7', '0', '0', '3', '3', '0', '9', '9', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0216586_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 481) (SourceJson.white (fragment0216586Field009Chars00 ++ tail)) fragment0216586Acc00900 =
      .ok (.obj (fragment0216586Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216586_object_field_009"
  err.flush

noncomputable def fragment0216586Chars : List Char := '{' :: (fragment0216586Field000Chars00 ++ fragment0216586Field001Chars00 ++ fragment0216586Field002Chars00 ++ fragment0216586Field003Chars00 ++ fragment0216586Field004Chars00 ++ fragment0216586Field005Chars00 ++ fragment0216586Field006Chars00 ++ fragment0216586Field007Chars00 ++ fragment0216586Field008Chars00 ++ fragment0216586Field009Chars00)
noncomputable def fragment0216586Value : SourceJson := .obj (fragment0216586Acc01000.reverse)

theorem value_fragment0216586 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 491) (fragment0216586Chars ++ tail) =
      .ok (fragment0216586Value, tail) := by
  have hinput : fragment0216586Chars ++ tail = '{' :: (fragment0216586Field000Chars00 ++ (fragment0216586Field001Chars00 ++ (fragment0216586Field002Chars00 ++ (fragment0216586Field003Chars00 ++ (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0216586Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 491) (fragment0216586Chars ++ tail) =
        SourceJson.value (fuel + 491) ('{' :: (fragment0216586Field000Chars00 ++ (fragment0216586Field001Chars00 ++ (fragment0216586Field002Chars00 ++ (fragment0216586Field003Chars00 ++ (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 491)) hinput
    _ = SourceJson.object (fuel + 490) (SourceJson.white (fragment0216586Field000Chars00 ++ (fragment0216586Field001Chars00 ++ (fragment0216586Field002Chars00 ++ (fragment0216586Field003Chars00 ++ (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))))))))))) fragment0216586Acc00000 := by rfl
    _ = SourceJson.object (fuel + 489) (SourceJson.white (fragment0216586Field001Chars00 ++ (fragment0216586Field002Chars00 ++ (fragment0216586Field003Chars00 ++ (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail))))))))))) fragment0216586Acc00100 := object_fragment0216586_field_000 fuel (fragment0216586Field001Chars00 ++ (fragment0216586Field002Chars00 ++ (fragment0216586Field003Chars00 ++ (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 488) (SourceJson.white (fragment0216586Field002Chars00 ++ (fragment0216586Field003Chars00 ++ (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))))))))) fragment0216586Acc00200 := object_fragment0216586_field_001 fuel (fragment0216586Field002Chars00 ++ (fragment0216586Field003Chars00 ++ (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 487) (SourceJson.white (fragment0216586Field003Chars00 ++ (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail))))))))) fragment0216586Acc00300 := object_fragment0216586_field_002 fuel (fragment0216586Field003Chars00 ++ (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 486) (SourceJson.white (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))))))) fragment0216586Acc00400 := object_fragment0216586_field_003 fuel (fragment0216586Field004Chars00 ++ (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 485) (SourceJson.white (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail))))))) fragment0216586Acc00500 := object_fragment0216586_field_004 fuel (fragment0216586Field005Chars00 ++ (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 484) (SourceJson.white (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))))) fragment0216586Acc00600 := object_fragment0216586_field_005 fuel (fragment0216586Field006Chars00 ++ (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 483) (SourceJson.white (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail))))) fragment0216586Acc00700 := object_fragment0216586_field_006 fuel (fragment0216586Field007Chars00 ++ (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 482) (SourceJson.white (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))) fragment0216586Acc00800 := object_fragment0216586_field_007 fuel (fragment0216586Field008Chars00 ++ (fragment0216586Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 481) (SourceJson.white (fragment0216586Field009Chars00 ++ (tail))) fragment0216586Acc00900 := object_fragment0216586_field_008 fuel (fragment0216586Field009Chars00 ++ (tail))
    _ = .ok (fragment0216586Value, tail) := object_fragment0216586_field_009 fuel (tail)

noncomputable def fragment0218704Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0218704Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0218704Field000Value00 : SourceJson := .number (String.ofList ['4', '9'])
noncomputable def fragment0218704Acc00100 : List (String × SourceJson) := (fragment0218704Field000Key00, fragment0218704Field000Value00) :: fragment0218704Acc00000
noncomputable def fragment0218704Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '9', ',']

theorem object_fragment0218704_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 423) (SourceJson.white (fragment0218704Field000Chars00 ++ tail)) fragment0218704Acc00000 =
      SourceJson.object (fuel + 422) (SourceJson.white tail) fragment0218704Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_000"
  err.flush

noncomputable def fragment0218704Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0218704Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0218704Acc00200 : List (String × SourceJson) := (fragment0218704Field001Key00, fragment0218704Field001Value00) :: fragment0218704Acc00100
noncomputable def fragment0218704Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0218704_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 422) (SourceJson.white (fragment0218704Field001Chars00 ++ tail)) fragment0218704Acc00100 =
      SourceJson.object (fuel + 421) (SourceJson.white tail) fragment0218704Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_001"
  err.flush

noncomputable def fragment0218704Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0218704Field002Value00 : SourceJson := .str (String.ofList ['2', '9', '1', '2', '3', '0', '0', '0', '4', '7', '0', '5', '6', '6', '7', '5', '5', '7', '8', '5', '7', '0', '1', '0', '2', '4', '0', '2', '8', '9', '2', '8', '0', '2', '5', '3', '8', '6', '2', '6', '8', '6', '7', '/', '3', '8', '9', '0', '9', '5', '5', '0', '4', '2', '0', '5', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0218704Acc00300 : List (String × SourceJson) := (fragment0218704Field002Key00, fragment0218704Field002Value00) :: fragment0218704Acc00200
noncomputable def fragment0218704Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '9', '1', '2', '3', '0', '0', '0', '4', '7', '0', '5', '6', '6', '7', '5', '5', '7', '8', '5', '7', '0', '1', '0', '2', '4', '0', '2', '8', '9', '2', '8', '0', '2', '5', '3', '8', '6', '2', '6', '8', '6', '7', '/', '3', '8', '9', '0', '9', '5', '5', '0', '4', '2', '0', '5', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0218704_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0218704Field002Chars00 ++ tail)) fragment0218704Acc00200 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0218704Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_002"
  err.flush

noncomputable def fragment0218704Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0218704Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0218704Acc00400 : List (String × SourceJson) := (fragment0218704Field003Key00, fragment0218704Field003Value00) :: fragment0218704Acc00300
noncomputable def fragment0218704Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0218704_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0218704Field003Chars00 ++ tail)) fragment0218704Acc00300 =
      SourceJson.object (fuel + 419) (SourceJson.white tail) fragment0218704Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_003"
  err.flush

noncomputable def fragment0218704Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0218704Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0218704Acc00500 : List (String × SourceJson) := (fragment0218704Field004Key00, fragment0218704Field004Value00) :: fragment0218704Acc00400
noncomputable def fragment0218704Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0218704_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 419) (SourceJson.white (fragment0218704Field004Chars00 ++ tail)) fragment0218704Acc00400 =
      SourceJson.object (fuel + 418) (SourceJson.white tail) fragment0218704Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_004"
  err.flush

noncomputable def fragment0218704Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0218704Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '8', '5', '1', '4', '9', '5', '7', '7', '3', '9', '1', '8', '0', '5', '9', '6', '3', '7', '0', '6', '9', '3', '/', '4', '2', '8', '6', '9', '0', '4', '3', '7', '3', '4', '4', '6', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '2', '4', '3', '0', '9', '7', '4', '6', '4', '5', '6', '7', '1', '6', '1', '2', '7', '5', '6', '7', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '1', '6', '2', '6', '0', '5', '3', '1', '2', '8', '7', '3', '8', '3', '0', '3', '1', '7', '1', '/', '7', '4', '5', '5', '4', '8', '5', '8', '6', '6', '8', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '3', '5', '2', '6', '9', '0', '4', '6', '8', '1', '9', '6', '2', '4', '7', '7', '3', '3', '8', '7', '/', '9', '5', '2', '6', '4', '5', '4', '1', '6', '3', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '5', '0', '5', '0', '2', '7', '4', '2', '7', '5', '3', '5', '7', '2', '2', '0', '7', '2', '0', '1', '/', '2', '8', '5', '7', '9', '3', '6', '2', '4', '8', '9', '6', '4', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '2', '8', '2', '7', '1', '0', '0', '0', '2', '0', '9', '8', '5', '4', '5', '7', '4', '5', '0', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '5', '4', '3', '5', '2', '9', '2', '0', '8', '1', '3', '2', '5', '8', '0', '6', '6', '8', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '9', '5', '1', '1', '9', '7', '9', '2', '1', '3', '7', '6', '4', '3', '0', '3', '8', '2', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '7', '1', '1', '9', '6', '4', '9', '9', '0', '1', '1', '4', '1', '1', '9', '0', '7', '8', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '1', '7', '2', '9', '5', '0', '9', '9', '5', '8', '8', '8', '0', '9', '0', '3', '2', '5', '4', '9', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0218704Acc00600 : List (String × SourceJson) := (fragment0218704Field005Key00, fragment0218704Field005Value00) :: fragment0218704Acc00500
noncomputable def fragment0218704Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '1', '4', '9', '5', '7', '7', '3', '9', '1', '8', '0', '5', '9', '6', '3', '7', '0', '6', '9', '3', '/', '4', '2', '8', '6', '9', '0', '4', '3', '7', '3', '4', '4', '6', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '2', '4', '3', '0', '9', '7', '4', '6', '4', '5', '6', '7', '1', '6', '1', '2', '7', '5', '6', '7', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '1', '6', '2', '6', '0', '5', '3', '1', '2', '8', '7', '3', '8', '3', '0', '3', '1', '7', '1', '/', '7', '4', '5', '5', '4', '8', '5', '8', '6', '6', '8', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '3', '5', '2', '6', '9', '0', '4', '6', '8', '1', '9', '6', '2', '4', '7', '7', '3', '3', '8', '7', '/', '9', '5', '2', '6', '4', '5', '4', '1', '6', '3', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '5', '0', '5', '0', '2', '7', '4', '2', '7', '5', '3', '5', '7', '2', '2', '0', '7', '2', '0', '1', '/', '2', '8', '5', '7', '9', '3', '6', '2', '4', '8', '9', '6', '4', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '2', '8', '2', '7', '1', '0', '0', '0', '2', '0', '9', '8', '5', '4', '5', '7', '4', '5', '0', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '5', '4', '3', '5', '2', '9', '2', '0', '8', '1', '3', '2', '5', '8', '0', '6', '6', '8', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '9', '5', '1', '1', '9', '7', '9', '2', '1', '3', '7', '6', '4', '3', '0', '3', '8', '2', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '7', '1', '1', '9', '6', '4', '9', '9', '0', '1', '1', '4', '1', '1', '9', '0', '7', '8', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '7', '2', '9', '5', '0', '9', '9', '5', '8', '8', '8', '0', '9', '0', '3', '2', '5', '4', '9', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0218704_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 418) (SourceJson.white (fragment0218704Field005Chars00 ++ tail)) fragment0218704Acc00500 =
      SourceJson.object (fuel + 417) (SourceJson.white tail) fragment0218704Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_005"
  err.flush

noncomputable def fragment0218704Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0218704Field006Value00 : SourceJson := .str (String.ofList ['9', '0', '7', '3', '6', '2', '2', '0', '0', '9', '1', '1', '2', '8', '8', '6', '8', '4', '3', '3', '6', '1', '7', '3', '5', '5', '7', '8', '9', '2', '5', '2', '6', '0', '3', '6', '5', '5', '1', '9', '3', '0', '7', '5', '5', '5', '6', '7', '3', '6', '/', '5', '8', '6', '5', '3', '4', '0', '1', '0', '5', '7', '3', '7', '8', '6', '3', '2', '3', '3', '3', '3', '1', '7', '7', '3', '1', '1', '7', '3', '6', '3', '8', '0', '5', '7', '1', '8', '7', '9', '6', '5', '8', '4', '6', '8', '3', '6', '6', '6', '3', '8', '3', '7', '4', '0', '3', '5', '3', '0', '5', '1', '9', '1'])
noncomputable def fragment0218704Acc00700 : List (String × SourceJson) := (fragment0218704Field006Key00, fragment0218704Field006Value00) :: fragment0218704Acc00600
noncomputable def fragment0218704Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '0', '7', '3', '6', '2', '2', '0', '0', '9', '1', '1', '2', '8', '8', '6', '8', '4', '3', '3', '6', '1', '7', '3', '5', '5', '7', '8', '9', '2', '5', '2', '6', '0', '3', '6', '5', '5', '1', '9', '3', '0', '7', '5', '5', '5', '6', '7', '3', '6', '/', '5', '8', '6', '5', '3', '4', '0', '1', '0', '5', '7', '3', '7', '8', '6', '3', '2', '3', '3', '3', '3', '1', '7', '7', '3', '1', '1', '7', '3', '6', '3', '8', '0', '5', '7', '1', '8', '7', '9', '6', '5', '8', '4', '6', '8', '3', '6', '6', '6', '3', '8', '3', '7', '4', '0', '3', '5', '3', '0', '5', '1', '9', '1', '"', ',']

theorem object_fragment0218704_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 417) (SourceJson.white (fragment0218704Field006Chars00 ++ tail)) fragment0218704Acc00600 =
      SourceJson.object (fuel + 416) (SourceJson.white tail) fragment0218704Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_006"
  err.flush

noncomputable def fragment0218704Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0218704Field007Value00 : SourceJson := .str (String.ofList ['2', '6', '3', '4', '0', '6', '4', '3', '3', '0', '8', '2', '1', '8', '5', '2', '6', '2', '5', '1', '9', '6', '5', '7', '1', '6', '4', '2', '6', '3', '7', '6', '3', '9', '4', '8', '7', '8', '8', '5', '6', '6', '7', '0', '6', '5', '2', '2', '8', '9', '9', '0', '8', '5', '4', '2', '5', '6', '6', '7', '0', '9', '6', '9', '6', '2', '0', '0', '2', '0', '4', '9', '2', '3', '7', '3', '0', '5', '4', '6', '2', '3', '9', '5', '0', '0', '0', '9', '4', '2', '0', '1', '8', '2', '7', '5', '6', '0', '5', '5', '7', '1', '5', '2', '0', '2', '1', '2', '6', '3', '9', '3', '4', '7', '8', '3', '6', '0', '3', '2', '8', '0', '2', '2', '2', '1', '0', '3', '4', '4', '1', '0', '4', '6', '0', '3', '6', '6', '4', '4', '1', '2', '6', '6', '7', '5', '2', '5', '6', '8', '9', '7', '4', '8', '7', '0', '7', '3', '3', '8', '6', '7', '6', '3', '7', '3', '3', '4', '3', '5', '4', '7', '4', '2', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '5', '1', '0', '2', '3', '3', '3', '2', '0', '8', '7', '8', '1', '6', '1', '4', '3', '5', '9', '6', '4', '1', '1', '4', '2', '1', '6', '5', '2', '1', '7', '7', '3', '7', '4', '8', '2', '8', '5', '3', '8', '7', '3', '5', '6', '9', '3', '8', '4', '4', '4', '2', '4', '4', '4', '6', '5', '4', '6', '2', '8', '9', '0', '3', '2', '0', '2', '1', '9', '3', '3', '7', '3', '4', '0', '6', '7', '1', '2', '5', '1', '8', '0', '2', '5', '3', '3', '9', '0', '8', '6', '6', '2', '4', '3', '7', '8', '0', '7', '7', '8', '8', '0', '1', '7', '0', '6', '0', '4', '3', '6', '5', '5', '8', '2', '2', '1', '3', '0', '2', '1', '6', '4', '0', '2', '0', '1', '7', '3', '8', '6', '6', '9', '5', '0', '5', '7', '4', '5', '0', '5', '7', '6', '4', '1', '1', '3', '2', '9', '3', '1', '9', '6', '0', '0', '3', '2', '6', '3', '0', '9', '9', '6', '5', '4', '6', '9', '6', '7', '5', '8', '7', '5', '4', '4', '0', '3', '5', '5', '6', '1', '7', '4', '0', '7', '1', '5', '1', '6', '0', '3', '4', '2', '3', '8', '2', '4', '3', '8', '4', '3', '1', '2', '8', '2', '5', '2', '2', '0', '0', '3'])
noncomputable def fragment0218704Acc00800 : List (String × SourceJson) := (fragment0218704Field007Key00, fragment0218704Field007Value00) :: fragment0218704Acc00700
noncomputable def fragment0218704Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '3', '4', '0', '6', '4', '3', '3', '0', '8', '2', '1', '8', '5', '2', '6', '2', '5', '1', '9', '6', '5', '7', '1', '6', '4', '2', '6', '3', '7', '6', '3', '9', '4', '8', '7', '8', '8', '5', '6', '6', '7', '0', '6', '5', '2', '2', '8', '9', '9', '0', '8', '5', '4', '2', '5', '6', '6', '7', '0', '9', '6', '9', '6', '2', '0', '0', '2', '0', '4', '9', '2', '3', '7', '3', '0', '5', '4', '6', '2', '3', '9', '5', '0', '0', '0', '9', '4', '2', '0', '1', '8', '2', '7', '5', '6', '0', '5', '5', '7', '1', '5', '2', '0', '2', '1', '2', '6', '3', '9', '3', '4', '7', '8', '3', '6', '0', '3', '2', '8', '0', '2', '2', '2', '1', '0', '3', '4', '4', '1', '0', '4', '6', '0', '3', '6', '6', '4', '4', '1', '2', '6', '6', '7', '5', '2', '5', '6', '8', '9', '7', '4', '8', '7', '0', '7', '3', '3', '8', '6', '7', '6', '3', '7', '3', '3', '4', '3', '5', '4', '7', '4', '2', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '5', '1', '0', '2', '3', '3', '3', '2', '0', '8', '7', '8', '1', '6', '1', '4', '3', '5', '9', '6', '4', '1', '1', '4', '2', '1', '6', '5', '2', '1', '7', '7', '3', '7', '4', '8', '2', '8', '5', '3', '8', '7', '3', '5', '6', '9', '3', '8', '4', '4', '4', '2', '4', '4', '4', '6', '5', '4', '6', '2', '8', '9', '0', '3', '2', '0', '2', '1', '9', '3', '3', '7', '3', '4', '0', '6', '7', '1', '2', '5', '1', '8', '0', '2', '5', '3', '3', '9', '0', '8', '6', '6', '2', '4', '3', '7', '8', '0', '7', '7', '8', '8', '0', '1', '7', '0', '6', '0', '4', '3', '6', '5', '5', '8', '2', '2', '1', '3', '0', '2', '1', '6', '4', '0', '2', '0', '1', '7', '3', '8', '6', '6', '9', '5', '0', '5', '7', '4', '5', '0', '5', '7', '6', '4', '1', '1', '3', '2', '9', '3', '1', '9', '6', '0', '0', '3', '2', '6', '3', '0', '9', '9', '6', '5', '4', '6', '9', '6', '7', '5', '8', '7', '5', '4', '4', '0', '3', '5', '5', '6', '1', '7', '4', '0', '7', '1', '5', '1', '6', '0', '3', '4', '2', '3', '8', '2', '4', '3', '8', '4', '3', '1', '2', '8', '2', '5', '2', '2', '0', '0', '3', '"', ',']

theorem object_fragment0218704_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 416) (SourceJson.white (fragment0218704Field007Chars00 ++ tail)) fragment0218704Acc00700 =
      SourceJson.object (fuel + 415) (SourceJson.white tail) fragment0218704Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_007"
  err.flush

noncomputable def fragment0218704Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0218704Field008Value00 : SourceJson := .str (String.ofList ['1', '2', '2', '5', '6', '5', '1', '6', '8', '6', '2', '9', '8', '1', '8', '9', '7'])
noncomputable def fragment0218704Acc00900 : List (String × SourceJson) := (fragment0218704Field008Key00, fragment0218704Field008Value00) :: fragment0218704Acc00800
noncomputable def fragment0218704Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '2', '5', '6', '5', '1', '6', '8', '6', '2', '9', '8', '1', '8', '9', '7', '"', ',']

theorem object_fragment0218704_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 415) (SourceJson.white (fragment0218704Field008Chars00 ++ tail)) fragment0218704Acc00800 =
      SourceJson.object (fuel + 414) (SourceJson.white tail) fragment0218704Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_008"
  err.flush

noncomputable def fragment0218704Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0218704Field009Value00 : SourceJson := .str (String.ofList ['4', '6', '2', '7', '0', '7', '9', '3', '9', '9', '8', '4', '6', '8', '2', '3', '3'])
noncomputable def fragment0218704Acc01000 : List (String × SourceJson) := (fragment0218704Field009Key00, fragment0218704Field009Value00) :: fragment0218704Acc00900
noncomputable def fragment0218704Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '6', '2', '7', '0', '7', '9', '3', '9', '9', '8', '4', '6', '8', '2', '3', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0218704_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 414) (SourceJson.white (fragment0218704Field009Chars00 ++ tail)) fragment0218704Acc00900 =
      .ok (.obj (fragment0218704Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0218704_object_field_009"
  err.flush

noncomputable def fragment0218704Chars : List Char := '{' :: (fragment0218704Field000Chars00 ++ fragment0218704Field001Chars00 ++ fragment0218704Field002Chars00 ++ fragment0218704Field003Chars00 ++ fragment0218704Field004Chars00 ++ fragment0218704Field005Chars00 ++ fragment0218704Field006Chars00 ++ fragment0218704Field007Chars00 ++ fragment0218704Field008Chars00 ++ fragment0218704Field009Chars00)
noncomputable def fragment0218704Value : SourceJson := .obj (fragment0218704Acc01000.reverse)

theorem value_fragment0218704 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 424) (fragment0218704Chars ++ tail) =
      .ok (fragment0218704Value, tail) := by
  have hinput : fragment0218704Chars ++ tail = '{' :: (fragment0218704Field000Chars00 ++ (fragment0218704Field001Chars00 ++ (fragment0218704Field002Chars00 ++ (fragment0218704Field003Chars00 ++ (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0218704Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 424) (fragment0218704Chars ++ tail) =
        SourceJson.value (fuel + 424) ('{' :: (fragment0218704Field000Chars00 ++ (fragment0218704Field001Chars00 ++ (fragment0218704Field002Chars00 ++ (fragment0218704Field003Chars00 ++ (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 424)) hinput
    _ = SourceJson.object (fuel + 423) (SourceJson.white (fragment0218704Field000Chars00 ++ (fragment0218704Field001Chars00 ++ (fragment0218704Field002Chars00 ++ (fragment0218704Field003Chars00 ++ (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))))))))))) fragment0218704Acc00000 := by rfl
    _ = SourceJson.object (fuel + 422) (SourceJson.white (fragment0218704Field001Chars00 ++ (fragment0218704Field002Chars00 ++ (fragment0218704Field003Chars00 ++ (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail))))))))))) fragment0218704Acc00100 := object_fragment0218704_field_000 fuel (fragment0218704Field001Chars00 ++ (fragment0218704Field002Chars00 ++ (fragment0218704Field003Chars00 ++ (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0218704Field002Chars00 ++ (fragment0218704Field003Chars00 ++ (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))))))))) fragment0218704Acc00200 := object_fragment0218704_field_001 fuel (fragment0218704Field002Chars00 ++ (fragment0218704Field003Chars00 ++ (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0218704Field003Chars00 ++ (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail))))))))) fragment0218704Acc00300 := object_fragment0218704_field_002 fuel (fragment0218704Field003Chars00 ++ (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 419) (SourceJson.white (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))))))) fragment0218704Acc00400 := object_fragment0218704_field_003 fuel (fragment0218704Field004Chars00 ++ (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 418) (SourceJson.white (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail))))))) fragment0218704Acc00500 := object_fragment0218704_field_004 fuel (fragment0218704Field005Chars00 ++ (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 417) (SourceJson.white (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))))) fragment0218704Acc00600 := object_fragment0218704_field_005 fuel (fragment0218704Field006Chars00 ++ (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 416) (SourceJson.white (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail))))) fragment0218704Acc00700 := object_fragment0218704_field_006 fuel (fragment0218704Field007Chars00 ++ (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 415) (SourceJson.white (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))) fragment0218704Acc00800 := object_fragment0218704_field_007 fuel (fragment0218704Field008Chars00 ++ (fragment0218704Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 414) (SourceJson.white (fragment0218704Field009Chars00 ++ (tail))) fragment0218704Acc00900 := object_fragment0218704_field_008 fuel (fragment0218704Field009Chars00 ++ (tail))
    _ = .ok (fragment0218704Value, tail) := object_fragment0218704_field_009 fuel (tail)

noncomputable def fragment0220688Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0220688Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0220688Field000Value00 : SourceJson := .number (String.ofList ['5', '0'])
noncomputable def fragment0220688Acc00100 : List (String × SourceJson) := (fragment0220688Field000Key00, fragment0220688Field000Value00) :: fragment0220688Acc00000
noncomputable def fragment0220688Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '0', ',']

theorem object_fragment0220688_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0220688Field000Chars00 ++ tail)) fragment0220688Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0220688Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_000"
  err.flush

noncomputable def fragment0220688Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0220688Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0220688Acc00200 : List (String × SourceJson) := (fragment0220688Field001Key00, fragment0220688Field001Value00) :: fragment0220688Acc00100
noncomputable def fragment0220688Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0220688_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0220688Field001Chars00 ++ tail)) fragment0220688Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0220688Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_001"
  err.flush

noncomputable def fragment0220688Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0220688Field002Value00 : SourceJson := .str (String.ofList ['6', '4', '4', '4', '5', '8', '0', '7', '1', '6', '6', '1', '1', '6', '1', '1', '9', '5', '0', '4', '2', '4', '2', '1', '5', '1', '8', '0', '9', '9', '7', '3', '6', '5', '6', '3', '5', '5', '3', '4', '8', '0', '8', '7', '/', '8', '5', '7', '5', '9', '8', '2', '5', '4', '1', '6', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0220688Acc00300 : List (String × SourceJson) := (fragment0220688Field002Key00, fragment0220688Field002Value00) :: fragment0220688Acc00200
noncomputable def fragment0220688Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '4', '4', '4', '5', '8', '0', '7', '1', '6', '6', '1', '1', '6', '1', '1', '9', '5', '0', '4', '2', '4', '2', '1', '5', '1', '8', '0', '9', '9', '7', '3', '6', '5', '6', '3', '5', '5', '3', '4', '8', '0', '8', '7', '/', '8', '5', '7', '5', '9', '8', '2', '5', '4', '1', '6', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0220688_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0220688Field002Chars00 ++ tail)) fragment0220688Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0220688Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_002"
  err.flush

noncomputable def fragment0220688Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0220688Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0220688Acc00400 : List (String × SourceJson) := (fragment0220688Field003Key00, fragment0220688Field003Value00) :: fragment0220688Acc00300
noncomputable def fragment0220688Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0220688_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0220688Field003Chars00 ++ tail)) fragment0220688Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0220688Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_003"
  err.flush

noncomputable def fragment0220688Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0220688Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0220688Acc00500 : List (String × SourceJson) := (fragment0220688Field004Key00, fragment0220688Field004Value00) :: fragment0220688Acc00400
noncomputable def fragment0220688Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0220688_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0220688Field004Chars00 ++ tail)) fragment0220688Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0220688Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_004"
  err.flush

noncomputable def fragment0220688Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0220688Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '8', '0', '8', '2', '2', '3', '7', '2', '8', '4', '7', '7', '1', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '4', '6', '4', '3', '7', '4', '6', '9', '2', '6', '3', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '1', '0', '5', '1', '5', '6', '8', '2', '4', '8', '7', '/', '2', '2', '2', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '7', '9', '1', '2', '2', '5', '3', '6', '2', '4', '7', '4', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '5', '1', '9', '4', '8', '7', '0', '6', '1', '8', '6', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '3', '8', '6', '1', '6', '1', '7', '1', '9', '7', '6', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '4', '1', '9', '3', '8', '4', '7', '0', '3', '6', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '7', '7', '7', '4', '7', '0', '4', '8', '9', '7', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '9', '6', '7', '1', '2', '0', '4', '1', '7', '7', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '5', '3', '6', '2', '8', '9', '0', '2', '8', '7', '8', '3', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0220688Acc00600 : List (String × SourceJson) := (fragment0220688Field005Key00, fragment0220688Field005Value00) :: fragment0220688Acc00500
noncomputable def fragment0220688Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '0', '8', '2', '2', '3', '7', '2', '8', '4', '7', '7', '1', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '4', '6', '4', '3', '7', '4', '6', '9', '2', '6', '3', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '0', '5', '1', '5', '6', '8', '2', '4', '8', '7', '/', '2', '2', '2', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '7', '9', '1', '2', '2', '5', '3', '6', '2', '4', '7', '4', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '5', '1', '9', '4', '8', '7', '0', '6', '1', '8', '6', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '3', '8', '6', '1', '6', '1', '7', '1', '9', '7', '6', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '4', '1', '9', '3', '8', '4', '7', '0', '3', '6', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '7', '7', '7', '4', '7', '0', '4', '8', '9', '7', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '9', '6', '7', '1', '2', '0', '4', '1', '7', '7', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '3', '6', '2', '8', '9', '0', '2', '8', '7', '8', '3', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0220688_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0220688Field005Chars00 ++ tail)) fragment0220688Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0220688Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_005"
  err.flush

noncomputable def fragment0220688Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0220688Field006Value00 : SourceJson := .str (String.ofList ['6', '0', '5', '5', '5', '3', '2', '1', '4', '0', '5', '2', '1', '1', '8', '8', '7', '6', '0', '8', '3', '0', '9', '9', '8', '1', '0', '3', '1', '2', '5', '7', '7', '9', '0', '2', '3', '9', '2', '8', '9', '8', '7', '2', '5', '9', '2', '2', '3', '6', '5', '4', '4', '0', '0', '0', '/', '9', '8', '1', '7', '4', '3', '8', '6', '7', '2', '4', '8', '7', '5', '6', '8', '0', '9', '3', '9', '3', '1', '3', '2', '4', '9', '7', '8', '2', '4', '3', '9', '0', '5', '9', '6', '0', '9', '7', '0', '6', '6', '6', '7', '2', '7', '9', '4', '1', '2', '5', '5', '4', '1', '9', '8', '5', '7', '3', '9', '1', '7', '6', '4', '3', '6', '9', '9'])
noncomputable def fragment0220688Acc00700 : List (String × SourceJson) := (fragment0220688Field006Key00, fragment0220688Field006Value00) :: fragment0220688Acc00600
noncomputable def fragment0220688Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '0', '5', '5', '5', '3', '2', '1', '4', '0', '5', '2', '1', '1', '8', '8', '7', '6', '0', '8', '3', '0', '9', '9', '8', '1', '0', '3', '1', '2', '5', '7', '7', '9', '0', '2', '3', '9', '2', '8', '9', '8', '7', '2', '5', '9', '2', '2', '3', '6', '5', '4', '4', '0', '0', '0', '/', '9', '8', '1', '7', '4', '3', '8', '6', '7', '2', '4', '8', '7', '5', '6', '8', '0', '9', '3', '9', '3', '1', '3', '2', '4', '9', '7', '8', '2', '4', '3', '9', '0', '5', '9', '6', '0', '9', '7', '0', '6', '6', '6', '7', '2', '7', '9', '4', '1', '2', '5', '5', '4', '1', '9', '8', '5', '7', '3', '9', '1', '7', '6', '4', '3', '6', '9', '9', '"', ',']

theorem object_fragment0220688_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0220688Field006Chars00 ++ tail)) fragment0220688Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0220688Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_006"
  err.flush

noncomputable def fragment0220688Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0220688Field007Value00 : SourceJson := .str (String.ofList ['1', '3', '2', '0', '2', '3', '4', '7', '9', '6', '7', '1', '9', '4', '4', '8', '4', '7', '0', '2', '7', '8', '2', '6', '4', '0', '9', '7', '1', '2', '5', '1', '0', '0', '1', '0', '2', '1', '0', '6', '6', '3', '4', '5', '3', '4', '7', '3', '6', '1', '1', '5', '8', '8', '4', '0', '0', '9', '6', '1', '3', '9', '2', '5', '1', '5', '0', '4', '0', '1', '9', '2', '0', '4', '7', '9', '4', '3', '2', '5', '5', '1', '2', '7', '4', '9', '8', '5', '7', '6', '2', '7', '1', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '0', '9', '7', '9', '3', '3', '6', '4', '7', '1', '9', '7', '7', '2', '1', '7', '8', '7', '2', '3', '9', '5', '5', '8', '7', '0', '7', '4', '6', '2', '2', '1', '8', '6', '1', '1', '6', '1', '0', '6', '7', '3', '4', '4', '0', '2', '6', '6', '6', '2', '7', '7', '1', '6', '4', '6', '0', '4', '2', '2', '2', '9', '0', '5', '7', '9', '8', '5', '6', '7', '3', '8', '1', '2', '3', '0', '5', '3', '1', '8', '4', '1', '6', '9', '7', '4', '2', '8', '6', '6', '8', '4', '4', '5', '4', '3', '9', '1', '9', '3', '4', '5', '9', '5', '6', '5', '5', '9', '6', '7', '1', '2', '7', '9', '2', '7', '9', '1', '9', '3', '8', '0', '7', '9', '5', '3', '5', '9'])
noncomputable def fragment0220688Acc00800 : List (String × SourceJson) := (fragment0220688Field007Key00, fragment0220688Field007Value00) :: fragment0220688Acc00700
noncomputable def fragment0220688Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '2', '0', '2', '3', '4', '7', '9', '6', '7', '1', '9', '4', '4', '8', '4', '7', '0', '2', '7', '8', '2', '6', '4', '0', '9', '7', '1', '2', '5', '1', '0', '0', '1', '0', '2', '1', '0', '6', '6', '3', '4', '5', '3', '4', '7', '3', '6', '1', '1', '5', '8', '8', '4', '0', '0', '9', '6', '1', '3', '9', '2', '5', '1', '5', '0', '4', '0', '1', '9', '2', '0', '4', '7', '9', '4', '3', '2', '5', '5', '1', '2', '7', '4', '9', '8', '5', '7', '6', '2', '7', '1', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '6', '0', '9', '7', '9', '3', '3', '6', '4', '7', '1', '9', '7', '7', '2', '1', '7', '8', '7', '2', '3', '9', '5', '5', '8', '7', '0', '7', '4', '6', '2', '2', '1', '8', '6', '1', '1', '6', '1', '0', '6', '7', '3', '4', '4', '0', '2', '6', '6', '6', '2', '7', '7', '1', '6', '4', '6', '0', '4', '2', '2', '2', '9', '0', '5', '7', '9', '8', '5', '6', '7', '3', '8', '1', '2', '3', '0', '5', '3', '1', '8', '4', '1', '6', '9', '7', '4', '2', '8', '6', '6', '8', '4', '4', '5', '4', '3', '9', '1', '9', '3', '4', '5', '9', '5', '6', '5', '5', '9', '6', '7', '1', '2', '7', '9', '2', '7', '9', '1', '9', '3', '8', '0', '7', '9', '5', '3', '5', '9', '"', ',']

theorem object_fragment0220688_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0220688Field007Chars00 ++ tail)) fragment0220688Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0220688Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_007"
  err.flush

noncomputable def fragment0220688Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0220688Field008Value00 : SourceJson := .str (String.ofList ['4', '8', '8', '6', '9', '0', '2', '7', '9', '1', '4', '9', '9', '6', '7', '6', '3'])
noncomputable def fragment0220688Acc00900 : List (String × SourceJson) := (fragment0220688Field008Key00, fragment0220688Field008Value00) :: fragment0220688Acc00800
noncomputable def fragment0220688Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '8', '8', '6', '9', '0', '2', '7', '9', '1', '4', '9', '9', '6', '7', '6', '3', '"', ',']

theorem object_fragment0220688_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0220688Field008Chars00 ++ tail)) fragment0220688Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0220688Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_008"
  err.flush

noncomputable def fragment0220688Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0220688Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '6', '9', '0', '7', '7', '3', '4', '8', '0', '6', '5', '3', '3', '5', '4', '8'])
noncomputable def fragment0220688Acc01000 : List (String × SourceJson) := (fragment0220688Field009Key00, fragment0220688Field009Value00) :: fragment0220688Acc00900
noncomputable def fragment0220688Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '6', '9', '0', '7', '7', '3', '4', '8', '0', '6', '5', '3', '3', '5', '4', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0220688_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0220688Field009Chars00 ++ tail)) fragment0220688Acc00900 =
      .ok (.obj (fragment0220688Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0220688_object_field_009"
  err.flush

noncomputable def fragment0220688Chars : List Char := '{' :: (fragment0220688Field000Chars00 ++ fragment0220688Field001Chars00 ++ fragment0220688Field002Chars00 ++ fragment0220688Field003Chars00 ++ fragment0220688Field004Chars00 ++ fragment0220688Field005Chars00 ++ fragment0220688Field006Chars00 ++ fragment0220688Field007Chars00 ++ fragment0220688Field008Chars00 ++ fragment0220688Field009Chars00)
noncomputable def fragment0220688Value : SourceJson := .obj (fragment0220688Acc01000.reverse)

theorem value_fragment0220688 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0220688Chars ++ tail) =
      .ok (fragment0220688Value, tail) := by
  have hinput : fragment0220688Chars ++ tail = '{' :: (fragment0220688Field000Chars00 ++ (fragment0220688Field001Chars00 ++ (fragment0220688Field002Chars00 ++ (fragment0220688Field003Chars00 ++ (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0220688Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0220688Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0220688Field000Chars00 ++ (fragment0220688Field001Chars00 ++ (fragment0220688Field002Chars00 ++ (fragment0220688Field003Chars00 ++ (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0220688Field000Chars00 ++ (fragment0220688Field001Chars00 ++ (fragment0220688Field002Chars00 ++ (fragment0220688Field003Chars00 ++ (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))))))))))) fragment0220688Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0220688Field001Chars00 ++ (fragment0220688Field002Chars00 ++ (fragment0220688Field003Chars00 ++ (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail))))))))))) fragment0220688Acc00100 := object_fragment0220688_field_000 fuel (fragment0220688Field001Chars00 ++ (fragment0220688Field002Chars00 ++ (fragment0220688Field003Chars00 ++ (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0220688Field002Chars00 ++ (fragment0220688Field003Chars00 ++ (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))))))))) fragment0220688Acc00200 := object_fragment0220688_field_001 fuel (fragment0220688Field002Chars00 ++ (fragment0220688Field003Chars00 ++ (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0220688Field003Chars00 ++ (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail))))))))) fragment0220688Acc00300 := object_fragment0220688_field_002 fuel (fragment0220688Field003Chars00 ++ (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))))))) fragment0220688Acc00400 := object_fragment0220688_field_003 fuel (fragment0220688Field004Chars00 ++ (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail))))))) fragment0220688Acc00500 := object_fragment0220688_field_004 fuel (fragment0220688Field005Chars00 ++ (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))))) fragment0220688Acc00600 := object_fragment0220688_field_005 fuel (fragment0220688Field006Chars00 ++ (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail))))) fragment0220688Acc00700 := object_fragment0220688_field_006 fuel (fragment0220688Field007Chars00 ++ (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))) fragment0220688Acc00800 := object_fragment0220688_field_007 fuel (fragment0220688Field008Chars00 ++ (fragment0220688Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0220688Field009Chars00 ++ (tail))) fragment0220688Acc00900 := object_fragment0220688_field_008 fuel (fragment0220688Field009Chars00 ++ (tail))
    _ = .ok (fragment0220688Value, tail) := object_fragment0220688_field_009 fuel (tail)

noncomputable def fragment0222362Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0222362Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0222362Field000Value00 : SourceJson := .number (String.ofList ['5', '1'])
noncomputable def fragment0222362Acc00100 : List (String × SourceJson) := (fragment0222362Field000Key00, fragment0222362Field000Value00) :: fragment0222362Acc00000
noncomputable def fragment0222362Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '1', ',']

theorem object_fragment0222362_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 493) (SourceJson.white (fragment0222362Field000Chars00 ++ tail)) fragment0222362Acc00000 =
      SourceJson.object (fuel + 492) (SourceJson.white tail) fragment0222362Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_000"
  err.flush

noncomputable def fragment0222362Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0222362Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0222362Acc00200 : List (String × SourceJson) := (fragment0222362Field001Key00, fragment0222362Field001Value00) :: fragment0222362Acc00100
noncomputable def fragment0222362Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0222362_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 492) (SourceJson.white (fragment0222362Field001Chars00 ++ tail)) fragment0222362Acc00100 =
      SourceJson.object (fuel + 491) (SourceJson.white tail) fragment0222362Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_001"
  err.flush

noncomputable def fragment0222362Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0222362Field002Value00 : SourceJson := .str (String.ofList ['3', '4', '8', '8', '1', '4', '0', '8', '9', '4', '0', '1', '2', '4', '3', '7', '5', '4', '7', '7', '5', '6', '8', '2', '7', '5', '7', '5', '4', '6', '2', '8', '1', '1', '9', '6', '7', '/', '4', '1', '0', '9', '6', '4', '4', '9', '6', '7', '2', '2', '9', '8', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0222362Acc00300 : List (String × SourceJson) := (fragment0222362Field002Key00, fragment0222362Field002Value00) :: fragment0222362Acc00200
noncomputable def fragment0222362Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '4', '8', '8', '1', '4', '0', '8', '9', '4', '0', '1', '2', '4', '3', '7', '5', '4', '7', '7', '5', '6', '8', '2', '7', '5', '7', '5', '4', '6', '2', '8', '1', '1', '9', '6', '7', '/', '4', '1', '0', '9', '6', '4', '4', '9', '6', '7', '2', '2', '9', '8', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0222362_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 491) (SourceJson.white (fragment0222362Field002Chars00 ++ tail)) fragment0222362Acc00200 =
      SourceJson.object (fuel + 490) (SourceJson.white tail) fragment0222362Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_002"
  err.flush

noncomputable def fragment0222362Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0222362Field003Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0222362Acc00400 : List (String × SourceJson) := (fragment0222362Field003Key00, fragment0222362Field003Value00) :: fragment0222362Acc00300
noncomputable def fragment0222362Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0222362_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 490) (SourceJson.white (fragment0222362Field003Chars00 ++ tail)) fragment0222362Acc00300 =
      SourceJson.object (fuel + 489) (SourceJson.white tail) fragment0222362Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_003"
  err.flush

noncomputable def fragment0222362Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0222362Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '2', '8', '2', '3', '3', '/', '1', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0222362Acc00500 : List (String × SourceJson) := (fragment0222362Field004Key00, fragment0222362Field004Value00) :: fragment0222362Acc00400
noncomputable def fragment0222362Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '2', '8', '2', '3', '3', '/', '1', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0222362_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 489) (SourceJson.white (fragment0222362Field004Chars00 ++ tail)) fragment0222362Acc00400 =
      SourceJson.object (fuel + 488) (SourceJson.white tail) fragment0222362Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_004"
  err.flush

noncomputable def fragment0222362Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0222362Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '5', '3', '8', '9', '7', '9', '9', '4', '0', '1', '9', '2', '2', '7', '2', '1', '0', '6', '7', '9', '7', '2', '1', '4', '1', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '7', '8', '4', '7', '4', '0', '9', '4', '8', '3', '6', '5', '8', '5', '3', '5', '1', '4', '4', '8', '1', '1', '/', '7', '2', '2', '9', '3', '0', '7', '3', '8', '0', '0', '5', '9', '4', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '3', '6', '7', '4', '9', '5', '0', '3', '7', '0', '9', '6', '8', '0', '5', '1', '6', '0', '0', '5', '2', '0', '9', '/', '9', '6', '7', '1', '2', '0', '6', '7', '6', '1', '7', '6', '8', '4', '4', '9', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '4', '0', '6', '2', '2', '7', '6', '5', '0', '5', '3', '7', '1', '1', '8', '3', '1', '5', '6', '8', '4', '7', '0', '8', '7', '/', '4', '3', '5', '2', '0', '4', '3', '0', '4', '2', '7', '9', '5', '8', '0', '2', '3', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '1', '6', '9', '7', '3', '1', '3', '2', '4', '2', '8', '2', '8', '3', '6', '7', '3', '9', '0', '1', '8', '7', '5', '6', '7', '/', '4', '3', '5', '2', '0', '4', '3', '0', '4', '2', '7', '9', '5', '8', '0', '2', '3', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '3', '7', '5', '7', '9', '5', '9', '9', '5', '5', '9', '4', '7', '7', '9', '2', '9', '5', '7', '5', '3', '0', '1', '/', '4', '3', '9', '6', '0', '0', '3', '0', '7', '3', '5', '3', '1', '1', '1', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '7', '9', '9', '4', '2', '7', '7', '9', '4', '3', '8', '9', '3', '2', '8', '9', '8', '1', '9', '0', '1', '6', '1', '/', '1', '9', '7', '8', '2', '0', '1', '3', '8', '3', '0', '8', '9', '0', '0', '1', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '3', '8', '4', '6', '4', '5', '7', '6', '5', '2', '3', '8', '1', '0', '1', '6', '2', '0', '8', '4', '3', '3', '1', '/', '1', '9', '7', '8', '2', '0', '1', '3', '8', '3', '0', '8', '9', '0', '0', '1', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '3', '0', '9', '3', '9', '8', '7', '0', '3', '8', '9', '7', '8', '6', '4', '4', '0', '5', '5', '5', '0', '5', '1', '/', '1', '9', '7', '8', '2', '0', '1', '3', '8', '3', '0', '8', '9', '0', '0', '1', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '4', '3', '0', '2', '3', '9', '3', '7', '7', '1', '7', '4', '9', '4', '0', '1', '0', '6', '1', '0', '1', '7', '/', '7', '2', '2', '9', '3', '0', '7', '3', '8', '0', '0', '5', '9', '4', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0222362Acc00600 : List (String × SourceJson) := (fragment0222362Field005Key00, fragment0222362Field005Value00) :: fragment0222362Acc00500
noncomputable def fragment0222362Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '3', '8', '9', '7', '9', '9', '4', '0', '1', '9', '2', '2', '7', '2', '1', '0', '6', '7', '9', '7', '2', '1', '4', '1', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '7', '8', '4', '7', '4', '0', '9', '4', '8', '3', '6', '5', '8', '5', '3', '5', '1', '4', '4', '8', '1', '1', '/', '7', '2', '2', '9', '3', '0', '7', '3', '8', '0', '0', '5', '9', '4', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '3', '6', '7', '4', '9', '5', '0', '3', '7', '0', '9', '6', '8', '0', '5', '1', '6', '0', '0', '5', '2', '0', '9', '/', '9', '6', '7', '1', '2', '0', '6', '7', '6', '1', '7', '6', '8', '4', '4', '9', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '4', '0', '6', '2', '2', '7', '6', '5', '0', '5', '3', '7', '1', '1', '8', '3', '1', '5', '6', '8', '4', '7', '0', '8', '7', '/', '4', '3', '5', '2', '0', '4', '3', '0', '4', '2', '7', '9', '5', '8', '0', '2', '3', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '1', '6', '9', '7', '3', '1', '3', '2', '4', '2', '8', '2', '8', '3', '6', '7', '3', '9', '0', '1', '8', '7', '5', '6', '7', '/', '4', '3', '5', '2', '0', '4', '3', '0', '4', '2', '7', '9', '5', '8', '0', '2', '3', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '3', '7', '5', '7', '9', '5', '9', '9', '5', '5', '9', '4', '7', '7', '9', '2', '9', '5', '7', '5', '3', '0', '1', '/', '4', '3', '9', '6', '0', '0', '3', '0', '7', '3', '5', '3', '1', '1', '1', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '7', '9', '9', '4', '2', '7', '7', '9', '4', '3', '8', '9', '3', '2', '8', '9', '8', '1', '9', '0', '1', '6', '1', '/', '1', '9', '7', '8', '2', '0', '1', '3', '8', '3', '0', '8', '9', '0', '0', '1', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '3', '8', '4', '6', '4', '5', '7', '6', '5', '2', '3', '8', '1', '0', '1', '6', '2', '0', '8', '4', '3', '3', '1', '/', '1', '9', '7', '8', '2', '0', '1', '3', '8', '3', '0', '8', '9', '0', '0', '1', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '3', '0', '9', '3', '9', '8', '7', '0', '3', '8', '9', '7', '8', '6', '4', '4', '0', '5', '5', '5', '0', '5', '1', '/', '1', '9', '7', '8', '2', '0', '1', '3', '8', '3', '0', '8', '9', '0', '0', '1', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '3', '0', '2', '3', '9', '3', '7', '7', '1', '7', '4', '9', '4', '0', '1', '0', '6', '1', '0', '1', '7', '/', '7', '2', '2', '9', '3', '0', '7', '3', '8', '0', '0', '5', '9', '4', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0222362_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 488) (SourceJson.white (fragment0222362Field005Chars00 ++ tail)) fragment0222362Acc00500 =
      SourceJson.object (fuel + 487) (SourceJson.white tail) fragment0222362Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_005"
  err.flush

noncomputable def fragment0222362Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0222362Field006Value00 : SourceJson := .str (String.ofList ['2', '5', '3', '1', '3', '3', '4', '9', '8', '5', '4', '0', '9', '0', '0', '7', '9', '1', '1', '2', '9', '1', '0', '5', '7', '2', '8', '8', '6', '6', '2', '6', '2', '8', '9', '3', '4', '9', '0', '2', '7', '5', '3', '8', '4', '8', '8', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '/', '4', '8', '2', '6', '6', '6', '4', '4', '1', '8', '8', '3', '5', '2', '8', '1', '3', '2', '9', '7', '8', '6', '0', '2', '8', '3', '0', '9', '6', '7', '7', '0', '8', '1', '8', '5', '9', '9', '1', '8', '0', '1', '1', '0', '0', '5', '9', '0', '5', '5', '2', '2', '0', '4', '6', '1', '8', '1', '6', '4', '8', '1', '6', '4', '5', '6', '1', '4', '1', '8', '1', '7', '4', '4', '4', '7'])
noncomputable def fragment0222362Acc00700 : List (String × SourceJson) := (fragment0222362Field006Key00, fragment0222362Field006Value00) :: fragment0222362Acc00600
noncomputable def fragment0222362Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '5', '3', '1', '3', '3', '4', '9', '8', '5', '4', '0', '9', '0', '0', '7', '9', '1', '1', '2', '9', '1', '0', '5', '7', '2', '8', '8', '6', '6', '2', '6', '2', '8', '9', '3', '4', '9', '0', '2', '7', '5', '3', '8', '4', '8', '8', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '/', '4', '8', '2', '6', '6', '6', '4', '4', '1', '8', '8', '3', '5', '2', '8', '1', '3', '2', '9', '7', '8', '6', '0', '2', '8', '3', '0', '9', '6', '7', '7', '0', '8', '1', '8', '5', '9', '9', '1', '8', '0', '1', '1', '0', '0', '5', '9', '0', '5', '5', '2', '2', '0', '4', '6', '1', '8', '1', '6', '4', '8', '1', '6', '4', '5', '6', '1', '4', '1', '8', '1', '7', '4', '4', '4', '7', '"', ',']

theorem object_fragment0222362_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 487) (SourceJson.white (fragment0222362Field006Chars00 ++ tail)) fragment0222362Acc00600 =
      SourceJson.object (fuel + 486) (SourceJson.white tail) fragment0222362Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_006"
  err.flush

noncomputable def fragment0222362Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0222362Field007Value00 : SourceJson := .str (String.ofList ['3', '2', '3', '2', '0', '5', '0', '8', '9', '5', '1', '7', '2', '8', '9', '9', '8', '9', '4', '3', '3', '6', '5', '2', '4', '6', '1', '6', '6', '2', '0', '2', '1', '5', '6', '5', '4', '7', '1', '0', '0', '6', '8', '5', '3', '8', '5', '2', '6', '5', '2', '2', '9', '2', '8', '8', '4', '1', '4', '5', '5', '0', '8', '8', '3', '6', '7', '0', '4', '3', '3', '8', '2', '5', '8', '8', '4', '2', '3', '9', '8', '3', '0', '4', '1', '2', '1', '2', '6', '1', '5', '0', '5', '7', '0', '8', '6', '9', '9', '3', '1', '4', '2', '1', '6', '5', '5', '0', '0', '8', '7', '7', '6', '7', '2', '6', '3', '3', '8', '0', '5', '0', '6', '2', '2', '7', '9', '9', '7', '7', '8', '7', '4', '6', '4', '1', '5', '8', '5', '2', '8', '1', '6', '0', '3', '5', '7', '4', '5', '9', '9', '1', '9', '0', '1', '5', '6', '3', '5', '8', '3', '5', '4', '4', '3', '3', '1', '9', '2', '9', '0', '9', '1', '8', '5', '4', '0', '0', '0', '7', '2', '5', '0', '4', '3', '2', '9', '1', '2', '4', '2', '1', '2', '9', '6', '6', '9', '1', '9', '7', '2', '0', '0', '0', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '3', '8', '0', '0', '4', '3', '7', '9', '3', '9', '6', '1', '9', '2', '8', '0', '3', '0', '1', '7', '1', '6', '9', '8', '0', '5', '6', '4', '4', '7', '2', '0', '2', '8', '8', '1', '7', '8', '1', '6', '9', '6', '1', '3', '2', '9', '9', '4', '3', '6', '9', '0', '7', '6', '5', '2', '5', '5', '3', '9', '7', '1', '0', '4', '2', '0', '5', '0', '3', '0', '2', '0', '9', '7', '9', '3', '7', '5', '0', '8', '8', '0', '9', '3', '7', '3', '9', '7', '1', '1', '1', '1', '5', '0', '7', '8', '8', '4', '9', '6', '5', '1', '0', '1', '5', '3', '2', '1', '8', '2', '7', '9', '1', '0', '7', '1', '9', '2', '1', '9', '5', '5', '3', '0', '6', '8', '6', '2', '5', '7', '3', '0', '8', '7', '9', '5', '0', '6', '1', '7', '1', '0', '1', '3', '1', '2', '6', '8', '5', '8', '6', '9', '0', '8', '9', '0', '7', '1', '3', '6', '8', '2', '1', '5', '7', '5', '7', '2', '4', '8', '9', '5', '6', '9', '6', '3', '9', '5', '8', '2', '9', '4', '7', '1', '5', '8', '4', '0', '7', '3', '0', '1', '3', '2', '3', '4', '0', '7', '8', '8', '2', '3', '3', '5', '2', '5', '7', '8', '2', '0', '7', '4', '0', '5', '4', '2', '0', '6', '1', '1', '5', '9', '4', '4', '9', '3', '4', '7', '3', '1', '7', '4', '3', '7', '6', '9', '9', '6', '3', '1', '6', '3', '9', '1', '5', '0', '9', '7'])
noncomputable def fragment0222362Acc00800 : List (String × SourceJson) := (fragment0222362Field007Key00, fragment0222362Field007Value00) :: fragment0222362Acc00700
noncomputable def fragment0222362Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '2', '3', '2', '0', '5', '0', '8', '9', '5', '1', '7', '2', '8', '9', '9', '8', '9', '4', '3', '3', '6', '5', '2', '4', '6', '1', '6', '6', '2', '0', '2', '1', '5', '6', '5', '4', '7', '1', '0', '0', '6', '8', '5', '3', '8', '5', '2', '6', '5', '2', '2', '9', '2', '8', '8', '4', '1', '4', '5', '5', '0', '8', '8', '3', '6', '7', '0', '4', '3', '3', '8', '2', '5', '8', '8', '4', '2', '3', '9', '8', '3', '0', '4', '1', '2', '1', '2', '6', '1', '5', '0', '5', '7', '0', '8', '6', '9', '9', '3', '1', '4', '2', '1', '6', '5', '5', '0', '0', '8', '7', '7', '6', '7', '2', '6', '3', '3', '8', '0', '5', '0', '6', '2', '2', '7', '9', '9', '7', '7', '8', '7', '4', '6', '4', '1', '5', '8', '5', '2', '8', '1', '6', '0', '3', '5', '7', '4', '5', '9', '9', '1', '9', '0', '1', '5', '6', '3', '5', '8', '3', '5', '4', '4', '3', '3', '1', '9', '2', '9', '0', '9', '1', '8', '5', '4', '0', '0', '0', '7', '2', '5', '0', '4', '3', '2', '9', '1', '2', '4', '2', '1', '2', '9', '6', '6', '9', '1', '9', '7', '2', '0', '0', '0', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '3', '8', '0', '0', '4', '3', '7', '9', '3', '9', '6', '1', '9', '2', '8', '0', '3', '0', '1', '7', '1', '6', '9', '8', '0', '5', '6', '4', '4', '7', '2', '0', '2', '8', '8', '1', '7', '8', '1', '6', '9', '6', '1', '3', '2', '9', '9', '4', '3', '6', '9', '0', '7', '6', '5', '2', '5', '5', '3', '9', '7', '1', '0', '4', '2', '0', '5', '0', '3', '0', '2', '0', '9', '7', '9', '3', '7', '5', '0', '8', '8', '0', '9', '3', '7', '3', '9', '7', '1', '1', '1', '1', '5', '0', '7', '8', '8', '4', '9', '6', '5', '1', '0', '1', '5', '3', '2', '1', '8', '2', '7', '9', '1', '0', '7', '1', '9', '2', '1', '9', '5', '5', '3', '0', '6', '8', '6', '2', '5', '7', '3', '0', '8', '7', '9', '5', '0', '6', '1', '7', '1', '0', '1', '3', '1', '2', '6', '8', '5', '8', '6', '9', '0', '8', '9', '0', '7', '1', '3', '6', '8', '2', '1', '5', '7', '5', '7', '2', '4', '8', '9', '5', '6', '9', '6', '3', '9', '5', '8', '2', '9', '4', '7', '1', '5', '8', '4', '0', '7', '3', '0', '1', '3', '2', '3', '4', '0', '7', '8', '8', '2', '3', '3', '5', '2', '5', '7', '8', '2', '0', '7', '4', '0', '5', '4', '2', '0', '6', '1', '1', '5', '9', '4', '4', '9', '3', '4', '7', '3', '1', '7', '4', '3', '7', '6', '9', '9', '6', '3', '1', '6', '3', '9', '1', '5', '0', '9', '7', '"', ',']

theorem object_fragment0222362_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 486) (SourceJson.white (fragment0222362Field007Chars00 ++ tail)) fragment0222362Acc00700 =
      SourceJson.object (fuel + 485) (SourceJson.white tail) fragment0222362Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_007"
  err.flush

noncomputable def fragment0222362Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0222362Field008Value00 : SourceJson := .str (String.ofList ['4', '1', '5', '5', '1', '0', '5', '9', '3', '2', '3'])
noncomputable def fragment0222362Acc00900 : List (String × SourceJson) := (fragment0222362Field008Key00, fragment0222362Field008Value00) :: fragment0222362Acc00800
noncomputable def fragment0222362Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '5', '5', '1', '0', '5', '9', '3', '2', '3', '"', ',']

theorem object_fragment0222362_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 485) (SourceJson.white (fragment0222362Field008Chars00 ++ tail)) fragment0222362Acc00800 =
      SourceJson.object (fuel + 484) (SourceJson.white tail) fragment0222362Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_008"
  err.flush

noncomputable def fragment0222362Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0222362Field009Value00 : SourceJson := .str (String.ofList ['1', '1', '4', '4', '1', '8', '6', '5', '6', '1', '6', '2'])
noncomputable def fragment0222362Acc01000 : List (String × SourceJson) := (fragment0222362Field009Key00, fragment0222362Field009Value00) :: fragment0222362Acc00900
noncomputable def fragment0222362Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '4', '4', '1', '8', '6', '5', '6', '1', '6', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0222362_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 484) (SourceJson.white (fragment0222362Field009Chars00 ++ tail)) fragment0222362Acc00900 =
      .ok (.obj (fragment0222362Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222362_object_field_009"
  err.flush

noncomputable def fragment0222362Chars : List Char := '{' :: (fragment0222362Field000Chars00 ++ fragment0222362Field001Chars00 ++ fragment0222362Field002Chars00 ++ fragment0222362Field003Chars00 ++ fragment0222362Field004Chars00 ++ fragment0222362Field005Chars00 ++ fragment0222362Field006Chars00 ++ fragment0222362Field007Chars00 ++ fragment0222362Field008Chars00 ++ fragment0222362Field009Chars00)
noncomputable def fragment0222362Value : SourceJson := .obj (fragment0222362Acc01000.reverse)

theorem value_fragment0222362 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 494) (fragment0222362Chars ++ tail) =
      .ok (fragment0222362Value, tail) := by
  have hinput : fragment0222362Chars ++ tail = '{' :: (fragment0222362Field000Chars00 ++ (fragment0222362Field001Chars00 ++ (fragment0222362Field002Chars00 ++ (fragment0222362Field003Chars00 ++ (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0222362Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 494) (fragment0222362Chars ++ tail) =
        SourceJson.value (fuel + 494) ('{' :: (fragment0222362Field000Chars00 ++ (fragment0222362Field001Chars00 ++ (fragment0222362Field002Chars00 ++ (fragment0222362Field003Chars00 ++ (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 494)) hinput
    _ = SourceJson.object (fuel + 493) (SourceJson.white (fragment0222362Field000Chars00 ++ (fragment0222362Field001Chars00 ++ (fragment0222362Field002Chars00 ++ (fragment0222362Field003Chars00 ++ (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))))))))))) fragment0222362Acc00000 := by rfl
    _ = SourceJson.object (fuel + 492) (SourceJson.white (fragment0222362Field001Chars00 ++ (fragment0222362Field002Chars00 ++ (fragment0222362Field003Chars00 ++ (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail))))))))))) fragment0222362Acc00100 := object_fragment0222362_field_000 fuel (fragment0222362Field001Chars00 ++ (fragment0222362Field002Chars00 ++ (fragment0222362Field003Chars00 ++ (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 491) (SourceJson.white (fragment0222362Field002Chars00 ++ (fragment0222362Field003Chars00 ++ (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))))))))) fragment0222362Acc00200 := object_fragment0222362_field_001 fuel (fragment0222362Field002Chars00 ++ (fragment0222362Field003Chars00 ++ (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 490) (SourceJson.white (fragment0222362Field003Chars00 ++ (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail))))))))) fragment0222362Acc00300 := object_fragment0222362_field_002 fuel (fragment0222362Field003Chars00 ++ (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 489) (SourceJson.white (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))))))) fragment0222362Acc00400 := object_fragment0222362_field_003 fuel (fragment0222362Field004Chars00 ++ (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 488) (SourceJson.white (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail))))))) fragment0222362Acc00500 := object_fragment0222362_field_004 fuel (fragment0222362Field005Chars00 ++ (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 487) (SourceJson.white (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))))) fragment0222362Acc00600 := object_fragment0222362_field_005 fuel (fragment0222362Field006Chars00 ++ (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 486) (SourceJson.white (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail))))) fragment0222362Acc00700 := object_fragment0222362_field_006 fuel (fragment0222362Field007Chars00 ++ (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 485) (SourceJson.white (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))) fragment0222362Acc00800 := object_fragment0222362_field_007 fuel (fragment0222362Field008Chars00 ++ (fragment0222362Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 484) (SourceJson.white (fragment0222362Field009Chars00 ++ (tail))) fragment0222362Acc00900 := object_fragment0222362_field_008 fuel (fragment0222362Field009Chars00 ++ (tail))
    _ = .ok (fragment0222362Value, tail) := object_fragment0222362_field_009 fuel (tail)

noncomputable def fragment0224508Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0224508Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0224508Field000Value00 : SourceJson := .number (String.ofList ['5', '2'])
noncomputable def fragment0224508Acc00100 : List (String × SourceJson) := (fragment0224508Field000Key00, fragment0224508Field000Value00) :: fragment0224508Acc00000
noncomputable def fragment0224508Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '2', ',']

theorem object_fragment0224508_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 450) (SourceJson.white (fragment0224508Field000Chars00 ++ tail)) fragment0224508Acc00000 =
      SourceJson.object (fuel + 449) (SourceJson.white tail) fragment0224508Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_000"
  err.flush

noncomputable def fragment0224508Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0224508Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0224508Acc00200 : List (String × SourceJson) := (fragment0224508Field001Key00, fragment0224508Field001Value00) :: fragment0224508Acc00100
noncomputable def fragment0224508Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0224508_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 449) (SourceJson.white (fragment0224508Field001Chars00 ++ tail)) fragment0224508Acc00100 =
      SourceJson.object (fuel + 448) (SourceJson.white tail) fragment0224508Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_001"
  err.flush

noncomputable def fragment0224508Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0224508Field002Value00 : SourceJson := .str (String.ofList ['3', '4', '5', '3', '0', '0', '3', '2', '4', '2', '3', '8', '3', '8', '6', '0', '8', '8', '7', '6', '3', '9', '4', '7', '4', '1', '8', '7', '3', '9', '2', '9', '4', '2', '0', '8', '8', '7', '/', '4', '4', '9', '4', '9', '2', '4', '1', '8', '2', '9', '0', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0224508Acc00300 : List (String × SourceJson) := (fragment0224508Field002Key00, fragment0224508Field002Value00) :: fragment0224508Acc00200
noncomputable def fragment0224508Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '4', '5', '3', '0', '0', '3', '2', '4', '2', '3', '8', '3', '8', '6', '0', '8', '8', '7', '6', '3', '9', '4', '7', '4', '1', '8', '7', '3', '9', '2', '9', '4', '2', '0', '8', '8', '7', '/', '4', '4', '9', '4', '9', '2', '4', '1', '8', '2', '9', '0', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0224508_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 448) (SourceJson.white (fragment0224508Field002Chars00 ++ tail)) fragment0224508Acc00200 =
      SourceJson.object (fuel + 447) (SourceJson.white tail) fragment0224508Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_002"
  err.flush

noncomputable def fragment0224508Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0224508Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0224508Acc00400 : List (String × SourceJson) := (fragment0224508Field003Key00, fragment0224508Field003Value00) :: fragment0224508Acc00300
noncomputable def fragment0224508Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0224508_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 447) (SourceJson.white (fragment0224508Field003Chars00 ++ tail)) fragment0224508Acc00300 =
      SourceJson.object (fuel + 446) (SourceJson.white tail) fragment0224508Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_003"
  err.flush

noncomputable def fragment0224508Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0224508Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0224508Acc00500 : List (String × SourceJson) := (fragment0224508Field004Key00, fragment0224508Field004Value00) :: fragment0224508Acc00400
noncomputable def fragment0224508Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0224508_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 446) (SourceJson.white (fragment0224508Field004Chars00 ++ tail)) fragment0224508Acc00400 =
      SourceJson.object (fuel + 445) (SourceJson.white tail) fragment0224508Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_004"
  err.flush

noncomputable def fragment0224508Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0224508Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '5', '5', '7', '3', '4', '4', '8', '7', '1', '2', '0', '2', '3', '0', '9', '9', '7', '4', '5', '5', '7', '6', '8', '1', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '8', '9', '9', '6', '6', '9', '4', '3', '7', '2', '4', '9', '3', '4', '3', '8', '9', '9', '3', '/', '5', '8', '6', '3', '0', '8', '8', '5', '2', '3', '6', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '1', '5', '2', '5', '8', '2', '9', '5', '3', '0', '1', '3', '8', '6', '8', '1', '9', '5', '7', '3', '/', '3', '4', '1', '0', '2', '2', '1', '5', '3', '7', '4', '1', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '4', '8', '7', '3', '4', '5', '8', '3', '4', '0', '2', '9', '6', '5', '4', '1', '7', '3', '8', '7', '9', '6', '1', '/', '3', '5', '2', '9', '5', '7', '9', '2', '9', '1', '2', '2', '3', '8', '8', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '2', '9', '5', '5', '4', '3', '3', '8', '0', '0', '1', '2', '2', '4', '2', '0', '0', '8', '8', '1', '4', '0', '1', '/', '3', '5', '2', '9', '5', '7', '9', '2', '9', '1', '2', '2', '3', '8', '8', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '6', '1', '3', '4', '3', '1', '9', '1', '3', '9', '3', '1', '4', '6', '3', '7', '9', '3', '6', '3', '/', '3', '5', '6', '5', '2', '3', '1', '6', '0', '7', '2', '9', '6', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '3', '4', '6', '5', '7', '0', '0', '6', '8', '4', '7', '0', '7', '6', '6', '1', '7', '4', '1', '8', '3', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '9', '8', '7', '1', '5', '1', '5', '3', '3', '7', '3', '3', '3', '7', '6', '8', '0', '2', '1', '9', '3', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '1', '1', '5', '1', '0', '8', '2', '8', '3', '3', '9', '4', '1', '5', '6', '4', '2', '2', '3', '5', '3', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '7', '0', '4', '4', '6', '4', '9', '5', '5', '9', '8', '6', '1', '4', '9', '6', '5', '7', '1', '/', '5', '8', '6', '3', '0', '8', '8', '5', '2', '3', '6', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0224508Acc00600 : List (String × SourceJson) := (fragment0224508Field005Key00, fragment0224508Field005Value00) :: fragment0224508Acc00500
noncomputable def fragment0224508Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '5', '7', '3', '4', '4', '8', '7', '1', '2', '0', '2', '3', '0', '9', '9', '7', '4', '5', '5', '7', '6', '8', '1', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '2', '8', '9', '9', '6', '6', '9', '4', '3', '7', '2', '4', '9', '3', '4', '3', '8', '9', '9', '3', '/', '5', '8', '6', '3', '0', '8', '8', '5', '2', '3', '6', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '1', '5', '2', '5', '8', '2', '9', '5', '3', '0', '1', '3', '8', '6', '8', '1', '9', '5', '7', '3', '/', '3', '4', '1', '0', '2', '2', '1', '5', '3', '7', '4', '1', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '4', '8', '7', '3', '4', '5', '8', '3', '4', '0', '2', '9', '6', '5', '4', '1', '7', '3', '8', '7', '9', '6', '1', '/', '3', '5', '2', '9', '5', '7', '9', '2', '9', '1', '2', '2', '3', '8', '8', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '2', '9', '5', '5', '4', '3', '3', '8', '0', '0', '1', '2', '2', '4', '2', '0', '0', '8', '8', '1', '4', '0', '1', '/', '3', '5', '2', '9', '5', '7', '9', '2', '9', '1', '2', '2', '3', '8', '8', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '6', '1', '3', '4', '3', '1', '9', '1', '3', '9', '3', '1', '4', '6', '3', '7', '9', '3', '6', '3', '/', '3', '5', '6', '5', '2', '3', '1', '6', '0', '7', '2', '9', '6', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '3', '4', '6', '5', '7', '0', '0', '6', '8', '4', '7', '0', '7', '6', '6', '1', '7', '4', '1', '8', '3', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '9', '8', '7', '1', '5', '1', '5', '3', '3', '7', '3', '3', '3', '7', '6', '8', '0', '2', '1', '9', '3', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '1', '1', '5', '1', '0', '8', '2', '8', '3', '3', '9', '4', '1', '5', '6', '4', '2', '2', '3', '5', '3', '/', '1', '6', '0', '4', '3', '5', '4', '2', '2', '3', '2', '8', '3', '5', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '7', '0', '4', '4', '6', '4', '9', '5', '5', '9', '8', '6', '1', '4', '9', '6', '5', '7', '1', '/', '5', '8', '6', '3', '0', '8', '8', '5', '2', '3', '6', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0224508_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 445) (SourceJson.white (fragment0224508Field005Chars00 ++ tail)) fragment0224508Acc00500 =
      SourceJson.object (fuel + 444) (SourceJson.white tail) fragment0224508Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_005"
  err.flush

noncomputable def fragment0224508Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0224508Field006Value00 : SourceJson := .str (String.ofList ['3', '0', '5', '4', '1', '8', '5', '1', '2', '8', '5', '3', '7', '4', '0', '5', '1', '2', '8', '5', '5', '3', '7', '5', '9', '6', '0', '2', '5', '4', '2', '8', '9', '1', '8', '9', '3', '8', '2', '4', '8', '1', '3', '4', '5', '1', '0', '9', '8', '2', '0', '0', '0', '0', '/', '9', '4', '1', '8', '8', '3', '2', '7', '9', '5', '4', '1', '4', '5', '8', '7', '1', '9', '7', '0', '6', '4', '1', '7', '1', '6', '7', '1', '3', '6', '4', '3', '2', '8', '4', '8', '8', '0', '3', '5', '2', '7', '4', '2', '0', '0', '9', '0', '9', '3', '4', '8', '4', '3', '2', '3', '9', '7', '8', '5', '0', '8', '5', '4', '0', '0', '4', '2', '2', '3', '9'])
noncomputable def fragment0224508Acc00700 : List (String × SourceJson) := (fragment0224508Field006Key00, fragment0224508Field006Value00) :: fragment0224508Acc00600
noncomputable def fragment0224508Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '0', '5', '4', '1', '8', '5', '1', '2', '8', '5', '3', '7', '4', '0', '5', '1', '2', '8', '5', '5', '3', '7', '5', '9', '6', '0', '2', '5', '4', '2', '8', '9', '1', '8', '9', '3', '8', '2', '4', '8', '1', '3', '4', '5', '1', '0', '9', '8', '2', '0', '0', '0', '0', '/', '9', '4', '1', '8', '8', '3', '2', '7', '9', '5', '4', '1', '4', '5', '8', '7', '1', '9', '7', '0', '6', '4', '1', '7', '1', '6', '7', '1', '3', '6', '4', '3', '2', '8', '4', '8', '8', '0', '3', '5', '2', '7', '4', '2', '0', '0', '9', '0', '9', '3', '4', '8', '4', '3', '2', '3', '9', '7', '8', '5', '0', '8', '5', '4', '0', '0', '4', '2', '2', '3', '9', '"', ',']

theorem object_fragment0224508_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 444) (SourceJson.white (fragment0224508Field006Chars00 ++ tail)) fragment0224508Acc00600 =
      SourceJson.object (fuel + 443) (SourceJson.white tail) fragment0224508Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_006"
  err.flush

noncomputable def fragment0224508Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0224508Field007Value00 : SourceJson := .str (String.ofList ['2', '3', '3', '6', '5', '7', '8', '8', '7', '9', '8', '3', '3', '0', '5', '2', '9', '9', '9', '9', '1', '6', '3', '9', '2', '9', '4', '0', '3', '6', '4', '1', '3', '4', '5', '4', '3', '9', '7', '3', '9', '2', '3', '6', '2', '3', '3', '2', '1', '2', '6', '3', '9', '0', '8', '7', '3', '2', '0', '2', '1', '5', '2', '4', '4', '7', '1', '9', '9', '6', '4', '2', '7', '6', '4', '0', '7', '6', '0', '9', '9', '0', '3', '2', '4', '1', '4', '6', '4', '6', '8', '8', '3', '6', '6', '5', '2', '7', '7', '3', '6', '5', '2', '3', '6', '4', '0', '3', '9', '4', '6', '3', '0', '4', '3', '7', '0', '4', '7', '5', '2', '1', '6', '8', '0', '7', '8', '1', '2', '4', '0', '1', '4', '3', '9', '2', '7', '1', '5', '3', '0', '5', '9', '2', '5', '9', '9', '8', '7', '2', '1', '8', '3', '6', '8', '4', '2', '0', '2', '5', '9', '6', '8', '0', '2', '8', '6', '8', '1', '4', '0', '1', '6', '5', '3', '5', '1', '3', '6', '2', '0', '6', '3', '2', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '4', '3', '1', '2', '3', '8', '7', '8', '5', '0', '3', '8', '2', '1', '2', '8', '0', '8', '8', '9', '8', '3', '9', '9', '8', '1', '8', '9', '2', '5', '2', '0', '5', '6', '4', '2', '9', '1', '7', '7', '3', '0', '0', '1', '0', '3', '2', '3', '7', '3', '1', '0', '4', '1', '7', '0', '2', '2', '1', '2', '1', '6', '3', '9', '0', '5', '4', '3', '5', '3', '3', '2', '5', '0', '5', '2', '7', '7', '6', '1', '7', '2', '4', '3', '6', '1', '2', '1', '6', '6', '8', '3', '2', '3', '7', '2', '8', '8', '7', '2', '5', '6', '6', '1', '2', '3', '0', '4', '4', '0', '9', '1', '8', '6', '6', '3', '5', '8', '7', '1', '0', '2', '8', '5', '9', '1', '7', '0', '2', '8', '5', '1', '3', '5', '5', '0', '6', '3', '9', '4', '1', '4', '6', '1', '5', '5', '6', '8', '8', '4', '8', '4', '3', '4', '8', '1', '2', '1', '9', '1', '2', '9', '4', '4', '0', '0', '7', '2', '6', '9', '6', '8', '4', '7', '8', '3', '7', '4', '5', '9', '9', '4', '5', '5', '1', '8', '2', '3', '3', '7', '7', '6', '5', '2', '5', '8', '0', '8', '3', '6', '5', '3', '0', '1', '2', '2', '6', '4', '1', '1', '3', '3', '9', '5', '3', '7', '6', '0', '2', '0', '0', '9', '5', '7', '0', '4', '9'])
noncomputable def fragment0224508Acc00800 : List (String × SourceJson) := (fragment0224508Field007Key00, fragment0224508Field007Value00) :: fragment0224508Acc00700
noncomputable def fragment0224508Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '3', '3', '6', '5', '7', '8', '8', '7', '9', '8', '3', '3', '0', '5', '2', '9', '9', '9', '9', '1', '6', '3', '9', '2', '9', '4', '0', '3', '6', '4', '1', '3', '4', '5', '4', '3', '9', '7', '3', '9', '2', '3', '6', '2', '3', '3', '2', '1', '2', '6', '3', '9', '0', '8', '7', '3', '2', '0', '2', '1', '5', '2', '4', '4', '7', '1', '9', '9', '6', '4', '2', '7', '6', '4', '0', '7', '6', '0', '9', '9', '0', '3', '2', '4', '1', '4', '6', '4', '6', '8', '8', '3', '6', '6', '5', '2', '7', '7', '3', '6', '5', '2', '3', '6', '4', '0', '3', '9', '4', '6', '3', '0', '4', '3', '7', '0', '4', '7', '5', '2', '1', '6', '8', '0', '7', '8', '1', '2', '4', '0', '1', '4', '3', '9', '2', '7', '1', '5', '3', '0', '5', '9', '2', '5', '9', '9', '8', '7', '2', '1', '8', '3', '6', '8', '4', '2', '0', '2', '5', '9', '6', '8', '0', '2', '8', '6', '8', '1', '4', '0', '1', '6', '5', '3', '5', '1', '3', '6', '2', '0', '6', '3', '2', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '4', '3', '1', '2', '3', '8', '7', '8', '5', '0', '3', '8', '2', '1', '2', '8', '0', '8', '8', '9', '8', '3', '9', '9', '8', '1', '8', '9', '2', '5', '2', '0', '5', '6', '4', '2', '9', '1', '7', '7', '3', '0', '0', '1', '0', '3', '2', '3', '7', '3', '1', '0', '4', '1', '7', '0', '2', '2', '1', '2', '1', '6', '3', '9', '0', '5', '4', '3', '5', '3', '3', '2', '5', '0', '5', '2', '7', '7', '6', '1', '7', '2', '4', '3', '6', '1', '2', '1', '6', '6', '8', '3', '2', '3', '7', '2', '8', '8', '7', '2', '5', '6', '6', '1', '2', '3', '0', '4', '4', '0', '9', '1', '8', '6', '6', '3', '5', '8', '7', '1', '0', '2', '8', '5', '9', '1', '7', '0', '2', '8', '5', '1', '3', '5', '5', '0', '6', '3', '9', '4', '1', '4', '6', '1', '5', '5', '6', '8', '8', '4', '8', '4', '3', '4', '8', '1', '2', '1', '9', '1', '2', '9', '4', '4', '0', '0', '7', '2', '6', '9', '6', '8', '4', '7', '8', '3', '7', '4', '5', '9', '9', '4', '5', '5', '1', '8', '2', '3', '3', '7', '7', '6', '5', '2', '5', '8', '0', '8', '3', '6', '5', '3', '0', '1', '2', '2', '6', '4', '1', '1', '3', '3', '9', '5', '3', '7', '6', '0', '2', '0', '0', '9', '5', '7', '0', '4', '9', '"', ',']

theorem object_fragment0224508_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 443) (SourceJson.white (fragment0224508Field007Chars00 ++ tail)) fragment0224508Acc00700 =
      SourceJson.object (fuel + 442) (SourceJson.white tail) fragment0224508Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_007"
  err.flush

noncomputable def fragment0224508Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0224508Field008Value00 : SourceJson := .str (String.ofList ['2', '5', '6', '9', '0', '8', '1', '3', '3', '9', '1', '4'])
noncomputable def fragment0224508Acc00900 : List (String × SourceJson) := (fragment0224508Field008Key00, fragment0224508Field008Value00) :: fragment0224508Acc00800
noncomputable def fragment0224508Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '6', '9', '0', '8', '1', '3', '3', '9', '1', '4', '"', ',']

theorem object_fragment0224508_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 442) (SourceJson.white (fragment0224508Field008Chars00 ++ tail)) fragment0224508Acc00800 =
      SourceJson.object (fuel + 441) (SourceJson.white tail) fragment0224508Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_008"
  err.flush

noncomputable def fragment0224508Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0224508Field009Value00 : SourceJson := .str (String.ofList ['7', '6', '1', '4', '3', '4', '2', '6', '2', '8', '8', '7'])
noncomputable def fragment0224508Acc01000 : List (String × SourceJson) := (fragment0224508Field009Key00, fragment0224508Field009Value00) :: fragment0224508Acc00900
noncomputable def fragment0224508Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '6', '1', '4', '3', '4', '2', '6', '2', '8', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0224508_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 441) (SourceJson.white (fragment0224508Field009Chars00 ++ tail)) fragment0224508Acc00900 =
      .ok (.obj (fragment0224508Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224508_object_field_009"
  err.flush

noncomputable def fragment0224508Chars : List Char := '{' :: (fragment0224508Field000Chars00 ++ fragment0224508Field001Chars00 ++ fragment0224508Field002Chars00 ++ fragment0224508Field003Chars00 ++ fragment0224508Field004Chars00 ++ fragment0224508Field005Chars00 ++ fragment0224508Field006Chars00 ++ fragment0224508Field007Chars00 ++ fragment0224508Field008Chars00 ++ fragment0224508Field009Chars00)
noncomputable def fragment0224508Value : SourceJson := .obj (fragment0224508Acc01000.reverse)

theorem value_fragment0224508 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 451) (fragment0224508Chars ++ tail) =
      .ok (fragment0224508Value, tail) := by
  have hinput : fragment0224508Chars ++ tail = '{' :: (fragment0224508Field000Chars00 ++ (fragment0224508Field001Chars00 ++ (fragment0224508Field002Chars00 ++ (fragment0224508Field003Chars00 ++ (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0224508Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 451) (fragment0224508Chars ++ tail) =
        SourceJson.value (fuel + 451) ('{' :: (fragment0224508Field000Chars00 ++ (fragment0224508Field001Chars00 ++ (fragment0224508Field002Chars00 ++ (fragment0224508Field003Chars00 ++ (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 451)) hinput
    _ = SourceJson.object (fuel + 450) (SourceJson.white (fragment0224508Field000Chars00 ++ (fragment0224508Field001Chars00 ++ (fragment0224508Field002Chars00 ++ (fragment0224508Field003Chars00 ++ (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))))))))))) fragment0224508Acc00000 := by rfl
    _ = SourceJson.object (fuel + 449) (SourceJson.white (fragment0224508Field001Chars00 ++ (fragment0224508Field002Chars00 ++ (fragment0224508Field003Chars00 ++ (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail))))))))))) fragment0224508Acc00100 := object_fragment0224508_field_000 fuel (fragment0224508Field001Chars00 ++ (fragment0224508Field002Chars00 ++ (fragment0224508Field003Chars00 ++ (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 448) (SourceJson.white (fragment0224508Field002Chars00 ++ (fragment0224508Field003Chars00 ++ (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))))))))) fragment0224508Acc00200 := object_fragment0224508_field_001 fuel (fragment0224508Field002Chars00 ++ (fragment0224508Field003Chars00 ++ (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 447) (SourceJson.white (fragment0224508Field003Chars00 ++ (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail))))))))) fragment0224508Acc00300 := object_fragment0224508_field_002 fuel (fragment0224508Field003Chars00 ++ (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 446) (SourceJson.white (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))))))) fragment0224508Acc00400 := object_fragment0224508_field_003 fuel (fragment0224508Field004Chars00 ++ (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 445) (SourceJson.white (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail))))))) fragment0224508Acc00500 := object_fragment0224508_field_004 fuel (fragment0224508Field005Chars00 ++ (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 444) (SourceJson.white (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))))) fragment0224508Acc00600 := object_fragment0224508_field_005 fuel (fragment0224508Field006Chars00 ++ (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 443) (SourceJson.white (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail))))) fragment0224508Acc00700 := object_fragment0224508_field_006 fuel (fragment0224508Field007Chars00 ++ (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 442) (SourceJson.white (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))) fragment0224508Acc00800 := object_fragment0224508_field_007 fuel (fragment0224508Field008Chars00 ++ (fragment0224508Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 441) (SourceJson.white (fragment0224508Field009Chars00 ++ (tail))) fragment0224508Acc00900 := object_fragment0224508_field_008 fuel (fragment0224508Field009Chars00 ++ (tail))
    _ = .ok (fragment0224508Value, tail) := object_fragment0224508_field_009 fuel (tail)

noncomputable def fragment0226556Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0226556Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0226556Field000Value00 : SourceJson := .number (String.ofList ['5', '3'])
noncomputable def fragment0226556Acc00100 : List (String × SourceJson) := (fragment0226556Field000Key00, fragment0226556Field000Value00) :: fragment0226556Acc00000
noncomputable def fragment0226556Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '3', ',']

theorem object_fragment0226556_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 383) (SourceJson.white (fragment0226556Field000Chars00 ++ tail)) fragment0226556Acc00000 =
      SourceJson.object (fuel + 382) (SourceJson.white tail) fragment0226556Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_000"
  err.flush

noncomputable def fragment0226556Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0226556Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0226556Acc00200 : List (String × SourceJson) := (fragment0226556Field001Key00, fragment0226556Field001Value00) :: fragment0226556Acc00100
noncomputable def fragment0226556Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0226556_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 382) (SourceJson.white (fragment0226556Field001Chars00 ++ tail)) fragment0226556Acc00100 =
      SourceJson.object (fuel + 381) (SourceJson.white tail) fragment0226556Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_001"
  err.flush

noncomputable def fragment0226556Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0226556Field002Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '1', '5', '0', '8', '7', '8', '5', '2', '1', '2', '3', '7', '8', '6', '7', '3', '9', '7', '1', '9', '7', '0', '5', '8', '8', '8', '1', '7', '0', '2', '6', '9', '1', '2', '1', '/', '6', '2', '7', '1', '9', '8', '7', '2', '3', '1', '9', '6', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0226556Acc00300 : List (String × SourceJson) := (fragment0226556Field002Key00, fragment0226556Field002Value00) :: fragment0226556Acc00200
noncomputable def fragment0226556Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '7', '5', '1', '5', '0', '8', '7', '8', '5', '2', '1', '2', '3', '7', '8', '6', '7', '3', '9', '7', '1', '9', '7', '0', '5', '8', '8', '8', '1', '7', '0', '2', '6', '9', '1', '2', '1', '/', '6', '2', '7', '1', '9', '8', '7', '2', '3', '1', '9', '6', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0226556_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 381) (SourceJson.white (fragment0226556Field002Chars00 ++ tail)) fragment0226556Acc00200 =
      SourceJson.object (fuel + 380) (SourceJson.white tail) fragment0226556Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_002"
  err.flush

noncomputable def fragment0226556Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0226556Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0226556Acc00400 : List (String × SourceJson) := (fragment0226556Field003Key00, fragment0226556Field003Value00) :: fragment0226556Acc00300
noncomputable def fragment0226556Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0226556_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 380) (SourceJson.white (fragment0226556Field003Chars00 ++ tail)) fragment0226556Acc00300 =
      SourceJson.object (fuel + 379) (SourceJson.white tail) fragment0226556Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_003"
  err.flush

noncomputable def fragment0226556Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0226556Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0226556Acc00500 : List (String × SourceJson) := (fragment0226556Field004Key00, fragment0226556Field004Value00) :: fragment0226556Acc00400
noncomputable def fragment0226556Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0226556_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 379) (SourceJson.white (fragment0226556Field004Chars00 ++ tail)) fragment0226556Acc00400 =
      SourceJson.object (fuel + 378) (SourceJson.white tail) fragment0226556Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_004"
  err.flush

noncomputable def fragment0226556Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0226556Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '6', '8', '6', '5', '2', '9', '5', '3', '9', '9', '2', '1', '9', '3', '6', '3', '3', '0', '0', '9', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '0', '5', '9', '6', '1', '2', '8', '0', '0', '6', '2', '5', '5', '6', '4', '8', '9', '1', '/', '9', '1', '4', '0', '5', '2', '1', '0', '5', '2', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '6', '5', '5', '6', '1', '5', '8', '0', '9', '4', '6', '2', '4', '6', '6', '3', '/', '7', '4', '1', '8', '3', '9', '3', '8', '9', '7', '3', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '6', '6', '4', '4', '9', '2', '2', '8', '5', '3', '1', '3', '9', '9', '8', '2', '5', '0', '9', '/', '1', '2', '7', '9', '6', '7', '2', '9', '4', '7', '2', '9', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '9', '6', '9', '0', '9', '9', '4', '5', '9', '7', '6', '7', '8', '6', '9', '3', '8', '6', '9', '/', '1', '2', '7', '9', '6', '7', '2', '9', '4', '7', '2', '9', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '1', '7', '2', '7', '1', '1', '9', '8', '6', '8', '7', '1', '7', '6', '5', '5', '0', '1', '/', '3', '8', '7', '7', '7', '9', '6', '8', '0', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '9', '2', '0', '1', '3', '5', '9', '9', '8', '0', '4', '9', '4', '3', '5', '1', '5', '7', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '6', '3', '7', '6', '9', '8', '4', '9', '2', '5', '6', '3', '4', '4', '2', '5', '7', '7', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '3', '2', '1', '5', '3', '3', '2', '8', '8', '6', '5', '1', '7', '2', '9', '6', '1', '7', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '3', '2', '1', '2', '4', '1', '8', '4', '0', '5', '5', '5', '3', '4', '2', '3', '7', '7', '/', '9', '1', '4', '0', '5', '2', '1', '0', '5', '2', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0226556Acc00600 : List (String × SourceJson) := (fragment0226556Field005Key00, fragment0226556Field005Value00) :: fragment0226556Acc00500
noncomputable def fragment0226556Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '8', '6', '5', '2', '9', '5', '3', '9', '9', '2', '1', '9', '3', '6', '3', '3', '0', '0', '9', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '0', '5', '9', '6', '1', '2', '8', '0', '0', '6', '2', '5', '5', '6', '4', '8', '9', '1', '/', '9', '1', '4', '0', '5', '2', '1', '0', '5', '2', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '6', '5', '5', '6', '1', '5', '8', '0', '9', '4', '6', '2', '4', '6', '6', '3', '/', '7', '4', '1', '8', '3', '9', '3', '8', '9', '7', '3', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '6', '6', '4', '4', '9', '2', '2', '8', '5', '3', '1', '3', '9', '9', '8', '2', '5', '0', '9', '/', '1', '2', '7', '9', '6', '7', '2', '9', '4', '7', '2', '9', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '9', '6', '9', '0', '9', '9', '4', '5', '9', '7', '6', '7', '8', '6', '9', '3', '8', '6', '9', '/', '1', '2', '7', '9', '6', '7', '2', '9', '4', '7', '2', '9', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '7', '2', '7', '1', '1', '9', '8', '6', '8', '7', '1', '7', '6', '5', '5', '0', '1', '/', '3', '8', '7', '7', '7', '9', '6', '8', '0', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '9', '2', '0', '1', '3', '5', '9', '9', '8', '0', '4', '9', '4', '3', '5', '1', '5', '7', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '6', '3', '7', '6', '9', '8', '4', '9', '2', '5', '6', '3', '4', '4', '2', '5', '7', '7', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '2', '1', '5', '3', '3', '2', '8', '8', '6', '5', '1', '7', '2', '9', '6', '1', '7', '/', '5', '8', '1', '6', '6', '9', '5', '2', '1', '4', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '3', '2', '1', '2', '4', '1', '8', '4', '0', '5', '5', '5', '3', '4', '2', '3', '7', '7', '/', '9', '1', '4', '0', '5', '2', '1', '0', '5', '2', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0226556_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 378) (SourceJson.white (fragment0226556Field005Chars00 ++ tail)) fragment0226556Acc00500 =
      SourceJson.object (fuel + 377) (SourceJson.white tail) fragment0226556Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_005"
  err.flush

noncomputable def fragment0226556Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0226556Field006Value00 : SourceJson := .str (String.ofList ['1', '0', '3', '0', '3', '7', '2', '3', '5', '5', '7', '7', '1', '3', '4', '1', '9', '5', '5', '0', '7', '9', '3', '4', '9', '9', '2', '0', '8', '5', '4', '5', '1', '9', '3', '7', '9', '9', '5', '7', '4', '9', '7', '1', '6', '1', '6', '0', '0', '/', '5', '4', '0', '7', '5', '0', '5', '0', '5', '1', '4', '3', '8', '0', '4', '4', '3', '1', '0', '8', '9', '6', '6', '0', '2', '2', '0', '8', '7', '4', '9', '2', '4', '3', '9', '9', '9', '6', '8', '6', '6', '7', '2', '0', '0', '5', '4', '5', '1', '6', '0', '5', '9', '9', '5', '2', '4', '6', '9', '4', '3', '9', '9', '1', '1'])
noncomputable def fragment0226556Acc00700 : List (String × SourceJson) := (fragment0226556Field006Key00, fragment0226556Field006Value00) :: fragment0226556Acc00600
noncomputable def fragment0226556Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '3', '0', '3', '7', '2', '3', '5', '5', '7', '7', '1', '3', '4', '1', '9', '5', '5', '0', '7', '9', '3', '4', '9', '9', '2', '0', '8', '5', '4', '5', '1', '9', '3', '7', '9', '9', '5', '7', '4', '9', '7', '1', '6', '1', '6', '0', '0', '/', '5', '4', '0', '7', '5', '0', '5', '0', '5', '1', '4', '3', '8', '0', '4', '4', '3', '1', '0', '8', '9', '6', '6', '0', '2', '2', '0', '8', '7', '4', '9', '2', '4', '3', '9', '9', '9', '6', '8', '6', '6', '7', '2', '0', '0', '5', '4', '5', '1', '6', '0', '5', '9', '9', '5', '2', '4', '6', '9', '4', '3', '9', '9', '1', '1', '"', ',']

theorem object_fragment0226556_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 377) (SourceJson.white (fragment0226556Field006Chars00 ++ tail)) fragment0226556Acc00600 =
      SourceJson.object (fuel + 376) (SourceJson.white tail) fragment0226556Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_006"
  err.flush

noncomputable def fragment0226556Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0226556Field007Value00 : SourceJson := .str (String.ofList ['4', '4', '3', '2', '1', '4', '2', '2', '4', '9', '8', '4', '1', '5', '4', '9', '5', '9', '7', '8', '8', '9', '1', '1', '5', '2', '1', '2', '0', '4', '3', '2', '0', '4', '7', '6', '3', '9', '8', '2', '6', '9', '6', '4', '7', '4', '0', '3', '2', '5', '8', '1', '6', '9', '2', '0', '6', '0', '9', '9', '0', '4', '8', '8', '0', '6', '4', '0', '7', '7', '3', '4', '7', '6', '1', '7', '8', '5', '8', '6', '0', '0', '6', '6', '5', '2', '6', '7', '3', '0', '8', '8', '3', '2', '3', '9', '6', '9', '1', '1', '9', '1', '3', '0', '3', '6', '5', '9', '9', '3', '8', '6', '1', '0', '2', '1', '7', '5', '7', '9', '3', '4', '5', '4', '8', '1', '6', '9', '6', '2', '7', '5', '3', '3', '7', '2', '5', '7', '4', '4', '4', '4', '2', '8', '8', '2', '1', '9', '1', '7', '5', '9', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '8', '5', '3', '1', '7', '1', '7', '7', '6', '2', '2', '1', '7', '7', '6', '0', '5', '6', '4', '9', '8', '5', '5', '4', '0', '4', '9', '3', '9', '6', '6', '6', '6', '5', '6', '6', '6', '4', '1', '6', '3', '2', '2', '0', '6', '5', '4', '5', '4', '9', '8', '1', '9', '6', '7', '4', '2', '7', '6', '5', '0', '3', '0', '3', '3', '1', '0', '5', '9', '7', '2', '0', '1', '4', '9', '0', '0', '2', '1', '3', '0', '6', '0', '7', '1', '3', '1', '6', '3', '6', '2', '9', '3', '3', '1', '3', '0', '1', '8', '5', '9', '7', '9', '3', '1', '3', '8', '2', '4', '8', '0', '2', '0', '8', '2', '9', '3', '8', '1', '4', '7', '2', '6', '7', '9', '7', '7', '7', '8', '6', '3', '8', '2', '8', '3', '8', '6', '0', '5', '7', '5', '2', '9', '5', '0', '7', '4', '6', '6', '1', '8', '3', '4', '5', '1', '6', '1', '9', '2', '1', '9', '8', '5', '0', '7', '3', '6', '5', '9', '1', '5', '6', '1', '0', '7', '1', '4', '8', '4', '9', '7', '8', '7', '5', '0', '4', '3', '4', '6', '6', '0', '1', '7'])
noncomputable def fragment0226556Acc00800 : List (String × SourceJson) := (fragment0226556Field007Key00, fragment0226556Field007Value00) :: fragment0226556Acc00700
noncomputable def fragment0226556Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '4', '3', '2', '1', '4', '2', '2', '4', '9', '8', '4', '1', '5', '4', '9', '5', '9', '7', '8', '8', '9', '1', '1', '5', '2', '1', '2', '0', '4', '3', '2', '0', '4', '7', '6', '3', '9', '8', '2', '6', '9', '6', '4', '7', '4', '0', '3', '2', '5', '8', '1', '6', '9', '2', '0', '6', '0', '9', '9', '0', '4', '8', '8', '0', '6', '4', '0', '7', '7', '3', '4', '7', '6', '1', '7', '8', '5', '8', '6', '0', '0', '6', '6', '5', '2', '6', '7', '3', '0', '8', '8', '3', '2', '3', '9', '6', '9', '1', '1', '9', '1', '3', '0', '3', '6', '5', '9', '9', '3', '8', '6', '1', '0', '2', '1', '7', '5', '7', '9', '3', '4', '5', '4', '8', '1', '6', '9', '6', '2', '7', '5', '3', '3', '7', '2', '5', '7', '4', '4', '4', '4', '2', '8', '8', '2', '1', '9', '1', '7', '5', '9', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '8', '5', '3', '1', '7', '1', '7', '7', '6', '2', '2', '1', '7', '7', '6', '0', '5', '6', '4', '9', '8', '5', '5', '4', '0', '4', '9', '3', '9', '6', '6', '6', '6', '5', '6', '6', '6', '4', '1', '6', '3', '2', '2', '0', '6', '5', '4', '5', '4', '9', '8', '1', '9', '6', '7', '4', '2', '7', '6', '5', '0', '3', '0', '3', '3', '1', '0', '5', '9', '7', '2', '0', '1', '4', '9', '0', '0', '2', '1', '3', '0', '6', '0', '7', '1', '3', '1', '6', '3', '6', '2', '9', '3', '3', '1', '3', '0', '1', '8', '5', '9', '7', '9', '3', '1', '3', '8', '2', '4', '8', '0', '2', '0', '8', '2', '9', '3', '8', '1', '4', '7', '2', '6', '7', '9', '7', '7', '7', '8', '6', '3', '8', '2', '8', '3', '8', '6', '0', '5', '7', '5', '2', '9', '5', '0', '7', '4', '6', '6', '1', '8', '3', '4', '5', '1', '6', '1', '9', '2', '1', '9', '8', '5', '0', '7', '3', '6', '5', '9', '1', '5', '6', '1', '0', '7', '1', '4', '8', '4', '9', '7', '8', '7', '5', '0', '4', '3', '4', '6', '6', '0', '1', '7', '"', ',']

theorem object_fragment0226556_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 376) (SourceJson.white (fragment0226556Field007Chars00 ++ tail)) fragment0226556Acc00700 =
      SourceJson.object (fuel + 375) (SourceJson.white tail) fragment0226556Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_007"
  err.flush

noncomputable def fragment0226556Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0226556Field008Value00 : SourceJson := .str (String.ofList ['1', '5', '0', '9', '6', '5', '2', '0', '0', '5', '4', '3', '9'])
noncomputable def fragment0226556Acc00900 : List (String × SourceJson) := (fragment0226556Field008Key00, fragment0226556Field008Value00) :: fragment0226556Acc00800
noncomputable def fragment0226556Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '0', '9', '6', '5', '2', '0', '0', '5', '4', '3', '9', '"', ',']

theorem object_fragment0226556_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 375) (SourceJson.white (fragment0226556Field008Chars00 ++ tail)) fragment0226556Acc00800 =
      SourceJson.object (fuel + 374) (SourceJson.white tail) fragment0226556Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_008"
  err.flush

noncomputable def fragment0226556Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0226556Field009Value00 : SourceJson := .str (String.ofList ['5', '9', '9', '9', '3', '1', '9', '6', '8', '3', '1', '0', '4'])
noncomputable def fragment0226556Acc01000 : List (String × SourceJson) := (fragment0226556Field009Key00, fragment0226556Field009Value00) :: fragment0226556Acc00900
noncomputable def fragment0226556Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '9', '9', '3', '1', '9', '6', '8', '3', '1', '0', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0226556_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 374) (SourceJson.white (fragment0226556Field009Chars00 ++ tail)) fragment0226556Acc00900 =
      .ok (.obj (fragment0226556Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0226556_object_field_009"
  err.flush

noncomputable def fragment0226556Chars : List Char := '{' :: (fragment0226556Field000Chars00 ++ fragment0226556Field001Chars00 ++ fragment0226556Field002Chars00 ++ fragment0226556Field003Chars00 ++ fragment0226556Field004Chars00 ++ fragment0226556Field005Chars00 ++ fragment0226556Field006Chars00 ++ fragment0226556Field007Chars00 ++ fragment0226556Field008Chars00 ++ fragment0226556Field009Chars00)
noncomputable def fragment0226556Value : SourceJson := .obj (fragment0226556Acc01000.reverse)

theorem value_fragment0226556 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 384) (fragment0226556Chars ++ tail) =
      .ok (fragment0226556Value, tail) := by
  have hinput : fragment0226556Chars ++ tail = '{' :: (fragment0226556Field000Chars00 ++ (fragment0226556Field001Chars00 ++ (fragment0226556Field002Chars00 ++ (fragment0226556Field003Chars00 ++ (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0226556Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 384) (fragment0226556Chars ++ tail) =
        SourceJson.value (fuel + 384) ('{' :: (fragment0226556Field000Chars00 ++ (fragment0226556Field001Chars00 ++ (fragment0226556Field002Chars00 ++ (fragment0226556Field003Chars00 ++ (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 384)) hinput
    _ = SourceJson.object (fuel + 383) (SourceJson.white (fragment0226556Field000Chars00 ++ (fragment0226556Field001Chars00 ++ (fragment0226556Field002Chars00 ++ (fragment0226556Field003Chars00 ++ (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))))))))))) fragment0226556Acc00000 := by rfl
    _ = SourceJson.object (fuel + 382) (SourceJson.white (fragment0226556Field001Chars00 ++ (fragment0226556Field002Chars00 ++ (fragment0226556Field003Chars00 ++ (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail))))))))))) fragment0226556Acc00100 := object_fragment0226556_field_000 fuel (fragment0226556Field001Chars00 ++ (fragment0226556Field002Chars00 ++ (fragment0226556Field003Chars00 ++ (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 381) (SourceJson.white (fragment0226556Field002Chars00 ++ (fragment0226556Field003Chars00 ++ (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))))))))) fragment0226556Acc00200 := object_fragment0226556_field_001 fuel (fragment0226556Field002Chars00 ++ (fragment0226556Field003Chars00 ++ (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 380) (SourceJson.white (fragment0226556Field003Chars00 ++ (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail))))))))) fragment0226556Acc00300 := object_fragment0226556_field_002 fuel (fragment0226556Field003Chars00 ++ (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 379) (SourceJson.white (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))))))) fragment0226556Acc00400 := object_fragment0226556_field_003 fuel (fragment0226556Field004Chars00 ++ (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 378) (SourceJson.white (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail))))))) fragment0226556Acc00500 := object_fragment0226556_field_004 fuel (fragment0226556Field005Chars00 ++ (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 377) (SourceJson.white (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))))) fragment0226556Acc00600 := object_fragment0226556_field_005 fuel (fragment0226556Field006Chars00 ++ (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 376) (SourceJson.white (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail))))) fragment0226556Acc00700 := object_fragment0226556_field_006 fuel (fragment0226556Field007Chars00 ++ (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 375) (SourceJson.white (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))) fragment0226556Acc00800 := object_fragment0226556_field_007 fuel (fragment0226556Field008Chars00 ++ (fragment0226556Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 374) (SourceJson.white (fragment0226556Field009Chars00 ++ (tail))) fragment0226556Acc00900 := object_fragment0226556_field_008 fuel (fragment0226556Field009Chars00 ++ (tail))
    _ = .ok (fragment0226556Value, tail) := object_fragment0226556_field_009 fuel (tail)

noncomputable def fragment0228459Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0228459Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0228459Field000Value00 : SourceJson := .number (String.ofList ['5', '4'])
noncomputable def fragment0228459Acc00100 : List (String × SourceJson) := (fragment0228459Field000Key00, fragment0228459Field000Value00) :: fragment0228459Acc00000
noncomputable def fragment0228459Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '4', ',']

theorem object_fragment0228459_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0228459Field000Chars00 ++ tail)) fragment0228459Acc00000 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0228459Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_000"
  err.flush

noncomputable def fragment0228459Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0228459Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0228459Acc00200 : List (String × SourceJson) := (fragment0228459Field001Key00, fragment0228459Field001Value00) :: fragment0228459Acc00100
noncomputable def fragment0228459Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0228459_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0228459Field001Chars00 ++ tail)) fragment0228459Acc00100 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0228459Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_001"
  err.flush

noncomputable def fragment0228459Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0228459Field002Value00 : SourceJson := .str (String.ofList ['1', '2', '7', '2', '7', '4', '1', '8', '8', '8', '1', '8', '7', '7', '5', '3', '7', '2', '7', '1', '4', '6', '8', '0', '6', '8', '9', '5', '2', '4', '4', '4', '7', '1', '6', '9', '5', '9', '8', '1', '/', '1', '3', '8', '2', '3', '9', '7', '1', '8', '5', '8', '2', '0', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0228459Acc00300 : List (String × SourceJson) := (fragment0228459Field002Key00, fragment0228459Field002Value00) :: fragment0228459Acc00200
noncomputable def fragment0228459Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '2', '7', '2', '7', '4', '1', '8', '8', '8', '1', '8', '7', '7', '5', '3', '7', '2', '7', '1', '4', '6', '8', '0', '6', '8', '9', '5', '2', '4', '4', '4', '7', '1', '6', '9', '5', '9', '8', '1', '/', '1', '3', '8', '2', '3', '9', '7', '1', '8', '5', '8', '2', '0', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0228459_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0228459Field002Chars00 ++ tail)) fragment0228459Acc00200 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0228459Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_002"
  err.flush

noncomputable def fragment0228459Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0228459Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0228459Acc00400 : List (String × SourceJson) := (fragment0228459Field003Key00, fragment0228459Field003Value00) :: fragment0228459Acc00300
noncomputable def fragment0228459Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0228459_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0228459Field003Chars00 ++ tail)) fragment0228459Acc00300 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0228459Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_003"
  err.flush

noncomputable def fragment0228459Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0228459Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0228459Acc00500 : List (String × SourceJson) := (fragment0228459Field004Key00, fragment0228459Field004Value00) :: fragment0228459Acc00400
noncomputable def fragment0228459Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0228459_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0228459Field004Chars00 ++ tail)) fragment0228459Acc00400 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0228459Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_004"
  err.flush

noncomputable def fragment0228459Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0228459Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '6', '2', '2', '1', '6', '4', '8', '8', '6', '2', '3', '/', '6', '3', '7', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '0', '6', '3', '7', '3', '8', '6', '8', '9', '9', '/', '6', '3', '7', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '3', '7', '8', '4', '3', '1', '8', '9', '3', '/', '3', '3', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '6', '1', '8', '0', '9', '4', '4', '7', '2', '8', '9', '/', '3', '8', '2', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '4', '1', '0', '2', '1', '8', '8', '6', '6', '4', '9', '/', '3', '8', '2', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '5', '7', '0', '0', '5', '6', '2', '8', '3', '/', '3', '4', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '4', '2', '5', '1', '7', '1', '7', '1', '/', '2', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '9', '0', '1', '8', '6', '5', '9', '2', '7', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '9', '5', '6', '7', '4', '4', '9', '6', '7', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '3', '9', '1', '8', '7', '5', '3', '4', '5', '9', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0228459Acc00600 : List (String × SourceJson) := (fragment0228459Field005Key00, fragment0228459Field005Value00) :: fragment0228459Acc00500
noncomputable def fragment0228459Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '2', '2', '1', '6', '4', '8', '8', '6', '2', '3', '/', '6', '3', '7', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '0', '6', '3', '7', '3', '8', '6', '8', '9', '9', '/', '6', '3', '7', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '3', '7', '8', '4', '3', '1', '8', '9', '3', '/', '3', '3', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '6', '1', '8', '0', '9', '4', '4', '7', '2', '8', '9', '/', '3', '8', '2', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '4', '1', '0', '2', '1', '8', '8', '6', '6', '4', '9', '/', '3', '8', '2', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '5', '7', '0', '0', '5', '6', '2', '8', '3', '/', '3', '4', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '4', '2', '5', '1', '7', '1', '7', '1', '/', '2', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '9', '0', '1', '8', '6', '5', '9', '2', '7', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '9', '5', '6', '7', '4', '4', '9', '6', '7', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '3', '9', '1', '8', '7', '5', '3', '4', '5', '9', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0228459_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0228459Field005Chars00 ++ tail)) fragment0228459Acc00500 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0228459Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_005"
  err.flush

noncomputable def fragment0228459Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0228459Field006Value00 : SourceJson := .str (String.ofList ['5', '6', '8', '0', '5', '6', '5', '7', '8', '2', '2', '7', '8', '4', '8', '7', '5', '1', '9', '7', '9', '7', '5', '9', '6', '0', '0', '2', '6', '2', '0', '4', '6', '7', '0', '4', '2', '6', '9', '8', '9', '7', '0', '9', '1', '3', '7', '9', '2', '0', '0', '0', '0', '/', '7', '5', '1', '6', '8', '6', '1', '7', '6', '9', '3', '0', '5', '2', '7', '0', '5', '6', '2', '8', '4', '6', '4', '7', '3', '3', '4', '8', '0', '2', '1', '0', '9', '9', '2', '0', '6', '6', '2', '2', '4', '5', '5', '4', '0', '5', '8', '6', '4', '8', '2', '5', '3', '5', '5', '0', '1', '0', '5', '7', '0', '3', '6', '2', '0', '6', '7', '2', '9'])
noncomputable def fragment0228459Acc00700 : List (String × SourceJson) := (fragment0228459Field006Key00, fragment0228459Field006Value00) :: fragment0228459Acc00600
noncomputable def fragment0228459Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '6', '8', '0', '5', '6', '5', '7', '8', '2', '2', '7', '8', '4', '8', '7', '5', '1', '9', '7', '9', '7', '5', '9', '6', '0', '0', '2', '6', '2', '0', '4', '6', '7', '0', '4', '2', '6', '9', '8', '9', '7', '0', '9', '1', '3', '7', '9', '2', '0', '0', '0', '0', '/', '7', '5', '1', '6', '8', '6', '1', '7', '6', '9', '3', '0', '5', '2', '7', '0', '5', '6', '2', '8', '4', '6', '4', '7', '3', '3', '4', '8', '0', '2', '1', '0', '9', '9', '2', '0', '6', '6', '2', '2', '4', '5', '5', '4', '0', '5', '8', '6', '4', '8', '2', '5', '3', '5', '5', '0', '1', '0', '5', '7', '0', '3', '6', '2', '0', '6', '7', '2', '9', '"', ',']

theorem object_fragment0228459_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0228459Field006Chars00 ++ tail)) fragment0228459Acc00600 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0228459Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_006"
  err.flush

noncomputable def fragment0228459Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0228459Field007Value00 : SourceJson := .str (String.ofList ['2', '6', '7', '0', '9', '5', '3', '7', '0', '8', '2', '8', '2', '4', '7', '7', '5', '4', '9', '5', '4', '3', '1', '8', '8', '3', '7', '8', '5', '4', '9', '0', '6', '0', '3', '7', '8', '0', '7', '9', '9', '8', '1', '7', '0', '4', '7', '5', '0', '2', '4', '5', '8', '2', '8', '9', '1', '1', '1', '7', '1', '9', '4', '0', '8', '4', '7', '9', '9', '9', '7', '4', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '2', '0', '0', '0', '3', '1', '4', '9', '3', '2', '2', '5', '9', '4', '6', '8', '2', '4', '6', '0', '3', '1', '5', '2', '2', '8', '6', '2', '3', '7', '2', '5', '2', '1', '4', '3', '9', '8', '4', '1', '1', '1', '7', '2', '3', '3', '2', '4', '4', '9', '8', '8', '9', '1', '4', '5', '4', '2', '7', '9', '4', '2', '6', '7', '0', '1', '6', '8', '4', '3', '3', '4', '8', '1', '2', '0', '3', '1', '6', '7', '1', '0', '5', '2', '2', '6', '8', '2', '5', '3', '1', '4', '9', '2', '4', '3', '9', '7', '2', '0', '8', '4', '2', '1', '0', '0', '9', '4', '6', '2', '6', '4', '3'])
noncomputable def fragment0228459Acc00800 : List (String × SourceJson) := (fragment0228459Field007Key00, fragment0228459Field007Value00) :: fragment0228459Acc00700
noncomputable def fragment0228459Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '7', '0', '9', '5', '3', '7', '0', '8', '2', '8', '2', '4', '7', '7', '5', '4', '9', '5', '4', '3', '1', '8', '8', '3', '7', '8', '5', '4', '9', '0', '6', '0', '3', '7', '8', '0', '7', '9', '9', '8', '1', '7', '0', '4', '7', '5', '0', '2', '4', '5', '8', '2', '8', '9', '1', '1', '1', '7', '1', '9', '4', '0', '8', '4', '7', '9', '9', '9', '7', '4', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '2', '0', '0', '0', '3', '1', '4', '9', '3', '2', '2', '5', '9', '4', '6', '8', '2', '4', '6', '0', '3', '1', '5', '2', '2', '8', '6', '2', '3', '7', '2', '5', '2', '1', '4', '3', '9', '8', '4', '1', '1', '1', '7', '2', '3', '3', '2', '4', '4', '9', '8', '8', '9', '1', '4', '5', '4', '2', '7', '9', '4', '2', '6', '7', '0', '1', '6', '8', '4', '3', '3', '4', '8', '1', '2', '0', '3', '1', '6', '7', '1', '0', '5', '2', '2', '6', '8', '2', '5', '3', '1', '4', '9', '2', '4', '3', '9', '7', '2', '0', '8', '4', '2', '1', '0', '0', '9', '4', '6', '2', '6', '4', '3', '"', ',']

theorem object_fragment0228459_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0228459Field007Chars00 ++ tail)) fragment0228459Acc00700 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0228459Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_007"
  err.flush

noncomputable def fragment0228459Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0228459Field008Value00 : SourceJson := .str (String.ofList ['5', '9', '8', '7', '3', '4', '9', '5', '4', '5', '3', '7', '9'])
noncomputable def fragment0228459Acc00900 : List (String × SourceJson) := (fragment0228459Field008Key00, fragment0228459Field008Value00) :: fragment0228459Acc00800
noncomputable def fragment0228459Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '8', '7', '3', '4', '9', '5', '4', '5', '3', '7', '9', '"', ',']

theorem object_fragment0228459_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0228459Field008Chars00 ++ tail)) fragment0228459Acc00800 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0228459Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_008"
  err.flush

noncomputable def fragment0228459Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0228459Field009Value00 : SourceJson := .str (String.ofList ['2', '9', '3', '9', '0', '8', '0', '9', '5', '6', '3', '3', '9', '9'])
noncomputable def fragment0228459Acc01000 : List (String × SourceJson) := (fragment0228459Field009Key00, fragment0228459Field009Value00) :: fragment0228459Acc00900
noncomputable def fragment0228459Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '3', '9', '0', '8', '0', '9', '5', '6', '3', '3', '9', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0228459_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0228459Field009Chars00 ++ tail)) fragment0228459Acc00900 =
      .ok (.obj (fragment0228459Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0228459_object_field_009"
  err.flush

noncomputable def fragment0228459Chars : List Char := '{' :: (fragment0228459Field000Chars00 ++ fragment0228459Field001Chars00 ++ fragment0228459Field002Chars00 ++ fragment0228459Field003Chars00 ++ fragment0228459Field004Chars00 ++ fragment0228459Field005Chars00 ++ fragment0228459Field006Chars00 ++ fragment0228459Field007Chars00 ++ fragment0228459Field008Chars00 ++ fragment0228459Field009Chars00)
noncomputable def fragment0228459Value : SourceJson := .obj (fragment0228459Acc01000.reverse)

theorem value_fragment0228459 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 225) (fragment0228459Chars ++ tail) =
      .ok (fragment0228459Value, tail) := by
  have hinput : fragment0228459Chars ++ tail = '{' :: (fragment0228459Field000Chars00 ++ (fragment0228459Field001Chars00 ++ (fragment0228459Field002Chars00 ++ (fragment0228459Field003Chars00 ++ (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0228459Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 225) (fragment0228459Chars ++ tail) =
        SourceJson.value (fuel + 225) ('{' :: (fragment0228459Field000Chars00 ++ (fragment0228459Field001Chars00 ++ (fragment0228459Field002Chars00 ++ (fragment0228459Field003Chars00 ++ (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 225)) hinput
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0228459Field000Chars00 ++ (fragment0228459Field001Chars00 ++ (fragment0228459Field002Chars00 ++ (fragment0228459Field003Chars00 ++ (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))))))))))) fragment0228459Acc00000 := by rfl
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0228459Field001Chars00 ++ (fragment0228459Field002Chars00 ++ (fragment0228459Field003Chars00 ++ (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail))))))))))) fragment0228459Acc00100 := object_fragment0228459_field_000 fuel (fragment0228459Field001Chars00 ++ (fragment0228459Field002Chars00 ++ (fragment0228459Field003Chars00 ++ (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0228459Field002Chars00 ++ (fragment0228459Field003Chars00 ++ (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))))))))) fragment0228459Acc00200 := object_fragment0228459_field_001 fuel (fragment0228459Field002Chars00 ++ (fragment0228459Field003Chars00 ++ (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0228459Field003Chars00 ++ (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail))))))))) fragment0228459Acc00300 := object_fragment0228459_field_002 fuel (fragment0228459Field003Chars00 ++ (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))))))) fragment0228459Acc00400 := object_fragment0228459_field_003 fuel (fragment0228459Field004Chars00 ++ (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail))))))) fragment0228459Acc00500 := object_fragment0228459_field_004 fuel (fragment0228459Field005Chars00 ++ (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))))) fragment0228459Acc00600 := object_fragment0228459_field_005 fuel (fragment0228459Field006Chars00 ++ (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail))))) fragment0228459Acc00700 := object_fragment0228459_field_006 fuel (fragment0228459Field007Chars00 ++ (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))) fragment0228459Acc00800 := object_fragment0228459_field_007 fuel (fragment0228459Field008Chars00 ++ (fragment0228459Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0228459Field009Chars00 ++ (tail))) fragment0228459Acc00900 := object_fragment0228459_field_008 fuel (fragment0228459Field009Chars00 ++ (tail))
    _ = .ok (fragment0228459Value, tail) := object_fragment0228459_field_009 fuel (tail)

noncomputable def fragment0230050Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0230050Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0230050Field000Value00 : SourceJson := .number (String.ofList ['5', '5'])
noncomputable def fragment0230050Acc00100 : List (String × SourceJson) := (fragment0230050Field000Key00, fragment0230050Field000Value00) :: fragment0230050Acc00000
noncomputable def fragment0230050Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '5', '5', ',']

theorem object_fragment0230050_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 438) (SourceJson.white (fragment0230050Field000Chars00 ++ tail)) fragment0230050Acc00000 =
      SourceJson.object (fuel + 437) (SourceJson.white tail) fragment0230050Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_000"
  err.flush

noncomputable def fragment0230050Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0230050Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0230050Acc00200 : List (String × SourceJson) := (fragment0230050Field001Key00, fragment0230050Field001Value00) :: fragment0230050Acc00100
noncomputable def fragment0230050Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0230050_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0230050Field001Chars00 ++ tail)) fragment0230050Acc00100 =
      SourceJson.object (fuel + 436) (SourceJson.white tail) fragment0230050Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_001"
  err.flush

noncomputable def fragment0230050Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0230050Field002Value00 : SourceJson := .str (String.ofList ['6', '5', '1', '5', '1', '5', '9', '8', '0', '2', '6', '8', '0', '9', '1', '6', '3', '1', '7', '3', '5', '9', '4', '5', '0', '9', '5', '5', '1', '6', '5', '8', '3', '1', '3', '9', '/', '1', '1', '7', '0', '5', '5', '3', '1', '7', '2', '6', '3', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0230050Acc00300 : List (String × SourceJson) := (fragment0230050Field002Key00, fragment0230050Field002Value00) :: fragment0230050Acc00200
noncomputable def fragment0230050Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '5', '1', '5', '1', '5', '9', '8', '0', '2', '6', '8', '0', '9', '1', '6', '3', '1', '7', '3', '5', '9', '4', '5', '0', '9', '5', '5', '1', '6', '5', '8', '3', '1', '3', '9', '/', '1', '1', '7', '0', '5', '5', '3', '1', '7', '2', '6', '3', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0230050_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0230050Field002Chars00 ++ tail)) fragment0230050Acc00200 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0230050Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_002"
  err.flush

noncomputable def fragment0230050Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0230050Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0230050Acc00400 : List (String × SourceJson) := (fragment0230050Field003Key00, fragment0230050Field003Value00) :: fragment0230050Acc00300
noncomputable def fragment0230050Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0230050_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0230050Field003Chars00 ++ tail)) fragment0230050Acc00300 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0230050Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_003"
  err.flush

noncomputable def fragment0230050Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0230050Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0230050Acc00500 : List (String × SourceJson) := (fragment0230050Field004Key00, fragment0230050Field004Value00) :: fragment0230050Acc00400
noncomputable def fragment0230050Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '1', '0', '0', '6', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0230050_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0230050Field004Chars00 ++ tail)) fragment0230050Acc00400 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0230050Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_004"
  err.flush

noncomputable def fragment0230050Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0230050Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '5', '9', '7', '1', '7', '2', '3', '4', '4', '4', '8', '5', '9', '7', '5', '5', '2', '5', '1', '9', '4', '2', '3', '/', '8', '8', '2', '3', '9', '4', '8', '2', '2', '8', '0', '5', '9', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '0', '1', '5', '2', '4', '2', '5', '6', '9', '7', '8', '4', '1', '4', '7', '1', '0', '3', '2', '9', '/', '2', '9', '3', '1', '5', '4', '4', '2', '6', '1', '8', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '1', '1', '1', '7', '4', '7', '5', '0', '9', '3', '8', '9', '0', '6', '0', '1', '5', '0', '9', '1', '9', '/', '7', '6', '7', '2', '9', '9', '8', '4', '5', '9', '1', '8', '2', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '9', '0', '0', '8', '2', '0', '9', '8', '4', '2', '3', '9', '2', '0', '7', '2', '8', '7', '4', '3', '9', '/', '1', '4', '7', '0', '6', '5', '8', '0', '3', '8', '0', '0', '9', '9', '5', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '1', '0', '1', '6', '4', '4', '0', '9', '2', '4', '9', '9', '9', '8', '9', '9', '3', '2', '9', '9', '9', '/', '1', '4', '7', '0', '6', '5', '8', '0', '3', '8', '0', '0', '9', '9', '5', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '7', '0', '3', '6', '6', '9', '4', '8', '3', '3', '1', '5', '6', '6', '3', '1', '9', '0', '7', '3', '3', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '7', '6', '0', '8', '9', '8', '8', '9', '6', '5', '0', '7', '4', '1', '1', '2', '3', '7', '0', '7', '/', '4', '0', '1', '0', '8', '8', '5', '5', '5', '8', '2', '0', '8', '9', '6', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '9', '1', '9', '1', '7', '5', '7', '3', '1', '9', '4', '0', '7', '0', '5', '5', '2', '9', '5', '9', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '8', '3', '1', '5', '4', '1', '0', '6', '7', '7', '1', '0', '9', '5', '3', '3', '9', '6', '7', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '7', '5', '3', '0', '9', '6', '1', '3', '7', '7', '3', '2', '0', '0', '7', '8', '5', '6', '3', '/', '2', '9', '3', '1', '5', '4', '4', '2', '6', '1', '8', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0230050Acc00600 : List (String × SourceJson) := (fragment0230050Field005Key00, fragment0230050Field005Value00) :: fragment0230050Acc00500
noncomputable def fragment0230050Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '9', '7', '1', '7', '2', '3', '4', '4', '4', '8', '5', '9', '7', '5', '5', '2', '5', '1', '9', '4', '2', '3', '/', '8', '8', '2', '3', '9', '4', '8', '2', '2', '8', '0', '5', '9', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '0', '1', '5', '2', '4', '2', '5', '6', '9', '7', '8', '4', '1', '4', '7', '1', '0', '3', '2', '9', '/', '2', '9', '3', '1', '5', '4', '4', '2', '6', '1', '8', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '1', '1', '7', '4', '7', '5', '0', '9', '3', '8', '9', '0', '6', '0', '1', '5', '0', '9', '1', '9', '/', '7', '6', '7', '2', '9', '9', '8', '4', '5', '9', '1', '8', '2', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '9', '0', '0', '8', '2', '0', '9', '8', '4', '2', '3', '9', '2', '0', '7', '2', '8', '7', '4', '3', '9', '/', '1', '4', '7', '0', '6', '5', '8', '0', '3', '8', '0', '0', '9', '9', '5', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '1', '0', '1', '6', '4', '4', '0', '9', '2', '4', '9', '9', '9', '8', '9', '9', '3', '2', '9', '9', '9', '/', '1', '4', '7', '0', '6', '5', '8', '0', '3', '8', '0', '0', '9', '9', '5', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '7', '0', '3', '6', '6', '9', '4', '8', '3', '3', '1', '5', '6', '6', '3', '1', '9', '0', '7', '3', '3', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '7', '6', '0', '8', '9', '8', '8', '9', '6', '5', '0', '7', '4', '1', '1', '2', '3', '7', '0', '7', '/', '4', '0', '1', '0', '8', '8', '5', '5', '5', '8', '2', '0', '8', '9', '6', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '9', '1', '9', '1', '7', '5', '7', '3', '1', '9', '4', '0', '7', '0', '5', '5', '2', '9', '5', '9', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '8', '3', '1', '5', '4', '1', '0', '6', '7', '7', '1', '0', '9', '5', '3', '3', '9', '6', '7', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '7', '5', '3', '0', '9', '6', '1', '3', '7', '7', '3', '2', '0', '0', '7', '8', '5', '6', '3', '/', '2', '9', '3', '1', '5', '4', '4', '2', '6', '1', '8', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0230050_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0230050Field005Chars00 ++ tail)) fragment0230050Acc00500 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0230050Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_005"
  err.flush

noncomputable def fragment0230050Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0230050Field006Value00 : SourceJson := .str (String.ofList ['1', '7', '2', '3', '2', '8', '5', '2', '6', '9', '4', '6', '7', '6', '5', '1', '9', '3', '5', '0', '2', '7', '4', '4', '6', '2', '3', '1', '6', '5', '2', '5', '3', '7', '3', '5', '6', '9', '9', '2', '2', '4', '3', '3', '7', '8', '7', '5', '/', '6', '0', '6', '6', '6', '2', '6', '6', '9', '5', '4', '5', '2', '9', '8', '7', '3', '8', '6', '3', '1', '9', '4', '0', '7', '9', '8', '5', '0', '5', '8', '1', '0', '2', '1', '9', '9', '5', '9', '1', '7', '8', '3', '0', '5', '0', '7', '5', '2', '6', '0', '0', '2', '8', '0', '2', '4', '3', '9', '9', '1', '2', '8', '2', '4'])
noncomputable def fragment0230050Acc00700 : List (String × SourceJson) := (fragment0230050Field006Key00, fragment0230050Field006Value00) :: fragment0230050Acc00600
noncomputable def fragment0230050Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '7', '2', '3', '2', '8', '5', '2', '6', '9', '4', '6', '7', '6', '5', '1', '9', '3', '5', '0', '2', '7', '4', '4', '6', '2', '3', '1', '6', '5', '2', '5', '3', '7', '3', '5', '6', '9', '9', '2', '2', '4', '3', '3', '7', '8', '7', '5', '/', '6', '0', '6', '6', '6', '2', '6', '6', '9', '5', '4', '5', '2', '9', '8', '7', '3', '8', '6', '3', '1', '9', '4', '0', '7', '9', '8', '5', '0', '5', '8', '1', '0', '2', '1', '9', '9', '5', '9', '1', '7', '8', '3', '0', '5', '0', '7', '5', '2', '6', '0', '0', '2', '8', '0', '2', '4', '3', '9', '9', '1', '2', '8', '2', '4', '"', ',']

theorem object_fragment0230050_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0230050Field006Chars00 ++ tail)) fragment0230050Acc00600 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0230050Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_006"
  err.flush

noncomputable def fragment0230050Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0230050Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '7', '0', '9', '4', '9', '5', '4', '9', '4', '5', '4', '1', '2', '5', '6', '8', '2', '2', '2', '2', '7', '8', '1', '0', '5', '0', '6', '1', '4', '5', '2', '4', '6', '6', '8', '4', '6', '0', '4', '8', '0', '9', '6', '6', '1', '1', '3', '7', '5', '3', '2', '4', '8', '7', '9', '6', '8', '8', '2', '7', '2', '5', '0', '4', '0', '0', '1', '6', '1', '2', '9', '0', '8', '9', '7', '7', '8', '2', '5', '3', '5', '8', '9', '2', '8', '6', '3', '5', '6', '0', '4', '5', '1', '6', '5', '9', '2', '3', '0', '0', '8', '5', '7', '9', '2', '8', '0', '9', '4', '8', '4', '9', '0', '9', '9', '9', '7', '3', '4', '8', '9', '3', '4', '2', '6', '5', '5', '0', '3', '5', '6', '4', '2', '8', '4', '7', '5', '4', '9', '1', '7', '4', '5', '2', '4', '6', '4', '1', '2', '5', '2', '3', '8', '6', '6', '5', '7', '3', '7', '3', '9', '0', '1', '7', '9', '2', '2', '5', '9', '3', '5', '4', '8', '1', '7', '5', '0', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '9', '4', '0', '0', '7', '4', '6', '3', '4', '5', '0', '4', '5', '4', '9', '9', '3', '0', '0', '9', '8', '6', '7', '2', '4', '6', '8', '4', '5', '2', '6', '8', '8', '4', '4', '3', '9', '5', '5', '5', '3', '8', '5', '4', '1', '1', '9', '3', '2', '7', '8', '1', '8', '9', '5', '2', '3', '6', '6', '4', '4', '5', '1', '9', '1', '4', '3', '5', '1', '0', '7', '5', '5', '5', '8', '4', '9', '2', '1', '1', '6', '8', '8', '8', '7', '2', '9', '8', '2', '2', '6', '0', '1', '4', '3', '1', '5', '5', '6', '6', '0', '3', '1', '7', '7', '9', '1', '4', '9', '5', '8', '8', '9', '0', '6', '5', '9', '0', '6', '9', '4', '4', '0', '9', '5', '6', '1', '6', '7', '3', '5', '3', '9', '4', '2', '4', '5', '2', '7', '7', '4', '5', '5', '7', '4', '9', '3', '0', '3', '6', '4', '4', '4', '9', '7', '2', '7', '4', '4', '9', '4', '3', '6', '2', '4', '0', '0', '6', '3', '3', '1', '9', '3', '6', '3', '4', '5', '5', '9', '3', '6', '6', '0', '0', '7', '5', '2', '6', '7', '7', '4', '4', '2', '3', '5', '9', '8', '8', '4', '5', '6', '4', '0', '5', '8', '3', '0', '6', '7', '8', '4', '8', '0', '2', '4', '9', '2', '3', '4', '0', '1'])
noncomputable def fragment0230050Acc00800 : List (String × SourceJson) := (fragment0230050Field007Key00, fragment0230050Field007Value00) :: fragment0230050Acc00700
noncomputable def fragment0230050Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '7', '0', '9', '4', '9', '5', '4', '9', '4', '5', '4', '1', '2', '5', '6', '8', '2', '2', '2', '2', '7', '8', '1', '0', '5', '0', '6', '1', '4', '5', '2', '4', '6', '6', '8', '4', '6', '0', '4', '8', '0', '9', '6', '6', '1', '1', '3', '7', '5', '3', '2', '4', '8', '7', '9', '6', '8', '8', '2', '7', '2', '5', '0', '4', '0', '0', '1', '6', '1', '2', '9', '0', '8', '9', '7', '7', '8', '2', '5', '3', '5', '8', '9', '2', '8', '6', '3', '5', '6', '0', '4', '5', '1', '6', '5', '9', '2', '3', '0', '0', '8', '5', '7', '9', '2', '8', '0', '9', '4', '8', '4', '9', '0', '9', '9', '9', '7', '3', '4', '8', '9', '3', '4', '2', '6', '5', '5', '0', '3', '5', '6', '4', '2', '8', '4', '7', '5', '4', '9', '1', '7', '4', '5', '2', '4', '6', '4', '1', '2', '5', '2', '3', '8', '6', '6', '5', '7', '3', '7', '3', '9', '0', '1', '7', '9', '2', '2', '5', '9', '3', '5', '4', '8', '1', '7', '5', '0', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '9', '4', '0', '0', '7', '4', '6', '3', '4', '5', '0', '4', '5', '4', '9', '9', '3', '0', '0', '9', '8', '6', '7', '2', '4', '6', '8', '4', '5', '2', '6', '8', '8', '4', '4', '3', '9', '5', '5', '5', '3', '8', '5', '4', '1', '1', '9', '3', '2', '7', '8', '1', '8', '9', '5', '2', '3', '6', '6', '4', '4', '5', '1', '9', '1', '4', '3', '5', '1', '0', '7', '5', '5', '5', '8', '4', '9', '2', '1', '1', '6', '8', '8', '8', '7', '2', '9', '8', '2', '2', '6', '0', '1', '4', '3', '1', '5', '5', '6', '6', '0', '3', '1', '7', '7', '9', '1', '4', '9', '5', '8', '8', '9', '0', '6', '5', '9', '0', '6', '9', '4', '4', '0', '9', '5', '6', '1', '6', '7', '3', '5', '3', '9', '4', '2', '4', '5', '2', '7', '7', '4', '5', '5', '7', '4', '9', '3', '0', '3', '6', '4', '4', '4', '9', '7', '2', '7', '4', '4', '9', '4', '3', '6', '2', '4', '0', '0', '6', '3', '3', '1', '9', '3', '6', '3', '4', '5', '5', '9', '3', '6', '6', '0', '0', '7', '5', '2', '6', '7', '7', '4', '4', '2', '3', '5', '9', '8', '8', '4', '5', '6', '4', '0', '5', '8', '3', '0', '6', '7', '8', '4', '8', '0', '2', '4', '9', '2', '3', '4', '0', '1', '"', ',']

theorem object_fragment0230050_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0230050Field007Chars00 ++ tail)) fragment0230050Acc00700 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0230050Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_007"
  err.flush

noncomputable def fragment0230050Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0230050Field008Value00 : SourceJson := .str (String.ofList ['2', '2', '5', '0', '5', '5', '4', '2', '5', '7', '6', '0'])
noncomputable def fragment0230050Acc00900 : List (String × SourceJson) := (fragment0230050Field008Key00, fragment0230050Field008Value00) :: fragment0230050Acc00800
noncomputable def fragment0230050Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '5', '0', '5', '5', '4', '2', '5', '7', '6', '0', '"', ',']

theorem object_fragment0230050_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0230050Field008Chars00 ++ tail)) fragment0230050Acc00800 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0230050Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_008"
  err.flush

noncomputable def fragment0230050Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0230050Field009Value00 : SourceJson := .str (String.ofList ['5', '8', '5', '0', '2', '0', '3', '3', '1', '4', '4', '2'])
noncomputable def fragment0230050Acc01000 : List (String × SourceJson) := (fragment0230050Field009Key00, fragment0230050Field009Value00) :: fragment0230050Acc00900
noncomputable def fragment0230050Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '5', '0', '2', '0', '3', '3', '1', '4', '4', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0230050_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0230050Field009Chars00 ++ tail)) fragment0230050Acc00900 =
      .ok (.obj (fragment0230050Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0230050_object_field_009"
  err.flush

noncomputable def fragment0230050Chars : List Char := '{' :: (fragment0230050Field000Chars00 ++ fragment0230050Field001Chars00 ++ fragment0230050Field002Chars00 ++ fragment0230050Field003Chars00 ++ fragment0230050Field004Chars00 ++ fragment0230050Field005Chars00 ++ fragment0230050Field006Chars00 ++ fragment0230050Field007Chars00 ++ fragment0230050Field008Chars00 ++ fragment0230050Field009Chars00)
noncomputable def fragment0230050Value : SourceJson := .obj (fragment0230050Acc01000.reverse)

theorem value_fragment0230050 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 439) (fragment0230050Chars ++ tail) =
      .ok (fragment0230050Value, tail) := by
  have hinput : fragment0230050Chars ++ tail = '{' :: (fragment0230050Field000Chars00 ++ (fragment0230050Field001Chars00 ++ (fragment0230050Field002Chars00 ++ (fragment0230050Field003Chars00 ++ (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0230050Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 439) (fragment0230050Chars ++ tail) =
        SourceJson.value (fuel + 439) ('{' :: (fragment0230050Field000Chars00 ++ (fragment0230050Field001Chars00 ++ (fragment0230050Field002Chars00 ++ (fragment0230050Field003Chars00 ++ (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 439)) hinput
    _ = SourceJson.object (fuel + 438) (SourceJson.white (fragment0230050Field000Chars00 ++ (fragment0230050Field001Chars00 ++ (fragment0230050Field002Chars00 ++ (fragment0230050Field003Chars00 ++ (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))))))))))) fragment0230050Acc00000 := by rfl
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0230050Field001Chars00 ++ (fragment0230050Field002Chars00 ++ (fragment0230050Field003Chars00 ++ (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail))))))))))) fragment0230050Acc00100 := object_fragment0230050_field_000 fuel (fragment0230050Field001Chars00 ++ (fragment0230050Field002Chars00 ++ (fragment0230050Field003Chars00 ++ (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0230050Field002Chars00 ++ (fragment0230050Field003Chars00 ++ (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))))))))) fragment0230050Acc00200 := object_fragment0230050_field_001 fuel (fragment0230050Field002Chars00 ++ (fragment0230050Field003Chars00 ++ (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0230050Field003Chars00 ++ (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail))))))))) fragment0230050Acc00300 := object_fragment0230050_field_002 fuel (fragment0230050Field003Chars00 ++ (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))))))) fragment0230050Acc00400 := object_fragment0230050_field_003 fuel (fragment0230050Field004Chars00 ++ (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail))))))) fragment0230050Acc00500 := object_fragment0230050_field_004 fuel (fragment0230050Field005Chars00 ++ (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))))) fragment0230050Acc00600 := object_fragment0230050_field_005 fuel (fragment0230050Field006Chars00 ++ (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail))))) fragment0230050Acc00700 := object_fragment0230050_field_006 fuel (fragment0230050Field007Chars00 ++ (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))) fragment0230050Acc00800 := object_fragment0230050_field_007 fuel (fragment0230050Field008Chars00 ++ (fragment0230050Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0230050Field009Chars00 ++ (tail))) fragment0230050Acc00900 := object_fragment0230050_field_008 fuel (fragment0230050Field009Chars00 ++ (tail))
    _ = .ok (fragment0230050Value, tail) := object_fragment0230050_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_before_reader"
  err.flush

noncomputable def chunk0048LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0048SuffixChars00 : List Char := [',']
noncomputable def chunk0048Chars00 : List Char := chunk0048LeadChars00 ++ fragment0216586Chars ++ chunk0048SuffixChars00
noncomputable def chunk0048Push00 (acc : List SourceJson) : List SourceJson := fragment0216586Value :: acc

noncomputable def chunk0048AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0048_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 609)
      (SourceJson.white (chunk0048LeadChars00 ++ (fragment0216586Chars ++ rest))) acc =
      (SourceJson.value (fuel + 608) (fragment0216586Chars ++ rest)).bind
        (chunk0048AfterValue00 (fuel + 608) acc) := by rfl

theorem array_chunk0048 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 609) (SourceJson.white (chunk0048Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 608) (SourceJson.white tail) (chunk0048Push00 acc) := by
  have hinput : chunk0048Chars00 ++ tail = chunk0048LeadChars00 ++ (fragment0216586Chars ++ (chunk0048SuffixChars00 ++ tail)) := by
    simp only [chunk0048Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 609) (SourceJson.white (chunk0048Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 609)
          (SourceJson.white (chunk0048LeadChars00 ++ (fragment0216586Chars ++ (chunk0048SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 609) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 608) (fragment0216586Chars ++ (chunk0048SuffixChars00 ++ tail))).bind
        (chunk0048AfterValue00 (fuel + 608) acc) := array_chunk0048_head fuel (chunk0048SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0216586Value, chunk0048SuffixChars00 ++ tail)).bind
        (chunk0048AfterValue00 (fuel + 608) acc) :=
      congrArg (fun result => result.bind (chunk0048AfterValue00 (fuel + 608) acc))
        (value_fragment0216586 (fuel + 117) (chunk0048SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 608) (SourceJson.white tail) (chunk0048Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_before_reader"
  err.flush

noncomputable def chunk0049LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0049SuffixChars00 : List Char := [',']
noncomputable def chunk0049Chars00 : List Char := chunk0049LeadChars00 ++ fragment0218704Chars ++ chunk0049SuffixChars00
noncomputable def chunk0049Push00 (acc : List SourceJson) : List SourceJson := fragment0218704Value :: acc

noncomputable def chunk0049AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0049_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 608)
      (SourceJson.white (chunk0049LeadChars00 ++ (fragment0218704Chars ++ rest))) acc =
      (SourceJson.value (fuel + 607) (fragment0218704Chars ++ rest)).bind
        (chunk0049AfterValue00 (fuel + 607) acc) := by rfl

theorem array_chunk0049 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 608) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 607) (SourceJson.white tail) (chunk0049Push00 acc) := by
  have hinput : chunk0049Chars00 ++ tail = chunk0049LeadChars00 ++ (fragment0218704Chars ++ (chunk0049SuffixChars00 ++ tail)) := by
    simp only [chunk0049Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 608) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 608)
          (SourceJson.white (chunk0049LeadChars00 ++ (fragment0218704Chars ++ (chunk0049SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 608) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 607) (fragment0218704Chars ++ (chunk0049SuffixChars00 ++ tail))).bind
        (chunk0049AfterValue00 (fuel + 607) acc) := array_chunk0049_head fuel (chunk0049SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0218704Value, chunk0049SuffixChars00 ++ tail)).bind
        (chunk0049AfterValue00 (fuel + 607) acc) :=
      congrArg (fun result => result.bind (chunk0049AfterValue00 (fuel + 607) acc))
        (value_fragment0218704 (fuel + 183) (chunk0049SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 607) (SourceJson.white tail) (chunk0049Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_before_reader"
  err.flush

noncomputable def chunk0050LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0050SuffixChars00 : List Char := [',']
noncomputable def chunk0050Chars00 : List Char := chunk0050LeadChars00 ++ fragment0220688Chars ++ chunk0050SuffixChars00
noncomputable def chunk0050Push00 (acc : List SourceJson) : List SourceJson := fragment0220688Value :: acc

noncomputable def chunk0050AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0050_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 607)
      (SourceJson.white (chunk0050LeadChars00 ++ (fragment0220688Chars ++ rest))) acc =
      (SourceJson.value (fuel + 606) (fragment0220688Chars ++ rest)).bind
        (chunk0050AfterValue00 (fuel + 606) acc) := by rfl

theorem array_chunk0050 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 607) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 606) (SourceJson.white tail) (chunk0050Push00 acc) := by
  have hinput : chunk0050Chars00 ++ tail = chunk0050LeadChars00 ++ (fragment0220688Chars ++ (chunk0050SuffixChars00 ++ tail)) := by
    simp only [chunk0050Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 607) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 607)
          (SourceJson.white (chunk0050LeadChars00 ++ (fragment0220688Chars ++ (chunk0050SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 607) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 606) (fragment0220688Chars ++ (chunk0050SuffixChars00 ++ tail))).bind
        (chunk0050AfterValue00 (fuel + 606) acc) := array_chunk0050_head fuel (chunk0050SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0220688Value, chunk0050SuffixChars00 ++ tail)).bind
        (chunk0050AfterValue00 (fuel + 606) acc) :=
      congrArg (fun result => result.bind (chunk0050AfterValue00 (fuel + 606) acc))
        (value_fragment0220688 (fuel + 345) (chunk0050SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 606) (SourceJson.white tail) (chunk0050Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_before_reader"
  err.flush

noncomputable def chunk0051LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0051SuffixChars00 : List Char := [',']
noncomputable def chunk0051Chars00 : List Char := chunk0051LeadChars00 ++ fragment0222362Chars ++ chunk0051SuffixChars00
noncomputable def chunk0051Push00 (acc : List SourceJson) : List SourceJson := fragment0222362Value :: acc

noncomputable def chunk0051AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0051_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 606)
      (SourceJson.white (chunk0051LeadChars00 ++ (fragment0222362Chars ++ rest))) acc =
      (SourceJson.value (fuel + 605) (fragment0222362Chars ++ rest)).bind
        (chunk0051AfterValue00 (fuel + 605) acc) := by rfl

theorem array_chunk0051 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 606) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 605) (SourceJson.white tail) (chunk0051Push00 acc) := by
  have hinput : chunk0051Chars00 ++ tail = chunk0051LeadChars00 ++ (fragment0222362Chars ++ (chunk0051SuffixChars00 ++ tail)) := by
    simp only [chunk0051Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 606) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 606)
          (SourceJson.white (chunk0051LeadChars00 ++ (fragment0222362Chars ++ (chunk0051SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 606) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 605) (fragment0222362Chars ++ (chunk0051SuffixChars00 ++ tail))).bind
        (chunk0051AfterValue00 (fuel + 605) acc) := array_chunk0051_head fuel (chunk0051SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0222362Value, chunk0051SuffixChars00 ++ tail)).bind
        (chunk0051AfterValue00 (fuel + 605) acc) :=
      congrArg (fun result => result.bind (chunk0051AfterValue00 (fuel + 605) acc))
        (value_fragment0222362 (fuel + 111) (chunk0051SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 605) (SourceJson.white tail) (chunk0051Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_before_reader"
  err.flush

noncomputable def chunk0052LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0052SuffixChars00 : List Char := [',']
noncomputable def chunk0052Chars00 : List Char := chunk0052LeadChars00 ++ fragment0224508Chars ++ chunk0052SuffixChars00
noncomputable def chunk0052Push00 (acc : List SourceJson) : List SourceJson := fragment0224508Value :: acc

noncomputable def chunk0052AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0052_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 605)
      (SourceJson.white (chunk0052LeadChars00 ++ (fragment0224508Chars ++ rest))) acc =
      (SourceJson.value (fuel + 604) (fragment0224508Chars ++ rest)).bind
        (chunk0052AfterValue00 (fuel + 604) acc) := by rfl

theorem array_chunk0052 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 605) (SourceJson.white (chunk0052Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 604) (SourceJson.white tail) (chunk0052Push00 acc) := by
  have hinput : chunk0052Chars00 ++ tail = chunk0052LeadChars00 ++ (fragment0224508Chars ++ (chunk0052SuffixChars00 ++ tail)) := by
    simp only [chunk0052Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 605) (SourceJson.white (chunk0052Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 605)
          (SourceJson.white (chunk0052LeadChars00 ++ (fragment0224508Chars ++ (chunk0052SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 605) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 604) (fragment0224508Chars ++ (chunk0052SuffixChars00 ++ tail))).bind
        (chunk0052AfterValue00 (fuel + 604) acc) := array_chunk0052_head fuel (chunk0052SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0224508Value, chunk0052SuffixChars00 ++ tail)).bind
        (chunk0052AfterValue00 (fuel + 604) acc) :=
      congrArg (fun result => result.bind (chunk0052AfterValue00 (fuel + 604) acc))
        (value_fragment0224508 (fuel + 153) (chunk0052SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 604) (SourceJson.white tail) (chunk0052Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0053_before_reader"
  err.flush

noncomputable def chunk0053LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0053SuffixChars00 : List Char := [',']
noncomputable def chunk0053Chars00 : List Char := chunk0053LeadChars00 ++ fragment0226556Chars ++ chunk0053SuffixChars00
noncomputable def chunk0053Push00 (acc : List SourceJson) : List SourceJson := fragment0226556Value :: acc

noncomputable def chunk0053AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0053_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 604)
      (SourceJson.white (chunk0053LeadChars00 ++ (fragment0226556Chars ++ rest))) acc =
      (SourceJson.value (fuel + 603) (fragment0226556Chars ++ rest)).bind
        (chunk0053AfterValue00 (fuel + 603) acc) := by rfl

theorem array_chunk0053 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 604) (SourceJson.white (chunk0053Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 603) (SourceJson.white tail) (chunk0053Push00 acc) := by
  have hinput : chunk0053Chars00 ++ tail = chunk0053LeadChars00 ++ (fragment0226556Chars ++ (chunk0053SuffixChars00 ++ tail)) := by
    simp only [chunk0053Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 604) (SourceJson.white (chunk0053Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 604)
          (SourceJson.white (chunk0053LeadChars00 ++ (fragment0226556Chars ++ (chunk0053SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 604) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 603) (fragment0226556Chars ++ (chunk0053SuffixChars00 ++ tail))).bind
        (chunk0053AfterValue00 (fuel + 603) acc) := array_chunk0053_head fuel (chunk0053SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0226556Value, chunk0053SuffixChars00 ++ tail)).bind
        (chunk0053AfterValue00 (fuel + 603) acc) :=
      congrArg (fun result => result.bind (chunk0053AfterValue00 (fuel + 603) acc))
        (value_fragment0226556 (fuel + 219) (chunk0053SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 603) (SourceJson.white tail) (chunk0053Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0053_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0054_before_reader"
  err.flush

noncomputable def chunk0054LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0054SuffixChars00 : List Char := [',']
noncomputable def chunk0054Chars00 : List Char := chunk0054LeadChars00 ++ fragment0228459Chars ++ chunk0054SuffixChars00
noncomputable def chunk0054Push00 (acc : List SourceJson) : List SourceJson := fragment0228459Value :: acc

noncomputable def chunk0054AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0054_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 603)
      (SourceJson.white (chunk0054LeadChars00 ++ (fragment0228459Chars ++ rest))) acc =
      (SourceJson.value (fuel + 602) (fragment0228459Chars ++ rest)).bind
        (chunk0054AfterValue00 (fuel + 602) acc) := by rfl

theorem array_chunk0054 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 603) (SourceJson.white (chunk0054Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 602) (SourceJson.white tail) (chunk0054Push00 acc) := by
  have hinput : chunk0054Chars00 ++ tail = chunk0054LeadChars00 ++ (fragment0228459Chars ++ (chunk0054SuffixChars00 ++ tail)) := by
    simp only [chunk0054Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 603) (SourceJson.white (chunk0054Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 603)
          (SourceJson.white (chunk0054LeadChars00 ++ (fragment0228459Chars ++ (chunk0054SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 603) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 602) (fragment0228459Chars ++ (chunk0054SuffixChars00 ++ tail))).bind
        (chunk0054AfterValue00 (fuel + 602) acc) := array_chunk0054_head fuel (chunk0054SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0228459Value, chunk0054SuffixChars00 ++ tail)).bind
        (chunk0054AfterValue00 (fuel + 602) acc) :=
      congrArg (fun result => result.bind (chunk0054AfterValue00 (fuel + 602) acc))
        (value_fragment0228459 (fuel + 377) (chunk0054SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 602) (SourceJson.white tail) (chunk0054Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0054_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0055_before_reader"
  err.flush

noncomputable def chunk0055LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0055SuffixChars00 : List Char := [',']
noncomputable def chunk0055Chars00 : List Char := chunk0055LeadChars00 ++ fragment0230050Chars ++ chunk0055SuffixChars00
noncomputable def chunk0055Push00 (acc : List SourceJson) : List SourceJson := fragment0230050Value :: acc

noncomputable def chunk0055AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0055_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 602)
      (SourceJson.white (chunk0055LeadChars00 ++ (fragment0230050Chars ++ rest))) acc =
      (SourceJson.value (fuel + 601) (fragment0230050Chars ++ rest)).bind
        (chunk0055AfterValue00 (fuel + 601) acc) := by rfl

theorem array_chunk0055 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 602) (SourceJson.white (chunk0055Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 601) (SourceJson.white tail) (chunk0055Push00 acc) := by
  have hinput : chunk0055Chars00 ++ tail = chunk0055LeadChars00 ++ (fragment0230050Chars ++ (chunk0055SuffixChars00 ++ tail)) := by
    simp only [chunk0055Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 602) (SourceJson.white (chunk0055Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 602)
          (SourceJson.white (chunk0055LeadChars00 ++ (fragment0230050Chars ++ (chunk0055SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 602) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 601) (fragment0230050Chars ++ (chunk0055SuffixChars00 ++ tail))).bind
        (chunk0055AfterValue00 (fuel + 601) acc) := array_chunk0055_head fuel (chunk0055SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0230050Value, chunk0055SuffixChars00 ++ tail)).bind
        (chunk0055AfterValue00 (fuel + 601) acc) :=
      congrArg (fun result => result.bind (chunk0055AfterValue00 (fuel + 601) acc))
        (value_fragment0230050 (fuel + 162) (chunk0055SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 601) (SourceJson.white tail) (chunk0055Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0055_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0048Chars00 ++ chunk0049Chars00 ++ chunk0050Chars00 ++ chunk0051Chars00 ++ chunk0052Chars00 ++ chunk0053Chars00 ++ chunk0054Chars00 ++ chunk0055Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0055Push00 (chunk0054Push00 (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 609) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 601) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0048Chars00 ++ (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 609) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 609) (SourceJson.white (chunk0048Chars00 ++ (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 609) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 608) (SourceJson.white (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))))))) (chunk0048Push00 (acc)) := array_chunk0048 fuel (chunk0049Chars00 ++ (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 607) (SourceJson.white (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))))) (chunk0049Push00 (chunk0048Push00 (acc))) := array_chunk0049 fuel (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))))) (chunk0048Push00 (acc))
    _ = SourceJson.array (fuel + 606) (SourceJson.white (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))))) (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))) := array_chunk0050 fuel (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))) (chunk0049Push00 (chunk0048Push00 (acc)))
    _ = SourceJson.array (fuel + 605) (SourceJson.white (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))) (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))) := array_chunk0051 fuel (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))) (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))
    _ = SourceJson.array (fuel + 604) (SourceJson.white (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))) (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))) := array_chunk0052 fuel (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))) (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))
    _ = SourceJson.array (fuel + 603) (SourceJson.white (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))) (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))))) := array_chunk0053 fuel (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))) (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))))
    _ = SourceJson.array (fuel + 602) (SourceJson.white (chunk0055Chars00 ++ (tail))) (chunk0054Push00 (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))))) := array_chunk0054 fuel (chunk0055Chars00 ++ (tail)) (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc)))))))
    _ = SourceJson.array (fuel + 601) (SourceJson.white tail) (blockPush acc) := array_chunk0055 fuel (tail) (chunk0054Push00 (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (chunk0049Push00 (chunk0048Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 216580).take 15468 = blockChars := by rfl

theorem block_original_split : sourceRest 216580 = blockChars ++ sourceRest 232048 := by
  calc
    sourceRest 216580 = (sourceRest 216580).take 15468 ++ (sourceRest 216580).drop 15468 :=
      (List.take_append_drop 15468 (sourceRest 216580)).symm
    _ = blockChars ++ (sourceRest 216580).drop 15468 :=
      congrArg (fun part => part ++ (sourceRest 216580).drop 15468) block_original_prefix
    _ = blockChars ++ sourceRest 232048 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 216580 15468)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 609) (SourceJson.white (sourceRest 216580)) acc =
      SourceJson.array (fuel + 601) (SourceJson.white (sourceRest 232048)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 609) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 232048) acc)

#print axioms object_fragment0216586_field_000
#print axioms object_fragment0216586_field_001
#print axioms object_fragment0216586_field_002
#print axioms object_fragment0216586_field_003
#print axioms object_fragment0216586_field_004
#print axioms object_fragment0216586_field_005
#print axioms object_fragment0216586_field_006
#print axioms object_fragment0216586_field_007
#print axioms object_fragment0216586_field_008
#print axioms object_fragment0216586_field_009
#print axioms value_fragment0216586
#print axioms object_fragment0218704_field_000
#print axioms object_fragment0218704_field_001
#print axioms object_fragment0218704_field_002
#print axioms object_fragment0218704_field_003
#print axioms object_fragment0218704_field_004
#print axioms object_fragment0218704_field_005
#print axioms object_fragment0218704_field_006
#print axioms object_fragment0218704_field_007
#print axioms object_fragment0218704_field_008
#print axioms object_fragment0218704_field_009
#print axioms value_fragment0218704
#print axioms object_fragment0220688_field_000
#print axioms object_fragment0220688_field_001
#print axioms object_fragment0220688_field_002
#print axioms object_fragment0220688_field_003
#print axioms object_fragment0220688_field_004
#print axioms object_fragment0220688_field_005
#print axioms object_fragment0220688_field_006
#print axioms object_fragment0220688_field_007
#print axioms object_fragment0220688_field_008
#print axioms object_fragment0220688_field_009
#print axioms value_fragment0220688
#print axioms object_fragment0222362_field_000
#print axioms object_fragment0222362_field_001
#print axioms object_fragment0222362_field_002
#print axioms object_fragment0222362_field_003
#print axioms object_fragment0222362_field_004
#print axioms object_fragment0222362_field_005
#print axioms object_fragment0222362_field_006
#print axioms object_fragment0222362_field_007
#print axioms object_fragment0222362_field_008
#print axioms object_fragment0222362_field_009
#print axioms value_fragment0222362
#print axioms object_fragment0224508_field_000
#print axioms object_fragment0224508_field_001
#print axioms object_fragment0224508_field_002
#print axioms object_fragment0224508_field_003
#print axioms object_fragment0224508_field_004
#print axioms object_fragment0224508_field_005
#print axioms object_fragment0224508_field_006
#print axioms object_fragment0224508_field_007
#print axioms object_fragment0224508_field_008
#print axioms object_fragment0224508_field_009
#print axioms value_fragment0224508
#print axioms object_fragment0226556_field_000
#print axioms object_fragment0226556_field_001
#print axioms object_fragment0226556_field_002
#print axioms object_fragment0226556_field_003
#print axioms object_fragment0226556_field_004
#print axioms object_fragment0226556_field_005
#print axioms object_fragment0226556_field_006
#print axioms object_fragment0226556_field_007
#print axioms object_fragment0226556_field_008
#print axioms object_fragment0226556_field_009
#print axioms value_fragment0226556
#print axioms object_fragment0228459_field_000
#print axioms object_fragment0228459_field_001
#print axioms object_fragment0228459_field_002
#print axioms object_fragment0228459_field_003
#print axioms object_fragment0228459_field_004
#print axioms object_fragment0228459_field_005
#print axioms object_fragment0228459_field_006
#print axioms object_fragment0228459_field_007
#print axioms object_fragment0228459_field_008
#print axioms object_fragment0228459_field_009
#print axioms value_fragment0228459
#print axioms object_fragment0230050_field_000
#print axioms object_fragment0230050_field_001
#print axioms object_fragment0230050_field_002
#print axioms object_fragment0230050_field_003
#print axioms object_fragment0230050_field_004
#print axioms object_fragment0230050_field_005
#print axioms object_fragment0230050_field_006
#print axioms object_fragment0230050_field_007
#print axioms object_fragment0230050_field_008
#print axioms object_fragment0230050_field_009
#print axioms value_fragment0230050
#print axioms array_chunk0048_head
#print axioms array_chunk0048
#print axioms array_chunk0049_head
#print axioms array_chunk0049
#print axioms array_chunk0050_head
#print axioms array_chunk0050
#print axioms array_chunk0051_head
#print axioms array_chunk0051
#print axioms array_chunk0052_head
#print axioms array_chunk0052
#print axioms array_chunk0053_head
#print axioms array_chunk0053
#print axioms array_chunk0054_head
#print axioms array_chunk0054
#print axioms array_chunk0055_head
#print axioms array_chunk0055
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock006

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
