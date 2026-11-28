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

namespace SimplicesBlock013

noncomputable def fragment0320757Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0320757Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0320757Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '4'])
noncomputable def fragment0320757Acc00100 : List (String × SourceJson) := (fragment0320757Field000Key00, fragment0320757Field000Value00) :: fragment0320757Acc00000
noncomputable def fragment0320757Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '4', ',']

theorem object_fragment0320757_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0320757Field000Chars00 ++ tail)) fragment0320757Acc00000 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0320757Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_000"
  err.flush

noncomputable def fragment0320757Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0320757Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0320757Acc00200 : List (String × SourceJson) := (fragment0320757Field001Key00, fragment0320757Field001Value00) :: fragment0320757Acc00100
noncomputable def fragment0320757Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0320757_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0320757Field001Chars00 ++ tail)) fragment0320757Acc00100 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0320757Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_001"
  err.flush

noncomputable def fragment0320757Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0320757Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '5', '4', '3', '4', '7', '9', '5', '2', '1', '7', '3', '4', '3', '4', '5', '6', '4', '0', '6', '6', '8', '0', '8', '0', '5', '5', '8', '1', '0', '8', '7', '4', '5', '7', '9', '7', '0', '0', '3', '/', '3', '6', '4', '2', '8', '4', '9', '7', '2', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0320757Acc00300 : List (String × SourceJson) := (fragment0320757Field002Key00, fragment0320757Field002Value00) :: fragment0320757Acc00200
noncomputable def fragment0320757Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '5', '4', '3', '4', '7', '9', '5', '2', '1', '7', '3', '4', '3', '4', '5', '6', '4', '0', '6', '6', '8', '0', '8', '0', '5', '5', '8', '1', '0', '8', '7', '4', '5', '7', '9', '7', '0', '0', '3', '/', '3', '6', '4', '2', '8', '4', '9', '7', '2', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0320757_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0320757Field002Chars00 ++ tail)) fragment0320757Acc00200 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0320757Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_002"
  err.flush

noncomputable def fragment0320757Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0320757Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0320757Acc00400 : List (String × SourceJson) := (fragment0320757Field003Key00, fragment0320757Field003Value00) :: fragment0320757Acc00300
noncomputable def fragment0320757Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0320757_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0320757Field003Chars00 ++ tail)) fragment0320757Acc00300 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0320757Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_003"
  err.flush

noncomputable def fragment0320757Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0320757Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0320757Acc00500 : List (String × SourceJson) := (fragment0320757Field004Key00, fragment0320757Field004Value00) :: fragment0320757Acc00400
noncomputable def fragment0320757Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '0', '6', '1', '/', '1', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0320757_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0320757Field004Chars00 ++ tail)) fragment0320757Acc00400 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0320757Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_004"
  err.flush

noncomputable def fragment0320757Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0320757Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '1', '4', '1', '5', '0', '9', '3', '9', '6', '3', '/', '9', '6', '7', '7', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '0', '7', '7', '3', '0', '6', '4', '0', '9', '1', '/', '3', '8', '7', '0', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '4', '1', '3', '3', '1', '7', '3', '/', '2', '5', '2', '4', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '0', '8', '7', '5', '1', '9', '9', '7', '0', '3', '/', '1', '1', '6', '1', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '6', '0', '2', '6', '6', '6', '8', '8', '6', '3', '/', '1', '1', '6', '1', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '6', '6', '0', '9', '4', '5', '3', '5', '0', '7', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '1', '5', '5', '7', '6', '2', '4', '9', '7', '7', '/', '1', '4', '7', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '8', '4', '6', '6', '1', '5', '8', '1', '1', '7', '/', '1', '4', '7', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '0', '4', '3', '3', '6', '1', '5', '2', '7', '7', '/', '1', '4', '7', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '8', '8', '3', '6', '7', '5', '0', '9', '3', '1', '/', '1', '1', '6', '1', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0320757Acc00600 : List (String × SourceJson) := (fragment0320757Field005Key00, fragment0320757Field005Value00) :: fragment0320757Acc00500
noncomputable def fragment0320757Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '4', '1', '5', '0', '9', '3', '9', '6', '3', '/', '9', '6', '7', '7', '2', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '0', '7', '7', '3', '0', '6', '4', '0', '9', '1', '/', '3', '8', '7', '0', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '4', '1', '3', '3', '1', '7', '3', '/', '2', '5', '2', '4', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '9', '0', '8', '7', '5', '1', '9', '9', '7', '0', '3', '/', '1', '1', '6', '1', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '6', '0', '2', '6', '6', '6', '8', '8', '6', '3', '/', '1', '1', '6', '1', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '6', '6', '0', '9', '4', '5', '3', '5', '0', '7', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '1', '5', '5', '7', '6', '2', '4', '9', '7', '7', '/', '1', '4', '7', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '8', '4', '6', '6', '1', '5', '8', '1', '1', '7', '/', '1', '4', '7', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '0', '0', '4', '3', '3', '6', '1', '5', '2', '7', '7', '/', '1', '4', '7', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '8', '8', '3', '6', '7', '5', '0', '9', '3', '1', '/', '1', '1', '6', '1', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0320757_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0320757Field005Chars00 ++ tail)) fragment0320757Acc00500 =
      SourceJson.object (fuel + 219) (SourceJson.white tail) fragment0320757Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_005"
  err.flush

noncomputable def fragment0320757Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0320757Field006Value00 : SourceJson := .str (String.ofList ['9', '8', '0', '4', '7', '7', '6', '1', '7', '7', '5', '8', '1', '2', '6', '3', '6', '5', '7', '6', '4', '4', '5', '1', '8', '8', '2', '2', '8', '8', '8', '7', '6', '2', '9', '3', '2', '8', '1', '3', '9', '0', '2', '3', '3', '6', '0', '0', '0', '/', '1', '6', '3', '9', '6', '2', '1', '8', '5', '0', '6', '2', '8', '5', '4', '6', '0', '2', '7', '0', '7', '3', '9', '3', '0', '0', '8', '2', '1', '8', '7', '9', '8', '9', '2', '4', '6', '0', '3', '1', '4', '1', '1', '0', '2', '0', '8', '8', '9', '7', '4', '9', '2', '1', '8', '0', '8', '3', '5', '1', '0', '9'])
noncomputable def fragment0320757Acc00700 : List (String × SourceJson) := (fragment0320757Field006Key00, fragment0320757Field006Value00) :: fragment0320757Acc00600
noncomputable def fragment0320757Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '8', '0', '4', '7', '7', '6', '1', '7', '7', '5', '8', '1', '2', '6', '3', '6', '5', '7', '6', '4', '4', '5', '1', '8', '8', '2', '2', '8', '8', '8', '7', '6', '2', '9', '3', '2', '8', '1', '3', '9', '0', '2', '3', '3', '6', '0', '0', '0', '/', '1', '6', '3', '9', '6', '2', '1', '8', '5', '0', '6', '2', '8', '5', '4', '6', '0', '2', '7', '0', '7', '3', '9', '3', '0', '0', '8', '2', '1', '8', '7', '9', '8', '9', '2', '4', '6', '0', '3', '1', '4', '1', '1', '0', '2', '0', '8', '8', '9', '7', '4', '9', '2', '1', '8', '0', '8', '3', '5', '1', '0', '9', '"', ',']

theorem object_fragment0320757_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 219) (SourceJson.white (fragment0320757Field006Chars00 ++ tail)) fragment0320757Acc00600 =
      SourceJson.object (fuel + 218) (SourceJson.white tail) fragment0320757Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_006"
  err.flush

noncomputable def fragment0320757Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0320757Field007Value00 : SourceJson := .str (String.ofList ['7', '1', '3', '4', '8', '4', '3', '0', '5', '5', '5', '0', '6', '4', '6', '4', '9', '5', '5', '1', '0', '1', '4', '2', '6', '2', '4', '9', '7', '7', '2', '4', '2', '7', '0', '4', '3', '1', '9', '4', '1', '5', '0', '0', '8', '5', '8', '5', '1', '2', '2', '1', '9', '2', '9', '8', '6', '5', '4', '0', '6', '3', '0', '8', '6', '3', '1', '6', '3', '3', '6', '4', '4', '8', '5', '9', '7', '7', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '1', '4', '6', '4', '4', '5', '3', '4', '5', '0', '0', '5', '2', '8', '2', '6', '4', '5', '7', '4', '7', '4', '0', '5', '3', '7', '6', '0', '9', '2', '3', '7', '4', '2', '4', '8', '7', '9', '0', '5', '9', '6', '1', '4', '3', '1', '5', '7', '2', '2', '3', '8', '0', '5', '4', '3', '1', '2', '0', '4', '9', '3', '3', '8', '0', '8', '2', '6', '6', '9', '1', '1', '6', '4', '5', '3', '3', '3', '2', '3', '3', '1', '6', '9', '3', '7', '8', '9', '2', '2', '9', '7', '1', '8', '5', '2', '3', '0', '6', '0', '9', '6', '8', '7', '0', '7', '4', '4', '6', '8', '3'])
noncomputable def fragment0320757Acc00800 : List (String × SourceJson) := (fragment0320757Field007Key00, fragment0320757Field007Value00) :: fragment0320757Acc00700
noncomputable def fragment0320757Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '1', '3', '4', '8', '4', '3', '0', '5', '5', '5', '0', '6', '4', '6', '4', '9', '5', '5', '1', '0', '1', '4', '2', '6', '2', '4', '9', '7', '7', '2', '4', '2', '7', '0', '4', '3', '1', '9', '4', '1', '5', '0', '0', '8', '5', '8', '5', '1', '2', '2', '1', '9', '2', '9', '8', '6', '5', '4', '0', '6', '3', '0', '8', '6', '3', '1', '6', '3', '3', '6', '4', '4', '8', '5', '9', '7', '7', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '1', '4', '6', '4', '4', '5', '3', '4', '5', '0', '0', '5', '2', '8', '2', '6', '4', '5', '7', '4', '7', '4', '0', '5', '3', '7', '6', '0', '9', '2', '3', '7', '4', '2', '4', '8', '7', '9', '0', '5', '9', '6', '1', '4', '3', '1', '5', '7', '2', '2', '3', '8', '0', '5', '4', '3', '1', '2', '0', '4', '9', '3', '3', '8', '0', '8', '2', '6', '6', '9', '1', '1', '6', '4', '5', '3', '3', '3', '2', '3', '3', '1', '6', '9', '3', '7', '8', '9', '2', '2', '9', '7', '1', '8', '5', '2', '3', '0', '6', '0', '9', '6', '8', '7', '0', '7', '4', '4', '6', '8', '3', '"', ',']

theorem object_fragment0320757_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0320757Field007Chars00 ++ tail)) fragment0320757Acc00700 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0320757Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_007"
  err.flush

noncomputable def fragment0320757Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0320757Field008Value00 : SourceJson := .str (String.ofList ['4', '7', '3', '7', '7', '6', '5', '6', '0', '1', '9', '6', '2', '4', '6', '1', '5'])
noncomputable def fragment0320757Acc00900 : List (String × SourceJson) := (fragment0320757Field008Key00, fragment0320757Field008Value00) :: fragment0320757Acc00800
noncomputable def fragment0320757Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '7', '3', '7', '7', '6', '5', '6', '0', '1', '9', '6', '2', '4', '6', '1', '5', '"', ',']

theorem object_fragment0320757_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0320757Field008Chars00 ++ tail)) fragment0320757Acc00800 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0320757Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_008"
  err.flush

noncomputable def fragment0320757Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0320757Field009Value00 : SourceJson := .str (String.ofList ['1', '7', '0', '5', '4', '0', '3', '0', '9', '5', '9', '6', '3', '0', '9', '8', '7', '9'])
noncomputable def fragment0320757Acc01000 : List (String × SourceJson) := (fragment0320757Field009Key00, fragment0320757Field009Value00) :: fragment0320757Acc00900
noncomputable def fragment0320757Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '7', '0', '5', '4', '0', '3', '0', '9', '5', '9', '6', '3', '0', '9', '8', '7', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0320757_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0320757Field009Chars00 ++ tail)) fragment0320757Acc00900 =
      .ok (.obj (fragment0320757Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0320757_object_field_009"
  err.flush

noncomputable def fragment0320757Chars : List Char := '{' :: (fragment0320757Field000Chars00 ++ fragment0320757Field001Chars00 ++ fragment0320757Field002Chars00 ++ fragment0320757Field003Chars00 ++ fragment0320757Field004Chars00 ++ fragment0320757Field005Chars00 ++ fragment0320757Field006Chars00 ++ fragment0320757Field007Chars00 ++ fragment0320757Field008Chars00 ++ fragment0320757Field009Chars00)
noncomputable def fragment0320757Value : SourceJson := .obj (fragment0320757Acc01000.reverse)

theorem value_fragment0320757 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 226) (fragment0320757Chars ++ tail) =
      .ok (fragment0320757Value, tail) := by
  have hinput : fragment0320757Chars ++ tail = '{' :: (fragment0320757Field000Chars00 ++ (fragment0320757Field001Chars00 ++ (fragment0320757Field002Chars00 ++ (fragment0320757Field003Chars00 ++ (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0320757Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 226) (fragment0320757Chars ++ tail) =
        SourceJson.value (fuel + 226) ('{' :: (fragment0320757Field000Chars00 ++ (fragment0320757Field001Chars00 ++ (fragment0320757Field002Chars00 ++ (fragment0320757Field003Chars00 ++ (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 226)) hinput
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0320757Field000Chars00 ++ (fragment0320757Field001Chars00 ++ (fragment0320757Field002Chars00 ++ (fragment0320757Field003Chars00 ++ (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))))))))))) fragment0320757Acc00000 := by rfl
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0320757Field001Chars00 ++ (fragment0320757Field002Chars00 ++ (fragment0320757Field003Chars00 ++ (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail))))))))))) fragment0320757Acc00100 := object_fragment0320757_field_000 fuel (fragment0320757Field001Chars00 ++ (fragment0320757Field002Chars00 ++ (fragment0320757Field003Chars00 ++ (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0320757Field002Chars00 ++ (fragment0320757Field003Chars00 ++ (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))))))))) fragment0320757Acc00200 := object_fragment0320757_field_001 fuel (fragment0320757Field002Chars00 ++ (fragment0320757Field003Chars00 ++ (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0320757Field003Chars00 ++ (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail))))))))) fragment0320757Acc00300 := object_fragment0320757_field_002 fuel (fragment0320757Field003Chars00 ++ (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))))))) fragment0320757Acc00400 := object_fragment0320757_field_003 fuel (fragment0320757Field004Chars00 ++ (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail))))))) fragment0320757Acc00500 := object_fragment0320757_field_004 fuel (fragment0320757Field005Chars00 ++ (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 219) (SourceJson.white (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))))) fragment0320757Acc00600 := object_fragment0320757_field_005 fuel (fragment0320757Field006Chars00 ++ (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail))))) fragment0320757Acc00700 := object_fragment0320757_field_006 fuel (fragment0320757Field007Chars00 ++ (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))) fragment0320757Acc00800 := object_fragment0320757_field_007 fuel (fragment0320757Field008Chars00 ++ (fragment0320757Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0320757Field009Chars00 ++ (tail))) fragment0320757Acc00900 := object_fragment0320757_field_008 fuel (fragment0320757Field009Chars00 ++ (tail))
    _ = .ok (fragment0320757Value, tail) := object_fragment0320757_field_009 fuel (tail)

noncomputable def fragment0322342Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0322342Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0322342Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '5'])
noncomputable def fragment0322342Acc00100 : List (String × SourceJson) := (fragment0322342Field000Key00, fragment0322342Field000Value00) :: fragment0322342Acc00000
noncomputable def fragment0322342Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '5', ',']

theorem object_fragment0322342_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0322342Field000Chars00 ++ tail)) fragment0322342Acc00000 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0322342Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_000"
  err.flush

noncomputable def fragment0322342Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0322342Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0322342Acc00200 : List (String × SourceJson) := (fragment0322342Field001Key00, fragment0322342Field001Value00) :: fragment0322342Acc00100
noncomputable def fragment0322342Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0322342_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0322342Field001Chars00 ++ tail)) fragment0322342Acc00100 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0322342Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_001"
  err.flush

noncomputable def fragment0322342Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0322342Field002Value00 : SourceJson := .str (String.ofList ['7', '3', '9', '9', '4', '4', '9', '3', '7', '8', '9', '6', '0', '5', '2', '8', '9', '4', '7', '2', '8', '7', '3', '0', '4', '7', '8', '9', '5', '2', '7', '2', '8', '7', '0', '1', '0', '9', '1', '/', '1', '6', '9', '6', '9', '7', '9', '6', '8', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0322342Acc00300 : List (String × SourceJson) := (fragment0322342Field002Key00, fragment0322342Field002Value00) :: fragment0322342Acc00200
noncomputable def fragment0322342Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '3', '9', '9', '4', '4', '9', '3', '7', '8', '9', '6', '0', '5', '2', '8', '9', '4', '7', '2', '8', '7', '3', '0', '4', '7', '8', '9', '5', '2', '7', '2', '8', '7', '0', '1', '0', '9', '1', '/', '1', '6', '9', '6', '9', '7', '9', '6', '8', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0322342_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0322342Field002Chars00 ++ tail)) fragment0322342Acc00200 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0322342Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_002"
  err.flush

noncomputable def fragment0322342Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0322342Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0322342Acc00400 : List (String × SourceJson) := (fragment0322342Field003Key00, fragment0322342Field003Value00) :: fragment0322342Acc00300
noncomputable def fragment0322342Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0322342_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0322342Field003Chars00 ++ tail)) fragment0322342Acc00300 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0322342Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_003"
  err.flush

noncomputable def fragment0322342Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0322342Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '7', '1', '7', '0', '7', '/', '1', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0322342Acc00500 : List (String × SourceJson) := (fragment0322342Field004Key00, fragment0322342Field004Value00) :: fragment0322342Acc00400
noncomputable def fragment0322342Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '8', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '7', '1', '7', '0', '7', '/', '1', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '6', '7', '1', '6', '0', '7', '/', '2', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '2', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0322342_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0322342Field004Chars00 ++ tail)) fragment0322342Acc00400 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0322342Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_004"
  err.flush

noncomputable def fragment0322342Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0322342Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '4', '4', '4', '9', '4', '7', '1', '4', '6', '0', '5', '1', '/', '5', '4', '1', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '1', '6', '5', '2', '4', '7', '8', '1', '3', '9', '7', '/', '5', '4', '1', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '2', '8', '0', '1', '5', '3', '2', '5', '2', '8', '7', '/', '4', '0', '6', '4', '4', '4', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '6', '0', '6', '2', '2', '6', '7', '3', '8', '1', '/', '2', '3', '2', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '8', '6', '3', '6', '5', '2', '0', '5', '7', '0', '1', '/', '2', '3', '2', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '1', '6', '3', '0', '6', '6', '9', '6', '7', '/', '1', '8', '4', '7', '4', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '8', '0', '0', '2', '1', '9', '6', '6', '9', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '3', '2', '5', '4', '4', '8', '6', '2', '3', '9', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '2', '3', '8', '2', '1', '4', '8', '1', '9', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '2', '9', '4', '1', '6', '3', '9', '7', '1', '5', '7', '/', '1', '6', '2', '5', '7', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0322342Acc00600 : List (String × SourceJson) := (fragment0322342Field005Key00, fragment0322342Field005Value00) :: fragment0322342Acc00500
noncomputable def fragment0322342Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '4', '4', '9', '4', '7', '1', '4', '6', '0', '5', '1', '/', '5', '4', '1', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '1', '6', '5', '2', '4', '7', '8', '1', '3', '9', '7', '/', '5', '4', '1', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '2', '8', '0', '1', '5', '3', '2', '5', '2', '8', '7', '/', '4', '0', '6', '4', '4', '4', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '6', '0', '6', '2', '2', '6', '7', '3', '8', '1', '/', '2', '3', '2', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '6', '3', '6', '5', '2', '0', '5', '7', '0', '1', '/', '2', '3', '2', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '1', '6', '3', '0', '6', '6', '9', '6', '7', '/', '1', '8', '4', '7', '4', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '8', '0', '0', '2', '1', '9', '6', '6', '9', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '2', '5', '4', '4', '8', '6', '2', '3', '9', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '2', '3', '8', '2', '1', '4', '8', '1', '9', '/', '7', '3', '8', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '2', '9', '4', '1', '6', '3', '9', '7', '1', '5', '7', '/', '1', '6', '2', '5', '7', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0322342_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0322342Field005Chars00 ++ tail)) fragment0322342Acc00500 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0322342Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_005"
  err.flush

noncomputable def fragment0322342Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0322342Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '6', '4', '5', '3', '8', '9', '0', '9', '5', '2', '1', '3', '7', '3', '8', '8', '5', '5', '2', '9', '1', '6', '1', '6', '3', '8', '0', '8', '1', '7', '0', '4', '2', '9', '8', '0', '4', '0', '1', '3', '8', '2', '6', '8', '6', '7', '2', '0', '0', '0', '/', '2', '0', '0', '7', '8', '8', '8', '0', '5', '9', '3', '2', '1', '8', '3', '3', '3', '9', '7', '4', '9', '0', '9', '6', '7', '8', '1', '7', '7', '0', '7', '1', '4', '0', '8', '2', '1', '1', '1', '3', '0', '9', '7', '6', '8', '7', '2', '8', '6', '8', '1', '1', '2', '0', '8', '6', '8', '6', '9', '9', '8', '3', '2', '1'])
noncomputable def fragment0322342Acc00700 : List (String × SourceJson) := (fragment0322342Field006Key00, fragment0322342Field006Value00) :: fragment0322342Acc00600
noncomputable def fragment0322342Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '6', '4', '5', '3', '8', '9', '0', '9', '5', '2', '1', '3', '7', '3', '8', '8', '5', '5', '2', '9', '1', '6', '1', '6', '3', '8', '0', '8', '1', '7', '0', '4', '2', '9', '8', '0', '4', '0', '1', '3', '8', '2', '6', '8', '6', '7', '2', '0', '0', '0', '/', '2', '0', '0', '7', '8', '8', '8', '0', '5', '9', '3', '2', '1', '8', '3', '3', '3', '9', '7', '4', '9', '0', '9', '6', '7', '8', '1', '7', '7', '0', '7', '1', '4', '0', '8', '2', '1', '1', '1', '3', '0', '9', '7', '6', '8', '7', '2', '8', '6', '8', '1', '1', '2', '0', '8', '6', '8', '6', '9', '9', '8', '3', '2', '1', '"', ',']

theorem object_fragment0322342_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0322342Field006Chars00 ++ tail)) fragment0322342Acc00600 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0322342Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_006"
  err.flush

noncomputable def fragment0322342Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0322342Field007Value00 : SourceJson := .str (String.ofList ['9', '0', '8', '0', '6', '7', '3', '2', '4', '5', '1', '6', '9', '2', '9', '6', '3', '1', '1', '3', '5', '5', '6', '8', '4', '7', '1', '1', '0', '7', '3', '5', '1', '3', '5', '7', '6', '5', '9', '5', '5', '0', '7', '0', '4', '1', '2', '4', '9', '8', '6', '1', '4', '1', '6', '5', '5', '1', '4', '3', '5', '4', '0', '9', '9', '8', '7', '5', '7', '1', '8', '4', '1', '8', '3', '1', '2', '4', '6', '9', '9', '3', '4', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '4', '2', '2', '6', '5', '3', '9', '4', '3', '4', '8', '0', '2', '4', '3', '8', '2', '3', '8', '7', '8', '0', '8', '4', '4', '3', '5', '0', '9', '7', '1', '6', '2', '1', '2', '7', '8', '0', '8', '3', '9', '4', '2', '7', '5', '2', '2', '4', '9', '9', '9', '4', '5', '4', '4', '8', '4', '4', '1', '5', '3', '2', '0', '2', '9', '7', '2', '6', '5', '9', '5', '2', '0', '5', '1', '2', '4', '8', '6', '6', '2', '7', '1', '4', '7', '6', '4', '9', '5', '0', '9', '8', '6', '9', '8', '7', '0', '2', '3', '1', '0', '9', '5', '1', '5', '3', '0', '0', '4', '0', '1', '5', '5', '4', '7', '5', '7', '6', '9'])
noncomputable def fragment0322342Acc00800 : List (String × SourceJson) := (fragment0322342Field007Key00, fragment0322342Field007Value00) :: fragment0322342Acc00700
noncomputable def fragment0322342Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '0', '8', '0', '6', '7', '3', '2', '4', '5', '1', '6', '9', '2', '9', '6', '3', '1', '1', '3', '5', '5', '6', '8', '4', '7', '1', '1', '0', '7', '3', '5', '1', '3', '5', '7', '6', '5', '9', '5', '5', '0', '7', '0', '4', '1', '2', '4', '9', '8', '6', '1', '4', '1', '6', '5', '5', '1', '4', '3', '5', '4', '0', '9', '9', '8', '7', '5', '7', '1', '8', '4', '1', '8', '3', '1', '2', '4', '6', '9', '9', '3', '4', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '4', '2', '2', '6', '5', '3', '9', '4', '3', '4', '8', '0', '2', '4', '3', '8', '2', '3', '8', '7', '8', '0', '8', '4', '4', '3', '5', '0', '9', '7', '1', '6', '2', '1', '2', '7', '8', '0', '8', '3', '9', '4', '2', '7', '5', '2', '2', '4', '9', '9', '9', '4', '5', '4', '4', '8', '4', '4', '1', '5', '3', '2', '0', '2', '9', '7', '2', '6', '5', '9', '5', '2', '0', '5', '1', '2', '4', '8', '6', '6', '2', '7', '1', '4', '7', '6', '4', '9', '5', '0', '9', '8', '6', '9', '8', '7', '0', '2', '3', '1', '0', '9', '5', '1', '5', '3', '0', '0', '4', '0', '1', '5', '5', '4', '7', '5', '7', '6', '9', '"', ',']

theorem object_fragment0322342_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0322342Field007Chars00 ++ tail)) fragment0322342Acc00700 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0322342Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_007"
  err.flush

noncomputable def fragment0322342Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0322342Field008Value00 : SourceJson := .str (String.ofList ['4', '5', '9', '5', '0', '9', '0', '7', '2', '4', '7', '7', '4', '0', '6', '7', '0'])
noncomputable def fragment0322342Acc00900 : List (String × SourceJson) := (fragment0322342Field008Key00, fragment0322342Field008Value00) :: fragment0322342Acc00800
noncomputable def fragment0322342Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '9', '5', '0', '9', '0', '7', '2', '4', '7', '7', '4', '0', '6', '7', '0', '"', ',']

theorem object_fragment0322342_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0322342Field008Chars00 ++ tail)) fragment0322342Acc00800 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0322342Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_008"
  err.flush

noncomputable def fragment0322342Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0322342Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '2', '6', '7', '2', '6', '9', '9', '4', '2', '4', '6', '9', '5', '3', '1', '7'])
noncomputable def fragment0322342Acc01000 : List (String × SourceJson) := (fragment0322342Field009Key00, fragment0322342Field009Value00) :: fragment0322342Acc00900
noncomputable def fragment0322342Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '2', '6', '7', '2', '6', '9', '9', '4', '2', '4', '6', '9', '5', '3', '1', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0322342_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0322342Field009Chars00 ++ tail)) fragment0322342Acc00900 =
      .ok (.obj (fragment0322342Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0322342_object_field_009"
  err.flush

noncomputable def fragment0322342Chars : List Char := '{' :: (fragment0322342Field000Chars00 ++ fragment0322342Field001Chars00 ++ fragment0322342Field002Chars00 ++ fragment0322342Field003Chars00 ++ fragment0322342Field004Chars00 ++ fragment0322342Field005Chars00 ++ fragment0322342Field006Chars00 ++ fragment0322342Field007Chars00 ++ fragment0322342Field008Chars00 ++ fragment0322342Field009Chars00)
noncomputable def fragment0322342Value : SourceJson := .obj (fragment0322342Acc01000.reverse)

theorem value_fragment0322342 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 240) (fragment0322342Chars ++ tail) =
      .ok (fragment0322342Value, tail) := by
  have hinput : fragment0322342Chars ++ tail = '{' :: (fragment0322342Field000Chars00 ++ (fragment0322342Field001Chars00 ++ (fragment0322342Field002Chars00 ++ (fragment0322342Field003Chars00 ++ (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0322342Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 240) (fragment0322342Chars ++ tail) =
        SourceJson.value (fuel + 240) ('{' :: (fragment0322342Field000Chars00 ++ (fragment0322342Field001Chars00 ++ (fragment0322342Field002Chars00 ++ (fragment0322342Field003Chars00 ++ (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 240)) hinput
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0322342Field000Chars00 ++ (fragment0322342Field001Chars00 ++ (fragment0322342Field002Chars00 ++ (fragment0322342Field003Chars00 ++ (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))))))))))) fragment0322342Acc00000 := by rfl
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0322342Field001Chars00 ++ (fragment0322342Field002Chars00 ++ (fragment0322342Field003Chars00 ++ (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail))))))))))) fragment0322342Acc00100 := object_fragment0322342_field_000 fuel (fragment0322342Field001Chars00 ++ (fragment0322342Field002Chars00 ++ (fragment0322342Field003Chars00 ++ (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0322342Field002Chars00 ++ (fragment0322342Field003Chars00 ++ (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))))))))) fragment0322342Acc00200 := object_fragment0322342_field_001 fuel (fragment0322342Field002Chars00 ++ (fragment0322342Field003Chars00 ++ (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0322342Field003Chars00 ++ (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail))))))))) fragment0322342Acc00300 := object_fragment0322342_field_002 fuel (fragment0322342Field003Chars00 ++ (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))))))) fragment0322342Acc00400 := object_fragment0322342_field_003 fuel (fragment0322342Field004Chars00 ++ (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail))))))) fragment0322342Acc00500 := object_fragment0322342_field_004 fuel (fragment0322342Field005Chars00 ++ (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))))) fragment0322342Acc00600 := object_fragment0322342_field_005 fuel (fragment0322342Field006Chars00 ++ (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail))))) fragment0322342Acc00700 := object_fragment0322342_field_006 fuel (fragment0322342Field007Chars00 ++ (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))) fragment0322342Acc00800 := object_fragment0322342_field_007 fuel (fragment0322342Field008Chars00 ++ (fragment0322342Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0322342Field009Chars00 ++ (tail))) fragment0322342Acc00900 := object_fragment0322342_field_008 fuel (fragment0322342Field009Chars00 ++ (tail))
    _ = .ok (fragment0322342Value, tail) := object_fragment0322342_field_009 fuel (tail)

noncomputable def fragment0323962Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0323962Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0323962Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '6'])
noncomputable def fragment0323962Acc00100 : List (String × SourceJson) := (fragment0323962Field000Key00, fragment0323962Field000Value00) :: fragment0323962Acc00000
noncomputable def fragment0323962Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '6', ',']

theorem object_fragment0323962_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 372) (SourceJson.white (fragment0323962Field000Chars00 ++ tail)) fragment0323962Acc00000 =
      SourceJson.object (fuel + 371) (SourceJson.white tail) fragment0323962Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_000"
  err.flush

noncomputable def fragment0323962Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0323962Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['9']), .number (String.ofList ['7'])]
noncomputable def fragment0323962Acc00200 : List (String × SourceJson) := (fragment0323962Field001Key00, fragment0323962Field001Value00) :: fragment0323962Acc00100
noncomputable def fragment0323962Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0323962_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 371) (SourceJson.white (fragment0323962Field001Chars00 ++ tail)) fragment0323962Acc00100 =
      SourceJson.object (fuel + 370) (SourceJson.white tail) fragment0323962Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_001"
  err.flush

noncomputable def fragment0323962Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0323962Field002Value00 : SourceJson := .str (String.ofList ['3', '0', '7', '3', '0', '8', '8', '2', '8', '8', '7', '8', '7', '3', '0', '2', '3', '7', '6', '4', '2', '3', '3', '6', '7', '3', '9', '5', '8', '6', '8', '6', '9', '6', '3', '3', '/', '1', '3', '5', '5', '5', '2', '5', '1', '9', '0', '8', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0323962Acc00300 : List (String × SourceJson) := (fragment0323962Field002Key00, fragment0323962Field002Value00) :: fragment0323962Acc00200
noncomputable def fragment0323962Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '0', '7', '3', '0', '8', '8', '2', '8', '8', '7', '8', '7', '3', '0', '2', '3', '7', '6', '4', '2', '3', '3', '6', '7', '3', '9', '5', '8', '6', '8', '6', '9', '6', '3', '3', '/', '1', '3', '5', '5', '5', '2', '5', '1', '9', '0', '8', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0323962_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 370) (SourceJson.white (fragment0323962Field002Chars00 ++ tail)) fragment0323962Acc00200 =
      SourceJson.object (fuel + 369) (SourceJson.white tail) fragment0323962Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_002"
  err.flush

noncomputable def fragment0323962Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0323962Field003Value00 : SourceJson := .str (String.ofList ['3', '3', '4', '4', '9', '0', '8', '1', '/', '2', '4', '5', '5', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0323962Acc00400 : List (String × SourceJson) := (fragment0323962Field003Key00, fragment0323962Field003Value00) :: fragment0323962Acc00300
noncomputable def fragment0323962Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '3', '4', '4', '9', '0', '8', '1', '/', '2', '4', '5', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0323962_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment0323962Field003Chars00 ++ tail)) fragment0323962Acc00300 =
      SourceJson.object (fuel + 368) (SourceJson.white tail) fragment0323962Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_003"
  err.flush

noncomputable def fragment0323962Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0323962Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '0', '1', '5', '6', '2', '9', '/', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '4', '0', '6', '0', '9', '/', '2', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '9', '3', '7', '1', '/', '2', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '9', '3', '7', '1', '/', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0323962Acc00500 : List (String × SourceJson) := (fragment0323962Field004Key00, fragment0323962Field004Value00) :: fragment0323962Acc00400
noncomputable def fragment0323962Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '1', '5', '6', '2', '9', '/', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '4', '0', '6', '0', '9', '/', '2', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '9', '3', '7', '1', '/', '2', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '9', '3', '7', '1', '/', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '4', '3', '7', '9', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '7', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0323962_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0323962Field004Chars00 ++ tail)) fragment0323962Acc00400 =
      SourceJson.object (fuel + 367) (SourceJson.white tail) fragment0323962Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_004"
  err.flush

noncomputable def fragment0323962Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0323962Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '0', '2', '8', '7', '7', '7', '1', '8', '0', '6', '0', '9', '0', '2', '0', '3', '7', '9', '/', '1', '8', '8', '8', '8', '5', '6', '2', '2', '4', '4', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '7', '6', '1', '9', '8', '5', '5', '1', '9', '6', '4', '1', '9', '8', '2', '0', '1', '/', '1', '8', '8', '8', '8', '5', '6', '2', '2', '4', '4', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '2', '0', '8', '0', '8', '2', '1', '8', '2', '4', '2', '2', '9', '4', '6', '1', '9', '1', '/', '1', '6', '5', '2', '7', '4', '9', '1', '9', '6', '3', '8', '2', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '3', '3', '8', '3', '9', '1', '1', '0', '3', '0', '3', '6', '6', '9', '1', '/', '1', '7', '2', '8', '3', '6', '5', '1', '7', '2', '6', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '5', '9', '8', '7', '5', '8', '6', '2', '9', '1', '4', '1', '1', '1', '9', '7', '/', '2', '5', '9', '2', '5', '4', '7', '7', '5', '9', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '6', '3', '4', '1', '0', '6', '0', '7', '1', '8', '5', '0', '7', '3', '1', '4', '2', '9', '/', '6', '6', '1', '0', '9', '9', '6', '7', '8', '5', '5', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '1', '5', '3', '5', '0', '9', '6', '1', '1', '8', '1', '4', '2', '4', '3', '7', '9', '/', '2', '6', '4', '4', '3', '9', '8', '7', '1', '4', '2', '1', '2', '6', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '0', '1', '1', '0', '6', '0', '7', '1', '3', '6', '4', '3', '9', '6', '6', '3', '8', '7', '/', '1', '3', '2', '2', '1', '9', '9', '3', '5', '7', '1', '0', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '2', '1', '0', '6', '0', '0', '0', '1', '4', '1', '0', '1', '4', '4', '3', '0', '7', '/', '1', '8', '8', '8', '8', '5', '6', '2', '2', '4', '4', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '2', '1', '0', '4', '7', '4', '0', '9', '0', '3', '5', '3', '1', '4', '7', '2', '3', '/', '1', '8', '8', '8', '8', '5', '6', '2', '2', '4', '4', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0323962Acc00600 : List (String × SourceJson) := (fragment0323962Field005Key00, fragment0323962Field005Value00) :: fragment0323962Acc00500
noncomputable def fragment0323962Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '2', '8', '7', '7', '7', '1', '8', '0', '6', '0', '9', '0', '2', '0', '3', '7', '9', '/', '1', '8', '8', '8', '8', '5', '6', '2', '2', '4', '4', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '7', '6', '1', '9', '8', '5', '5', '1', '9', '6', '4', '1', '9', '8', '2', '0', '1', '/', '1', '8', '8', '8', '8', '5', '6', '2', '2', '4', '4', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '0', '8', '0', '8', '2', '1', '8', '2', '4', '2', '2', '9', '4', '6', '1', '9', '1', '/', '1', '6', '5', '2', '7', '4', '9', '1', '9', '6', '3', '8', '2', '9', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '3', '3', '8', '3', '9', '1', '1', '0', '3', '0', '3', '6', '6', '9', '1', '/', '1', '7', '2', '8', '3', '6', '5', '1', '7', '2', '6', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '5', '9', '8', '7', '5', '8', '6', '2', '9', '1', '4', '1', '1', '1', '9', '7', '/', '2', '5', '9', '2', '5', '4', '7', '7', '5', '9', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '6', '3', '4', '1', '0', '6', '0', '7', '1', '8', '5', '0', '7', '3', '1', '4', '2', '9', '/', '6', '6', '1', '0', '9', '9', '6', '7', '8', '5', '5', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '1', '5', '3', '5', '0', '9', '6', '1', '1', '8', '1', '4', '2', '4', '3', '7', '9', '/', '2', '6', '4', '4', '3', '9', '8', '7', '1', '4', '2', '1', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '0', '1', '1', '0', '6', '0', '7', '1', '3', '6', '4', '3', '9', '6', '6', '3', '8', '7', '/', '1', '3', '2', '2', '1', '9', '9', '3', '5', '7', '1', '0', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '2', '1', '0', '6', '0', '0', '0', '1', '4', '1', '0', '1', '4', '4', '3', '0', '7', '/', '1', '8', '8', '8', '8', '5', '6', '2', '2', '4', '4', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '2', '1', '0', '4', '7', '4', '0', '9', '0', '3', '5', '3', '1', '4', '7', '2', '3', '/', '1', '8', '8', '8', '8', '5', '6', '2', '2', '4', '4', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0323962_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 367) (SourceJson.white (fragment0323962Field005Chars00 ++ tail)) fragment0323962Acc00500 =
      SourceJson.object (fuel + 366) (SourceJson.white tail) fragment0323962Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_005"
  err.flush

noncomputable def fragment0323962Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0323962Field006Value00 : SourceJson := .str (String.ofList ['3', '4', '0', '5', '4', '3', '7', '8', '0', '1', '4', '4', '1', '2', '0', '9', '3', '9', '9', '9', '1', '4', '1', '7', '9', '0', '7', '0', '4', '6', '0', '6', '3', '2', '7', '8', '0', '7', '1', '6', '5', '7', '4', '2', '0', '8', '0', '0', '0', '0', '/', '3', '7', '9', '8', '4', '1', '3', '5', '7', '8', '6', '9', '2', '6', '6', '3', '8', '9', '1', '6', '0', '4', '7', '6', '4', '9', '5', '5', '8', '2', '2', '4', '3', '0', '4', '0', '0', '5', '6', '2', '1', '8', '9', '9', '4', '8', '2', '7', '5', '9', '2', '5', '9', '5', '2', '3', '9', '3', '1', '6', '8', '7', '6', '6', '0', '9', '3'])
noncomputable def fragment0323962Acc00700 : List (String × SourceJson) := (fragment0323962Field006Key00, fragment0323962Field006Value00) :: fragment0323962Acc00600
noncomputable def fragment0323962Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '0', '5', '4', '3', '7', '8', '0', '1', '4', '4', '1', '2', '0', '9', '3', '9', '9', '9', '1', '4', '1', '7', '9', '0', '7', '0', '4', '6', '0', '6', '3', '2', '7', '8', '0', '7', '1', '6', '5', '7', '4', '2', '0', '8', '0', '0', '0', '0', '/', '3', '7', '9', '8', '4', '1', '3', '5', '7', '8', '6', '9', '2', '6', '6', '3', '8', '9', '1', '6', '0', '4', '7', '6', '4', '9', '5', '5', '8', '2', '2', '4', '3', '0', '4', '0', '0', '5', '6', '2', '1', '8', '9', '9', '4', '8', '2', '7', '5', '9', '2', '5', '9', '5', '2', '3', '9', '3', '1', '6', '8', '7', '6', '6', '0', '9', '3', '"', ',']

theorem object_fragment0323962_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 366) (SourceJson.white (fragment0323962Field006Chars00 ++ tail)) fragment0323962Acc00600 =
      SourceJson.object (fuel + 365) (SourceJson.white tail) fragment0323962Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_006"
  err.flush

noncomputable def fragment0323962Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0323962Field007Value00 : SourceJson := .str (String.ofList ['3', '8', '4', '5', '7', '6', '1', '6', '9', '2', '2', '2', '3', '8', '7', '5', '5', '3', '9', '3', '0', '5', '0', '1', '0', '7', '2', '7', '8', '3', '4', '2', '7', '5', '8', '7', '6', '4', '7', '4', '5', '5', '3', '9', '7', '3', '5', '8', '1', '6', '6', '5', '0', '5', '0', '8', '6', '1', '4', '8', '3', '7', '4', '3', '0', '2', '0', '2', '0', '3', '7', '8', '1', '8', '9', '5', '4', '5', '5', '9', '3', '6', '6', '1', '9', '4', '0', '6', '3', '5', '1', '4', '0', '3', '8', '4', '3', '4', '2', '9', '8', '0', '4', '1', '8', '5', '2', '5', '7', '1', '2', '3', '2', '3', '9', '1', '8', '2', '7', '4', '6', '6', '5', '3', '1', '6', '1', '7', '0', '0', '3', '5', '6', '2', '3', '1', '5', '1', '3', '8', '3', '0', '4', '6', '7', '0', '4', '5', '8', '2', '9', '0', '1', '6', '2', '8', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '7', '1', '6', '3', '1', '9', '5', '6', '6', '2', '3', '7', '3', '5', '6', '7', '6', '4', '2', '4', '0', '5', '2', '0', '9', '4', '6', '4', '8', '0', '8', '8', '4', '1', '1', '7', '3', '2', '3', '0', '5', '6', '4', '0', '2', '8', '4', '0', '4', '4', '5', '9', '1', '0', '1', '9', '3', '2', '6', '5', '8', '5', '4', '0', '7', '4', '2', '2', '4', '1', '9', '8', '1', '9', '8', '6', '0', '1', '3', '0', '1', '9', '1', '8', '5', '2', '4', '7', '1', '8', '3', '2', '5', '0', '6', '1', '3', '4', '4', '0', '2', '1', '0', '9', '1', '9', '8', '9', '1', '4', '2', '0', '8', '4', '0', '6', '1', '8', '0', '6', '4', '0', '8', '8', '9', '4', '3', '5', '9', '2', '3', '1', '0', '9', '9', '1', '6', '0', '0', '2', '1', '4', '2', '8', '7', '3', '5', '7', '7', '8', '6', '1', '2', '5', '9', '9', '8', '8', '0', '6', '2', '7', '1', '7', '4', '1', '1', '0', '2', '0', '9', '1', '4', '6', '8', '6', '8', '6', '4', '5', '2', '8', '1', '0', '8', '7', '3'])
noncomputable def fragment0323962Acc00800 : List (String × SourceJson) := (fragment0323962Field007Key00, fragment0323962Field007Value00) :: fragment0323962Acc00700
noncomputable def fragment0323962Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '8', '4', '5', '7', '6', '1', '6', '9', '2', '2', '2', '3', '8', '7', '5', '5', '3', '9', '3', '0', '5', '0', '1', '0', '7', '2', '7', '8', '3', '4', '2', '7', '5', '8', '7', '6', '4', '7', '4', '5', '5', '3', '9', '7', '3', '5', '8', '1', '6', '6', '5', '0', '5', '0', '8', '6', '1', '4', '8', '3', '7', '4', '3', '0', '2', '0', '2', '0', '3', '7', '8', '1', '8', '9', '5', '4', '5', '5', '9', '3', '6', '6', '1', '9', '4', '0', '6', '3', '5', '1', '4', '0', '3', '8', '4', '3', '4', '2', '9', '8', '0', '4', '1', '8', '5', '2', '5', '7', '1', '2', '3', '2', '3', '9', '1', '8', '2', '7', '4', '6', '6', '5', '3', '1', '6', '1', '7', '0', '0', '3', '5', '6', '2', '3', '1', '5', '1', '3', '8', '3', '0', '4', '6', '7', '0', '4', '5', '8', '2', '9', '0', '1', '6', '2', '8', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '7', '1', '6', '3', '1', '9', '5', '6', '6', '2', '3', '7', '3', '5', '6', '7', '6', '4', '2', '4', '0', '5', '2', '0', '9', '4', '6', '4', '8', '0', '8', '8', '4', '1', '1', '7', '3', '2', '3', '0', '5', '6', '4', '0', '2', '8', '4', '0', '4', '4', '5', '9', '1', '0', '1', '9', '3', '2', '6', '5', '8', '5', '4', '0', '7', '4', '2', '2', '4', '1', '9', '8', '1', '9', '8', '6', '0', '1', '3', '0', '1', '9', '1', '8', '5', '2', '4', '7', '1', '8', '3', '2', '5', '0', '6', '1', '3', '4', '4', '0', '2', '1', '0', '9', '1', '9', '8', '9', '1', '4', '2', '0', '8', '4', '0', '6', '1', '8', '0', '6', '4', '0', '8', '8', '9', '4', '3', '5', '9', '2', '3', '1', '0', '9', '9', '1', '6', '0', '0', '2', '1', '4', '2', '8', '7', '3', '5', '7', '7', '8', '6', '1', '2', '5', '9', '9', '8', '8', '0', '6', '2', '7', '1', '7', '4', '1', '1', '0', '2', '0', '9', '1', '4', '6', '8', '6', '8', '6', '4', '5', '2', '8', '1', '0', '8', '7', '3', '"', ',']

theorem object_fragment0323962_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 365) (SourceJson.white (fragment0323962Field007Chars00 ++ tail)) fragment0323962Acc00700 =
      SourceJson.object (fuel + 364) (SourceJson.white tail) fragment0323962Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_007"
  err.flush

noncomputable def fragment0323962Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0323962Field008Value00 : SourceJson := .str (String.ofList ['7', '1', '0', '3', '1', '3', '8', '5', '5', '9', '6', '9'])
noncomputable def fragment0323962Acc00900 : List (String × SourceJson) := (fragment0323962Field008Key00, fragment0323962Field008Value00) :: fragment0323962Acc00800
noncomputable def fragment0323962Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '1', '0', '3', '1', '3', '8', '5', '5', '9', '6', '9', '"', ',']

theorem object_fragment0323962_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 364) (SourceJson.white (fragment0323962Field008Chars00 ++ tail)) fragment0323962Acc00800 =
      SourceJson.object (fuel + 363) (SourceJson.white tail) fragment0323962Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_008"
  err.flush

noncomputable def fragment0323962Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0323962Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '2', '7', '9', '5', '1', '6', '4', '5', '4', '3', '0'])
noncomputable def fragment0323962Acc01000 : List (String × SourceJson) := (fragment0323962Field009Key00, fragment0323962Field009Value00) :: fragment0323962Acc00900
noncomputable def fragment0323962Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '2', '7', '9', '5', '1', '6', '4', '5', '4', '3', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0323962_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 363) (SourceJson.white (fragment0323962Field009Chars00 ++ tail)) fragment0323962Acc00900 =
      .ok (.obj (fragment0323962Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0323962_object_field_009"
  err.flush

noncomputable def fragment0323962Chars : List Char := '{' :: (fragment0323962Field000Chars00 ++ fragment0323962Field001Chars00 ++ fragment0323962Field002Chars00 ++ fragment0323962Field003Chars00 ++ fragment0323962Field004Chars00 ++ fragment0323962Field005Chars00 ++ fragment0323962Field006Chars00 ++ fragment0323962Field007Chars00 ++ fragment0323962Field008Chars00 ++ fragment0323962Field009Chars00)
noncomputable def fragment0323962Value : SourceJson := .obj (fragment0323962Acc01000.reverse)

theorem value_fragment0323962 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 373) (fragment0323962Chars ++ tail) =
      .ok (fragment0323962Value, tail) := by
  have hinput : fragment0323962Chars ++ tail = '{' :: (fragment0323962Field000Chars00 ++ (fragment0323962Field001Chars00 ++ (fragment0323962Field002Chars00 ++ (fragment0323962Field003Chars00 ++ (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0323962Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 373) (fragment0323962Chars ++ tail) =
        SourceJson.value (fuel + 373) ('{' :: (fragment0323962Field000Chars00 ++ (fragment0323962Field001Chars00 ++ (fragment0323962Field002Chars00 ++ (fragment0323962Field003Chars00 ++ (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 373)) hinput
    _ = SourceJson.object (fuel + 372) (SourceJson.white (fragment0323962Field000Chars00 ++ (fragment0323962Field001Chars00 ++ (fragment0323962Field002Chars00 ++ (fragment0323962Field003Chars00 ++ (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))))))))))) fragment0323962Acc00000 := by rfl
    _ = SourceJson.object (fuel + 371) (SourceJson.white (fragment0323962Field001Chars00 ++ (fragment0323962Field002Chars00 ++ (fragment0323962Field003Chars00 ++ (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail))))))))))) fragment0323962Acc00100 := object_fragment0323962_field_000 fuel (fragment0323962Field001Chars00 ++ (fragment0323962Field002Chars00 ++ (fragment0323962Field003Chars00 ++ (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 370) (SourceJson.white (fragment0323962Field002Chars00 ++ (fragment0323962Field003Chars00 ++ (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))))))))) fragment0323962Acc00200 := object_fragment0323962_field_001 fuel (fragment0323962Field002Chars00 ++ (fragment0323962Field003Chars00 ++ (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment0323962Field003Chars00 ++ (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail))))))))) fragment0323962Acc00300 := object_fragment0323962_field_002 fuel (fragment0323962Field003Chars00 ++ (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))))))) fragment0323962Acc00400 := object_fragment0323962_field_003 fuel (fragment0323962Field004Chars00 ++ (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 367) (SourceJson.white (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail))))))) fragment0323962Acc00500 := object_fragment0323962_field_004 fuel (fragment0323962Field005Chars00 ++ (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 366) (SourceJson.white (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))))) fragment0323962Acc00600 := object_fragment0323962_field_005 fuel (fragment0323962Field006Chars00 ++ (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 365) (SourceJson.white (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail))))) fragment0323962Acc00700 := object_fragment0323962_field_006 fuel (fragment0323962Field007Chars00 ++ (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 364) (SourceJson.white (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))) fragment0323962Acc00800 := object_fragment0323962_field_007 fuel (fragment0323962Field008Chars00 ++ (fragment0323962Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 363) (SourceJson.white (fragment0323962Field009Chars00 ++ (tail))) fragment0323962Acc00900 := object_fragment0323962_field_008 fuel (fragment0323962Field009Chars00 ++ (tail))
    _ = .ok (fragment0323962Value, tail) := object_fragment0323962_field_009 fuel (tail)

noncomputable def fragment0325840Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0325840Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0325840Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '7'])
noncomputable def fragment0325840Acc00100 : List (String × SourceJson) := (fragment0325840Field000Key00, fragment0325840Field000Value00) :: fragment0325840Acc00000
noncomputable def fragment0325840Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '7', ',']

theorem object_fragment0325840_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0325840Field000Chars00 ++ tail)) fragment0325840Acc00000 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0325840Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_000"
  err.flush

noncomputable def fragment0325840Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0325840Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '4']), .number (String.ofList ['7'])]
noncomputable def fragment0325840Acc00200 : List (String × SourceJson) := (fragment0325840Field001Key00, fragment0325840Field001Value00) :: fragment0325840Acc00100
noncomputable def fragment0325840Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0325840_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0325840Field001Chars00 ++ tail)) fragment0325840Acc00100 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0325840Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_001"
  err.flush

noncomputable def fragment0325840Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0325840Field002Value00 : SourceJson := .str (String.ofList ['3', '6', '2', '7', '2', '6', '4', '0', '5', '7', '4', '1', '5', '4', '5', '9', '8', '1', '9', '8', '5', '5', '3', '4', '8', '4', '4', '7', '2', '5', '1', '2', '1', '6', '6', '7', '/', '1', '9', '5', '3', '1', '2', '2', '3', '1', '7', '9', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0325840Acc00300 : List (String × SourceJson) := (fragment0325840Field002Key00, fragment0325840Field002Value00) :: fragment0325840Acc00200
noncomputable def fragment0325840Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '6', '2', '7', '2', '6', '4', '0', '5', '7', '4', '1', '5', '4', '5', '9', '8', '1', '9', '8', '5', '5', '3', '4', '8', '4', '4', '7', '2', '5', '1', '2', '1', '6', '6', '7', '/', '1', '9', '5', '3', '1', '2', '2', '3', '1', '7', '9', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0325840_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0325840Field002Chars00 ++ tail)) fragment0325840Acc00200 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0325840Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_002"
  err.flush

noncomputable def fragment0325840Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0325840Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0325840Acc00400 : List (String × SourceJson) := (fragment0325840Field003Key00, fragment0325840Field003Value00) :: fragment0325840Acc00300
noncomputable def fragment0325840Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0325840_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0325840Field003Chars00 ++ tail)) fragment0325840Acc00300 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0325840Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_003"
  err.flush

noncomputable def fragment0325840Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0325840Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0325840Acc00500 : List (String × SourceJson) := (fragment0325840Field004Key00, fragment0325840Field004Value00) :: fragment0325840Acc00400
noncomputable def fragment0325840Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '4', '1', '8', '7', '5', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0325840_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0325840Field004Chars00 ++ tail)) fragment0325840Acc00400 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0325840Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_004"
  err.flush

noncomputable def fragment0325840Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0325840Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '4', '7', '3', '5', '4', '1', '7', '1', '1', '6', '9', '/', '1', '2', '2', '0', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '2', '5', '0', '4', '3', '0', '0', '7', '4', '7', '/', '2', '4', '4', '0', '9', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '5', '5', '4', '0', '4', '7', '4', '1', '7', '/', '1', '3', '3', '4', '8', '9', '1', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '9', '4', '0', '3', '6', '9', '1', '2', '8', '5', '1', '/', '2', '8', '4', '7', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '7', '8', '5', '6', '1', '7', '2', '8', '8', '1', '9', '/', '2', '8', '4', '7', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '1', '3', '5', '2', '1', '9', '2', '5', '0', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '9', '9', '5', '3', '6', '4', '8', '7', '0', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '6', '6', '4', '8', '0', '1', '8', '6', '4', '3', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '4', '4', '9', '5', '7', '2', '2', '1', '/', '4', '8', '8', '1', '8', '8', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '1', '1', '2', '3', '1', '1', '6', '8', '7', '7', '/', '1', '2', '2', '0', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0325840Acc00600 : List (String × SourceJson) := (fragment0325840Field005Key00, fragment0325840Field005Value00) :: fragment0325840Acc00500
noncomputable def fragment0325840Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '4', '7', '3', '5', '4', '1', '7', '1', '1', '6', '9', '/', '1', '2', '2', '0', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '2', '5', '0', '4', '3', '0', '0', '7', '4', '7', '/', '2', '4', '4', '0', '9', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '3', '5', '5', '4', '0', '4', '7', '4', '1', '7', '/', '1', '3', '3', '4', '8', '9', '1', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '9', '4', '0', '3', '6', '9', '1', '2', '8', '5', '1', '/', '2', '8', '4', '7', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '8', '5', '6', '1', '7', '2', '8', '8', '1', '9', '/', '2', '8', '4', '7', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '1', '3', '5', '2', '1', '9', '2', '5', '0', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '9', '9', '5', '3', '6', '4', '8', '7', '0', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '6', '4', '8', '0', '1', '8', '6', '4', '3', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '4', '4', '9', '5', '7', '2', '2', '1', '/', '4', '8', '8', '1', '8', '8', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '1', '1', '2', '3', '1', '1', '6', '8', '7', '7', '/', '1', '2', '2', '0', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0325840_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0325840Field005Chars00 ++ tail)) fragment0325840Acc00500 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0325840Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_005"
  err.flush

noncomputable def fragment0325840Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0325840Field006Value00 : SourceJson := .str (String.ofList ['5', '5', '7', '8', '8', '6', '7', '0', '8', '0', '0', '9', '5', '2', '0', '5', '1', '8', '5', '9', '4', '3', '9', '4', '6', '5', '4', '3', '4', '3', '4', '1', '3', '6', '7', '2', '0', '5', '0', '9', '6', '1', '7', '0', '6', '0', '8', '9', '1', '3', '1', '2', '5', '/', '1', '8', '1', '8', '8', '0', '2', '8', '6', '3', '5', '5', '2', '7', '3', '6', '2', '8', '6', '0', '1', '9', '2', '9', '9', '0', '0', '3', '2', '2', '6', '4', '3', '0', '6', '8', '5', '1', '0', '2', '3', '8', '6', '1', '7', '7', '9', '9', '5', '2', '5', '6', '5', '0', '6', '4', '8', '6', '8', '0', '4', '0', '0', '9', '4', '1', '8', '7', '5', '2'])
noncomputable def fragment0325840Acc00700 : List (String × SourceJson) := (fragment0325840Field006Key00, fragment0325840Field006Value00) :: fragment0325840Acc00600
noncomputable def fragment0325840Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '5', '7', '8', '8', '6', '7', '0', '8', '0', '0', '9', '5', '2', '0', '5', '1', '8', '5', '9', '4', '3', '9', '4', '6', '5', '4', '3', '4', '3', '4', '1', '3', '6', '7', '2', '0', '5', '0', '9', '6', '1', '7', '0', '6', '0', '8', '9', '1', '3', '1', '2', '5', '/', '1', '8', '1', '8', '8', '0', '2', '8', '6', '3', '5', '5', '2', '7', '3', '6', '2', '8', '6', '0', '1', '9', '2', '9', '9', '0', '0', '3', '2', '2', '6', '4', '3', '0', '6', '8', '5', '1', '0', '2', '3', '8', '6', '1', '7', '7', '9', '9', '5', '2', '5', '6', '5', '0', '6', '4', '8', '6', '8', '0', '4', '0', '0', '9', '4', '1', '8', '7', '5', '2', '"', ',']

theorem object_fragment0325840_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0325840Field006Chars00 ++ tail)) fragment0325840Acc00600 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0325840Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_006"
  err.flush

noncomputable def fragment0325840Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0325840Field007Value00 : SourceJson := .str (String.ofList ['2', '7', '1', '9', '2', '1', '8', '5', '4', '0', '5', '1', '9', '1', '6', '5', '2', '9', '8', '0', '7', '6', '6', '7', '9', '6', '3', '2', '0', '8', '4', '0', '3', '3', '7', '3', '3', '3', '2', '7', '4', '9', '9', '0', '3', '1', '8', '9', '6', '0', '4', '1', '6', '5', '8', '9', '5', '2', '9', '5', '7', '0', '6', '5', '0', '5', '5', '9', '6', '7', '1', '4', '3', '5', '2', '1', '9', '4', '7', '3', '6', '3', '5', '0', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '7', '2', '3', '8', '1', '4', '4', '9', '6', '1', '3', '2', '8', '1', '0', '0', '2', '8', '7', '2', '7', '6', '5', '5', '0', '8', '1', '0', '3', '2', '4', '6', '0', '6', '8', '0', '3', '7', '5', '6', '5', '1', '8', '6', '1', '8', '6', '6', '6', '6', '8', '3', '8', '3', '4', '0', '0', '2', '0', '8', '8', '2', '2', '3', '6', '2', '1', '0', '7', '6', '8', '3', '1', '5', '1', '2', '9', '6', '7', '2', '7', '9', '0', '1', '0', '4', '5', '3', '1', '2', '6', '5', '2', '9', '3', '2', '2', '2', '4', '8', '2', '7', '1', '2', '2', '3', '5', '4', '2', '8', '9', '0', '4', '2', '9'])
noncomputable def fragment0325840Acc00800 : List (String × SourceJson) := (fragment0325840Field007Key00, fragment0325840Field007Value00) :: fragment0325840Acc00700
noncomputable def fragment0325840Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '7', '1', '9', '2', '1', '8', '5', '4', '0', '5', '1', '9', '1', '6', '5', '2', '9', '8', '0', '7', '6', '6', '7', '9', '6', '3', '2', '0', '8', '4', '0', '3', '3', '7', '3', '3', '3', '2', '7', '4', '9', '9', '0', '3', '1', '8', '9', '6', '0', '4', '1', '6', '5', '8', '9', '5', '2', '9', '5', '7', '0', '6', '5', '0', '5', '5', '9', '6', '7', '1', '4', '3', '5', '2', '1', '9', '4', '7', '3', '6', '3', '5', '0', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '2', '7', '2', '3', '8', '1', '4', '4', '9', '6', '1', '3', '2', '8', '1', '0', '0', '2', '8', '7', '2', '7', '6', '5', '5', '0', '8', '1', '0', '3', '2', '4', '6', '0', '6', '8', '0', '3', '7', '5', '6', '5', '1', '8', '6', '1', '8', '6', '6', '6', '6', '8', '3', '8', '3', '4', '0', '0', '2', '0', '8', '8', '2', '2', '3', '6', '2', '1', '0', '7', '6', '8', '3', '1', '5', '1', '2', '9', '6', '7', '2', '7', '9', '0', '1', '0', '4', '5', '3', '1', '2', '6', '5', '2', '9', '3', '2', '2', '2', '4', '8', '2', '7', '1', '2', '2', '3', '5', '4', '2', '8', '9', '0', '4', '2', '9', '"', ',']

theorem object_fragment0325840_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0325840Field007Chars00 ++ tail)) fragment0325840Acc00700 =
      SourceJson.object (fuel + 221) (SourceJson.white tail) fragment0325840Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_007"
  err.flush

noncomputable def fragment0325840Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0325840Field008Value00 : SourceJson := .str (String.ofList ['2', '4', '3', '0', '1', '8', '8', '5', '4', '0', '6', '3', '0'])
noncomputable def fragment0325840Acc00900 : List (String × SourceJson) := (fragment0325840Field008Key00, fragment0325840Field008Value00) :: fragment0325840Acc00800
noncomputable def fragment0325840Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '4', '3', '0', '1', '8', '8', '5', '4', '0', '6', '3', '0', '"', ',']

theorem object_fragment0325840_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 221) (SourceJson.white (fragment0325840Field008Chars00 ++ tail)) fragment0325840Acc00800 =
      SourceJson.object (fuel + 220) (SourceJson.white tail) fragment0325840Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_008"
  err.flush

noncomputable def fragment0325840Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0325840Field009Value00 : SourceJson := .str (String.ofList ['6', '5', '8', '3', '5', '4', '4', '4', '8', '4', '5', '6', '8'])
noncomputable def fragment0325840Acc01000 : List (String × SourceJson) := (fragment0325840Field009Key00, fragment0325840Field009Value00) :: fragment0325840Acc00900
noncomputable def fragment0325840Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '5', '8', '3', '5', '4', '4', '4', '8', '4', '5', '6', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0325840_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 220) (SourceJson.white (fragment0325840Field009Chars00 ++ tail)) fragment0325840Acc00900 =
      .ok (.obj (fragment0325840Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0325840_object_field_009"
  err.flush

noncomputable def fragment0325840Chars : List Char := '{' :: (fragment0325840Field000Chars00 ++ fragment0325840Field001Chars00 ++ fragment0325840Field002Chars00 ++ fragment0325840Field003Chars00 ++ fragment0325840Field004Chars00 ++ fragment0325840Field005Chars00 ++ fragment0325840Field006Chars00 ++ fragment0325840Field007Chars00 ++ fragment0325840Field008Chars00 ++ fragment0325840Field009Chars00)
noncomputable def fragment0325840Value : SourceJson := .obj (fragment0325840Acc01000.reverse)

theorem value_fragment0325840 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 230) (fragment0325840Chars ++ tail) =
      .ok (fragment0325840Value, tail) := by
  have hinput : fragment0325840Chars ++ tail = '{' :: (fragment0325840Field000Chars00 ++ (fragment0325840Field001Chars00 ++ (fragment0325840Field002Chars00 ++ (fragment0325840Field003Chars00 ++ (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0325840Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 230) (fragment0325840Chars ++ tail) =
        SourceJson.value (fuel + 230) ('{' :: (fragment0325840Field000Chars00 ++ (fragment0325840Field001Chars00 ++ (fragment0325840Field002Chars00 ++ (fragment0325840Field003Chars00 ++ (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 230)) hinput
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0325840Field000Chars00 ++ (fragment0325840Field001Chars00 ++ (fragment0325840Field002Chars00 ++ (fragment0325840Field003Chars00 ++ (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))))))))))) fragment0325840Acc00000 := by rfl
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0325840Field001Chars00 ++ (fragment0325840Field002Chars00 ++ (fragment0325840Field003Chars00 ++ (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail))))))))))) fragment0325840Acc00100 := object_fragment0325840_field_000 fuel (fragment0325840Field001Chars00 ++ (fragment0325840Field002Chars00 ++ (fragment0325840Field003Chars00 ++ (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0325840Field002Chars00 ++ (fragment0325840Field003Chars00 ++ (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))))))))) fragment0325840Acc00200 := object_fragment0325840_field_001 fuel (fragment0325840Field002Chars00 ++ (fragment0325840Field003Chars00 ++ (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0325840Field003Chars00 ++ (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail))))))))) fragment0325840Acc00300 := object_fragment0325840_field_002 fuel (fragment0325840Field003Chars00 ++ (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))))))) fragment0325840Acc00400 := object_fragment0325840_field_003 fuel (fragment0325840Field004Chars00 ++ (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail))))))) fragment0325840Acc00500 := object_fragment0325840_field_004 fuel (fragment0325840Field005Chars00 ++ (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))))) fragment0325840Acc00600 := object_fragment0325840_field_005 fuel (fragment0325840Field006Chars00 ++ (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail))))) fragment0325840Acc00700 := object_fragment0325840_field_006 fuel (fragment0325840Field007Chars00 ++ (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 221) (SourceJson.white (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))) fragment0325840Acc00800 := object_fragment0325840_field_007 fuel (fragment0325840Field008Chars00 ++ (fragment0325840Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 220) (SourceJson.white (fragment0325840Field009Chars00 ++ (tail))) fragment0325840Acc00900 := object_fragment0325840_field_008 fuel (fragment0325840Field009Chars00 ++ (tail))
    _ = .ok (fragment0325840Value, tail) := object_fragment0325840_field_009 fuel (tail)

noncomputable def fragment0327431Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0327431Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0327431Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '8'])
noncomputable def fragment0327431Acc00100 : List (String × SourceJson) := (fragment0327431Field000Key00, fragment0327431Field000Value00) :: fragment0327431Acc00000
noncomputable def fragment0327431Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '8', ',']

theorem object_fragment0327431_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0327431Field000Chars00 ++ tail)) fragment0327431Acc00000 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0327431Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_000"
  err.flush

noncomputable def fragment0327431Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0327431Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['7'])]
noncomputable def fragment0327431Acc00200 : List (String × SourceJson) := (fragment0327431Field001Key00, fragment0327431Field001Value00) :: fragment0327431Acc00100
noncomputable def fragment0327431Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0327431_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0327431Field001Chars00 ++ tail)) fragment0327431Acc00100 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0327431Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_001"
  err.flush

noncomputable def fragment0327431Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0327431Field002Value00 : SourceJson := .str (String.ofList ['3', '0', '6', '0', '1', '8', '2', '5', '2', '0', '5', '6', '9', '5', '8', '8', '7', '3', '3', '1', '9', '0', '7', '9', '5', '5', '3', '2', '9', '2', '7', '3', '9', '3', '/', '1', '1', '8', '3', '7', '1', '0', '4', '9', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0327431Acc00300 : List (String × SourceJson) := (fragment0327431Field002Key00, fragment0327431Field002Value00) :: fragment0327431Acc00200
noncomputable def fragment0327431Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '0', '6', '0', '1', '8', '2', '5', '2', '0', '5', '6', '9', '5', '8', '8', '7', '3', '3', '1', '9', '0', '7', '9', '5', '5', '3', '2', '9', '2', '7', '3', '9', '3', '/', '1', '1', '8', '3', '7', '1', '0', '4', '9', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0327431_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0327431Field002Chars00 ++ tail)) fragment0327431Acc00200 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0327431Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_002"
  err.flush

noncomputable def fragment0327431Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0327431Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0327431Acc00400 : List (String × SourceJson) := (fragment0327431Field003Key00, fragment0327431Field003Value00) :: fragment0327431Acc00300
noncomputable def fragment0327431Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0327431_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0327431Field003Chars00 ++ tail)) fragment0327431Acc00300 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0327431Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_003"
  err.flush

noncomputable def fragment0327431Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0327431Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0327431Acc00500 : List (String × SourceJson) := (fragment0327431Field004Key00, fragment0327431Field004Value00) :: fragment0327431Acc00400
noncomputable def fragment0327431Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '5', '6', '1', '7', '/', '1', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0327431_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0327431Field004Chars00 ++ tail)) fragment0327431Acc00400 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0327431Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_004"
  err.flush

noncomputable def fragment0327431Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0327431Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '3', '8', '8', '6', '7', '8', '6', '0', '1', '7', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '7', '3', '7', '1', '2', '4', '8', '2', '4', '2', '3', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '0', '5', '2', '5', '5', '3', '1', '9', '1', '7', '/', '6', '1', '0', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '2', '3', '8', '5', '7', '0', '4', '6', '0', '3', '/', '4', '7', '4', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '9', '4', '1', '9', '5', '2', '1', '7', '9', '3', '/', '1', '4', '2', '3', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '3', '6', '7', '1', '9', '5', '9', '2', '1', '9', '/', '6', '1', '0', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '2', '8', '6', '1', '0', '3', '4', '1', '4', '7', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '3', '0', '8', '3', '1', '7', '0', '8', '4', '5', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '4', '2', '3', '3', '4', '9', '5', '3', '8', '1', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '4', '2', '3', '2', '0', '7', '1', '4', '9', '7', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0327431Acc00600 : List (String × SourceJson) := (fragment0327431Field005Key00, fragment0327431Field005Value00) :: fragment0327431Acc00500
noncomputable def fragment0327431Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '8', '8', '6', '7', '8', '6', '0', '1', '7', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '3', '7', '1', '2', '4', '8', '2', '4', '2', '3', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '0', '5', '2', '5', '5', '3', '1', '9', '1', '7', '/', '6', '1', '0', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '2', '3', '8', '5', '7', '0', '4', '6', '0', '3', '/', '4', '7', '4', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '9', '4', '1', '9', '5', '2', '1', '7', '9', '3', '/', '1', '4', '2', '3', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '3', '6', '7', '1', '9', '5', '9', '2', '1', '9', '/', '6', '1', '0', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '2', '8', '6', '1', '0', '3', '4', '1', '4', '7', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '3', '0', '8', '3', '1', '7', '0', '8', '4', '5', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '4', '2', '3', '3', '4', '9', '5', '3', '8', '1', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '4', '2', '3', '2', '0', '7', '1', '4', '9', '7', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0327431_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0327431Field005Chars00 ++ tail)) fragment0327431Acc00500 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0327431Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_005"
  err.flush

noncomputable def fragment0327431Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0327431Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '1', '0', '6', '1', '3', '3', '2', '6', '1', '8', '5', '0', '9', '9', '4', '2', '5', '7', '6', '8', '6', '5', '5', '6', '8', '3', '7', '5', '8', '0', '4', '0', '1', '6', '0', '3', '1', '3', '0', '3', '9', '6', '1', '7', '1', '8', '7', '5', '/', '3', '5', '3', '0', '0', '0', '8', '7', '5', '7', '5', '5', '3', '3', '9', '3', '0', '4', '4', '4', '9', '6', '4', '9', '7', '3', '9', '9', '9', '6', '4', '7', '0', '2', '2', '1', '0', '7', '2', '4', '4', '0', '9', '2', '2', '4', '9', '2', '6', '3', '3', '8', '9', '4', '5', '7', '9', '4', '6', '4', '5', '7', '4', '1', '7', '4'])
noncomputable def fragment0327431Acc00700 : List (String × SourceJson) := (fragment0327431Field006Key00, fragment0327431Field006Value00) :: fragment0327431Acc00600
noncomputable def fragment0327431Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '1', '0', '6', '1', '3', '3', '2', '6', '1', '8', '5', '0', '9', '9', '4', '2', '5', '7', '6', '8', '6', '5', '5', '6', '8', '3', '7', '5', '8', '0', '4', '0', '1', '6', '0', '3', '1', '3', '0', '3', '9', '6', '1', '7', '1', '8', '7', '5', '/', '3', '5', '3', '0', '0', '0', '8', '7', '5', '7', '5', '5', '3', '3', '9', '3', '0', '4', '4', '4', '9', '6', '4', '9', '7', '3', '9', '9', '9', '6', '4', '7', '0', '2', '2', '1', '0', '7', '2', '4', '4', '0', '9', '2', '2', '4', '9', '2', '6', '3', '3', '8', '9', '4', '5', '7', '9', '4', '6', '4', '5', '7', '4', '1', '7', '4', '"', ',']

theorem object_fragment0327431_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0327431Field006Chars00 ++ tail)) fragment0327431Acc00600 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0327431Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_006"
  err.flush

noncomputable def fragment0327431Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0327431Field007Value00 : SourceJson := .str (String.ofList ['2', '1', '8', '3', '2', '3', '0', '0', '7', '4', '0', '9', '0', '2', '8', '6', '2', '3', '6', '5', '7', '5', '0', '9', '2', '7', '0', '6', '2', '0', '5', '7', '2', '0', '6', '3', '4', '9', '1', '5', '7', '2', '9', '0', '0', '4', '0', '4', '8', '8', '3', '8', '2', '3', '1', '8', '6', '3', '3', '4', '7', '9', '1', '5', '5', '5', '6', '4', '1', '8', '1', '3', '4', '1', '9', '5', '7', '2', '0', '2', '0', '8', '2', '9', '4', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '9', '5', '1', '3', '6', '3', '9', '5', '8', '0', '4', '1', '4', '0', '6', '9', '8', '9', '1', '6', '7', '6', '8', '3', '2', '9', '7', '8', '4', '2', '7', '1', '9', '3', '3', '0', '8', '0', '0', '4', '9', '1', '4', '6', '3', '0', '4', '5', '5', '2', '2', '7', '8', '8', '4', '6', '7', '8', '7', '7', '5', '5', '2', '3', '5', '6', '7', '3', '5', '1', '2', '5', '5', '0', '7', '4', '1', '8', '0', '5', '2', '0', '3', '8', '7', '6', '7', '1', '7', '1', '4', '8', '5', '6', '8', '2', '6', '9', '6', '9', '1', '4', '0', '5', '0', '1', '0', '2', '3', '4', '0', '7', '0', '3', '2', '7', '2', '3'])
noncomputable def fragment0327431Acc00800 : List (String × SourceJson) := (fragment0327431Field007Key00, fragment0327431Field007Value00) :: fragment0327431Acc00700
noncomputable def fragment0327431Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '8', '3', '2', '3', '0', '0', '7', '4', '0', '9', '0', '2', '8', '6', '2', '3', '6', '5', '7', '5', '0', '9', '2', '7', '0', '6', '2', '0', '5', '7', '2', '0', '6', '3', '4', '9', '1', '5', '7', '2', '9', '0', '0', '4', '0', '4', '8', '8', '3', '8', '2', '3', '1', '8', '6', '3', '3', '4', '7', '9', '1', '5', '5', '5', '6', '4', '1', '8', '1', '3', '4', '1', '9', '5', '7', '2', '0', '2', '0', '8', '2', '9', '4', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '9', '5', '1', '3', '6', '3', '9', '5', '8', '0', '4', '1', '4', '0', '6', '9', '8', '9', '1', '6', '7', '6', '8', '3', '2', '9', '7', '8', '4', '2', '7', '1', '9', '3', '3', '0', '8', '0', '0', '4', '9', '1', '4', '6', '3', '0', '4', '5', '5', '2', '2', '7', '8', '8', '4', '6', '7', '8', '7', '7', '5', '5', '2', '3', '5', '6', '7', '3', '5', '1', '2', '5', '5', '0', '7', '4', '1', '8', '0', '5', '2', '0', '3', '8', '7', '6', '7', '1', '7', '1', '4', '8', '5', '6', '8', '2', '6', '9', '6', '9', '1', '4', '0', '5', '0', '1', '0', '2', '3', '4', '0', '7', '0', '3', '2', '7', '2', '3', '"', ',']

theorem object_fragment0327431_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0327431Field007Chars00 ++ tail)) fragment0327431Acc00700 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0327431Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_007"
  err.flush

noncomputable def fragment0327431Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0327431Field008Value00 : SourceJson := .str (String.ofList ['2', '9', '4', '1', '5', '6', '4', '5', '3', '2', '3', '3', '0'])
noncomputable def fragment0327431Acc00900 : List (String × SourceJson) := (fragment0327431Field008Key00, fragment0327431Field008Value00) :: fragment0327431Acc00800
noncomputable def fragment0327431Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '4', '1', '5', '6', '4', '5', '3', '2', '3', '3', '0', '"', ',']

theorem object_fragment0327431_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0327431Field008Chars00 ++ tail)) fragment0327431Acc00800 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0327431Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_008"
  err.flush

noncomputable def fragment0327431Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0327431Field009Value00 : SourceJson := .str (String.ofList ['8', '6', '6', '9', '7', '4', '8', '4', '6', '8', '3', '1', '6'])
noncomputable def fragment0327431Acc01000 : List (String × SourceJson) := (fragment0327431Field009Key00, fragment0327431Field009Value00) :: fragment0327431Acc00900
noncomputable def fragment0327431Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '6', '6', '9', '7', '4', '8', '4', '6', '8', '3', '1', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0327431_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0327431Field009Chars00 ++ tail)) fragment0327431Acc00900 =
      .ok (.obj (fragment0327431Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0327431_object_field_009"
  err.flush

noncomputable def fragment0327431Chars : List Char := '{' :: (fragment0327431Field000Chars00 ++ fragment0327431Field001Chars00 ++ fragment0327431Field002Chars00 ++ fragment0327431Field003Chars00 ++ fragment0327431Field004Chars00 ++ fragment0327431Field005Chars00 ++ fragment0327431Field006Chars00 ++ fragment0327431Field007Chars00 ++ fragment0327431Field008Chars00 ++ fragment0327431Field009Chars00)
noncomputable def fragment0327431Value : SourceJson := .obj (fragment0327431Acc01000.reverse)

theorem value_fragment0327431 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 236) (fragment0327431Chars ++ tail) =
      .ok (fragment0327431Value, tail) := by
  have hinput : fragment0327431Chars ++ tail = '{' :: (fragment0327431Field000Chars00 ++ (fragment0327431Field001Chars00 ++ (fragment0327431Field002Chars00 ++ (fragment0327431Field003Chars00 ++ (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0327431Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 236) (fragment0327431Chars ++ tail) =
        SourceJson.value (fuel + 236) ('{' :: (fragment0327431Field000Chars00 ++ (fragment0327431Field001Chars00 ++ (fragment0327431Field002Chars00 ++ (fragment0327431Field003Chars00 ++ (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 236)) hinput
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0327431Field000Chars00 ++ (fragment0327431Field001Chars00 ++ (fragment0327431Field002Chars00 ++ (fragment0327431Field003Chars00 ++ (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))))))))))) fragment0327431Acc00000 := by rfl
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0327431Field001Chars00 ++ (fragment0327431Field002Chars00 ++ (fragment0327431Field003Chars00 ++ (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail))))))))))) fragment0327431Acc00100 := object_fragment0327431_field_000 fuel (fragment0327431Field001Chars00 ++ (fragment0327431Field002Chars00 ++ (fragment0327431Field003Chars00 ++ (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0327431Field002Chars00 ++ (fragment0327431Field003Chars00 ++ (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))))))))) fragment0327431Acc00200 := object_fragment0327431_field_001 fuel (fragment0327431Field002Chars00 ++ (fragment0327431Field003Chars00 ++ (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0327431Field003Chars00 ++ (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail))))))))) fragment0327431Acc00300 := object_fragment0327431_field_002 fuel (fragment0327431Field003Chars00 ++ (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))))))) fragment0327431Acc00400 := object_fragment0327431_field_003 fuel (fragment0327431Field004Chars00 ++ (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail))))))) fragment0327431Acc00500 := object_fragment0327431_field_004 fuel (fragment0327431Field005Chars00 ++ (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))))) fragment0327431Acc00600 := object_fragment0327431_field_005 fuel (fragment0327431Field006Chars00 ++ (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail))))) fragment0327431Acc00700 := object_fragment0327431_field_006 fuel (fragment0327431Field007Chars00 ++ (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))) fragment0327431Acc00800 := object_fragment0327431_field_007 fuel (fragment0327431Field008Chars00 ++ (fragment0327431Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0327431Field009Chars00 ++ (tail))) fragment0327431Acc00900 := object_fragment0327431_field_008 fuel (fragment0327431Field009Chars00 ++ (tail))
    _ = .ok (fragment0327431Value, tail) := object_fragment0327431_field_009 fuel (tail)

noncomputable def fragment0329023Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0329023Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0329023Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '9'])
noncomputable def fragment0329023Acc00100 : List (String × SourceJson) := (fragment0329023Field000Key00, fragment0329023Field000Value00) :: fragment0329023Acc00000
noncomputable def fragment0329023Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '9', ',']

theorem object_fragment0329023_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0329023Field000Chars00 ++ tail)) fragment0329023Acc00000 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0329023Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_000"
  err.flush

noncomputable def fragment0329023Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0329023Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7'])]
noncomputable def fragment0329023Acc00200 : List (String × SourceJson) := (fragment0329023Field001Key00, fragment0329023Field001Value00) :: fragment0329023Acc00100
noncomputable def fragment0329023Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0329023_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0329023Field001Chars00 ++ tail)) fragment0329023Acc00100 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0329023Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_001"
  err.flush

noncomputable def fragment0329023Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0329023Field002Value00 : SourceJson := .str (String.ofList ['5', '9', '5', '0', '3', '1', '3', '1', '8', '7', '0', '5', '8', '7', '3', '0', '8', '2', '5', '0', '5', '6', '3', '0', '6', '4', '5', '7', '1', '9', '6', '5', '0', '3', '/', '1', '8', '4', '1', '3', '2', '7', '4', '3', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0329023Acc00300 : List (String × SourceJson) := (fragment0329023Field002Key00, fragment0329023Field002Value00) :: fragment0329023Acc00200
noncomputable def fragment0329023Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '9', '5', '0', '3', '1', '3', '1', '8', '7', '0', '5', '8', '7', '3', '0', '8', '2', '5', '0', '5', '6', '3', '0', '6', '4', '5', '7', '1', '9', '6', '5', '0', '3', '/', '1', '8', '4', '1', '3', '2', '7', '4', '3', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0329023_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0329023Field002Chars00 ++ tail)) fragment0329023Acc00200 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0329023Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_002"
  err.flush

noncomputable def fragment0329023Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0329023Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0329023Acc00400 : List (String × SourceJson) := (fragment0329023Field003Key00, fragment0329023Field003Value00) :: fragment0329023Acc00300
noncomputable def fragment0329023Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0329023_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0329023Field003Chars00 ++ tail)) fragment0329023Acc00300 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0329023Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_003"
  err.flush

noncomputable def fragment0329023Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0329023Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0'])]
noncomputable def fragment0329023Acc00500 : List (String × SourceJson) := (fragment0329023Field004Key00, fragment0329023Field004Value00) :: fragment0329023Acc00400
noncomputable def fragment0329023Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '1', '6', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '8', '4', '2', '3', '/', '5', '0', '2', '5', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0329023_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0329023Field004Chars00 ++ tail)) fragment0329023Acc00400 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0329023Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_004"
  err.flush

noncomputable def fragment0329023Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0329023Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '7', '4', '4', '3', '9', '0', '0', '9', '4', '7', '9', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '9', '7', '4', '7', '5', '7', '5', '8', '7', '7', '1', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '6', '6', '8', '1', '3', '9', '6', '4', '7', '4', '7', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '4', '9', '1', '2', '3', '1', '6', '5', '0', '9', '/', '1', '4', '2', '3', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '2', '3', '9', '1', '5', '7', '4', '8', '3', '1', '/', '4', '7', '4', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '4', '2', '8', '7', '7', '2', '5', '4', '2', '2', '9', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '9', '7', '7', '7', '6', '2', '9', '3', '7', '7', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '9', '7', '4', '6', '2', '1', '7', '3', '2', '7', '1', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '2', '5', '1', '5', '0', '5', '8', '8', '7', '3', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '2', '5', '1', '4', '7', '7', '4', '0', '9', '6', '9', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0329023Acc00600 : List (String × SourceJson) := (fragment0329023Field005Key00, fragment0329023Field005Value00) :: fragment0329023Acc00500
noncomputable def fragment0329023Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '4', '3', '9', '0', '0', '9', '4', '7', '9', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '9', '7', '4', '7', '5', '7', '5', '8', '7', '7', '1', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '6', '6', '8', '1', '3', '9', '6', '4', '7', '4', '7', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '4', '9', '1', '2', '3', '1', '6', '5', '0', '9', '/', '1', '4', '2', '3', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '2', '3', '9', '1', '5', '7', '4', '8', '3', '1', '/', '4', '7', '4', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '4', '2', '8', '7', '7', '2', '5', '4', '2', '2', '9', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '9', '7', '7', '7', '6', '2', '9', '3', '7', '7', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '7', '4', '6', '2', '1', '7', '3', '2', '7', '1', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '5', '1', '5', '0', '5', '8', '8', '7', '3', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '5', '1', '4', '7', '7', '4', '0', '9', '6', '9', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0329023_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0329023Field005Chars00 ++ tail)) fragment0329023Acc00500 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0329023Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_005"
  err.flush

noncomputable def fragment0329023Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0329023Field006Value00 : SourceJson := .str (String.ofList ['2', '5', '4', '8', '3', '9', '6', '9', '3', '5', '6', '4', '5', '0', '5', '5', '8', '1', '7', '0', '6', '0', '4', '2', '4', '1', '8', '6', '5', '4', '8', '7', '6', '0', '0', '8', '8', '9', '7', '1', '4', '7', '8', '4', '4', '5', '3', '1', '2', '5', '/', '6', '4', '8', '9', '3', '7', '4', '4', '0', '2', '1', '7', '6', '8', '5', '8', '6', '0', '9', '7', '8', '8', '7', '1', '7', '1', '0', '6', '8', '3', '1', '8', '9', '6', '2', '7', '3', '6', '0', '2', '0', '6', '2', '1', '2', '1', '5', '7', '7', '8', '9', '2', '1', '4', '2', '0', '7', '0', '0', '2', '5', '6', '1', '0', '0', '4'])
noncomputable def fragment0329023Acc00700 : List (String × SourceJson) := (fragment0329023Field006Key00, fragment0329023Field006Value00) :: fragment0329023Acc00600
noncomputable def fragment0329023Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '5', '4', '8', '3', '9', '6', '9', '3', '5', '6', '4', '5', '0', '5', '5', '8', '1', '7', '0', '6', '0', '4', '2', '4', '1', '8', '6', '5', '4', '8', '7', '6', '0', '0', '8', '8', '9', '7', '1', '4', '7', '8', '4', '4', '5', '3', '1', '2', '5', '/', '6', '4', '8', '9', '3', '7', '4', '4', '0', '2', '1', '7', '6', '8', '5', '8', '6', '0', '9', '7', '8', '8', '7', '1', '7', '1', '0', '6', '8', '3', '1', '8', '9', '6', '2', '7', '3', '6', '0', '2', '0', '6', '2', '1', '2', '1', '5', '7', '7', '8', '9', '2', '1', '4', '2', '0', '7', '0', '0', '2', '5', '6', '1', '0', '0', '4', '"', ',']

theorem object_fragment0329023_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0329023Field006Chars00 ++ tail)) fragment0329023Acc00600 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0329023Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_006"
  err.flush

noncomputable def fragment0329023Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0329023Field007Value00 : SourceJson := .str (String.ofList ['6', '6', '8', '6', '0', '9', '5', '2', '2', '9', '7', '2', '9', '5', '7', '6', '2', '8', '8', '7', '9', '6', '8', '8', '5', '7', '8', '5', '3', '8', '4', '6', '4', '8', '1', '0', '4', '7', '2', '2', '5', '9', '8', '2', '8', '3', '4', '9', '3', '4', '2', '1', '8', '4', '8', '9', '7', '9', '7', '5', '6', '3', '8', '6', '5', '8', '7', '9', '7', '9', '6', '4', '1', '5', '6', '0', '1', '6', '7', '8', '0', '0', '6', '6', '8', '8', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '1', '6', '9', '5', '8', '6', '5', '3', '1', '1', '8', '9', '3', '0', '7', '1', '9', '7', '4', '8', '9', '5', '7', '1', '2', '0', '4', '2', '9', '3', '4', '2', '3', '1', '0', '7', '6', '9', '5', '5', '0', '2', '2', '6', '1', '4', '1', '2', '3', '7', '9', '7', '9', '3', '2', '4', '8', '5', '9', '6', '1', '2', '7', '1', '4', '6', '5', '1', '1', '4', '7', '2', '4', '8', '0', '1', '6', '3', '8', '4', '0', '5', '4', '1', '2', '0', '0', '5', '2', '5', '9', '1', '9', '4', '8', '2', '6', '6', '2', '9', '4', '4', '0', '6', '4', '8', '3', '1', '6', '8', '9', '2', '7', '0', '4', '3', '7', '4', '5', '0', '7'])
noncomputable def fragment0329023Acc00800 : List (String × SourceJson) := (fragment0329023Field007Key00, fragment0329023Field007Value00) :: fragment0329023Acc00700
noncomputable def fragment0329023Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '6', '8', '6', '0', '9', '5', '2', '2', '9', '7', '2', '9', '5', '7', '6', '2', '8', '8', '7', '9', '6', '8', '8', '5', '7', '8', '5', '3', '8', '4', '6', '4', '8', '1', '0', '4', '7', '2', '2', '5', '9', '8', '2', '8', '3', '4', '9', '3', '4', '2', '1', '8', '4', '8', '9', '7', '9', '7', '5', '6', '3', '8', '6', '5', '8', '7', '9', '7', '9', '6', '4', '1', '5', '6', '0', '1', '6', '7', '8', '0', '0', '6', '6', '8', '8', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '1', '6', '9', '5', '8', '6', '5', '3', '1', '1', '8', '9', '3', '0', '7', '1', '9', '7', '4', '8', '9', '5', '7', '1', '2', '0', '4', '2', '9', '3', '4', '2', '3', '1', '0', '7', '6', '9', '5', '5', '0', '2', '2', '6', '1', '4', '1', '2', '3', '7', '9', '7', '9', '3', '2', '4', '8', '5', '9', '6', '1', '2', '7', '1', '4', '6', '5', '1', '1', '4', '7', '2', '4', '8', '0', '1', '6', '3', '8', '4', '0', '5', '4', '1', '2', '0', '0', '5', '2', '5', '9', '1', '9', '4', '8', '2', '6', '6', '2', '9', '4', '4', '0', '6', '4', '8', '3', '1', '6', '8', '9', '2', '7', '0', '4', '3', '7', '4', '5', '0', '7', '"', ',']

theorem object_fragment0329023_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0329023Field007Chars00 ++ tail)) fragment0329023Acc00700 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0329023Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_007"
  err.flush

noncomputable def fragment0329023Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0329023Field008Value00 : SourceJson := .str (String.ofList ['3', '1', '1', '1', '3', '1', '3', '8', '8', '1', '0', '4', '8'])
noncomputable def fragment0329023Acc00900 : List (String × SourceJson) := (fragment0329023Field008Key00, fragment0329023Field008Value00) :: fragment0329023Acc00800
noncomputable def fragment0329023Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '1', '1', '3', '1', '3', '8', '8', '1', '0', '4', '8', '"', ',']

theorem object_fragment0329023_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0329023Field008Chars00 ++ tail)) fragment0329023Acc00800 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0329023Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_008"
  err.flush

noncomputable def fragment0329023Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0329023Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '2', '4', '6', '9', '9', '0', '4', '7', '4', '9', '8', '0'])
noncomputable def fragment0329023Acc01000 : List (String × SourceJson) := (fragment0329023Field009Key00, fragment0329023Field009Value00) :: fragment0329023Acc00900
noncomputable def fragment0329023Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '2', '4', '6', '9', '9', '0', '4', '7', '4', '9', '8', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0329023_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0329023Field009Chars00 ++ tail)) fragment0329023Acc00900 =
      .ok (.obj (fragment0329023Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0329023_object_field_009"
  err.flush

noncomputable def fragment0329023Chars : List Char := '{' :: (fragment0329023Field000Chars00 ++ fragment0329023Field001Chars00 ++ fragment0329023Field002Chars00 ++ fragment0329023Field003Chars00 ++ fragment0329023Field004Chars00 ++ fragment0329023Field005Chars00 ++ fragment0329023Field006Chars00 ++ fragment0329023Field007Chars00 ++ fragment0329023Field008Chars00 ++ fragment0329023Field009Chars00)
noncomputable def fragment0329023Value : SourceJson := .obj (fragment0329023Acc01000.reverse)

theorem value_fragment0329023 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 240) (fragment0329023Chars ++ tail) =
      .ok (fragment0329023Value, tail) := by
  have hinput : fragment0329023Chars ++ tail = '{' :: (fragment0329023Field000Chars00 ++ (fragment0329023Field001Chars00 ++ (fragment0329023Field002Chars00 ++ (fragment0329023Field003Chars00 ++ (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0329023Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 240) (fragment0329023Chars ++ tail) =
        SourceJson.value (fuel + 240) ('{' :: (fragment0329023Field000Chars00 ++ (fragment0329023Field001Chars00 ++ (fragment0329023Field002Chars00 ++ (fragment0329023Field003Chars00 ++ (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 240)) hinput
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0329023Field000Chars00 ++ (fragment0329023Field001Chars00 ++ (fragment0329023Field002Chars00 ++ (fragment0329023Field003Chars00 ++ (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))))))))))) fragment0329023Acc00000 := by rfl
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0329023Field001Chars00 ++ (fragment0329023Field002Chars00 ++ (fragment0329023Field003Chars00 ++ (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail))))))))))) fragment0329023Acc00100 := object_fragment0329023_field_000 fuel (fragment0329023Field001Chars00 ++ (fragment0329023Field002Chars00 ++ (fragment0329023Field003Chars00 ++ (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0329023Field002Chars00 ++ (fragment0329023Field003Chars00 ++ (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))))))))) fragment0329023Acc00200 := object_fragment0329023_field_001 fuel (fragment0329023Field002Chars00 ++ (fragment0329023Field003Chars00 ++ (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0329023Field003Chars00 ++ (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail))))))))) fragment0329023Acc00300 := object_fragment0329023_field_002 fuel (fragment0329023Field003Chars00 ++ (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))))))) fragment0329023Acc00400 := object_fragment0329023_field_003 fuel (fragment0329023Field004Chars00 ++ (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail))))))) fragment0329023Acc00500 := object_fragment0329023_field_004 fuel (fragment0329023Field005Chars00 ++ (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))))) fragment0329023Acc00600 := object_fragment0329023_field_005 fuel (fragment0329023Field006Chars00 ++ (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail))))) fragment0329023Acc00700 := object_fragment0329023_field_006 fuel (fragment0329023Field007Chars00 ++ (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))) fragment0329023Acc00800 := object_fragment0329023_field_007 fuel (fragment0329023Field008Chars00 ++ (fragment0329023Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0329023Field009Chars00 ++ (tail))) fragment0329023Acc00900 := object_fragment0329023_field_008 fuel (fragment0329023Field009Chars00 ++ (tail))
    _ = .ok (fragment0329023Value, tail) := object_fragment0329023_field_009 fuel (tail)

noncomputable def fragment0330628Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0330628Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0330628Field000Value00 : SourceJson := .number (String.ofList ['1', '1', '0'])
noncomputable def fragment0330628Acc00100 : List (String × SourceJson) := (fragment0330628Field000Key00, fragment0330628Field000Value00) :: fragment0330628Acc00000
noncomputable def fragment0330628Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '0', ',']

theorem object_fragment0330628_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0330628Field000Chars00 ++ tail)) fragment0330628Acc00000 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0330628Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_000"
  err.flush

noncomputable def fragment0330628Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0330628Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7'])]
noncomputable def fragment0330628Acc00200 : List (String × SourceJson) := (fragment0330628Field001Key00, fragment0330628Field001Value00) :: fragment0330628Acc00100
noncomputable def fragment0330628Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0330628_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0330628Field001Chars00 ++ tail)) fragment0330628Acc00100 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0330628Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_001"
  err.flush

noncomputable def fragment0330628Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0330628Field002Value00 : SourceJson := .str (String.ofList ['8', '0', '3', '0', '1', '3', '2', '9', '7', '7', '3', '5', '8', '8', '4', '7', '8', '3', '7', '4', '0', '5', '2', '2', '4', '8', '7', '9', '1', '5', '0', '7', '7', '2', '8', '4', '1', '/', '1', '8', '0', '0', '4', '0', '9', '0', '5', '0', '3', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0330628Acc00300 : List (String × SourceJson) := (fragment0330628Field002Key00, fragment0330628Field002Value00) :: fragment0330628Acc00200
noncomputable def fragment0330628Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '0', '3', '0', '1', '3', '2', '9', '7', '7', '3', '5', '8', '8', '4', '7', '8', '3', '7', '4', '0', '5', '2', '2', '4', '8', '7', '9', '1', '5', '0', '7', '7', '2', '8', '4', '1', '/', '1', '8', '0', '0', '4', '0', '9', '0', '5', '0', '3', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0330628_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0330628Field002Chars00 ++ tail)) fragment0330628Acc00200 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0330628Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_002"
  err.flush

noncomputable def fragment0330628Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0330628Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0330628Acc00400 : List (String × SourceJson) := (fragment0330628Field003Key00, fragment0330628Field003Value00) :: fragment0330628Acc00300
noncomputable def fragment0330628Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0330628_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0330628Field003Chars00 ++ tail)) fragment0330628Acc00300 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0330628Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_003"
  err.flush

noncomputable def fragment0330628Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0330628Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0330628Acc00500 : List (String × SourceJson) := (fragment0330628Field004Key00, fragment0330628Field004Value00) :: fragment0330628Acc00400
noncomputable def fragment0330628Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0330628_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0330628Field004Chars00 ++ tail)) fragment0330628Acc00400 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0330628Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_004"
  err.flush

noncomputable def fragment0330628Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0330628Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '6', '7', '2', '3', '0', '2', '1', '0', '6', '5', '4', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '5', '5', '6', '9', '4', '6', '8', '6', '9', '0', '1', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '6', '2', '1', '1', '5', '3', '1', '8', '6', '4', '7', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '2', '1', '4', '0', '1', '1', '5', '1', '3', '7', '9', '/', '5', '6', '9', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '8', '0', '9', '0', '1', '5', '6', '6', '6', '3', '/', '1', '1', '3', '9', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '1', '5', '4', '1', '4', '4', '3', '3', '1', '6', '1', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '2', '7', '3', '8', '4', '0', '1', '9', '0', '9', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '9', '8', '2', '9', '5', '1', '8', '1', '9', '9', '/', '1', '0', '6', '7', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '2', '2', '9', '5', '0', '2', '9', '9', '5', '9', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '1', '1', '4', '6', '9', '4', '5', '4', '2', '5', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0330628Acc00600 : List (String × SourceJson) := (fragment0330628Field005Key00, fragment0330628Field005Value00) :: fragment0330628Acc00500
noncomputable def fragment0330628Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '7', '2', '3', '0', '2', '1', '0', '6', '5', '4', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '5', '5', '6', '9', '4', '6', '8', '6', '9', '0', '1', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '6', '2', '1', '1', '5', '3', '1', '8', '6', '4', '7', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '2', '1', '4', '0', '1', '1', '5', '1', '3', '7', '9', '/', '5', '6', '9', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '8', '0', '9', '0', '1', '5', '6', '6', '6', '3', '/', '1', '1', '3', '9', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '5', '1', '5', '4', '1', '4', '4', '3', '3', '1', '6', '1', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '6', '2', '7', '3', '8', '4', '0', '1', '9', '0', '9', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '9', '8', '2', '9', '5', '1', '8', '1', '9', '9', '/', '1', '0', '6', '7', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '2', '2', '9', '5', '0', '2', '9', '9', '5', '9', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '1', '1', '4', '6', '9', '4', '5', '4', '2', '5', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0330628_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0330628Field005Chars00 ++ tail)) fragment0330628Acc00500 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0330628Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_005"
  err.flush

noncomputable def fragment0330628Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0330628Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '7', '2', '0', '6', '8', '1', '1', '9', '7', '8', '1', '3', '4', '8', '8', '3', '2', '3', '0', '4', '5', '2', '2', '6', '8', '9', '3', '4', '4', '5', '8', '2', '3', '5', '2', '7', '8', '3', '1', '2', '9', '6', '0', '0', '0', '0', '0', '/', '4', '4', '5', '3', '4', '6', '4', '1', '9', '6', '1', '0', '6', '0', '1', '9', '0', '3', '0', '7', '9', '9', '8', '1', '5', '1', '9', '9', '8', '1', '1', '1', '2', '8', '2', '9', '5', '7', '8', '3', '9', '0', '8', '7', '4', '3', '6', '6', '7', '5', '8', '3', '7', '6', '2', '3', '3', '0', '8', '6', '6', '1', '9', '3', '7'])
noncomputable def fragment0330628Acc00700 : List (String × SourceJson) := (fragment0330628Field006Key00, fragment0330628Field006Value00) :: fragment0330628Acc00600
noncomputable def fragment0330628Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '7', '2', '0', '6', '8', '1', '1', '9', '7', '8', '1', '3', '4', '8', '8', '3', '2', '3', '0', '4', '5', '2', '2', '6', '8', '9', '3', '4', '4', '5', '8', '2', '3', '5', '2', '7', '8', '3', '1', '2', '9', '6', '0', '0', '0', '0', '0', '/', '4', '4', '5', '3', '4', '6', '4', '1', '9', '6', '1', '0', '6', '0', '1', '9', '0', '3', '0', '7', '9', '9', '8', '1', '5', '1', '9', '9', '8', '1', '1', '1', '2', '8', '2', '9', '5', '7', '8', '3', '9', '0', '8', '7', '4', '3', '6', '6', '7', '5', '8', '3', '7', '6', '2', '3', '3', '0', '8', '6', '6', '1', '9', '3', '7', '"', ',']

theorem object_fragment0330628_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0330628Field006Chars00 ++ tail)) fragment0330628Acc00600 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0330628Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_006"
  err.flush

noncomputable def fragment0330628Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0330628Field007Value00 : SourceJson := .str (String.ofList ['2', '0', '0', '7', '0', '0', '3', '1', '8', '8', '2', '8', '2', '4', '8', '0', '3', '2', '9', '9', '3', '2', '5', '0', '6', '4', '9', '9', '8', '5', '3', '4', '1', '2', '4', '3', '9', '0', '7', '3', '4', '6', '4', '8', '8', '3', '9', '6', '6', '9', '4', '8', '3', '9', '8', '4', '5', '5', '5', '2', '8', '0', '2', '9', '4', '5', '1', '8', '4', '4', '1', '5', '6', '4', '3', '5', '9', '4', '9', '5', '7', '7', '9', '4', '3', '4', '3', '1', '0', '6', '6', '4', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '9', '2', '7', '3', '2', '2', '9', '4', '4', '2', '0', '1', '1', '1', '1', '8', '2', '4', '6', '1', '2', '9', '9', '7', '5', '3', '0', '2', '8', '2', '0', '7', '8', '9', '5', '9', '3', '0', '6', '8', '6', '7', '1', '7', '7', '4', '6', '2', '2', '3', '9', '2', '8', '3', '0', '7', '8', '8', '5', '5', '8', '2', '7', '6', '2', '2', '8', '7', '7', '7', '0', '1', '3', '9', '7', '6', '5', '6', '8', '0', '4', '7', '9', '1', '8', '6', '4', '8', '3', '3', '2', '7', '5', '9', '0', '7', '6', '1', '4', '6', '9', '1', '7', '5', '6', '3', '3', '8', '1', '7', '9', '2', '6', '1', '5', '3', '7', '5', '8', '7', '9'])
noncomputable def fragment0330628Acc00800 : List (String × SourceJson) := (fragment0330628Field007Key00, fragment0330628Field007Value00) :: fragment0330628Acc00700
noncomputable def fragment0330628Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '0', '0', '7', '0', '0', '3', '1', '8', '8', '2', '8', '2', '4', '8', '0', '3', '2', '9', '9', '3', '2', '5', '0', '6', '4', '9', '9', '8', '5', '3', '4', '1', '2', '4', '3', '9', '0', '7', '3', '4', '6', '4', '8', '8', '3', '9', '6', '6', '9', '4', '8', '3', '9', '8', '4', '5', '5', '5', '2', '8', '0', '2', '9', '4', '5', '1', '8', '4', '4', '1', '5', '6', '4', '3', '5', '9', '4', '9', '5', '7', '7', '9', '4', '3', '4', '3', '1', '0', '6', '6', '4', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '9', '2', '7', '3', '2', '2', '9', '4', '4', '2', '0', '1', '1', '1', '1', '8', '2', '4', '6', '1', '2', '9', '9', '7', '5', '3', '0', '2', '8', '2', '0', '7', '8', '9', '5', '9', '3', '0', '6', '8', '6', '7', '1', '7', '7', '4', '6', '2', '2', '3', '9', '2', '8', '3', '0', '7', '8', '8', '5', '5', '8', '2', '7', '6', '2', '2', '8', '7', '7', '7', '0', '1', '3', '9', '7', '6', '5', '6', '8', '0', '4', '7', '9', '1', '8', '6', '4', '8', '3', '3', '2', '7', '5', '9', '0', '7', '6', '1', '4', '6', '9', '1', '7', '5', '6', '3', '3', '8', '1', '7', '9', '2', '6', '1', '5', '3', '7', '5', '8', '7', '9', '"', ',']

theorem object_fragment0330628_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0330628Field007Chars00 ++ tail)) fragment0330628Acc00700 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0330628Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_007"
  err.flush

noncomputable def fragment0330628Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0330628Field008Value00 : SourceJson := .str (String.ofList ['3', '5', '0', '8', '3', '5', '4', '9', '9', '2', '9', '4', '7'])
noncomputable def fragment0330628Acc00900 : List (String × SourceJson) := (fragment0330628Field008Key00, fragment0330628Field008Value00) :: fragment0330628Acc00800
noncomputable def fragment0330628Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '5', '0', '8', '3', '5', '4', '9', '9', '2', '9', '4', '7', '"', ',']

theorem object_fragment0330628_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0330628Field008Chars00 ++ tail)) fragment0330628Acc00800 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0330628Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_008"
  err.flush

noncomputable def fragment0330628Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0330628Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '3', '3', '1', '6', '7', '3', '4', '6', '1', '9', '9', '8'])
noncomputable def fragment0330628Acc01000 : List (String × SourceJson) := (fragment0330628Field009Key00, fragment0330628Field009Value00) :: fragment0330628Acc00900
noncomputable def fragment0330628Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '3', '3', '1', '6', '7', '3', '4', '6', '1', '9', '9', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0330628_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0330628Field009Chars00 ++ tail)) fragment0330628Acc00900 =
      .ok (.obj (fragment0330628Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0330628_object_field_009"
  err.flush

noncomputable def fragment0330628Chars : List Char := '{' :: (fragment0330628Field000Chars00 ++ fragment0330628Field001Chars00 ++ fragment0330628Field002Chars00 ++ fragment0330628Field003Chars00 ++ fragment0330628Field004Chars00 ++ fragment0330628Field005Chars00 ++ fragment0330628Field006Chars00 ++ fragment0330628Field007Chars00 ++ fragment0330628Field008Chars00 ++ fragment0330628Field009Chars00)
noncomputable def fragment0330628Value : SourceJson := .obj (fragment0330628Acc01000.reverse)

theorem value_fragment0330628 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 242) (fragment0330628Chars ++ tail) =
      .ok (fragment0330628Value, tail) := by
  have hinput : fragment0330628Chars ++ tail = '{' :: (fragment0330628Field000Chars00 ++ (fragment0330628Field001Chars00 ++ (fragment0330628Field002Chars00 ++ (fragment0330628Field003Chars00 ++ (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0330628Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 242) (fragment0330628Chars ++ tail) =
        SourceJson.value (fuel + 242) ('{' :: (fragment0330628Field000Chars00 ++ (fragment0330628Field001Chars00 ++ (fragment0330628Field002Chars00 ++ (fragment0330628Field003Chars00 ++ (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 242)) hinput
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0330628Field000Chars00 ++ (fragment0330628Field001Chars00 ++ (fragment0330628Field002Chars00 ++ (fragment0330628Field003Chars00 ++ (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))))))))))) fragment0330628Acc00000 := by rfl
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0330628Field001Chars00 ++ (fragment0330628Field002Chars00 ++ (fragment0330628Field003Chars00 ++ (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail))))))))))) fragment0330628Acc00100 := object_fragment0330628_field_000 fuel (fragment0330628Field001Chars00 ++ (fragment0330628Field002Chars00 ++ (fragment0330628Field003Chars00 ++ (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0330628Field002Chars00 ++ (fragment0330628Field003Chars00 ++ (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))))))))) fragment0330628Acc00200 := object_fragment0330628_field_001 fuel (fragment0330628Field002Chars00 ++ (fragment0330628Field003Chars00 ++ (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0330628Field003Chars00 ++ (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail))))))))) fragment0330628Acc00300 := object_fragment0330628_field_002 fuel (fragment0330628Field003Chars00 ++ (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))))))) fragment0330628Acc00400 := object_fragment0330628_field_003 fuel (fragment0330628Field004Chars00 ++ (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail))))))) fragment0330628Acc00500 := object_fragment0330628_field_004 fuel (fragment0330628Field005Chars00 ++ (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))))) fragment0330628Acc00600 := object_fragment0330628_field_005 fuel (fragment0330628Field006Chars00 ++ (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail))))) fragment0330628Acc00700 := object_fragment0330628_field_006 fuel (fragment0330628Field007Chars00 ++ (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))) fragment0330628Acc00800 := object_fragment0330628_field_007 fuel (fragment0330628Field008Chars00 ++ (fragment0330628Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0330628Field009Chars00 ++ (tail))) fragment0330628Acc00900 := object_fragment0330628_field_008 fuel (fragment0330628Field009Chars00 ++ (tail))
    _ = .ok (fragment0330628Value, tail) := object_fragment0330628_field_009 fuel (tail)

noncomputable def fragment0332239Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0332239Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0332239Field000Value00 : SourceJson := .number (String.ofList ['1', '1', '1'])
noncomputable def fragment0332239Acc00100 : List (String × SourceJson) := (fragment0332239Field000Key00, fragment0332239Field000Value00) :: fragment0332239Acc00000
noncomputable def fragment0332239Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', '1', ',']

theorem object_fragment0332239_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0332239Field000Chars00 ++ tail)) fragment0332239Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0332239Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_000"
  err.flush

noncomputable def fragment0332239Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0332239Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7'])]
noncomputable def fragment0332239Acc00200 : List (String × SourceJson) := (fragment0332239Field001Key00, fragment0332239Field001Value00) :: fragment0332239Acc00100
noncomputable def fragment0332239Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0332239_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0332239Field001Chars00 ++ tail)) fragment0332239Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0332239Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_001"
  err.flush

noncomputable def fragment0332239Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0332239Field002Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '8', '2', '8', '9', '6', '0', '9', '1', '6', '8', '2', '6', '6', '1', '5', '9', '6', '7', '8', '4', '4', '0', '3', '9', '4', '0', '9', '2', '5', '6', '5', '4', '3', '9', '3', '3', '/', '2', '7', '4', '3', '4', '8', '0', '4', '5', '7', '6', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0332239Acc00300 : List (String × SourceJson) := (fragment0332239Field002Key00, fragment0332239Field002Value00) :: fragment0332239Acc00200
noncomputable def fragment0332239Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '4', '5', '8', '2', '8', '9', '6', '0', '9', '1', '6', '8', '2', '6', '6', '1', '5', '9', '6', '7', '8', '4', '4', '0', '3', '9', '4', '0', '9', '2', '5', '6', '5', '4', '3', '9', '3', '3', '/', '2', '7', '4', '3', '4', '8', '0', '4', '5', '7', '6', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0332239_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0332239Field002Chars00 ++ tail)) fragment0332239Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0332239Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_002"
  err.flush

noncomputable def fragment0332239Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0332239Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0332239Acc00400 : List (String × SourceJson) := (fragment0332239Field003Key00, fragment0332239Field003Value00) :: fragment0332239Acc00300
noncomputable def fragment0332239Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0332239_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0332239Field003Chars00 ++ tail)) fragment0332239Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0332239Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_003"
  err.flush

noncomputable def fragment0332239Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0332239Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0332239Acc00500 : List (String × SourceJson) := (fragment0332239Field004Key00, fragment0332239Field004Value00) :: fragment0332239Acc00400
noncomputable def fragment0332239Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0332239_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0332239Field004Chars00 ++ tail)) fragment0332239Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0332239Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_004"
  err.flush

noncomputable def fragment0332239Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0332239Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '7', '4', '0', '2', '2', '6', '8', '8', '0', '7', '2', '2', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '4', '6', '3', '9', '8', '2', '0', '8', '6', '8', '4', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '9', '5', '2', '5', '6', '5', '6', '5', '6', '5', '0', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '1', '8', '9', '7', '0', '8', '9', '1', '6', '7', '/', '1', '1', '8', '6', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '9', '6', '1', '3', '0', '8', '6', '5', '0', '9', '1', '/', '2', '8', '4', '7', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '4', '3', '5', '0', '8', '3', '1', '0', '2', '5', '3', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '1', '4', '7', '8', '8', '5', '0', '7', '1', '/', '3', '8', '1', '3', '9', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '9', '9', '1', '7', '9', '9', '1', '8', '4', '1', '1', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '4', '1', '1', '6', '7', '4', '1', '1', '8', '8', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '4', '1', '1', '1', '0', '4', '5', '6', '5', '2', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0332239Acc00600 : List (String × SourceJson) := (fragment0332239Field005Key00, fragment0332239Field005Value00) :: fragment0332239Acc00500
noncomputable def fragment0332239Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '4', '0', '2', '2', '6', '8', '8', '0', '7', '2', '2', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '4', '6', '3', '9', '8', '2', '0', '8', '6', '8', '4', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '9', '5', '2', '5', '6', '5', '6', '5', '6', '5', '0', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '5', '1', '8', '9', '7', '0', '8', '9', '1', '6', '7', '/', '1', '1', '8', '6', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '9', '6', '1', '3', '0', '8', '6', '5', '0', '9', '1', '/', '2', '8', '4', '7', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '4', '3', '5', '0', '8', '3', '1', '0', '2', '5', '3', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '1', '4', '7', '8', '8', '5', '0', '7', '1', '/', '3', '8', '1', '3', '9', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '9', '9', '1', '7', '9', '9', '1', '8', '4', '1', '1', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '4', '1', '1', '6', '7', '4', '1', '1', '8', '8', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '4', '1', '1', '1', '0', '4', '5', '6', '5', '2', '3', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0332239_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0332239Field005Chars00 ++ tail)) fragment0332239Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0332239Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_005"
  err.flush

noncomputable def fragment0332239Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0332239Field006Value00 : SourceJson := .str (String.ofList ['2', '1', '2', '6', '4', '0', '7', '9', '1', '0', '1', '8', '7', '9', '2', '5', '6', '3', '7', '2', '6', '7', '4', '3', '7', '2', '1', '7', '5', '2', '6', '8', '6', '2', '4', '8', '0', '4', '8', '9', '9', '1', '8', '1', '6', '0', '0', '0', '0', '/', '4', '0', '2', '9', '3', '2', '4', '7', '4', '8', '8', '5', '7', '8', '2', '6', '7', '4', '2', '1', '5', '2', '2', '1', '3', '7', '5', '2', '2', '1', '0', '0', '6', '8', '4', '5', '8', '0', '9', '0', '2', '0', '3', '1', '4', '9', '0', '3', '2', '5', '7', '5', '7', '8', '4', '9', '6', '6', '0', '2', '1', '7', '9', '4', '3'])
noncomputable def fragment0332239Acc00700 : List (String × SourceJson) := (fragment0332239Field006Key00, fragment0332239Field006Value00) :: fragment0332239Acc00600
noncomputable def fragment0332239Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '1', '2', '6', '4', '0', '7', '9', '1', '0', '1', '8', '7', '9', '2', '5', '6', '3', '7', '2', '6', '7', '4', '3', '7', '2', '1', '7', '5', '2', '6', '8', '6', '2', '4', '8', '0', '4', '8', '9', '9', '1', '8', '1', '6', '0', '0', '0', '0', '/', '4', '0', '2', '9', '3', '2', '4', '7', '4', '8', '8', '5', '7', '8', '2', '6', '7', '4', '2', '1', '5', '2', '2', '1', '3', '7', '5', '2', '2', '1', '0', '0', '6', '8', '4', '5', '8', '0', '9', '0', '2', '0', '3', '1', '4', '9', '0', '3', '2', '5', '7', '5', '7', '8', '4', '9', '6', '6', '0', '2', '1', '7', '9', '4', '3', '"', ',']

theorem object_fragment0332239_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0332239Field006Chars00 ++ tail)) fragment0332239Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0332239Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_006"
  err.flush

noncomputable def fragment0332239Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0332239Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '7', '1', '1', '1', '3', '7', '4', '4', '9', '0', '4', '6', '1', '3', '1', '1', '2', '2', '5', '4', '7', '1', '7', '3', '1', '4', '8', '1', '3', '3', '1', '6', '8', '2', '7', '3', '7', '7', '6', '3', '5', '6', '2', '0', '1', '9', '6', '1', '5', '1', '3', '9', '5', '2', '1', '5', '7', '1', '6', '6', '7', '3', '0', '1', '2', '8', '9', '5', '2', '0', '7', '9', '3', '7', '5', '1', '2', '1', '4', '3', '7', '2', '7', '2', '0', '1', '7', '6', '9', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '2', '8', '2', '4', '8', '9', '3', '8', '1', '6', '5', '2', '7', '5', '3', '4', '0', '5', '3', '4', '9', '5', '9', '5', '7', '4', '4', '7', '6', '7', '5', '7', '7', '8', '5', '6', '9', '3', '2', '6', '5', '9', '2', '4', '2', '0', '0', '5', '2', '8', '4', '7', '5', '3', '8', '5', '5', '0', '3', '5', '9', '9', '8', '2', '4', '2', '8', '5', '2', '9', '7', '9', '6', '1', '8', '6', '0', '1', '7', '5', '0', '2', '3', '4', '6', '0', '1', '7', '1', '7', '5', '7', '6', '0', '3', '6', '9', '0', '5', '5', '5', '0', '2', '6', '3', '3', '1', '8', '3', '1', '4', '7', '3', '0', '3', '7', '7', '3', '7', '0', '8', '9', '5', '7', '2', '2', '1', '5', '7', '6', '3'])
noncomputable def fragment0332239Acc00800 : List (String × SourceJson) := (fragment0332239Field007Key00, fragment0332239Field007Value00) :: fragment0332239Acc00700
noncomputable def fragment0332239Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '7', '1', '1', '1', '3', '7', '4', '4', '9', '0', '4', '6', '1', '3', '1', '1', '2', '2', '5', '4', '7', '1', '7', '3', '1', '4', '8', '1', '3', '3', '1', '6', '8', '2', '7', '3', '7', '7', '6', '3', '5', '6', '2', '0', '1', '9', '6', '1', '5', '1', '3', '9', '5', '2', '1', '5', '7', '1', '6', '6', '7', '3', '0', '1', '2', '8', '9', '5', '2', '0', '7', '9', '3', '7', '5', '1', '2', '1', '4', '3', '7', '2', '7', '2', '0', '1', '7', '6', '9', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '2', '8', '2', '4', '8', '9', '3', '8', '1', '6', '5', '2', '7', '5', '3', '4', '0', '5', '3', '4', '9', '5', '9', '5', '7', '4', '4', '7', '6', '7', '5', '7', '7', '8', '5', '6', '9', '3', '2', '6', '5', '9', '2', '4', '2', '0', '0', '5', '2', '8', '4', '7', '5', '3', '8', '5', '5', '0', '3', '5', '9', '9', '8', '2', '4', '2', '8', '5', '2', '9', '7', '9', '6', '1', '8', '6', '0', '1', '7', '5', '0', '2', '3', '4', '6', '0', '1', '7', '1', '7', '5', '7', '6', '0', '3', '6', '9', '0', '5', '5', '5', '0', '2', '6', '3', '3', '1', '8', '3', '1', '4', '7', '3', '0', '3', '7', '7', '3', '7', '0', '8', '9', '5', '7', '2', '2', '1', '5', '7', '6', '3', '"', ',']

theorem object_fragment0332239_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0332239Field007Chars00 ++ tail)) fragment0332239Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0332239Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_007"
  err.flush

noncomputable def fragment0332239Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0332239Field008Value00 : SourceJson := .str (String.ofList ['4', '1', '8', '1', '1', '3', '2', '1', '2', '4', '6', '2', '5'])
noncomputable def fragment0332239Acc00900 : List (String × SourceJson) := (fragment0332239Field008Key00, fragment0332239Field008Value00) :: fragment0332239Acc00800
noncomputable def fragment0332239Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '8', '1', '1', '3', '2', '1', '2', '4', '6', '2', '5', '"', ',']

theorem object_fragment0332239_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0332239Field008Chars00 ++ tail)) fragment0332239Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0332239Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_008"
  err.flush

noncomputable def fragment0332239Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0332239Field009Value00 : SourceJson := .str (String.ofList ['1', '5', '0', '2', '8', '8', '6', '9', '8', '6', '9', '1', '7', '6'])
noncomputable def fragment0332239Acc01000 : List (String × SourceJson) := (fragment0332239Field009Key00, fragment0332239Field009Value00) :: fragment0332239Acc00900
noncomputable def fragment0332239Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '0', '2', '8', '8', '6', '9', '8', '6', '9', '1', '7', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0332239_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0332239Field009Chars00 ++ tail)) fragment0332239Acc00900 =
      .ok (.obj (fragment0332239Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0332239_object_field_009"
  err.flush

noncomputable def fragment0332239Chars : List Char := '{' :: (fragment0332239Field000Chars00 ++ fragment0332239Field001Chars00 ++ fragment0332239Field002Chars00 ++ fragment0332239Field003Chars00 ++ fragment0332239Field004Chars00 ++ fragment0332239Field005Chars00 ++ fragment0332239Field006Chars00 ++ fragment0332239Field007Chars00 ++ fragment0332239Field008Chars00 ++ fragment0332239Field009Chars00)
noncomputable def fragment0332239Value : SourceJson := .obj (fragment0332239Acc01000.reverse)

theorem value_fragment0332239 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0332239Chars ++ tail) =
      .ok (fragment0332239Value, tail) := by
  have hinput : fragment0332239Chars ++ tail = '{' :: (fragment0332239Field000Chars00 ++ (fragment0332239Field001Chars00 ++ (fragment0332239Field002Chars00 ++ (fragment0332239Field003Chars00 ++ (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0332239Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0332239Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0332239Field000Chars00 ++ (fragment0332239Field001Chars00 ++ (fragment0332239Field002Chars00 ++ (fragment0332239Field003Chars00 ++ (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0332239Field000Chars00 ++ (fragment0332239Field001Chars00 ++ (fragment0332239Field002Chars00 ++ (fragment0332239Field003Chars00 ++ (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))))))))))) fragment0332239Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0332239Field001Chars00 ++ (fragment0332239Field002Chars00 ++ (fragment0332239Field003Chars00 ++ (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail))))))))))) fragment0332239Acc00100 := object_fragment0332239_field_000 fuel (fragment0332239Field001Chars00 ++ (fragment0332239Field002Chars00 ++ (fragment0332239Field003Chars00 ++ (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0332239Field002Chars00 ++ (fragment0332239Field003Chars00 ++ (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))))))))) fragment0332239Acc00200 := object_fragment0332239_field_001 fuel (fragment0332239Field002Chars00 ++ (fragment0332239Field003Chars00 ++ (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0332239Field003Chars00 ++ (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail))))))))) fragment0332239Acc00300 := object_fragment0332239_field_002 fuel (fragment0332239Field003Chars00 ++ (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))))))) fragment0332239Acc00400 := object_fragment0332239_field_003 fuel (fragment0332239Field004Chars00 ++ (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail))))))) fragment0332239Acc00500 := object_fragment0332239_field_004 fuel (fragment0332239Field005Chars00 ++ (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))))) fragment0332239Acc00600 := object_fragment0332239_field_005 fuel (fragment0332239Field006Chars00 ++ (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail))))) fragment0332239Acc00700 := object_fragment0332239_field_006 fuel (fragment0332239Field007Chars00 ++ (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))) fragment0332239Acc00800 := object_fragment0332239_field_007 fuel (fragment0332239Field008Chars00 ++ (fragment0332239Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0332239Field009Chars00 ++ (tail))) fragment0332239Acc00900 := object_fragment0332239_field_008 fuel (fragment0332239Field009Chars00 ++ (tail))
    _ = .ok (fragment0332239Value, tail) := object_fragment0332239_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0104_before_reader"
  err.flush

noncomputable def chunk0104LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0104SuffixChars00 : List Char := [',']
noncomputable def chunk0104Chars00 : List Char := chunk0104LeadChars00 ++ fragment0320757Chars ++ chunk0104SuffixChars00
noncomputable def chunk0104Push00 (acc : List SourceJson) : List SourceJson := fragment0320757Value :: acc

noncomputable def chunk0104AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0104_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 553)
      (SourceJson.white (chunk0104LeadChars00 ++ (fragment0320757Chars ++ rest))) acc =
      (SourceJson.value (fuel + 552) (fragment0320757Chars ++ rest)).bind
        (chunk0104AfterValue00 (fuel + 552) acc) := by rfl

theorem array_chunk0104 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 553) (SourceJson.white (chunk0104Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 552) (SourceJson.white tail) (chunk0104Push00 acc) := by
  have hinput : chunk0104Chars00 ++ tail = chunk0104LeadChars00 ++ (fragment0320757Chars ++ (chunk0104SuffixChars00 ++ tail)) := by
    simp only [chunk0104Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 553) (SourceJson.white (chunk0104Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 553)
          (SourceJson.white (chunk0104LeadChars00 ++ (fragment0320757Chars ++ (chunk0104SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 553) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 552) (fragment0320757Chars ++ (chunk0104SuffixChars00 ++ tail))).bind
        (chunk0104AfterValue00 (fuel + 552) acc) := array_chunk0104_head fuel (chunk0104SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0320757Value, chunk0104SuffixChars00 ++ tail)).bind
        (chunk0104AfterValue00 (fuel + 552) acc) :=
      congrArg (fun result => result.bind (chunk0104AfterValue00 (fuel + 552) acc))
        (value_fragment0320757 (fuel + 326) (chunk0104SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 552) (SourceJson.white tail) (chunk0104Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0104_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0105_before_reader"
  err.flush

noncomputable def chunk0105LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0105SuffixChars00 : List Char := [',']
noncomputable def chunk0105Chars00 : List Char := chunk0105LeadChars00 ++ fragment0322342Chars ++ chunk0105SuffixChars00
noncomputable def chunk0105Push00 (acc : List SourceJson) : List SourceJson := fragment0322342Value :: acc

noncomputable def chunk0105AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0105_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 552)
      (SourceJson.white (chunk0105LeadChars00 ++ (fragment0322342Chars ++ rest))) acc =
      (SourceJson.value (fuel + 551) (fragment0322342Chars ++ rest)).bind
        (chunk0105AfterValue00 (fuel + 551) acc) := by rfl

theorem array_chunk0105 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 552) (SourceJson.white (chunk0105Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 551) (SourceJson.white tail) (chunk0105Push00 acc) := by
  have hinput : chunk0105Chars00 ++ tail = chunk0105LeadChars00 ++ (fragment0322342Chars ++ (chunk0105SuffixChars00 ++ tail)) := by
    simp only [chunk0105Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 552) (SourceJson.white (chunk0105Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 552)
          (SourceJson.white (chunk0105LeadChars00 ++ (fragment0322342Chars ++ (chunk0105SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 552) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 551) (fragment0322342Chars ++ (chunk0105SuffixChars00 ++ tail))).bind
        (chunk0105AfterValue00 (fuel + 551) acc) := array_chunk0105_head fuel (chunk0105SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0322342Value, chunk0105SuffixChars00 ++ tail)).bind
        (chunk0105AfterValue00 (fuel + 551) acc) :=
      congrArg (fun result => result.bind (chunk0105AfterValue00 (fuel + 551) acc))
        (value_fragment0322342 (fuel + 311) (chunk0105SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 551) (SourceJson.white tail) (chunk0105Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0105_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0106_before_reader"
  err.flush

noncomputable def chunk0106LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0106SuffixChars00 : List Char := [',']
noncomputable def chunk0106Chars00 : List Char := chunk0106LeadChars00 ++ fragment0323962Chars ++ chunk0106SuffixChars00
noncomputable def chunk0106Push00 (acc : List SourceJson) : List SourceJson := fragment0323962Value :: acc

noncomputable def chunk0106AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0106_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 551)
      (SourceJson.white (chunk0106LeadChars00 ++ (fragment0323962Chars ++ rest))) acc =
      (SourceJson.value (fuel + 550) (fragment0323962Chars ++ rest)).bind
        (chunk0106AfterValue00 (fuel + 550) acc) := by rfl

theorem array_chunk0106 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 551) (SourceJson.white (chunk0106Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 550) (SourceJson.white tail) (chunk0106Push00 acc) := by
  have hinput : chunk0106Chars00 ++ tail = chunk0106LeadChars00 ++ (fragment0323962Chars ++ (chunk0106SuffixChars00 ++ tail)) := by
    simp only [chunk0106Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 551) (SourceJson.white (chunk0106Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 551)
          (SourceJson.white (chunk0106LeadChars00 ++ (fragment0323962Chars ++ (chunk0106SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 551) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 550) (fragment0323962Chars ++ (chunk0106SuffixChars00 ++ tail))).bind
        (chunk0106AfterValue00 (fuel + 550) acc) := array_chunk0106_head fuel (chunk0106SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0323962Value, chunk0106SuffixChars00 ++ tail)).bind
        (chunk0106AfterValue00 (fuel + 550) acc) :=
      congrArg (fun result => result.bind (chunk0106AfterValue00 (fuel + 550) acc))
        (value_fragment0323962 (fuel + 177) (chunk0106SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 550) (SourceJson.white tail) (chunk0106Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0106_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0107_before_reader"
  err.flush

noncomputable def chunk0107LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0107SuffixChars00 : List Char := [',']
noncomputable def chunk0107Chars00 : List Char := chunk0107LeadChars00 ++ fragment0325840Chars ++ chunk0107SuffixChars00
noncomputable def chunk0107Push00 (acc : List SourceJson) : List SourceJson := fragment0325840Value :: acc

noncomputable def chunk0107AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0107_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 550)
      (SourceJson.white (chunk0107LeadChars00 ++ (fragment0325840Chars ++ rest))) acc =
      (SourceJson.value (fuel + 549) (fragment0325840Chars ++ rest)).bind
        (chunk0107AfterValue00 (fuel + 549) acc) := by rfl

theorem array_chunk0107 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 550) (SourceJson.white (chunk0107Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 549) (SourceJson.white tail) (chunk0107Push00 acc) := by
  have hinput : chunk0107Chars00 ++ tail = chunk0107LeadChars00 ++ (fragment0325840Chars ++ (chunk0107SuffixChars00 ++ tail)) := by
    simp only [chunk0107Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 550) (SourceJson.white (chunk0107Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 550)
          (SourceJson.white (chunk0107LeadChars00 ++ (fragment0325840Chars ++ (chunk0107SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 550) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 549) (fragment0325840Chars ++ (chunk0107SuffixChars00 ++ tail))).bind
        (chunk0107AfterValue00 (fuel + 549) acc) := array_chunk0107_head fuel (chunk0107SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0325840Value, chunk0107SuffixChars00 ++ tail)).bind
        (chunk0107AfterValue00 (fuel + 549) acc) :=
      congrArg (fun result => result.bind (chunk0107AfterValue00 (fuel + 549) acc))
        (value_fragment0325840 (fuel + 319) (chunk0107SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 549) (SourceJson.white tail) (chunk0107Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0107_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0108_before_reader"
  err.flush

noncomputable def chunk0108LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0108SuffixChars00 : List Char := [',']
noncomputable def chunk0108Chars00 : List Char := chunk0108LeadChars00 ++ fragment0327431Chars ++ chunk0108SuffixChars00
noncomputable def chunk0108Push00 (acc : List SourceJson) : List SourceJson := fragment0327431Value :: acc

noncomputable def chunk0108AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0108_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 549)
      (SourceJson.white (chunk0108LeadChars00 ++ (fragment0327431Chars ++ rest))) acc =
      (SourceJson.value (fuel + 548) (fragment0327431Chars ++ rest)).bind
        (chunk0108AfterValue00 (fuel + 548) acc) := by rfl

theorem array_chunk0108 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 549) (SourceJson.white (chunk0108Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 548) (SourceJson.white tail) (chunk0108Push00 acc) := by
  have hinput : chunk0108Chars00 ++ tail = chunk0108LeadChars00 ++ (fragment0327431Chars ++ (chunk0108SuffixChars00 ++ tail)) := by
    simp only [chunk0108Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 549) (SourceJson.white (chunk0108Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 549)
          (SourceJson.white (chunk0108LeadChars00 ++ (fragment0327431Chars ++ (chunk0108SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 549) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 548) (fragment0327431Chars ++ (chunk0108SuffixChars00 ++ tail))).bind
        (chunk0108AfterValue00 (fuel + 548) acc) := array_chunk0108_head fuel (chunk0108SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0327431Value, chunk0108SuffixChars00 ++ tail)).bind
        (chunk0108AfterValue00 (fuel + 548) acc) :=
      congrArg (fun result => result.bind (chunk0108AfterValue00 (fuel + 548) acc))
        (value_fragment0327431 (fuel + 312) (chunk0108SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 548) (SourceJson.white tail) (chunk0108Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0108_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0109_before_reader"
  err.flush

noncomputable def chunk0109LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0109SuffixChars00 : List Char := [',']
noncomputable def chunk0109Chars00 : List Char := chunk0109LeadChars00 ++ fragment0329023Chars ++ chunk0109SuffixChars00
noncomputable def chunk0109Push00 (acc : List SourceJson) : List SourceJson := fragment0329023Value :: acc

noncomputable def chunk0109AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0109_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 548)
      (SourceJson.white (chunk0109LeadChars00 ++ (fragment0329023Chars ++ rest))) acc =
      (SourceJson.value (fuel + 547) (fragment0329023Chars ++ rest)).bind
        (chunk0109AfterValue00 (fuel + 547) acc) := by rfl

theorem array_chunk0109 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 548) (SourceJson.white (chunk0109Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 547) (SourceJson.white tail) (chunk0109Push00 acc) := by
  have hinput : chunk0109Chars00 ++ tail = chunk0109LeadChars00 ++ (fragment0329023Chars ++ (chunk0109SuffixChars00 ++ tail)) := by
    simp only [chunk0109Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 548) (SourceJson.white (chunk0109Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 548)
          (SourceJson.white (chunk0109LeadChars00 ++ (fragment0329023Chars ++ (chunk0109SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 548) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 547) (fragment0329023Chars ++ (chunk0109SuffixChars00 ++ tail))).bind
        (chunk0109AfterValue00 (fuel + 547) acc) := array_chunk0109_head fuel (chunk0109SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0329023Value, chunk0109SuffixChars00 ++ tail)).bind
        (chunk0109AfterValue00 (fuel + 547) acc) :=
      congrArg (fun result => result.bind (chunk0109AfterValue00 (fuel + 547) acc))
        (value_fragment0329023 (fuel + 307) (chunk0109SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 547) (SourceJson.white tail) (chunk0109Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0109_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0110_before_reader"
  err.flush

noncomputable def chunk0110LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0110SuffixChars00 : List Char := [',']
noncomputable def chunk0110Chars00 : List Char := chunk0110LeadChars00 ++ fragment0330628Chars ++ chunk0110SuffixChars00
noncomputable def chunk0110Push00 (acc : List SourceJson) : List SourceJson := fragment0330628Value :: acc

noncomputable def chunk0110AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0110_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 547)
      (SourceJson.white (chunk0110LeadChars00 ++ (fragment0330628Chars ++ rest))) acc =
      (SourceJson.value (fuel + 546) (fragment0330628Chars ++ rest)).bind
        (chunk0110AfterValue00 (fuel + 546) acc) := by rfl

theorem array_chunk0110 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 547) (SourceJson.white (chunk0110Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 546) (SourceJson.white tail) (chunk0110Push00 acc) := by
  have hinput : chunk0110Chars00 ++ tail = chunk0110LeadChars00 ++ (fragment0330628Chars ++ (chunk0110SuffixChars00 ++ tail)) := by
    simp only [chunk0110Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 547) (SourceJson.white (chunk0110Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 547)
          (SourceJson.white (chunk0110LeadChars00 ++ (fragment0330628Chars ++ (chunk0110SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 547) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 546) (fragment0330628Chars ++ (chunk0110SuffixChars00 ++ tail))).bind
        (chunk0110AfterValue00 (fuel + 546) acc) := array_chunk0110_head fuel (chunk0110SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0330628Value, chunk0110SuffixChars00 ++ tail)).bind
        (chunk0110AfterValue00 (fuel + 546) acc) :=
      congrArg (fun result => result.bind (chunk0110AfterValue00 (fuel + 546) acc))
        (value_fragment0330628 (fuel + 304) (chunk0110SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 546) (SourceJson.white tail) (chunk0110Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0110_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0111_before_reader"
  err.flush

noncomputable def chunk0111LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0111SuffixChars00 : List Char := [',']
noncomputable def chunk0111Chars00 : List Char := chunk0111LeadChars00 ++ fragment0332239Chars ++ chunk0111SuffixChars00
noncomputable def chunk0111Push00 (acc : List SourceJson) : List SourceJson := fragment0332239Value :: acc

noncomputable def chunk0111AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0111_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 546)
      (SourceJson.white (chunk0111LeadChars00 ++ (fragment0332239Chars ++ rest))) acc =
      (SourceJson.value (fuel + 545) (fragment0332239Chars ++ rest)).bind
        (chunk0111AfterValue00 (fuel + 545) acc) := by rfl

theorem array_chunk0111 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 546) (SourceJson.white (chunk0111Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 545) (SourceJson.white tail) (chunk0111Push00 acc) := by
  have hinput : chunk0111Chars00 ++ tail = chunk0111LeadChars00 ++ (fragment0332239Chars ++ (chunk0111SuffixChars00 ++ tail)) := by
    simp only [chunk0111Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 546) (SourceJson.white (chunk0111Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 546)
          (SourceJson.white (chunk0111LeadChars00 ++ (fragment0332239Chars ++ (chunk0111SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 546) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 545) (fragment0332239Chars ++ (chunk0111SuffixChars00 ++ tail))).bind
        (chunk0111AfterValue00 (fuel + 545) acc) := array_chunk0111_head fuel (chunk0111SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0332239Value, chunk0111SuffixChars00 ++ tail)).bind
        (chunk0111AfterValue00 (fuel + 545) acc) :=
      congrArg (fun result => result.bind (chunk0111AfterValue00 (fuel + 545) acc))
        (value_fragment0332239 (fuel + 284) (chunk0111SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 545) (SourceJson.white tail) (chunk0111Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0111_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0104Chars00 ++ chunk0105Chars00 ++ chunk0106Chars00 ++ chunk0107Chars00 ++ chunk0108Chars00 ++ chunk0109Chars00 ++ chunk0110Chars00 ++ chunk0111Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0111Push00 (chunk0110Push00 (chunk0109Push00 (chunk0108Push00 (chunk0107Push00 (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 553) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 545) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0104Chars00 ++ (chunk0105Chars00 ++ (chunk0106Chars00 ++ (chunk0107Chars00 ++ (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 553) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 553) (SourceJson.white (chunk0104Chars00 ++ (chunk0105Chars00 ++ (chunk0106Chars00 ++ (chunk0107Chars00 ++ (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 553) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 552) (SourceJson.white (chunk0105Chars00 ++ (chunk0106Chars00 ++ (chunk0107Chars00 ++ (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail))))))))) (chunk0104Push00 (acc)) := array_chunk0104 fuel (chunk0105Chars00 ++ (chunk0106Chars00 ++ (chunk0107Chars00 ++ (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 551) (SourceJson.white (chunk0106Chars00 ++ (chunk0107Chars00 ++ (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail)))))))) (chunk0105Push00 (chunk0104Push00 (acc))) := array_chunk0105 fuel (chunk0106Chars00 ++ (chunk0107Chars00 ++ (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail))))))) (chunk0104Push00 (acc))
    _ = SourceJson.array (fuel + 550) (SourceJson.white (chunk0107Chars00 ++ (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail))))))) (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc)))) := array_chunk0106 fuel (chunk0107Chars00 ++ (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail)))))) (chunk0105Push00 (chunk0104Push00 (acc)))
    _ = SourceJson.array (fuel + 549) (SourceJson.white (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail)))))) (chunk0107Push00 (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc))))) := array_chunk0107 fuel (chunk0108Chars00 ++ (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail))))) (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc))))
    _ = SourceJson.array (fuel + 548) (SourceJson.white (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail))))) (chunk0108Push00 (chunk0107Push00 (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc)))))) := array_chunk0108 fuel (chunk0109Chars00 ++ (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail)))) (chunk0107Push00 (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc)))))
    _ = SourceJson.array (fuel + 547) (SourceJson.white (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail)))) (chunk0109Push00 (chunk0108Push00 (chunk0107Push00 (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc))))))) := array_chunk0109 fuel (chunk0110Chars00 ++ (chunk0111Chars00 ++ (tail))) (chunk0108Push00 (chunk0107Push00 (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc))))))
    _ = SourceJson.array (fuel + 546) (SourceJson.white (chunk0111Chars00 ++ (tail))) (chunk0110Push00 (chunk0109Push00 (chunk0108Push00 (chunk0107Push00 (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc)))))))) := array_chunk0110 fuel (chunk0111Chars00 ++ (tail)) (chunk0109Push00 (chunk0108Push00 (chunk0107Push00 (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc)))))))
    _ = SourceJson.array (fuel + 545) (SourceJson.white tail) (blockPush acc) := array_chunk0111 fuel (tail) (chunk0110Push00 (chunk0109Push00 (chunk0108Push00 (chunk0107Push00 (chunk0106Push00 (chunk0105Push00 (chunk0104Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 320751).take 13127 = blockChars := by rfl

theorem block_original_split : sourceRest 320751 = blockChars ++ sourceRest 333878 := by
  calc
    sourceRest 320751 = (sourceRest 320751).take 13127 ++ (sourceRest 320751).drop 13127 :=
      (List.take_append_drop 13127 (sourceRest 320751)).symm
    _ = blockChars ++ (sourceRest 320751).drop 13127 :=
      congrArg (fun part => part ++ (sourceRest 320751).drop 13127) block_original_prefix
    _ = blockChars ++ sourceRest 333878 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 320751 13127)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 553) (SourceJson.white (sourceRest 320751)) acc =
      SourceJson.array (fuel + 545) (SourceJson.white (sourceRest 333878)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 553) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 333878) acc)

#print axioms object_fragment0320757_field_000
#print axioms object_fragment0320757_field_001
#print axioms object_fragment0320757_field_002
#print axioms object_fragment0320757_field_003
#print axioms object_fragment0320757_field_004
#print axioms object_fragment0320757_field_005
#print axioms object_fragment0320757_field_006
#print axioms object_fragment0320757_field_007
#print axioms object_fragment0320757_field_008
#print axioms object_fragment0320757_field_009
#print axioms value_fragment0320757
#print axioms object_fragment0322342_field_000
#print axioms object_fragment0322342_field_001
#print axioms object_fragment0322342_field_002
#print axioms object_fragment0322342_field_003
#print axioms object_fragment0322342_field_004
#print axioms object_fragment0322342_field_005
#print axioms object_fragment0322342_field_006
#print axioms object_fragment0322342_field_007
#print axioms object_fragment0322342_field_008
#print axioms object_fragment0322342_field_009
#print axioms value_fragment0322342
#print axioms object_fragment0323962_field_000
#print axioms object_fragment0323962_field_001
#print axioms object_fragment0323962_field_002
#print axioms object_fragment0323962_field_003
#print axioms object_fragment0323962_field_004
#print axioms object_fragment0323962_field_005
#print axioms object_fragment0323962_field_006
#print axioms object_fragment0323962_field_007
#print axioms object_fragment0323962_field_008
#print axioms object_fragment0323962_field_009
#print axioms value_fragment0323962
#print axioms object_fragment0325840_field_000
#print axioms object_fragment0325840_field_001
#print axioms object_fragment0325840_field_002
#print axioms object_fragment0325840_field_003
#print axioms object_fragment0325840_field_004
#print axioms object_fragment0325840_field_005
#print axioms object_fragment0325840_field_006
#print axioms object_fragment0325840_field_007
#print axioms object_fragment0325840_field_008
#print axioms object_fragment0325840_field_009
#print axioms value_fragment0325840
#print axioms object_fragment0327431_field_000
#print axioms object_fragment0327431_field_001
#print axioms object_fragment0327431_field_002
#print axioms object_fragment0327431_field_003
#print axioms object_fragment0327431_field_004
#print axioms object_fragment0327431_field_005
#print axioms object_fragment0327431_field_006
#print axioms object_fragment0327431_field_007
#print axioms object_fragment0327431_field_008
#print axioms object_fragment0327431_field_009
#print axioms value_fragment0327431
#print axioms object_fragment0329023_field_000
#print axioms object_fragment0329023_field_001
#print axioms object_fragment0329023_field_002
#print axioms object_fragment0329023_field_003
#print axioms object_fragment0329023_field_004
#print axioms object_fragment0329023_field_005
#print axioms object_fragment0329023_field_006
#print axioms object_fragment0329023_field_007
#print axioms object_fragment0329023_field_008
#print axioms object_fragment0329023_field_009
#print axioms value_fragment0329023
#print axioms object_fragment0330628_field_000
#print axioms object_fragment0330628_field_001
#print axioms object_fragment0330628_field_002
#print axioms object_fragment0330628_field_003
#print axioms object_fragment0330628_field_004
#print axioms object_fragment0330628_field_005
#print axioms object_fragment0330628_field_006
#print axioms object_fragment0330628_field_007
#print axioms object_fragment0330628_field_008
#print axioms object_fragment0330628_field_009
#print axioms value_fragment0330628
#print axioms object_fragment0332239_field_000
#print axioms object_fragment0332239_field_001
#print axioms object_fragment0332239_field_002
#print axioms object_fragment0332239_field_003
#print axioms object_fragment0332239_field_004
#print axioms object_fragment0332239_field_005
#print axioms object_fragment0332239_field_006
#print axioms object_fragment0332239_field_007
#print axioms object_fragment0332239_field_008
#print axioms object_fragment0332239_field_009
#print axioms value_fragment0332239
#print axioms array_chunk0104_head
#print axioms array_chunk0104
#print axioms array_chunk0105_head
#print axioms array_chunk0105
#print axioms array_chunk0106_head
#print axioms array_chunk0106
#print axioms array_chunk0107_head
#print axioms array_chunk0107
#print axioms array_chunk0108_head
#print axioms array_chunk0108
#print axioms array_chunk0109_head
#print axioms array_chunk0109
#print axioms array_chunk0110_head
#print axioms array_chunk0110
#print axioms array_chunk0111_head
#print axioms array_chunk0111
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock013

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
