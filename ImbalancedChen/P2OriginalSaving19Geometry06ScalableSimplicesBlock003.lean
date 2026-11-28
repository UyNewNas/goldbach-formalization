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

namespace SimplicesBlock003

noncomputable def fragment0170831Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0170831Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0170831Field000Value00 : SourceJson := .number (String.ofList ['2', '4'])
noncomputable def fragment0170831Acc00100 : List (String × SourceJson) := (fragment0170831Field000Key00, fragment0170831Field000Value00) :: fragment0170831Acc00000
noncomputable def fragment0170831Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '4', ',']

theorem object_fragment0170831_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0170831Field000Chars00 ++ tail)) fragment0170831Acc00000 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0170831Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_000"
  err.flush

noncomputable def fragment0170831Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0170831Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0170831Acc00200 : List (String × SourceJson) := (fragment0170831Field001Key00, fragment0170831Field001Value00) :: fragment0170831Acc00100
noncomputable def fragment0170831Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0170831_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0170831Field001Chars00 ++ tail)) fragment0170831Acc00100 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0170831Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_001"
  err.flush

noncomputable def fragment0170831Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0170831Field002Value00 : SourceJson := .str (String.ofList ['3', '4', '6', '7', '0', '8', '6', '1', '1', '9', '7', '6', '4', '7', '3', '3', '6', '6', '6', '4', '2', '2', '3', '5', '2', '6', '9', '8', '5', '4', '0', '6', '3', '7', '6', '4', '7', '9', '4', '1', '4', '3', '/', '2', '3', '6', '9', '8', '2', '3', '7', '4', '7', '1', '2', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0170831Acc00300 : List (String × SourceJson) := (fragment0170831Field002Key00, fragment0170831Field002Value00) :: fragment0170831Acc00200
noncomputable def fragment0170831Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '4', '6', '7', '0', '8', '6', '1', '1', '9', '7', '6', '4', '7', '3', '3', '6', '6', '6', '4', '2', '2', '3', '5', '2', '6', '9', '8', '5', '4', '0', '6', '3', '7', '6', '4', '7', '9', '4', '1', '4', '3', '/', '2', '3', '6', '9', '8', '2', '3', '7', '4', '7', '1', '2', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0170831_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0170831Field002Chars00 ++ tail)) fragment0170831Acc00200 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0170831Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_002"
  err.flush

noncomputable def fragment0170831Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0170831Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0170831Acc00400 : List (String × SourceJson) := (fragment0170831Field003Key00, fragment0170831Field003Value00) :: fragment0170831Acc00300
noncomputable def fragment0170831Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0170831_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0170831Field003Chars00 ++ tail)) fragment0170831Acc00300 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0170831Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_003"
  err.flush

noncomputable def fragment0170831Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0170831Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0170831Acc00500 : List (String × SourceJson) := (fragment0170831Field004Key00, fragment0170831Field004Value00) :: fragment0170831Acc00400
noncomputable def fragment0170831Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0170831_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0170831Field004Chars00 ++ tail)) fragment0170831Acc00400 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0170831Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_004"
  err.flush

noncomputable def fragment0170831Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0170831Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '6', '1', '7', '7', '1', '3', '5', '8', '7', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '4', '9', '2', '2', '4', '0', '6', '3', '/', '1', '9', '9', '2', '3', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '5', '8', '6', '2', '5', '3', '8', '0', '3', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '7', '9', '9', '0', '9', '4', '4', '1', '4', '9', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '0', '1', '6', '5', '6', '2', '5', '2', '4', '3', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '3', '4', '7', '5', '1', '0', '1', '7', '/', '3', '4', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '0', '0', '5', '6', '0', '3', '1', '/', '2', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '4', '0', '8', '1', '6', '7', '9', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '7', '3', '1', '5', '2', '3', '4', '7', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '0', '2', '6', '6', '6', '7', '3', '/', '3', '7', '3', '5', '7', '0', '3', '1', '2', '5', '0'])]
noncomputable def fragment0170831Acc00600 : List (String × SourceJson) := (fragment0170831Field005Key00, fragment0170831Field005Value00) :: fragment0170831Acc00500
noncomputable def fragment0170831Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '6', '1', '7', '7', '1', '3', '5', '8', '7', '/', '3', '1', '8', '7', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '1', '4', '9', '2', '2', '4', '0', '6', '3', '/', '1', '9', '9', '2', '3', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '6', '5', '8', '6', '2', '5', '3', '8', '0', '3', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '7', '9', '9', '0', '9', '4', '4', '1', '4', '9', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '5', '0', '1', '6', '5', '6', '2', '5', '2', '4', '3', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '3', '4', '7', '5', '1', '0', '1', '7', '/', '3', '4', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '0', '0', '5', '6', '0', '3', '1', '/', '2', '4', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '4', '0', '8', '1', '6', '7', '9', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '7', '3', '1', '5', '2', '3', '4', '7', '/', '8', '6', '9', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '0', '2', '6', '6', '6', '7', '3', '/', '3', '7', '3', '5', '7', '0', '3', '1', '2', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0170831_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0170831Field005Chars00 ++ tail)) fragment0170831Acc00500 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0170831Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_005"
  err.flush

noncomputable def fragment0170831Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0170831Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '8', '9', '5', '3', '9', '4', '6', '8', '4', '8', '5', '0', '9', '5', '9', '3', '9', '5', '8', '5', '3', '7', '5', '7', '9', '8', '0', '1', '8', '1', '5', '5', '5', '6', '2', '6', '4', '4', '1', '7', '0', '9', '4', '6', '5', '1', '6', '4', '8', '0', '0', '/', '1', '0', '7', '3', '8', '4', '7', '7', '6', '9', '5', '0', '6', '6', '3', '5', '9', '1', '3', '0', '4', '6', '2', '1', '9', '5', '5', '5', '1', '8', '9', '5', '7', '8', '6', '2', '6', '4', '3', '4', '5', '3', '1', '3', '4', '9', '9', '8', '5', '8', '9', '8', '5', '1', '3', '9', '4', '1', '7', '5', '7', '3', '5', '0', '7', '7', '2', '2', '3'])
noncomputable def fragment0170831Acc00700 : List (String × SourceJson) := (fragment0170831Field006Key00, fragment0170831Field006Value00) :: fragment0170831Acc00600
noncomputable def fragment0170831Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '8', '9', '5', '3', '9', '4', '6', '8', '4', '8', '5', '0', '9', '5', '9', '3', '9', '5', '8', '5', '3', '7', '5', '7', '9', '8', '0', '1', '8', '1', '5', '5', '5', '6', '2', '6', '4', '4', '1', '7', '0', '9', '4', '6', '5', '1', '6', '4', '8', '0', '0', '/', '1', '0', '7', '3', '8', '4', '7', '7', '6', '9', '5', '0', '6', '6', '3', '5', '9', '1', '3', '0', '4', '6', '2', '1', '9', '5', '5', '5', '1', '8', '9', '5', '7', '8', '6', '2', '6', '4', '3', '4', '5', '3', '1', '3', '4', '9', '9', '8', '5', '8', '9', '8', '5', '1', '3', '9', '4', '1', '7', '5', '7', '3', '5', '0', '7', '7', '2', '2', '3', '"', ',']

theorem object_fragment0170831_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0170831Field006Chars00 ++ tail)) fragment0170831Acc00600 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0170831Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_006"
  err.flush

noncomputable def fragment0170831Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0170831Field007Value00 : SourceJson := .str (String.ofList ['4', '0', '4', '7', '6', '9', '2', '6', '9', '8', '4', '8', '7', '3', '2', '0', '8', '4', '4', '7', '5', '2', '9', '5', '6', '8', '7', '0', '2', '7', '9', '4', '4', '1', '8', '3', '5', '5', '3', '8', '7', '1', '2', '0', '0', '4', '8', '9', '5', '8', '8', '8', '7', '0', '8', '8', '8', '3', '4', '0', '5', '2', '6', '3', '8', '4', '7', '0', '2', '9', '5', '9', '1', '9', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '8', '1', '3', '5', '3', '8', '4', '4', '0', '5', '4', '8', '2', '1', '9', '4', '2', '8', '3', '2', '0', '7', '6', '1', '3', '1', '8', '5', '8', '0', '8', '3', '6', '6', '8', '4', '0', '0', '0', '0', '8', '6', '2', '2', '1', '4', '5', '4', '4', '4', '5', '2', '8', '3', '2', '6', '9', '2', '2', '8', '4', '6', '7', '8', '4', '2', '0', '7', '7', '6', '7', '2', '3', '7', '3', '7', '9', '2', '4', '4', '6', '3', '0', '2', '4', '8', '5', '1', '6', '4', '5', '2', '7', '8', '3', '7', '8', '9', '7', '2', '3'])
noncomputable def fragment0170831Acc00800 : List (String × SourceJson) := (fragment0170831Field007Key00, fragment0170831Field007Value00) :: fragment0170831Acc00700
noncomputable def fragment0170831Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '0', '4', '7', '6', '9', '2', '6', '9', '8', '4', '8', '7', '3', '2', '0', '8', '4', '4', '7', '5', '2', '9', '5', '6', '8', '7', '0', '2', '7', '9', '4', '4', '1', '8', '3', '5', '5', '3', '8', '7', '1', '2', '0', '0', '4', '8', '9', '5', '8', '8', '8', '7', '0', '8', '8', '8', '3', '4', '0', '5', '2', '6', '3', '8', '4', '7', '0', '2', '9', '5', '9', '1', '9', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '8', '1', '3', '5', '3', '8', '4', '4', '0', '5', '4', '8', '2', '1', '9', '4', '2', '8', '3', '2', '0', '7', '6', '1', '3', '1', '8', '5', '8', '0', '8', '3', '6', '6', '8', '4', '0', '0', '0', '0', '8', '6', '2', '2', '1', '4', '5', '4', '4', '4', '5', '2', '8', '3', '2', '6', '9', '2', '2', '8', '4', '6', '7', '8', '4', '2', '0', '7', '7', '6', '7', '2', '3', '7', '3', '7', '9', '2', '4', '4', '6', '3', '0', '2', '4', '8', '5', '1', '6', '4', '5', '2', '7', '8', '3', '7', '8', '9', '7', '2', '3', '"', ',']

theorem object_fragment0170831_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0170831Field007Chars00 ++ tail)) fragment0170831Acc00700 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0170831Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_007"
  err.flush

noncomputable def fragment0170831Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0170831Field008Value00 : SourceJson := .str (String.ofList ['9', '5', '1', '4', '1', '8', '3', '0', '6', '0', '1', '0', '3'])
noncomputable def fragment0170831Acc00900 : List (String × SourceJson) := (fragment0170831Field008Key00, fragment0170831Field008Value00) :: fragment0170831Acc00800
noncomputable def fragment0170831Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '5', '1', '4', '1', '8', '3', '0', '6', '0', '1', '0', '3', '"', ',']

theorem object_fragment0170831_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0170831Field008Chars00 ++ tail)) fragment0170831Acc00800 =
      SourceJson.object (fuel + 193) (SourceJson.white tail) fragment0170831Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_008"
  err.flush

noncomputable def fragment0170831Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0170831Field009Value00 : SourceJson := .str (String.ofList ['4', '1', '7', '4', '9', '3', '1', '4', '1', '7', '4', '8', '3', '9'])
noncomputable def fragment0170831Acc01000 : List (String × SourceJson) := (fragment0170831Field009Key00, fragment0170831Field009Value00) :: fragment0170831Acc00900
noncomputable def fragment0170831Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '7', '4', '9', '3', '1', '4', '1', '7', '4', '8', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0170831_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment0170831Field009Chars00 ++ tail)) fragment0170831Acc00900 =
      .ok (.obj (fragment0170831Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0170831_object_field_009"
  err.flush

noncomputable def fragment0170831Chars : List Char := '{' :: (fragment0170831Field000Chars00 ++ fragment0170831Field001Chars00 ++ fragment0170831Field002Chars00 ++ fragment0170831Field003Chars00 ++ fragment0170831Field004Chars00 ++ fragment0170831Field005Chars00 ++ fragment0170831Field006Chars00 ++ fragment0170831Field007Chars00 ++ fragment0170831Field008Chars00 ++ fragment0170831Field009Chars00)
noncomputable def fragment0170831Value : SourceJson := .obj (fragment0170831Acc01000.reverse)

theorem value_fragment0170831 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 203) (fragment0170831Chars ++ tail) =
      .ok (fragment0170831Value, tail) := by
  have hinput : fragment0170831Chars ++ tail = '{' :: (fragment0170831Field000Chars00 ++ (fragment0170831Field001Chars00 ++ (fragment0170831Field002Chars00 ++ (fragment0170831Field003Chars00 ++ (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0170831Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 203) (fragment0170831Chars ++ tail) =
        SourceJson.value (fuel + 203) ('{' :: (fragment0170831Field000Chars00 ++ (fragment0170831Field001Chars00 ++ (fragment0170831Field002Chars00 ++ (fragment0170831Field003Chars00 ++ (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 203)) hinput
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0170831Field000Chars00 ++ (fragment0170831Field001Chars00 ++ (fragment0170831Field002Chars00 ++ (fragment0170831Field003Chars00 ++ (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))))))))))) fragment0170831Acc00000 := by rfl
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0170831Field001Chars00 ++ (fragment0170831Field002Chars00 ++ (fragment0170831Field003Chars00 ++ (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail))))))))))) fragment0170831Acc00100 := object_fragment0170831_field_000 fuel (fragment0170831Field001Chars00 ++ (fragment0170831Field002Chars00 ++ (fragment0170831Field003Chars00 ++ (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0170831Field002Chars00 ++ (fragment0170831Field003Chars00 ++ (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))))))))) fragment0170831Acc00200 := object_fragment0170831_field_001 fuel (fragment0170831Field002Chars00 ++ (fragment0170831Field003Chars00 ++ (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0170831Field003Chars00 ++ (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail))))))))) fragment0170831Acc00300 := object_fragment0170831_field_002 fuel (fragment0170831Field003Chars00 ++ (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))))))) fragment0170831Acc00400 := object_fragment0170831_field_003 fuel (fragment0170831Field004Chars00 ++ (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail))))))) fragment0170831Acc00500 := object_fragment0170831_field_004 fuel (fragment0170831Field005Chars00 ++ (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))))) fragment0170831Acc00600 := object_fragment0170831_field_005 fuel (fragment0170831Field006Chars00 ++ (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail))))) fragment0170831Acc00700 := object_fragment0170831_field_006 fuel (fragment0170831Field007Chars00 ++ (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))) fragment0170831Acc00800 := object_fragment0170831_field_007 fuel (fragment0170831Field008Chars00 ++ (fragment0170831Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment0170831Field009Chars00 ++ (tail))) fragment0170831Acc00900 := object_fragment0170831_field_008 fuel (fragment0170831Field009Chars00 ++ (tail))
    _ = .ok (fragment0170831Value, tail) := object_fragment0170831_field_009 fuel (tail)

noncomputable def fragment0172379Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0172379Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0172379Field000Value00 : SourceJson := .number (String.ofList ['2', '5'])
noncomputable def fragment0172379Acc00100 : List (String × SourceJson) := (fragment0172379Field000Key00, fragment0172379Field000Value00) :: fragment0172379Acc00000
noncomputable def fragment0172379Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '5', ',']

theorem object_fragment0172379_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 467) (SourceJson.white (fragment0172379Field000Chars00 ++ tail)) fragment0172379Acc00000 =
      SourceJson.object (fuel + 466) (SourceJson.white tail) fragment0172379Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_000"
  err.flush

noncomputable def fragment0172379Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0172379Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0172379Acc00200 : List (String × SourceJson) := (fragment0172379Field001Key00, fragment0172379Field001Value00) :: fragment0172379Acc00100
noncomputable def fragment0172379Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0172379_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 466) (SourceJson.white (fragment0172379Field001Chars00 ++ tail)) fragment0172379Acc00100 =
      SourceJson.object (fuel + 465) (SourceJson.white tail) fragment0172379Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_001"
  err.flush

noncomputable def fragment0172379Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0172379Field002Value00 : SourceJson := .str (String.ofList ['9', '5', '8', '5', '5', '0', '9', '2', '1', '1', '9', '9', '5', '0', '7', '2', '1', '7', '1', '4', '1', '8', '9', '1', '5', '5', '4', '3', '8', '4', '8', '7', '7', '2', '3', '5', '0', '9', '3', '1', '1', '2', '6', '7', '/', '2', '4', '5', '1', '3', '2', '2', '3', '9', '1', '4', '2', '6', '3', '3', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0172379Acc00300 : List (String × SourceJson) := (fragment0172379Field002Key00, fragment0172379Field002Value00) :: fragment0172379Acc00200
noncomputable def fragment0172379Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '5', '8', '5', '5', '0', '9', '2', '1', '1', '9', '9', '5', '0', '7', '2', '1', '7', '1', '4', '1', '8', '9', '1', '5', '5', '4', '3', '8', '4', '8', '7', '7', '2', '3', '5', '0', '9', '3', '1', '1', '2', '6', '7', '/', '2', '4', '5', '1', '3', '2', '2', '3', '9', '1', '4', '2', '6', '3', '3', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0172379_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 465) (SourceJson.white (fragment0172379Field002Chars00 ++ tail)) fragment0172379Acc00200 =
      SourceJson.object (fuel + 464) (SourceJson.white tail) fragment0172379Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_002"
  err.flush

noncomputable def fragment0172379Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0172379Field003Value00 : SourceJson := .str (String.ofList ['1', '5', '4', '4', '2', '3', '4', '4', '5', '9', '/', '5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0'])
noncomputable def fragment0172379Acc00400 : List (String × SourceJson) := (fragment0172379Field003Key00, fragment0172379Field003Value00) :: fragment0172379Acc00300
noncomputable def fragment0172379Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '5', '4', '4', '2', '3', '4', '4', '5', '9', '/', '5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0172379_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 464) (SourceJson.white (fragment0172379Field003Chars00 ++ tail)) fragment0172379Acc00300 =
      SourceJson.object (fuel + 463) (SourceJson.white tail) fragment0172379Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_003"
  err.flush

noncomputable def fragment0172379Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0172379Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0172379Acc00500 : List (String × SourceJson) := (fragment0172379Field004Key00, fragment0172379Field004Value00) :: fragment0172379Acc00400
noncomputable def fragment0172379Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0172379_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 463) (SourceJson.white (fragment0172379Field004Chars00 ++ tail)) fragment0172379Acc00400 =
      SourceJson.object (fuel + 462) (SourceJson.white tail) fragment0172379Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_004"
  err.flush

noncomputable def fragment0172379Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0172379Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '0', '5', '6', '9', '8', '8', '7', '6', '1', '9', '9', '1', '8', '2', '1', '6', '8', '8', '0', '5', '1', '1', '3', '9', '/', '7', '9', '4', '2', '1', '0', '4', '3', '8', '7', '1', '6', '8', '5', '4', '6', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '6', '8', '5', '6', '4', '3', '2', '6', '8', '1', '1', '3', '2', '1', '8', '0', '4', '5', '8', '6', '2', '3', '/', '3', '5', '4', '5', '5', '8', '2', '3', '1', '5', '7', '0', '0', '2', '4', '4', '0', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '3', '4', '3', '2', '1', '7', '8', '7', '5', '5', '6', '5', '7', '2', '0', '9', '6', '6', '9', '7', '2', '7', '/', '6', '2', '0', '4', '7', '6', '9', '0', '5', '2', '4', '7', '5', '4', '2', '7', '0', '8', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '9', '1', '4', '0', '1', '1', '4', '0', '8', '3', '7', '2', '5', '1', '4', '9', '6', '4', '8', '4', '6', '0', '8', '9', '/', '1', '9', '8', '5', '5', '2', '6', '0', '9', '6', '7', '9', '2', '1', '3', '6', '6', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '7', '5', '0', '5', '3', '5', '6', '7', '4', '5', '0', '1', '5', '2', '9', '5', '4', '5', '2', '0', '9', '6', '1', '/', '6', '6', '1', '8', '4', '2', '0', '3', '2', '2', '6', '4', '0', '4', '5', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '9', '9', '2', '5', '1', '5', '5', '9', '1', '3', '2', '2', '7', '9', '7', '0', '9', '9', '7', '/', '3', '6', '1', '0', '0', '4', '7', '4', '4', '8', '7', '1', '2', '9', '7', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '7', '3', '8', '2', '4', '2', '0', '3', '8', '3', '8', '7', '9', '7', '7', '0', '8', '8', '4', '7', '/', '1', '1', '5', '5', '2', '1', '5', '1', '8', '3', '5', '8', '8', '1', '5', '2', '2', '4', '3', '2', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '0', '3', '3', '0', '6', '2', '5', '7', '0', '9', '9', '4', '5', '1', '8', '6', '5', '7', '0', '7', '/', '2', '3', '6', '7', '2', '4', '4', '2', '2', '8', '6', '6', '4', '2', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '7', '6', '7', '1', '8', '1', '1', '3', '3', '8', '3', '6', '6', '3', '5', '2', '7', '5', '4', '0', '9', '/', '7', '2', '2', '0', '0', '9', '4', '8', '9', '7', '4', '2', '5', '9', '5', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '1', '3', '8', '0', '4', '8', '0', '1', '9', '9', '7', '3', '6', '3', '0', '6', '1', '3', '2', '6', '7', '/', '1', '1', '8', '1', '8', '6', '0', '7', '7', '1', '9', '0', '0', '0', '8', '1', '3', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0172379Acc00600 : List (String × SourceJson) := (fragment0172379Field005Key00, fragment0172379Field005Value00) :: fragment0172379Acc00500
noncomputable def fragment0172379Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '5', '6', '9', '8', '8', '7', '6', '1', '9', '9', '1', '8', '2', '1', '6', '8', '8', '0', '5', '1', '1', '3', '9', '/', '7', '9', '4', '2', '1', '0', '4', '3', '8', '7', '1', '6', '8', '5', '4', '6', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '6', '8', '5', '6', '4', '3', '2', '6', '8', '1', '1', '3', '2', '1', '8', '0', '4', '5', '8', '6', '2', '3', '/', '3', '5', '4', '5', '5', '8', '2', '3', '1', '5', '7', '0', '0', '2', '4', '4', '0', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '3', '4', '3', '2', '1', '7', '8', '7', '5', '5', '6', '5', '7', '2', '0', '9', '6', '6', '9', '7', '2', '7', '/', '6', '2', '0', '4', '7', '6', '9', '0', '5', '2', '4', '7', '5', '4', '2', '7', '0', '8', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '1', '4', '0', '1', '1', '4', '0', '8', '3', '7', '2', '5', '1', '4', '9', '6', '4', '8', '4', '6', '0', '8', '9', '/', '1', '9', '8', '5', '5', '2', '6', '0', '9', '6', '7', '9', '2', '1', '3', '6', '6', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '7', '5', '0', '5', '3', '5', '6', '7', '4', '5', '0', '1', '5', '2', '9', '5', '4', '5', '2', '0', '9', '6', '1', '/', '6', '6', '1', '8', '4', '2', '0', '3', '2', '2', '6', '4', '0', '4', '5', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '4', '2', '1', '9', '9', '2', '5', '1', '5', '5', '9', '1', '3', '2', '2', '7', '9', '7', '0', '9', '9', '7', '/', '3', '6', '1', '0', '0', '4', '7', '4', '4', '8', '7', '1', '2', '9', '7', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '7', '3', '8', '2', '4', '2', '0', '3', '8', '3', '8', '7', '9', '7', '7', '0', '8', '8', '4', '7', '/', '1', '1', '5', '5', '2', '1', '5', '1', '8', '3', '5', '8', '8', '1', '5', '2', '2', '4', '3', '2', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '0', '3', '3', '0', '6', '2', '5', '7', '0', '9', '9', '4', '5', '1', '8', '6', '5', '7', '0', '7', '/', '2', '3', '6', '7', '2', '4', '4', '2', '2', '8', '6', '6', '4', '2', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '7', '6', '7', '1', '8', '1', '1', '3', '3', '8', '3', '6', '6', '3', '5', '2', '7', '5', '4', '0', '9', '/', '7', '2', '2', '0', '0', '9', '4', '8', '9', '7', '4', '2', '5', '9', '5', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '1', '3', '8', '0', '4', '8', '0', '1', '9', '9', '7', '3', '6', '3', '0', '6', '1', '3', '2', '6', '7', '/', '1', '1', '8', '1', '8', '6', '0', '7', '7', '1', '9', '0', '0', '0', '8', '1', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0172379_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 462) (SourceJson.white (fragment0172379Field005Chars00 ++ tail)) fragment0172379Acc00500 =
      SourceJson.object (fuel + 461) (SourceJson.white tail) fragment0172379Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_005"
  err.flush

noncomputable def fragment0172379Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0172379Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '9', '4', '6', '9', '1', '0', '2', '4', '9', '2', '4', '7', '6', '5', '0', '0', '2', '9', '1', '8', '0', '2', '1', '6', '7', '1', '3', '2', '4', '4', '1', '5', '9', '6', '7', '8', '9', '1', '7', '4', '8', '6', '8', '2', '9', '8', '6', '8', '7', '4', '2', '7', '8', '4', '0', '0', '0', '0', '0', '0', '/', '9', '2', '5', '0', '0', '1', '3', '4', '9', '1', '9', '6', '2', '9', '8', '8', '8', '6', '9', '5', '2', '7', '6', '3', '7', '1', '8', '8', '0', '2', '0', '3', '6', '5', '4', '8', '5', '6', '5', '1', '4', '0', '2', '5', '8', '7', '4', '7', '9', '7', '1', '7', '8', '4', '2', '9', '8', '7', '0', '3', '5', '3', '5', '2', '4', '7', '3', '1', '3', '5', '2', '8', '1', '2', '7'])
noncomputable def fragment0172379Acc00700 : List (String × SourceJson) := (fragment0172379Field006Key00, fragment0172379Field006Value00) :: fragment0172379Acc00600
noncomputable def fragment0172379Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '9', '4', '6', '9', '1', '0', '2', '4', '9', '2', '4', '7', '6', '5', '0', '0', '2', '9', '1', '8', '0', '2', '1', '6', '7', '1', '3', '2', '4', '4', '1', '5', '9', '6', '7', '8', '9', '1', '7', '4', '8', '6', '8', '2', '9', '8', '6', '8', '7', '4', '2', '7', '8', '4', '0', '0', '0', '0', '0', '0', '/', '9', '2', '5', '0', '0', '1', '3', '4', '9', '1', '9', '6', '2', '9', '8', '8', '8', '6', '9', '5', '2', '7', '6', '3', '7', '1', '8', '8', '0', '2', '0', '3', '6', '5', '4', '8', '5', '6', '5', '1', '4', '0', '2', '5', '8', '7', '4', '7', '9', '7', '1', '7', '8', '4', '2', '9', '8', '7', '0', '3', '5', '3', '5', '2', '4', '7', '3', '1', '3', '5', '2', '8', '1', '2', '7', '"', ',']

theorem object_fragment0172379_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 461) (SourceJson.white (fragment0172379Field006Chars00 ++ tail)) fragment0172379Acc00600 =
      SourceJson.object (fuel + 460) (SourceJson.white tail) fragment0172379Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_006"
  err.flush

noncomputable def fragment0172379Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0172379Field007Value00 : SourceJson := .str (String.ofList ['8', '1', '4', '4', '4', '6', '1', '6', '2', '0', '1', '4', '5', '0', '6', '0', '5', '8', '7', '9', '0', '4', '8', '2', '6', '2', '9', '2', '0', '5', '1', '2', '5', '9', '3', '3', '1', '7', '9', '9', '2', '7', '9', '9', '8', '4', '1', '6', '5', '6', '4', '1', '6', '6', '5', '0', '5', '1', '7', '4', '8', '2', '1', '4', '7', '7', '5', '7', '9', '0', '9', '1', '9', '2', '7', '2', '9', '0', '2', '9', '1', '8', '5', '0', '3', '8', '5', '1', '5', '5', '0', '1', '0', '4', '0', '0', '0', '7', '8', '8', '3', '6', '5', '8', '4', '0', '2', '9', '9', '6', '7', '8', '3', '3', '4', '8', '7', '6', '1', '8', '0', '5', '4', '3', '7', '4', '3', '3', '1', '2', '2', '4', '5', '5', '9', '9', '9', '1', '3', '3', '9', '0', '8', '9', '1', '6', '5', '2', '2', '6', '7', '3', '1', '2', '0', '1', '9', '5', '5', '2', '1', '4', '9', '3', '5', '5', '6', '3', '2', '0', '9', '0', '2', '8', '7', '8', '2', '1', '2', '8', '6', '3', '4', '0', '3', '8', '5', '3', '5', '0', '1', '3', '7', '1', '2', '3', '8', '5', '9', '9', '1', '7', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '6', '9', '5', '6', '6', '5', '2', '8', '6', '9', '8', '6', '7', '5', '7', '0', '0', '9', '2', '6', '8', '5', '3', '6', '4', '8', '5', '4', '8', '6', '5', '8', '8', '1', '3', '5', '3', '2', '1', '3', '0', '3', '4', '1', '6', '8', '8', '9', '4', '4', '7', '6', '8', '4', '8', '8', '4', '7', '0', '4', '7', '1', '4', '0', '4', '2', '1', '1', '0', '1', '3', '2', '2', '4', '9', '1', '7', '8', '0', '2', '8', '9', '1', '3', '8', '6', '2', '4', '3', '4', '3', '4', '7', '1', '8', '1', '8', '9', '7', '6', '0', '3', '5', '3', '3', '2', '1', '2', '0', '0', '5', '1', '5', '3', '3', '4', '5', '8', '6', '1', '7', '4', '4', '1', '6', '0', '2', '1', '4', '6', '0', '5', '7', '3', '0', '4', '5', '1', '0', '0', '4', '9', '4', '1', '6', '6', '2', '2', '9', '5', '8', '4', '5', '3', '7', '4', '1', '4', '4', '4', '9', '5', '1', '9', '1', '0', '2', '3', '6', '5', '2', '5', '8', '0', '8', '3', '3', '2', '9', '9', '8', '1', '4', '9', '9', '5', '9', '7', '1', '9', '1', '1', '1', '0', '2', '4', '4', '3', '4', '2', '1', '6', '4', '6', '4', '5', '7', '4', '6', '1', '9', '1', '9', '2', '2', '0', '7', '5', '6', '2', '9', '0', '5', '1', '5', '9', '0', '3', '2', '5', '0', '9', '9'])
noncomputable def fragment0172379Acc00800 : List (String × SourceJson) := (fragment0172379Field007Key00, fragment0172379Field007Value00) :: fragment0172379Acc00700
noncomputable def fragment0172379Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '1', '4', '4', '4', '6', '1', '6', '2', '0', '1', '4', '5', '0', '6', '0', '5', '8', '7', '9', '0', '4', '8', '2', '6', '2', '9', '2', '0', '5', '1', '2', '5', '9', '3', '3', '1', '7', '9', '9', '2', '7', '9', '9', '8', '4', '1', '6', '5', '6', '4', '1', '6', '6', '5', '0', '5', '1', '7', '4', '8', '2', '1', '4', '7', '7', '5', '7', '9', '0', '9', '1', '9', '2', '7', '2', '9', '0', '2', '9', '1', '8', '5', '0', '3', '8', '5', '1', '5', '5', '0', '1', '0', '4', '0', '0', '0', '7', '8', '8', '3', '6', '5', '8', '4', '0', '2', '9', '9', '6', '7', '8', '3', '3', '4', '8', '7', '6', '1', '8', '0', '5', '4', '3', '7', '4', '3', '3', '1', '2', '2', '4', '5', '5', '9', '9', '9', '1', '3', '3', '9', '0', '8', '9', '1', '6', '5', '2', '2', '6', '7', '3', '1', '2', '0', '1', '9', '5', '5', '2', '1', '4', '9', '3', '5', '5', '6', '3', '2', '0', '9', '0', '2', '8', '7', '8', '2', '1', '2', '8', '6', '3', '4', '0', '3', '8', '5', '3', '5', '0', '1', '3', '7', '1', '2', '3', '8', '5', '9', '9', '1', '7', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '6', '9', '5', '6', '6', '5', '2', '8', '6', '9', '8', '6', '7', '5', '7', '0', '0', '9', '2', '6', '8', '5', '3', '6', '4', '8', '5', '4', '8', '6', '5', '8', '8', '1', '3', '5', '3', '2', '1', '3', '0', '3', '4', '1', '6', '8', '8', '9', '4', '4', '7', '6', '8', '4', '8', '8', '4', '7', '0', '4', '7', '1', '4', '0', '4', '2', '1', '1', '0', '1', '3', '2', '2', '4', '9', '1', '7', '8', '0', '2', '8', '9', '1', '3', '8', '6', '2', '4', '3', '4', '3', '4', '7', '1', '8', '1', '8', '9', '7', '6', '0', '3', '5', '3', '3', '2', '1', '2', '0', '0', '5', '1', '5', '3', '3', '4', '5', '8', '6', '1', '7', '4', '4', '1', '6', '0', '2', '1', '4', '6', '0', '5', '7', '3', '0', '4', '5', '1', '0', '0', '4', '9', '4', '1', '6', '6', '2', '2', '9', '5', '8', '4', '5', '3', '7', '4', '1', '4', '4', '4', '9', '5', '1', '9', '1', '0', '2', '3', '6', '5', '2', '5', '8', '0', '8', '3', '3', '2', '9', '9', '8', '1', '4', '9', '9', '5', '9', '7', '1', '9', '1', '1', '1', '0', '2', '4', '4', '3', '4', '2', '1', '6', '4', '6', '4', '5', '7', '4', '6', '1', '9', '1', '9', '2', '2', '0', '7', '5', '6', '2', '9', '0', '5', '1', '5', '9', '0', '3', '2', '5', '0', '9', '9', '"', ',']

theorem object_fragment0172379_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 460) (SourceJson.white (fragment0172379Field007Chars00 ++ tail)) fragment0172379Acc00700 =
      SourceJson.object (fuel + 459) (SourceJson.white tail) fragment0172379Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_007"
  err.flush

noncomputable def fragment0172379Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0172379Field008Value00 : SourceJson := .str (String.ofList ['1', '6', '2', '2', '8', '3', '9', '6', '7', '0', '0', '9', '8', '6', '9', '9'])
noncomputable def fragment0172379Acc00900 : List (String × SourceJson) := (fragment0172379Field008Key00, fragment0172379Field008Value00) :: fragment0172379Acc00800
noncomputable def fragment0172379Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '2', '2', '8', '3', '9', '6', '7', '0', '0', '9', '8', '6', '9', '9', '"', ',']

theorem object_fragment0172379_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 459) (SourceJson.white (fragment0172379Field008Chars00 ++ tail)) fragment0172379Acc00800 =
      SourceJson.object (fuel + 458) (SourceJson.white tail) fragment0172379Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_008"
  err.flush

noncomputable def fragment0172379Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0172379Field009Value00 : SourceJson := .str (String.ofList ['4', '7', '1', '1', '4', '9', '6', '0', '4', '8', '6', '4', '5', '1', '1', '3'])
noncomputable def fragment0172379Acc01000 : List (String × SourceJson) := (fragment0172379Field009Key00, fragment0172379Field009Value00) :: fragment0172379Acc00900
noncomputable def fragment0172379Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '7', '1', '1', '4', '9', '6', '0', '4', '8', '6', '4', '5', '1', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0172379_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 458) (SourceJson.white (fragment0172379Field009Chars00 ++ tail)) fragment0172379Acc00900 =
      .ok (.obj (fragment0172379Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0172379_object_field_009"
  err.flush

noncomputable def fragment0172379Chars : List Char := '{' :: (fragment0172379Field000Chars00 ++ fragment0172379Field001Chars00 ++ fragment0172379Field002Chars00 ++ fragment0172379Field003Chars00 ++ fragment0172379Field004Chars00 ++ fragment0172379Field005Chars00 ++ fragment0172379Field006Chars00 ++ fragment0172379Field007Chars00 ++ fragment0172379Field008Chars00 ++ fragment0172379Field009Chars00)
noncomputable def fragment0172379Value : SourceJson := .obj (fragment0172379Acc01000.reverse)

theorem value_fragment0172379 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 468) (fragment0172379Chars ++ tail) =
      .ok (fragment0172379Value, tail) := by
  have hinput : fragment0172379Chars ++ tail = '{' :: (fragment0172379Field000Chars00 ++ (fragment0172379Field001Chars00 ++ (fragment0172379Field002Chars00 ++ (fragment0172379Field003Chars00 ++ (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0172379Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 468) (fragment0172379Chars ++ tail) =
        SourceJson.value (fuel + 468) ('{' :: (fragment0172379Field000Chars00 ++ (fragment0172379Field001Chars00 ++ (fragment0172379Field002Chars00 ++ (fragment0172379Field003Chars00 ++ (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 468)) hinput
    _ = SourceJson.object (fuel + 467) (SourceJson.white (fragment0172379Field000Chars00 ++ (fragment0172379Field001Chars00 ++ (fragment0172379Field002Chars00 ++ (fragment0172379Field003Chars00 ++ (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))))))))))) fragment0172379Acc00000 := by rfl
    _ = SourceJson.object (fuel + 466) (SourceJson.white (fragment0172379Field001Chars00 ++ (fragment0172379Field002Chars00 ++ (fragment0172379Field003Chars00 ++ (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail))))))))))) fragment0172379Acc00100 := object_fragment0172379_field_000 fuel (fragment0172379Field001Chars00 ++ (fragment0172379Field002Chars00 ++ (fragment0172379Field003Chars00 ++ (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 465) (SourceJson.white (fragment0172379Field002Chars00 ++ (fragment0172379Field003Chars00 ++ (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))))))))) fragment0172379Acc00200 := object_fragment0172379_field_001 fuel (fragment0172379Field002Chars00 ++ (fragment0172379Field003Chars00 ++ (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 464) (SourceJson.white (fragment0172379Field003Chars00 ++ (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail))))))))) fragment0172379Acc00300 := object_fragment0172379_field_002 fuel (fragment0172379Field003Chars00 ++ (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 463) (SourceJson.white (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))))))) fragment0172379Acc00400 := object_fragment0172379_field_003 fuel (fragment0172379Field004Chars00 ++ (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 462) (SourceJson.white (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail))))))) fragment0172379Acc00500 := object_fragment0172379_field_004 fuel (fragment0172379Field005Chars00 ++ (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 461) (SourceJson.white (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))))) fragment0172379Acc00600 := object_fragment0172379_field_005 fuel (fragment0172379Field006Chars00 ++ (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 460) (SourceJson.white (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail))))) fragment0172379Acc00700 := object_fragment0172379_field_006 fuel (fragment0172379Field007Chars00 ++ (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 459) (SourceJson.white (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))) fragment0172379Acc00800 := object_fragment0172379_field_007 fuel (fragment0172379Field008Chars00 ++ (fragment0172379Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 458) (SourceJson.white (fragment0172379Field009Chars00 ++ (tail))) fragment0172379Acc00900 := object_fragment0172379_field_008 fuel (fragment0172379Field009Chars00 ++ (tail))
    _ = .ok (fragment0172379Value, tail) := object_fragment0172379_field_009 fuel (tail)

noncomputable def fragment0174476Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0174476Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0174476Field000Value00 : SourceJson := .number (String.ofList ['2', '6'])
noncomputable def fragment0174476Acc00100 : List (String × SourceJson) := (fragment0174476Field000Key00, fragment0174476Field000Value00) :: fragment0174476Acc00000
noncomputable def fragment0174476Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '6', ',']

theorem object_fragment0174476_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 466) (SourceJson.white (fragment0174476Field000Chars00 ++ tail)) fragment0174476Acc00000 =
      SourceJson.object (fuel + 465) (SourceJson.white tail) fragment0174476Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_000"
  err.flush

noncomputable def fragment0174476Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0174476Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0174476Acc00200 : List (String × SourceJson) := (fragment0174476Field001Key00, fragment0174476Field001Value00) :: fragment0174476Acc00100
noncomputable def fragment0174476Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0174476_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 465) (SourceJson.white (fragment0174476Field001Chars00 ++ tail)) fragment0174476Acc00100 =
      SourceJson.object (fuel + 464) (SourceJson.white tail) fragment0174476Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_001"
  err.flush

noncomputable def fragment0174476Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0174476Field002Value00 : SourceJson := .str (String.ofList ['2', '5', '3', '9', '9', '7', '4', '9', '5', '1', '8', '0', '8', '5', '2', '0', '1', '8', '7', '8', '5', '3', '9', '5', '8', '9', '3', '8', '7', '7', '7', '3', '8', '1', '4', '3', '5', '6', '8', '6', '0', '0', '1', '/', '7', '6', '0', '0', '9', '9', '9', '6', '6', '3', '3', '3', '7', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0174476Acc00300 : List (String × SourceJson) := (fragment0174476Field002Key00, fragment0174476Field002Value00) :: fragment0174476Acc00200
noncomputable def fragment0174476Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '5', '3', '9', '9', '7', '4', '9', '5', '1', '8', '0', '8', '5', '2', '0', '1', '8', '7', '8', '5', '3', '9', '5', '8', '9', '3', '8', '7', '7', '7', '3', '8', '1', '4', '3', '5', '6', '8', '6', '0', '0', '1', '/', '7', '6', '0', '0', '9', '9', '9', '6', '6', '3', '3', '3', '7', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0174476_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 464) (SourceJson.white (fragment0174476Field002Chars00 ++ tail)) fragment0174476Acc00200 =
      SourceJson.object (fuel + 463) (SourceJson.white tail) fragment0174476Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_002"
  err.flush

noncomputable def fragment0174476Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0174476Field003Value00 : SourceJson := .str (String.ofList ['2', '4', '2', '7', '7', '4', '2', '3', '/', '1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0'])
noncomputable def fragment0174476Acc00400 : List (String × SourceJson) := (fragment0174476Field003Key00, fragment0174476Field003Value00) :: fragment0174476Acc00300
noncomputable def fragment0174476Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '4', '2', '7', '7', '4', '2', '3', '/', '1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0', '"', ',']

theorem object_fragment0174476_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 463) (SourceJson.white (fragment0174476Field003Chars00 ++ tail)) fragment0174476Acc00300 =
      SourceJson.object (fuel + 462) (SourceJson.white tail) fragment0174476Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_003"
  err.flush

noncomputable def fragment0174476Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0174476Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0174476Acc00500 : List (String × SourceJson) := (fragment0174476Field004Key00, fragment0174476Field004Value00) :: fragment0174476Acc00400
noncomputable def fragment0174476Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0174476_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 462) (SourceJson.white (fragment0174476Field004Chars00 ++ tail)) fragment0174476Acc00400 =
      SourceJson.object (fuel + 461) (SourceJson.white tail) fragment0174476Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_004"
  err.flush

noncomputable def fragment0174476Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0174476Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '7', '8', '8', '1', '7', '4', '5', '7', '4', '7', '6', '2', '9', '9', '4', '5', '7', '0', '3', '4', '4', '3', '8', '7', '/', '1', '9', '9', '7', '7', '6', '7', '3', '8', '9', '2', '0', '6', '5', '0', '2', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '9', '6', '6', '7', '2', '4', '4', '9', '5', '6', '7', '5', '0', '5', '1', '5', '2', '2', '1', '8', '9', '/', '1', '0', '1', '9', '2', '6', '9', '0', '7', '6', '1', '2', '5', '7', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '2', '7', '4', '9', '4', '0', '1', '5', '5', '1', '9', '1', '7', '3', '5', '9', '3', '7', '8', '8', '7', '8', '1', '/', '9', '9', '8', '8', '8', '3', '6', '9', '4', '6', '0', '3', '2', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '2', '4', '4', '8', '5', '3', '7', '4', '9', '9', '6', '1', '8', '6', '2', '4', '3', '2', '6', '3', '9', '4', '1', '/', '9', '9', '8', '8', '8', '3', '6', '9', '4', '6', '0', '3', '2', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '2', '6', '3', '8', '9', '8', '6', '7', '1', '8', '8', '8', '5', '1', '2', '0', '7', '3', '0', '0', '4', '3', '9', '/', '3', '3', '2', '9', '6', '1', '2', '3', '1', '5', '3', '4', '4', '1', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '6', '4', '1', '0', '9', '4', '0', '8', '0', '1', '7', '8', '4', '9', '5', '0', '1', '9', '9', '4', '7', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '3', '0', '4', '8', '7', '4', '7', '5', '6', '9', '0', '0', '6', '3', '5', '3', '8', '6', '9', '3', '7', '/', '7', '2', '6', '4', '6', '0', '8', '6', '8', '8', '0', '2', '3', '6', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '1', '9', '9', '6', '1', '3', '7', '2', '8', '6', '1', '9', '9', '5', '6', '1', '3', '3', '3', '7', '/', '3', '6', '3', '2', '3', '0', '4', '3', '4', '4', '0', '1', '1', '8', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '8', '7', '0', '3', '6', '1', '7', '6', '7', '4', '2', '7', '8', '3', '3', '3', '1', '7', '3', '6', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '7', '6', '6', '6', '8', '9', '4', '8', '2', '4', '5', '8', '2', '4', '4', '7', '4', '9', '8', '1', '/', '3', '3', '9', '7', '5', '6', '3', '5', '8', '7', '0', '8', '5', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0174476Acc00600 : List (String × SourceJson) := (fragment0174476Field005Key00, fragment0174476Field005Value00) :: fragment0174476Acc00500
noncomputable def fragment0174476Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '8', '1', '7', '4', '5', '7', '4', '7', '6', '2', '9', '9', '4', '5', '7', '0', '3', '4', '4', '3', '8', '7', '/', '1', '9', '9', '7', '7', '6', '7', '3', '8', '9', '2', '0', '6', '5', '0', '2', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '9', '6', '6', '7', '2', '4', '4', '9', '5', '6', '7', '5', '0', '5', '1', '5', '2', '2', '1', '8', '9', '/', '1', '0', '1', '9', '2', '6', '9', '0', '7', '6', '1', '2', '5', '7', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '2', '7', '4', '9', '4', '0', '1', '5', '5', '1', '9', '1', '7', '3', '5', '9', '3', '7', '8', '8', '7', '8', '1', '/', '9', '9', '8', '8', '8', '3', '6', '9', '4', '6', '0', '3', '2', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '2', '4', '4', '8', '5', '3', '7', '4', '9', '9', '6', '1', '8', '6', '2', '4', '3', '2', '6', '3', '9', '4', '1', '/', '9', '9', '8', '8', '8', '3', '6', '9', '4', '6', '0', '3', '2', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '2', '6', '3', '8', '9', '8', '6', '7', '1', '8', '8', '8', '5', '1', '2', '0', '7', '3', '0', '0', '4', '3', '9', '/', '3', '3', '2', '9', '6', '1', '2', '3', '1', '5', '3', '4', '4', '1', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '6', '4', '1', '0', '9', '4', '0', '8', '0', '1', '7', '8', '4', '9', '5', '0', '1', '9', '9', '4', '7', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '3', '0', '4', '8', '7', '4', '7', '5', '6', '9', '0', '0', '6', '3', '5', '3', '8', '6', '9', '3', '7', '/', '7', '2', '6', '4', '6', '0', '8', '6', '8', '8', '0', '2', '3', '6', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '1', '9', '9', '6', '1', '3', '7', '2', '8', '6', '1', '9', '9', '5', '6', '1', '3', '3', '3', '7', '/', '3', '6', '3', '2', '3', '0', '4', '3', '4', '4', '0', '1', '1', '8', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '1', '8', '7', '0', '3', '6', '1', '7', '6', '7', '4', '2', '7', '8', '3', '3', '3', '1', '7', '3', '6', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '7', '6', '6', '6', '8', '9', '4', '8', '2', '4', '5', '8', '2', '4', '4', '7', '4', '9', '8', '1', '/', '3', '3', '9', '7', '5', '6', '3', '5', '8', '7', '0', '8', '5', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0174476_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 461) (SourceJson.white (fragment0174476Field005Chars00 ++ tail)) fragment0174476Acc00500 =
      SourceJson.object (fuel + 460) (SourceJson.white tail) fragment0174476Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_005"
  err.flush

noncomputable def fragment0174476Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0174476Field006Value00 : SourceJson := .str (String.ofList ['2', '8', '7', '0', '1', '8', '1', '0', '6', '4', '8', '1', '8', '5', '0', '4', '5', '9', '2', '5', '0', '3', '6', '2', '2', '9', '0', '6', '4', '7', '6', '4', '3', '1', '9', '1', '6', '0', '5', '5', '1', '0', '2', '4', '3', '8', '6', '5', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '/', '2', '8', '8', '1', '8', '6', '2', '5', '5', '8', '3', '3', '2', '1', '9', '4', '4', '9', '9', '0', '7', '0', '2', '4', '0', '7', '4', '8', '3', '9', '0', '5', '6', '9', '0', '8', '7', '7', '0', '0', '7', '3', '8', '0', '4', '3', '6', '1', '5', '3', '3', '5', '1', '4', '4', '7', '7', '8', '6', '1', '6', '1', '0', '1', '3', '3', '2', '1', '8', '0', '3'])
noncomputable def fragment0174476Acc00700 : List (String × SourceJson) := (fragment0174476Field006Key00, fragment0174476Field006Value00) :: fragment0174476Acc00600
noncomputable def fragment0174476Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '8', '7', '0', '1', '8', '1', '0', '6', '4', '8', '1', '8', '5', '0', '4', '5', '9', '2', '5', '0', '3', '6', '2', '2', '9', '0', '6', '4', '7', '6', '4', '3', '1', '9', '1', '6', '0', '5', '5', '1', '0', '2', '4', '3', '8', '6', '5', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '/', '2', '8', '8', '1', '8', '6', '2', '5', '5', '8', '3', '3', '2', '1', '9', '4', '4', '9', '9', '0', '7', '0', '2', '4', '0', '7', '4', '8', '3', '9', '0', '5', '6', '9', '0', '8', '7', '7', '0', '0', '7', '3', '8', '0', '4', '3', '6', '1', '5', '3', '3', '5', '1', '4', '4', '7', '7', '8', '6', '1', '6', '1', '0', '1', '3', '3', '2', '1', '8', '0', '3', '"', ',']

theorem object_fragment0174476_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 460) (SourceJson.white (fragment0174476Field006Chars00 ++ tail)) fragment0174476Acc00600 =
      SourceJson.object (fuel + 459) (SourceJson.white tail) fragment0174476Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_006"
  err.flush

noncomputable def fragment0174476Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0174476Field007Value00 : SourceJson := .str (String.ofList ['4', '9', '3', '8', '1', '1', '5', '3', '2', '8', '1', '0', '3', '8', '3', '9', '9', '4', '1', '2', '4', '8', '0', '8', '4', '7', '8', '0', '6', '5', '3', '3', '7', '3', '1', '0', '2', '6', '2', '0', '6', '3', '7', '3', '8', '3', '5', '2', '2', '2', '2', '3', '5', '0', '5', '2', '0', '2', '5', '3', '0', '2', '0', '5', '8', '7', '0', '5', '6', '9', '9', '7', '1', '4', '4', '1', '5', '4', '7', '8', '1', '3', '4', '8', '9', '3', '9', '0', '0', '3', '7', '3', '7', '0', '0', '6', '8', '9', '1', '2', '9', '7', '8', '4', '4', '4', '4', '6', '9', '6', '6', '3', '5', '8', '2', '3', '8', '3', '7', '8', '3', '7', '7', '4', '0', '6', '3', '1', '3', '2', '6', '2', '7', '9', '9', '6', '3', '7', '3', '5', '5', '1', '5', '4', '2', '2', '9', '5', '5', '2', '8', '6', '2', '8', '9', '0', '4', '6', '1', '6', '2', '8', '4', '6', '0', '9', '2', '7', '9', '8', '8', '1', '8', '9', '1', '1', '6', '0', '8', '2', '2', '4', '7', '0', '7', '7', '9', '0', '7', '4', '1', '4', '7', '0', '1', '0', '5', '8', '2', '9', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '0', '5', '8', '5', '0', '7', '2', '1', '9', '2', '1', '4', '5', '0', '4', '0', '3', '3', '4', '9', '2', '5', '5', '8', '0', '6', '0', '2', '7', '4', '9', '9', '7', '2', '9', '5', '9', '1', '3', '4', '9', '5', '7', '9', '2', '0', '4', '1', '0', '6', '5', '1', '3', '6', '6', '8', '4', '1', '5', '2', '1', '6', '2', '6', '4', '3', '2', '5', '1', '0', '8', '1', '6', '6', '2', '1', '8', '7', '0', '6', '9', '7', '2', '5', '4', '3', '6', '0', '2', '8', '4', '8', '3', '4', '2', '6', '3', '9', '7', '0', '5', '7', '3', '6', '3', '9', '0', '7', '6', '6', '9', '9', '5', '3', '9', '0', '6', '8', '0', '2', '0', '6', '7', '5', '1', '7', '8', '8', '6', '2', '6', '6', '0', '0', '2', '6', '0', '9', '5', '2', '3', '9', '0', '9', '9', '7', '0', '6', '2', '4', '6', '8', '2', '9', '9', '7', '1', '6', '6', '7', '9', '8', '7', '8', '9', '3', '6', '0', '3', '3', '1', '1', '8', '5', '8', '9', '8', '9', '3', '1', '9', '3', '2', '2', '9', '5', '2', '1', '3', '2', '6', '3', '0', '3', '8', '6', '5', '7', '6', '5', '6', '6', '4', '6', '0', '3', '6', '5', '1', '5', '9', '4', '2', '5', '2', '7', '5', '5', '3', '2', '1', '3', '4', '3', '5', '1', '9', '7', '9', '1', '5', '1'])
noncomputable def fragment0174476Acc00800 : List (String × SourceJson) := (fragment0174476Field007Key00, fragment0174476Field007Value00) :: fragment0174476Acc00700
noncomputable def fragment0174476Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '9', '3', '8', '1', '1', '5', '3', '2', '8', '1', '0', '3', '8', '3', '9', '9', '4', '1', '2', '4', '8', '0', '8', '4', '7', '8', '0', '6', '5', '3', '3', '7', '3', '1', '0', '2', '6', '2', '0', '6', '3', '7', '3', '8', '3', '5', '2', '2', '2', '2', '3', '5', '0', '5', '2', '0', '2', '5', '3', '0', '2', '0', '5', '8', '7', '0', '5', '6', '9', '9', '7', '1', '4', '4', '1', '5', '4', '7', '8', '1', '3', '4', '8', '9', '3', '9', '0', '0', '3', '7', '3', '7', '0', '0', '6', '8', '9', '1', '2', '9', '7', '8', '4', '4', '4', '4', '6', '9', '6', '6', '3', '5', '8', '2', '3', '8', '3', '7', '8', '3', '7', '7', '4', '0', '6', '3', '1', '3', '2', '6', '2', '7', '9', '9', '6', '3', '7', '3', '5', '5', '1', '5', '4', '2', '2', '9', '5', '5', '2', '8', '6', '2', '8', '9', '0', '4', '6', '1', '6', '2', '8', '4', '6', '0', '9', '2', '7', '9', '8', '8', '1', '8', '9', '1', '1', '6', '0', '8', '2', '2', '4', '7', '0', '7', '7', '9', '0', '7', '4', '1', '4', '7', '0', '1', '0', '5', '8', '2', '9', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '0', '5', '8', '5', '0', '7', '2', '1', '9', '2', '1', '4', '5', '0', '4', '0', '3', '3', '4', '9', '2', '5', '5', '8', '0', '6', '0', '2', '7', '4', '9', '9', '7', '2', '9', '5', '9', '1', '3', '4', '9', '5', '7', '9', '2', '0', '4', '1', '0', '6', '5', '1', '3', '6', '6', '8', '4', '1', '5', '2', '1', '6', '2', '6', '4', '3', '2', '5', '1', '0', '8', '1', '6', '6', '2', '1', '8', '7', '0', '6', '9', '7', '2', '5', '4', '3', '6', '0', '2', '8', '4', '8', '3', '4', '2', '6', '3', '9', '7', '0', '5', '7', '3', '6', '3', '9', '0', '7', '6', '6', '9', '9', '5', '3', '9', '0', '6', '8', '0', '2', '0', '6', '7', '5', '1', '7', '8', '8', '6', '2', '6', '6', '0', '0', '2', '6', '0', '9', '5', '2', '3', '9', '0', '9', '9', '7', '0', '6', '2', '4', '6', '8', '2', '9', '9', '7', '1', '6', '6', '7', '9', '8', '7', '8', '9', '3', '6', '0', '3', '3', '1', '1', '8', '5', '8', '9', '8', '9', '3', '1', '9', '3', '2', '2', '9', '5', '2', '1', '3', '2', '6', '3', '0', '3', '8', '6', '5', '7', '6', '5', '6', '6', '4', '6', '0', '3', '6', '5', '1', '5', '9', '4', '2', '5', '2', '7', '5', '5', '3', '2', '1', '3', '4', '3', '5', '1', '9', '7', '9', '1', '5', '1', '"', ',']

theorem object_fragment0174476_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 459) (SourceJson.white (fragment0174476Field007Chars00 ++ tail)) fragment0174476Acc00700 =
      SourceJson.object (fuel + 458) (SourceJson.white tail) fragment0174476Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_007"
  err.flush

noncomputable def fragment0174476Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0174476Field008Value00 : SourceJson := .str (String.ofList ['7', '8', '9', '0', '7', '0', '1', '4', '9', '0', '6', '5', '0', '0', '7', '1'])
noncomputable def fragment0174476Acc00900 : List (String × SourceJson) := (fragment0174476Field008Key00, fragment0174476Field008Value00) :: fragment0174476Acc00800
noncomputable def fragment0174476Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '8', '9', '0', '7', '0', '1', '4', '9', '0', '6', '5', '0', '0', '7', '1', '"', ',']

theorem object_fragment0174476_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 458) (SourceJson.white (fragment0174476Field008Chars00 ++ tail)) fragment0174476Acc00800 =
      SourceJson.object (fuel + 457) (SourceJson.white tail) fragment0174476Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_008"
  err.flush

noncomputable def fragment0174476Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0174476Field009Value00 : SourceJson := .str (String.ofList ['2', '9', '9', '6', '0', '3', '7', '7', '3', '3', '5', '7', '4', '3', '0', '1', '6'])
noncomputable def fragment0174476Acc01000 : List (String × SourceJson) := (fragment0174476Field009Key00, fragment0174476Field009Value00) :: fragment0174476Acc00900
noncomputable def fragment0174476Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '9', '6', '0', '3', '7', '7', '3', '3', '5', '7', '4', '3', '0', '1', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0174476_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 457) (SourceJson.white (fragment0174476Field009Chars00 ++ tail)) fragment0174476Acc00900 =
      .ok (.obj (fragment0174476Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0174476_object_field_009"
  err.flush

noncomputable def fragment0174476Chars : List Char := '{' :: (fragment0174476Field000Chars00 ++ fragment0174476Field001Chars00 ++ fragment0174476Field002Chars00 ++ fragment0174476Field003Chars00 ++ fragment0174476Field004Chars00 ++ fragment0174476Field005Chars00 ++ fragment0174476Field006Chars00 ++ fragment0174476Field007Chars00 ++ fragment0174476Field008Chars00 ++ fragment0174476Field009Chars00)
noncomputable def fragment0174476Value : SourceJson := .obj (fragment0174476Acc01000.reverse)

theorem value_fragment0174476 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 467) (fragment0174476Chars ++ tail) =
      .ok (fragment0174476Value, tail) := by
  have hinput : fragment0174476Chars ++ tail = '{' :: (fragment0174476Field000Chars00 ++ (fragment0174476Field001Chars00 ++ (fragment0174476Field002Chars00 ++ (fragment0174476Field003Chars00 ++ (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0174476Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 467) (fragment0174476Chars ++ tail) =
        SourceJson.value (fuel + 467) ('{' :: (fragment0174476Field000Chars00 ++ (fragment0174476Field001Chars00 ++ (fragment0174476Field002Chars00 ++ (fragment0174476Field003Chars00 ++ (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 467)) hinput
    _ = SourceJson.object (fuel + 466) (SourceJson.white (fragment0174476Field000Chars00 ++ (fragment0174476Field001Chars00 ++ (fragment0174476Field002Chars00 ++ (fragment0174476Field003Chars00 ++ (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))))))))))) fragment0174476Acc00000 := by rfl
    _ = SourceJson.object (fuel + 465) (SourceJson.white (fragment0174476Field001Chars00 ++ (fragment0174476Field002Chars00 ++ (fragment0174476Field003Chars00 ++ (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail))))))))))) fragment0174476Acc00100 := object_fragment0174476_field_000 fuel (fragment0174476Field001Chars00 ++ (fragment0174476Field002Chars00 ++ (fragment0174476Field003Chars00 ++ (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 464) (SourceJson.white (fragment0174476Field002Chars00 ++ (fragment0174476Field003Chars00 ++ (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))))))))) fragment0174476Acc00200 := object_fragment0174476_field_001 fuel (fragment0174476Field002Chars00 ++ (fragment0174476Field003Chars00 ++ (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 463) (SourceJson.white (fragment0174476Field003Chars00 ++ (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail))))))))) fragment0174476Acc00300 := object_fragment0174476_field_002 fuel (fragment0174476Field003Chars00 ++ (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 462) (SourceJson.white (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))))))) fragment0174476Acc00400 := object_fragment0174476_field_003 fuel (fragment0174476Field004Chars00 ++ (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 461) (SourceJson.white (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail))))))) fragment0174476Acc00500 := object_fragment0174476_field_004 fuel (fragment0174476Field005Chars00 ++ (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 460) (SourceJson.white (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))))) fragment0174476Acc00600 := object_fragment0174476_field_005 fuel (fragment0174476Field006Chars00 ++ (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 459) (SourceJson.white (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail))))) fragment0174476Acc00700 := object_fragment0174476_field_006 fuel (fragment0174476Field007Chars00 ++ (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 458) (SourceJson.white (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))) fragment0174476Acc00800 := object_fragment0174476_field_007 fuel (fragment0174476Field008Chars00 ++ (fragment0174476Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 457) (SourceJson.white (fragment0174476Field009Chars00 ++ (tail))) fragment0174476Acc00900 := object_fragment0174476_field_008 fuel (fragment0174476Field009Chars00 ++ (tail))
    _ = .ok (fragment0174476Value, tail) := object_fragment0174476_field_009 fuel (tail)

noncomputable def fragment0176562Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0176562Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0176562Field000Value00 : SourceJson := .number (String.ofList ['2', '7'])
noncomputable def fragment0176562Acc00100 : List (String × SourceJson) := (fragment0176562Field000Key00, fragment0176562Field000Value00) :: fragment0176562Acc00000
noncomputable def fragment0176562Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '7', ',']

theorem object_fragment0176562_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 411) (SourceJson.white (fragment0176562Field000Chars00 ++ tail)) fragment0176562Acc00000 =
      SourceJson.object (fuel + 410) (SourceJson.white tail) fragment0176562Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_000"
  err.flush

noncomputable def fragment0176562Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0176562Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0176562Acc00200 : List (String × SourceJson) := (fragment0176562Field001Key00, fragment0176562Field001Value00) :: fragment0176562Acc00100
noncomputable def fragment0176562Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0176562_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 410) (SourceJson.white (fragment0176562Field001Chars00 ++ tail)) fragment0176562Acc00100 =
      SourceJson.object (fuel + 409) (SourceJson.white tail) fragment0176562Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_001"
  err.flush

noncomputable def fragment0176562Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0176562Field002Value00 : SourceJson := .str (String.ofList ['1', '9', '3', '4', '1', '9', '3', '3', '2', '7', '7', '6', '1', '8', '6', '6', '0', '1', '3', '1', '4', '7', '1', '9', '0', '6', '3', '4', '8', '9', '1', '8', '0', '1', '8', '9', '0', '8', '3', '/', '1', '6', '5', '7', '1', '9', '4', '6', '9', '4', '0', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0176562Acc00300 : List (String × SourceJson) := (fragment0176562Field002Key00, fragment0176562Field002Value00) :: fragment0176562Acc00200
noncomputable def fragment0176562Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '9', '3', '4', '1', '9', '3', '3', '2', '7', '7', '6', '1', '8', '6', '6', '0', '1', '3', '1', '4', '7', '1', '9', '0', '6', '3', '4', '8', '9', '1', '8', '0', '1', '8', '9', '0', '8', '3', '/', '1', '6', '5', '7', '1', '9', '4', '6', '9', '4', '0', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0176562_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 409) (SourceJson.white (fragment0176562Field002Chars00 ++ tail)) fragment0176562Acc00200 =
      SourceJson.object (fuel + 408) (SourceJson.white tail) fragment0176562Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_002"
  err.flush

noncomputable def fragment0176562Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0176562Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0176562Acc00400 : List (String × SourceJson) := (fragment0176562Field003Key00, fragment0176562Field003Value00) :: fragment0176562Acc00300
noncomputable def fragment0176562Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0176562_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 408) (SourceJson.white (fragment0176562Field003Chars00 ++ tail)) fragment0176562Acc00300 =
      SourceJson.object (fuel + 407) (SourceJson.white tail) fragment0176562Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_003"
  err.flush

noncomputable def fragment0176562Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0176562Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0176562Acc00500 : List (String × SourceJson) := (fragment0176562Field004Key00, fragment0176562Field004Value00) :: fragment0176562Acc00400
noncomputable def fragment0176562Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0176562_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0176562Field004Chars00 ++ tail)) fragment0176562Acc00400 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0176562Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_004"
  err.flush

noncomputable def fragment0176562Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0176562Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '7', '1', '2', '5', '5', '5', '3', '0', '4', '8', '7', '1', '9', '9', '2', '0', '5', '2', '2', '7', '7', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '3', '1', '1', '4', '1', '0', '0', '1', '4', '8', '2', '3', '3', '9', '5', '4', '0', '5', '2', '3', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '3', '0', '3', '1', '2', '9', '5', '2', '0', '9', '9', '0', '0', '4', '6', '7', '4', '6', '8', '6', '1', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '8', '5', '1', '6', '7', '5', '6', '4', '2', '4', '4', '2', '1', '8', '8', '9', '1', '5', '5', '5', '1', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '6', '8', '1', '2', '4', '5', '4', '1', '0', '5', '8', '0', '9', '9', '5', '8', '0', '4', '4', '9', '/', '2', '8', '5', '7', '9', '3', '6', '2', '4', '8', '9', '6', '4', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '6', '4', '6', '0', '3', '4', '6', '1', '5', '6', '9', '3', '0', '3', '8', '0', '9', '/', '1', '2', '4', '7', '0', '9', '9', '4', '5', '4', '0', '9', '3', '4', '2', '7', '2', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '4', '4', '0', '7', '3', '3', '3', '0', '2', '1', '0', '3', '9', '0', '1', '0', '4', '2', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '2', '0', '0', '1', '1', '8', '1', '3', '5', '8', '3', '6', '4', '5', '5', '2', '5', '5', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '5', '2', '2', '7', '1', '5', '4', '9', '5', '8', '3', '9', '9', '2', '9', '9', '4', '3', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '9', '8', '5', '7', '3', '9', '4', '8', '6', '5', '7', '8', '3', '3', '9', '0', '0', '6', '7', '/', '2', '0', '4', '1', '3', '8', '3', '0', '3', '4', '9', '7', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0176562Acc00600 : List (String × SourceJson) := (fragment0176562Field005Key00, fragment0176562Field005Value00) :: fragment0176562Acc00500
noncomputable def fragment0176562Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '1', '2', '5', '5', '5', '3', '0', '4', '8', '7', '1', '9', '9', '2', '0', '5', '2', '2', '7', '7', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '3', '1', '1', '4', '1', '0', '0', '1', '4', '8', '2', '3', '3', '9', '5', '4', '0', '5', '2', '3', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '3', '0', '3', '1', '2', '9', '5', '2', '0', '9', '9', '0', '0', '4', '6', '7', '4', '6', '8', '6', '1', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '8', '5', '1', '6', '7', '5', '6', '4', '2', '4', '4', '2', '1', '8', '8', '9', '1', '5', '5', '5', '1', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '6', '8', '1', '2', '4', '5', '4', '1', '0', '5', '8', '0', '9', '9', '5', '8', '0', '4', '4', '9', '/', '2', '8', '5', '7', '9', '3', '6', '2', '4', '8', '9', '6', '4', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '6', '4', '6', '0', '3', '4', '6', '1', '5', '6', '9', '3', '0', '3', '8', '0', '9', '/', '1', '2', '4', '7', '0', '9', '9', '4', '5', '4', '0', '9', '3', '4', '2', '7', '2', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '4', '4', '0', '7', '3', '3', '3', '0', '2', '1', '0', '3', '9', '0', '1', '0', '4', '2', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '0', '0', '1', '1', '8', '1', '3', '5', '8', '3', '6', '4', '5', '5', '2', '5', '5', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '5', '2', '2', '7', '1', '5', '4', '9', '5', '8', '3', '9', '9', '2', '9', '9', '4', '3', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '9', '8', '5', '7', '3', '9', '4', '8', '6', '5', '7', '8', '3', '3', '9', '0', '0', '6', '7', '/', '2', '0', '4', '1', '3', '8', '3', '0', '3', '4', '9', '7', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0176562_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0176562Field005Chars00 ++ tail)) fragment0176562Acc00500 =
      SourceJson.object (fuel + 405) (SourceJson.white tail) fragment0176562Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_005"
  err.flush

noncomputable def fragment0176562Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0176562Field006Value00 : SourceJson := .str (String.ofList ['2', '4', '1', '0', '4', '8', '5', '0', '2', '7', '6', '5', '3', '1', '7', '2', '1', '7', '5', '0', '9', '6', '5', '2', '6', '8', '0', '3', '3', '1', '2', '4', '6', '9', '2', '0', '5', '0', '1', '6', '8', '4', '0', '3', '4', '5', '6', '0', '0', '/', '1', '0', '4', '7', '8', '9', '8', '4', '3', '6', '5', '7', '0', '6', '5', '2', '5', '8', '5', '9', '0', '8', '0', '4', '8', '7', '2', '9', '4', '7', '1', '8', '7', '7', '1', '9', '7', '2', '5', '2', '9', '8', '7', '0', '3', '3', '3', '1', '3', '8', '6', '4', '3', '2', '6', '4', '2', '5', '3', '5', '8', '5', '0', '1', '9', '7'])
noncomputable def fragment0176562Acc00700 : List (String × SourceJson) := (fragment0176562Field006Key00, fragment0176562Field006Value00) :: fragment0176562Acc00600
noncomputable def fragment0176562Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '1', '0', '4', '8', '5', '0', '2', '7', '6', '5', '3', '1', '7', '2', '1', '7', '5', '0', '9', '6', '5', '2', '6', '8', '0', '3', '3', '1', '2', '4', '6', '9', '2', '0', '5', '0', '1', '6', '8', '4', '0', '3', '4', '5', '6', '0', '0', '/', '1', '0', '4', '7', '8', '9', '8', '4', '3', '6', '5', '7', '0', '6', '5', '2', '5', '8', '5', '9', '0', '8', '0', '4', '8', '7', '2', '9', '4', '7', '1', '8', '7', '7', '1', '9', '7', '2', '5', '2', '9', '8', '7', '0', '3', '3', '3', '1', '3', '8', '6', '4', '3', '2', '6', '4', '2', '5', '3', '5', '8', '5', '0', '1', '9', '7', '"', ',']

theorem object_fragment0176562_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 405) (SourceJson.white (fragment0176562Field006Chars00 ++ tail)) fragment0176562Acc00600 =
      SourceJson.object (fuel + 404) (SourceJson.white tail) fragment0176562Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_006"
  err.flush

noncomputable def fragment0176562Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0176562Field007Value00 : SourceJson := .str (String.ofList ['8', '4', '2', '5', '1', '8', '6', '5', '7', '4', '2', '2', '0', '1', '2', '6', '0', '9', '0', '4', '2', '3', '9', '4', '7', '2', '3', '7', '7', '5', '0', '9', '9', '0', '4', '7', '0', '1', '0', '3', '9', '4', '8', '1', '0', '3', '0', '4', '6', '6', '3', '6', '1', '0', '5', '9', '7', '4', '8', '8', '6', '0', '5', '0', '0', '5', '6', '2', '5', '1', '8', '0', '5', '8', '3', '8', '2', '1', '0', '9', '7', '9', '5', '7', '7', '8', '5', '0', '6', '2', '4', '5', '5', '9', '1', '2', '1', '0', '1', '7', '5', '3', '0', '8', '9', '5', '7', '3', '5', '9', '6', '0', '2', '9', '6', '2', '4', '1', '4', '1', '5', '1', '8', '8', '2', '1', '7', '2', '8', '1', '8', '6', '3', '4', '7', '3', '1', '3', '7', '3', '2', '1', '7', '6', '8', '9', '7', '3', '4', '6', '2', '3', '8', '4', '1', '2', '0', '6', '4', '1', '6', '1', '1', '3', '5', '3', '4', '5', '3', '9', '4', '0', '9', '6', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '7', '6', '7', '8', '3', '6', '3', '6', '2', '5', '1', '6', '5', '9', '2', '4', '9', '1', '7', '4', '0', '3', '4', '1', '6', '4', '4', '9', '2', '5', '5', '9', '3', '8', '0', '7', '5', '4', '0', '6', '9', '6', '8', '4', '2', '1', '8', '6', '8', '2', '4', '3', '8', '7', '7', '3', '4', '0', '8', '7', '5', '4', '5', '1', '6', '2', '8', '4', '3', '5', '6', '0', '2', '0', '0', '1', '2', '8', '0', '7', '1', '4', '8', '1', '9', '8', '9', '4', '6', '7', '7', '1', '4', '6', '9', '7', '1', '9', '9', '3', '3', '4', '7', '2', '3', '6', '6', '2', '9', '1', '4', '2', '3', '7', '1', '1', '0', '5', '8', '9', '6', '1', '0', '7', '0', '6', '0', '2', '4', '4', '7', '2', '5', '2', '0', '7', '2', '7', '0', '8', '0', '8', '8', '6', '5', '2', '4', '3', '1', '8', '8', '9', '9', '9', '2', '8', '0', '9', '5', '6', '0', '3', '6', '9', '0', '4', '0', '7', '8', '3', '6', '1', '1', '0', '5', '5', '5', '3', '7', '1', '8', '9', '3', '5', '1', '2', '8', '6', '3', '4', '2', '6', '9', '6', '3', '9', '2', '4', '8', '1', '2', '0', '1', '3', '5', '3', '9'])
noncomputable def fragment0176562Acc00800 : List (String × SourceJson) := (fragment0176562Field007Key00, fragment0176562Field007Value00) :: fragment0176562Acc00700
noncomputable def fragment0176562Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '4', '2', '5', '1', '8', '6', '5', '7', '4', '2', '2', '0', '1', '2', '6', '0', '9', '0', '4', '2', '3', '9', '4', '7', '2', '3', '7', '7', '5', '0', '9', '9', '0', '4', '7', '0', '1', '0', '3', '9', '4', '8', '1', '0', '3', '0', '4', '6', '6', '3', '6', '1', '0', '5', '9', '7', '4', '8', '8', '6', '0', '5', '0', '0', '5', '6', '2', '5', '1', '8', '0', '5', '8', '3', '8', '2', '1', '0', '9', '7', '9', '5', '7', '7', '8', '5', '0', '6', '2', '4', '5', '5', '9', '1', '2', '1', '0', '1', '7', '5', '3', '0', '8', '9', '5', '7', '3', '5', '9', '6', '0', '2', '9', '6', '2', '4', '1', '4', '1', '5', '1', '8', '8', '2', '1', '7', '2', '8', '1', '8', '6', '3', '4', '7', '3', '1', '3', '7', '3', '2', '1', '7', '6', '8', '9', '7', '3', '4', '6', '2', '3', '8', '4', '1', '2', '0', '6', '4', '1', '6', '1', '1', '3', '5', '3', '4', '5', '3', '9', '4', '0', '9', '6', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '7', '6', '7', '8', '3', '6', '3', '6', '2', '5', '1', '6', '5', '9', '2', '4', '9', '1', '7', '4', '0', '3', '4', '1', '6', '4', '4', '9', '2', '5', '5', '9', '3', '8', '0', '7', '5', '4', '0', '6', '9', '6', '8', '4', '2', '1', '8', '6', '8', '2', '4', '3', '8', '7', '7', '3', '4', '0', '8', '7', '5', '4', '5', '1', '6', '2', '8', '4', '3', '5', '6', '0', '2', '0', '0', '1', '2', '8', '0', '7', '1', '4', '8', '1', '9', '8', '9', '4', '6', '7', '7', '1', '4', '6', '9', '7', '1', '9', '9', '3', '3', '4', '7', '2', '3', '6', '6', '2', '9', '1', '4', '2', '3', '7', '1', '1', '0', '5', '8', '9', '6', '1', '0', '7', '0', '6', '0', '2', '4', '4', '7', '2', '5', '2', '0', '7', '2', '7', '0', '8', '0', '8', '8', '6', '5', '2', '4', '3', '1', '8', '8', '9', '9', '9', '2', '8', '0', '9', '5', '6', '0', '3', '6', '9', '0', '4', '0', '7', '8', '3', '6', '1', '1', '0', '5', '5', '5', '3', '7', '1', '8', '9', '3', '5', '1', '2', '8', '6', '3', '4', '2', '6', '9', '6', '3', '9', '2', '4', '8', '1', '2', '0', '1', '3', '5', '3', '9', '"', ',']

theorem object_fragment0176562_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 404) (SourceJson.white (fragment0176562Field007Chars00 ++ tail)) fragment0176562Acc00700 =
      SourceJson.object (fuel + 403) (SourceJson.white tail) fragment0176562Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_007"
  err.flush

noncomputable def fragment0176562Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0176562Field008Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '4', '8', '8', '6', '3', '8', '6', '3', '2'])
noncomputable def fragment0176562Acc00900 : List (String × SourceJson) := (fragment0176562Field008Key00, fragment0176562Field008Value00) :: fragment0176562Acc00800
noncomputable def fragment0176562Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '2', '2', '4', '8', '8', '6', '3', '8', '6', '3', '2', '"', ',']

theorem object_fragment0176562_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0176562Field008Chars00 ++ tail)) fragment0176562Acc00800 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0176562Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_008"
  err.flush

noncomputable def fragment0176562Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0176562Field009Value00 : SourceJson := .str (String.ofList ['6', '8', '3', '3', '7', '7', '5', '9', '3', '9', '1', '3', '0'])
noncomputable def fragment0176562Acc01000 : List (String × SourceJson) := (fragment0176562Field009Key00, fragment0176562Field009Value00) :: fragment0176562Acc00900
noncomputable def fragment0176562Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '8', '3', '3', '7', '7', '5', '9', '3', '9', '1', '3', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0176562_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0176562Field009Chars00 ++ tail)) fragment0176562Acc00900 =
      .ok (.obj (fragment0176562Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176562_object_field_009"
  err.flush

noncomputable def fragment0176562Chars : List Char := '{' :: (fragment0176562Field000Chars00 ++ fragment0176562Field001Chars00 ++ fragment0176562Field002Chars00 ++ fragment0176562Field003Chars00 ++ fragment0176562Field004Chars00 ++ fragment0176562Field005Chars00 ++ fragment0176562Field006Chars00 ++ fragment0176562Field007Chars00 ++ fragment0176562Field008Chars00 ++ fragment0176562Field009Chars00)
noncomputable def fragment0176562Value : SourceJson := .obj (fragment0176562Acc01000.reverse)

theorem value_fragment0176562 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 412) (fragment0176562Chars ++ tail) =
      .ok (fragment0176562Value, tail) := by
  have hinput : fragment0176562Chars ++ tail = '{' :: (fragment0176562Field000Chars00 ++ (fragment0176562Field001Chars00 ++ (fragment0176562Field002Chars00 ++ (fragment0176562Field003Chars00 ++ (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0176562Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 412) (fragment0176562Chars ++ tail) =
        SourceJson.value (fuel + 412) ('{' :: (fragment0176562Field000Chars00 ++ (fragment0176562Field001Chars00 ++ (fragment0176562Field002Chars00 ++ (fragment0176562Field003Chars00 ++ (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 412)) hinput
    _ = SourceJson.object (fuel + 411) (SourceJson.white (fragment0176562Field000Chars00 ++ (fragment0176562Field001Chars00 ++ (fragment0176562Field002Chars00 ++ (fragment0176562Field003Chars00 ++ (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))))))))))) fragment0176562Acc00000 := by rfl
    _ = SourceJson.object (fuel + 410) (SourceJson.white (fragment0176562Field001Chars00 ++ (fragment0176562Field002Chars00 ++ (fragment0176562Field003Chars00 ++ (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail))))))))))) fragment0176562Acc00100 := object_fragment0176562_field_000 fuel (fragment0176562Field001Chars00 ++ (fragment0176562Field002Chars00 ++ (fragment0176562Field003Chars00 ++ (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 409) (SourceJson.white (fragment0176562Field002Chars00 ++ (fragment0176562Field003Chars00 ++ (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))))))))) fragment0176562Acc00200 := object_fragment0176562_field_001 fuel (fragment0176562Field002Chars00 ++ (fragment0176562Field003Chars00 ++ (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 408) (SourceJson.white (fragment0176562Field003Chars00 ++ (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail))))))))) fragment0176562Acc00300 := object_fragment0176562_field_002 fuel (fragment0176562Field003Chars00 ++ (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))))))) fragment0176562Acc00400 := object_fragment0176562_field_003 fuel (fragment0176562Field004Chars00 ++ (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail))))))) fragment0176562Acc00500 := object_fragment0176562_field_004 fuel (fragment0176562Field005Chars00 ++ (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 405) (SourceJson.white (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))))) fragment0176562Acc00600 := object_fragment0176562_field_005 fuel (fragment0176562Field006Chars00 ++ (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 404) (SourceJson.white (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail))))) fragment0176562Acc00700 := object_fragment0176562_field_006 fuel (fragment0176562Field007Chars00 ++ (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))) fragment0176562Acc00800 := object_fragment0176562_field_007 fuel (fragment0176562Field008Chars00 ++ (fragment0176562Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0176562Field009Chars00 ++ (tail))) fragment0176562Acc00900 := object_fragment0176562_field_008 fuel (fragment0176562Field009Chars00 ++ (tail))
    _ = .ok (fragment0176562Value, tail) := object_fragment0176562_field_009 fuel (tail)

noncomputable def fragment0178519Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0178519Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0178519Field000Value00 : SourceJson := .number (String.ofList ['2', '8'])
noncomputable def fragment0178519Acc00100 : List (String × SourceJson) := (fragment0178519Field000Key00, fragment0178519Field000Value00) :: fragment0178519Acc00000
noncomputable def fragment0178519Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '8', ',']

theorem object_fragment0178519_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0178519Field000Chars00 ++ tail)) fragment0178519Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0178519Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_000"
  err.flush

noncomputable def fragment0178519Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0178519Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0178519Acc00200 : List (String × SourceJson) := (fragment0178519Field001Key00, fragment0178519Field001Value00) :: fragment0178519Acc00100
noncomputable def fragment0178519Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0178519_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0178519Field001Chars00 ++ tail)) fragment0178519Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0178519Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_001"
  err.flush

noncomputable def fragment0178519Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0178519Field002Value00 : SourceJson := .str (String.ofList ['4', '2', '8', '0', '1', '4', '4', '4', '9', '7', '7', '7', '9', '6', '2', '2', '2', '3', '6', '9', '8', '6', '7', '7', '3', '2', '7', '4', '5', '8', '2', '2', '1', '5', '6', '4', '4', '8', '6', '3', '/', '3', '6', '5', '2', '5', '9', '2', '3', '8', '6', '8', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0178519Acc00300 : List (String × SourceJson) := (fragment0178519Field002Key00, fragment0178519Field002Value00) :: fragment0178519Acc00200
noncomputable def fragment0178519Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '2', '8', '0', '1', '4', '4', '4', '9', '7', '7', '7', '9', '6', '2', '2', '2', '3', '6', '9', '8', '6', '7', '7', '3', '2', '7', '4', '5', '8', '2', '2', '1', '5', '6', '4', '4', '8', '6', '3', '/', '3', '6', '5', '2', '5', '9', '2', '3', '8', '6', '8', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0178519_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0178519Field002Chars00 ++ tail)) fragment0178519Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0178519Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_002"
  err.flush

noncomputable def fragment0178519Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0178519Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0178519Acc00400 : List (String × SourceJson) := (fragment0178519Field003Key00, fragment0178519Field003Value00) :: fragment0178519Acc00300
noncomputable def fragment0178519Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0178519_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0178519Field003Chars00 ++ tail)) fragment0178519Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0178519Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_003"
  err.flush

noncomputable def fragment0178519Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0178519Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0178519Acc00500 : List (String × SourceJson) := (fragment0178519Field004Key00, fragment0178519Field004Value00) :: fragment0178519Acc00400
noncomputable def fragment0178519Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0178519_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0178519Field004Chars00 ++ tail)) fragment0178519Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0178519Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_004"
  err.flush

noncomputable def fragment0178519Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0178519Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '6', '2', '5', '9', '7', '7', '1', '8', '7', '1', '0', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '9', '4', '0', '8', '6', '1', '2', '0', '0', '2', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '4', '1', '7', '6', '7', '1', '5', '2', '9', '0', '0', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '5', '0', '2', '5', '3', '2', '4', '3', '6', '6', '2', '1', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '2', '9', '6', '7', '3', '1', '6', '3', '2', '8', '0', '7', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '5', '1', '7', '3', '0', '0', '4', '0', '2', '1', '7', '/', '4', '6', '5', '9', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '0', '1', '6', '3', '6', '4', '6', '5', '1', '7', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '9', '1', '5', '8', '5', '4', '1', '6', '0', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '3', '8', '1', '3', '6', '4', '0', '5', '9', '3', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '5', '8', '3', '9', '3', '7', '6', '7', '9', '5', '4', '7', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0178519Acc00600 : List (String × SourceJson) := (fragment0178519Field005Key00, fragment0178519Field005Value00) :: fragment0178519Acc00500
noncomputable def fragment0178519Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '2', '5', '9', '7', '7', '1', '8', '7', '1', '0', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '9', '4', '0', '8', '6', '1', '2', '0', '0', '2', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '4', '1', '7', '6', '7', '1', '5', '2', '9', '0', '0', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '5', '0', '2', '5', '3', '2', '4', '3', '6', '6', '2', '1', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '2', '9', '6', '7', '3', '1', '6', '3', '2', '8', '0', '7', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '5', '1', '7', '3', '0', '0', '4', '0', '2', '1', '7', '/', '4', '6', '5', '9', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '0', '1', '6', '3', '6', '4', '6', '5', '1', '7', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '9', '1', '5', '8', '5', '4', '1', '6', '0', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '3', '8', '1', '3', '6', '4', '0', '5', '9', '3', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '8', '3', '9', '3', '7', '6', '7', '9', '5', '4', '7', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0178519_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0178519Field005Chars00 ++ tail)) fragment0178519Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0178519Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_005"
  err.flush

noncomputable def fragment0178519Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0178519Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '9', '1', '9', '4', '6', '3', '9', '8', '2', '2', '8', '1', '1', '0', '1', '6', '5', '8', '3', '5', '6', '6', '8', '5', '1', '6', '3', '3', '8', '7', '6', '0', '7', '1', '6', '3', '7', '0', '9', '9', '5', '2', '7', '7', '5', '6', '8', '0', '0', '/', '1', '6', '5', '5', '1', '1', '3', '8', '8', '4', '4', '4', '7', '7', '7', '1', '0', '1', '8', '4', '9', '7', '7', '3', '8', '9', '0', '4', '9', '3', '9', '0', '7', '9', '0', '8', '8', '3', '6', '2', '4', '0', '1', '6', '6', '6', '6', '4', '4', '9', '3', '2', '1', '4', '7', '0', '9', '2', '1', '9', '5', '5', '9', '4', '7', '0', '3'])
noncomputable def fragment0178519Acc00700 : List (String × SourceJson) := (fragment0178519Field006Key00, fragment0178519Field006Value00) :: fragment0178519Acc00600
noncomputable def fragment0178519Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '9', '1', '9', '4', '6', '3', '9', '8', '2', '2', '8', '1', '1', '0', '1', '6', '5', '8', '3', '5', '6', '6', '8', '5', '1', '6', '3', '3', '8', '7', '6', '0', '7', '1', '6', '3', '7', '0', '9', '9', '5', '2', '7', '7', '5', '6', '8', '0', '0', '/', '1', '6', '5', '5', '1', '1', '3', '8', '8', '4', '4', '4', '7', '7', '7', '1', '0', '1', '8', '4', '9', '7', '7', '3', '8', '9', '0', '4', '9', '3', '9', '0', '7', '9', '0', '8', '8', '3', '6', '2', '4', '0', '1', '6', '6', '6', '6', '4', '4', '9', '3', '2', '1', '4', '7', '0', '9', '2', '1', '9', '5', '5', '9', '4', '7', '0', '3', '"', ',']

theorem object_fragment0178519_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0178519Field006Chars00 ++ tail)) fragment0178519Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0178519Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_006"
  err.flush

noncomputable def fragment0178519Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0178519Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '9', '6', '2', '8', '3', '3', '0', '5', '1', '2', '1', '0', '1', '0', '2', '6', '5', '5', '2', '6', '9', '3', '7', '3', '7', '6', '5', '8', '2', '8', '9', '5', '1', '7', '6', '7', '1', '9', '5', '3', '6', '3', '8', '4', '9', '2', '6', '2', '0', '6', '6', '2', '8', '5', '6', '4', '0', '7', '4', '2', '4', '6', '7', '5', '5', '9', '2', '6', '9', '4', '3', '3', '8', '9', '2', '8', '1', '0', '7', '6', '0', '4', '0', '9', '7', '6', '5', '2', '5', '1', '6', '3', '6', '2', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '6', '8', '1', '6', '7', '7', '2', '9', '6', '0', '7', '0', '4', '4', '6', '9', '9', '5', '6', '6', '5', '7', '2', '0', '7', '0', '6', '5', '1', '7', '8', '8', '1', '2', '3', '6', '4', '8', '2', '7', '3', '4', '5', '0', '4', '5', '7', '4', '7', '0', '6', '6', '2', '5', '8', '6', '4', '5', '7', '4', '9', '9', '3', '2', '2', '1', '6', '0', '9', '6', '7', '3', '9', '5', '2', '4', '6', '8', '9', '5', '0', '2', '4', '7', '3', '6', '2', '5', '4', '3', '6', '7', '0', '9', '9', '7', '5', '1', '6', '3', '1', '5', '2', '6', '8', '5', '1', '3', '6', '5', '0', '9', '7', '5', '1', '3', '9', '2', '4', '4', '7', '2', '5', '7', '8', '7', '4', '3', '0', '7'])
noncomputable def fragment0178519Acc00800 : List (String × SourceJson) := (fragment0178519Field007Key00, fragment0178519Field007Value00) :: fragment0178519Acc00700
noncomputable def fragment0178519Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '9', '6', '2', '8', '3', '3', '0', '5', '1', '2', '1', '0', '1', '0', '2', '6', '5', '5', '2', '6', '9', '3', '7', '3', '7', '6', '5', '8', '2', '8', '9', '5', '1', '7', '6', '7', '1', '9', '5', '3', '6', '3', '8', '4', '9', '2', '6', '2', '0', '6', '6', '2', '8', '5', '6', '4', '0', '7', '4', '2', '4', '6', '7', '5', '5', '9', '2', '6', '9', '4', '3', '3', '8', '9', '2', '8', '1', '0', '7', '6', '0', '4', '0', '9', '7', '6', '5', '2', '5', '1', '6', '3', '6', '2', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '6', '8', '1', '6', '7', '7', '2', '9', '6', '0', '7', '0', '4', '4', '6', '9', '9', '5', '6', '6', '5', '7', '2', '0', '7', '0', '6', '5', '1', '7', '8', '8', '1', '2', '3', '6', '4', '8', '2', '7', '3', '4', '5', '0', '4', '5', '7', '4', '7', '0', '6', '6', '2', '5', '8', '6', '4', '5', '7', '4', '9', '9', '3', '2', '2', '1', '6', '0', '9', '6', '7', '3', '9', '5', '2', '4', '6', '8', '9', '5', '0', '2', '4', '7', '3', '6', '2', '5', '4', '3', '6', '7', '0', '9', '9', '7', '5', '1', '6', '3', '1', '5', '2', '6', '8', '5', '1', '3', '6', '5', '0', '9', '7', '5', '1', '3', '9', '2', '4', '4', '7', '2', '5', '7', '8', '7', '4', '3', '0', '7', '"', ',']

theorem object_fragment0178519_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0178519Field007Chars00 ++ tail)) fragment0178519Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0178519Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_007"
  err.flush

noncomputable def fragment0178519Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0178519Field008Value00 : SourceJson := .str (String.ofList ['7', '6', '2', '0', '4', '4', '1', '6', '5', '8', '9', '0', '7'])
noncomputable def fragment0178519Acc00900 : List (String × SourceJson) := (fragment0178519Field008Key00, fragment0178519Field008Value00) :: fragment0178519Acc00800
noncomputable def fragment0178519Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '6', '2', '0', '4', '4', '1', '6', '5', '8', '9', '0', '7', '"', ',']

theorem object_fragment0178519_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0178519Field008Chars00 ++ tail)) fragment0178519Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0178519Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_008"
  err.flush

noncomputable def fragment0178519Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0178519Field009Value00 : SourceJson := .str (String.ofList ['3', '3', '5', '6', '2', '8', '8', '8', '4', '3', '5', '9', '9', '9'])
noncomputable def fragment0178519Acc01000 : List (String × SourceJson) := (fragment0178519Field009Key00, fragment0178519Field009Value00) :: fragment0178519Acc00900
noncomputable def fragment0178519Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '3', '5', '6', '2', '8', '8', '8', '4', '3', '5', '9', '9', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0178519_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0178519Field009Chars00 ++ tail)) fragment0178519Acc00900 =
      .ok (.obj (fragment0178519Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0178519_object_field_009"
  err.flush

noncomputable def fragment0178519Chars : List Char := '{' :: (fragment0178519Field000Chars00 ++ fragment0178519Field001Chars00 ++ fragment0178519Field002Chars00 ++ fragment0178519Field003Chars00 ++ fragment0178519Field004Chars00 ++ fragment0178519Field005Chars00 ++ fragment0178519Field006Chars00 ++ fragment0178519Field007Chars00 ++ fragment0178519Field008Chars00 ++ fragment0178519Field009Chars00)
noncomputable def fragment0178519Value : SourceJson := .obj (fragment0178519Acc01000.reverse)

theorem value_fragment0178519 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0178519Chars ++ tail) =
      .ok (fragment0178519Value, tail) := by
  have hinput : fragment0178519Chars ++ tail = '{' :: (fragment0178519Field000Chars00 ++ (fragment0178519Field001Chars00 ++ (fragment0178519Field002Chars00 ++ (fragment0178519Field003Chars00 ++ (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0178519Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0178519Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0178519Field000Chars00 ++ (fragment0178519Field001Chars00 ++ (fragment0178519Field002Chars00 ++ (fragment0178519Field003Chars00 ++ (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0178519Field000Chars00 ++ (fragment0178519Field001Chars00 ++ (fragment0178519Field002Chars00 ++ (fragment0178519Field003Chars00 ++ (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))))))))))) fragment0178519Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0178519Field001Chars00 ++ (fragment0178519Field002Chars00 ++ (fragment0178519Field003Chars00 ++ (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail))))))))))) fragment0178519Acc00100 := object_fragment0178519_field_000 fuel (fragment0178519Field001Chars00 ++ (fragment0178519Field002Chars00 ++ (fragment0178519Field003Chars00 ++ (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0178519Field002Chars00 ++ (fragment0178519Field003Chars00 ++ (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))))))))) fragment0178519Acc00200 := object_fragment0178519_field_001 fuel (fragment0178519Field002Chars00 ++ (fragment0178519Field003Chars00 ++ (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0178519Field003Chars00 ++ (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail))))))))) fragment0178519Acc00300 := object_fragment0178519_field_002 fuel (fragment0178519Field003Chars00 ++ (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))))))) fragment0178519Acc00400 := object_fragment0178519_field_003 fuel (fragment0178519Field004Chars00 ++ (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail))))))) fragment0178519Acc00500 := object_fragment0178519_field_004 fuel (fragment0178519Field005Chars00 ++ (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))))) fragment0178519Acc00600 := object_fragment0178519_field_005 fuel (fragment0178519Field006Chars00 ++ (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail))))) fragment0178519Acc00700 := object_fragment0178519_field_006 fuel (fragment0178519Field007Chars00 ++ (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))) fragment0178519Acc00800 := object_fragment0178519_field_007 fuel (fragment0178519Field008Chars00 ++ (fragment0178519Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0178519Field009Chars00 ++ (tail))) fragment0178519Acc00900 := object_fragment0178519_field_008 fuel (fragment0178519Field009Chars00 ++ (tail))
    _ = .ok (fragment0178519Value, tail) := object_fragment0178519_field_009 fuel (tail)

noncomputable def fragment0180173Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0180173Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0180173Field000Value00 : SourceJson := .number (String.ofList ['2', '9'])
noncomputable def fragment0180173Acc00100 : List (String × SourceJson) := (fragment0180173Field000Key00, fragment0180173Field000Value00) :: fragment0180173Acc00000
noncomputable def fragment0180173Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '9', ',']

theorem object_fragment0180173_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 425) (SourceJson.white (fragment0180173Field000Chars00 ++ tail)) fragment0180173Acc00000 =
      SourceJson.object (fuel + 424) (SourceJson.white tail) fragment0180173Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_000"
  err.flush

noncomputable def fragment0180173Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0180173Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['3']), .number (String.ofList ['0'])]
noncomputable def fragment0180173Acc00200 : List (String × SourceJson) := (fragment0180173Field001Key00, fragment0180173Field001Value00) :: fragment0180173Acc00100
noncomputable def fragment0180173Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0180173_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 424) (SourceJson.white (fragment0180173Field001Chars00 ++ tail)) fragment0180173Acc00100 =
      SourceJson.object (fuel + 423) (SourceJson.white tail) fragment0180173Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_001"
  err.flush

noncomputable def fragment0180173Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0180173Field002Value00 : SourceJson := .str (String.ofList ['1', '4', '1', '0', '1', '8', '2', '5', '3', '1', '3', '3', '9', '5', '7', '1', '0', '7', '7', '7', '7', '3', '9', '4', '6', '2', '7', '9', '7', '7', '7', '1', '9', '7', '2', '8', '4', '4', '7', '4', '2', '7', '7', '/', '3', '6', '1', '9', '5', '2', '3', '6', '4', '9', '2', '0', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0180173Acc00300 : List (String × SourceJson) := (fragment0180173Field002Key00, fragment0180173Field002Value00) :: fragment0180173Acc00200
noncomputable def fragment0180173Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '4', '1', '0', '1', '8', '2', '5', '3', '1', '3', '3', '9', '5', '7', '1', '0', '7', '7', '7', '7', '3', '9', '4', '6', '2', '7', '9', '7', '7', '7', '1', '9', '7', '2', '8', '4', '4', '7', '4', '2', '7', '7', '/', '3', '6', '1', '9', '5', '2', '3', '6', '4', '9', '2', '0', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0180173_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 423) (SourceJson.white (fragment0180173Field002Chars00 ++ tail)) fragment0180173Acc00200 =
      SourceJson.object (fuel + 422) (SourceJson.white tail) fragment0180173Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_002"
  err.flush

noncomputable def fragment0180173Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0180173Field003Value00 : SourceJson := .str (String.ofList ['3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0180173Acc00400 : List (String × SourceJson) := (fragment0180173Field003Key00, fragment0180173Field003Value00) :: fragment0180173Acc00300
noncomputable def fragment0180173Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0180173_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 422) (SourceJson.white (fragment0180173Field003Chars00 ++ tail)) fragment0180173Acc00300 =
      SourceJson.object (fuel + 421) (SourceJson.white tail) fragment0180173Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_003"
  err.flush

noncomputable def fragment0180173Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0180173Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0180173Acc00500 : List (String × SourceJson) := (fragment0180173Field004Key00, fragment0180173Field004Value00) :: fragment0180173Acc00400
noncomputable def fragment0180173Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0180173_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0180173Field004Chars00 ++ tail)) fragment0180173Acc00400 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0180173Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_004"
  err.flush

noncomputable def fragment0180173Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0180173Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '2', '5', '6', '0', '2', '8', '3', '8', '9', '8', '4', '9', '7', '0', '6', '5', '0', '5', '5', '8', '1', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '7', '3', '3', '2', '4', '2', '4', '5', '2', '2', '8', '5', '3', '3', '4', '2', '1', '0', '8', '5', '7', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '0', '3', '7', '8', '5', '2', '7', '0', '3', '3', '8', '6', '6', '6', '8', '5', '7', '5', '4', '9', '7', '/', '1', '1', '6', '5', '6', '1', '7', '3', '3', '5', '1', '6', '0', '9', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '0', '0', '4', '6', '9', '1', '0', '9', '2', '2', '2', '3', '5', '4', '0', '8', '6', '3', '6', '7', '/', '1', '1', '6', '5', '6', '1', '7', '3', '3', '5', '1', '6', '0', '9', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '6', '7', '1', '9', '4', '4', '8', '0', '3', '7', '4', '5', '8', '6', '6', '1', '0', '9', '3', '1', '/', '1', '2', '9', '5', '1', '3', '0', '3', '7', '2', '4', '0', '1', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '9', '0', '0', '3', '5', '8', '1', '9', '4', '4', '6', '0', '7', '2', '5', '3', '5', '6', '6', '9', '/', '2', '1', '1', '9', '3', '0', '4', '2', '4', '5', '7', '4', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '8', '0', '5', '7', '5', '8', '3', '5', '8', '2', '9', '1', '2', '3', '0', '6', '9', '1', '/', '3', '0', '2', '7', '5', '7', '7', '4', '9', '3', '9', '2', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '4', '9', '0', '1', '1', '1', '7', '7', '3', '6', '0', '1', '0', '9', '3', '9', '6', '9', '/', '8', '4', '7', '7', '2', '1', '6', '9', '8', '2', '9', '8', '8', '9', '9', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '1', '0', '1', '3', '6', '0', '2', '9', '0', '0', '6', '2', '5', '7', '3', '5', '4', '3', '/', '5', '2', '9', '8', '2', '6', '0', '6', '1', '4', '3', '6', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '5', '0', '8', '6', '0', '5', '7', '9', '9', '9', '3', '1', '7', '3', '9', '3', '4', '5', '1', '/', '6', '4', '7', '5', '6', '5', '1', '8', '6', '2', '0', '0', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0180173Acc00600 : List (String × SourceJson) := (fragment0180173Field005Key00, fragment0180173Field005Value00) :: fragment0180173Acc00500
noncomputable def fragment0180173Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '5', '6', '0', '2', '8', '3', '8', '9', '8', '4', '9', '7', '0', '6', '5', '0', '5', '5', '8', '1', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '7', '3', '3', '2', '4', '2', '4', '5', '2', '2', '8', '5', '3', '3', '4', '2', '1', '0', '8', '5', '7', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '0', '3', '7', '8', '5', '2', '7', '0', '3', '3', '8', '6', '6', '6', '8', '5', '7', '5', '4', '9', '7', '/', '1', '1', '6', '5', '6', '1', '7', '3', '3', '5', '1', '6', '0', '9', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '1', '0', '0', '4', '6', '9', '1', '0', '9', '2', '2', '2', '3', '5', '4', '0', '8', '6', '3', '6', '7', '/', '1', '1', '6', '5', '6', '1', '7', '3', '3', '5', '1', '6', '0', '9', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '2', '6', '7', '1', '9', '4', '4', '8', '0', '3', '7', '4', '5', '8', '6', '6', '1', '0', '9', '3', '1', '/', '1', '2', '9', '5', '1', '3', '0', '3', '7', '2', '4', '0', '1', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '0', '0', '3', '5', '8', '1', '9', '4', '4', '6', '0', '7', '2', '5', '3', '5', '6', '6', '9', '/', '2', '1', '1', '9', '3', '0', '4', '2', '4', '5', '7', '4', '7', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '8', '0', '5', '7', '5', '8', '3', '5', '8', '2', '9', '1', '2', '3', '0', '6', '9', '1', '/', '3', '0', '2', '7', '5', '7', '7', '4', '9', '3', '9', '2', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '4', '9', '0', '1', '1', '1', '7', '7', '3', '6', '0', '1', '0', '9', '3', '9', '6', '9', '/', '8', '4', '7', '7', '2', '1', '6', '9', '8', '2', '9', '8', '8', '9', '9', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '1', '0', '1', '3', '6', '0', '2', '9', '0', '0', '6', '2', '5', '7', '3', '5', '4', '3', '/', '5', '2', '9', '8', '2', '6', '0', '6', '1', '4', '3', '6', '8', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '5', '0', '8', '6', '0', '5', '7', '9', '9', '9', '3', '1', '7', '3', '9', '3', '4', '5', '1', '/', '6', '4', '7', '5', '6', '5', '1', '8', '6', '2', '0', '0', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0180173_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0180173Field005Chars00 ++ tail)) fragment0180173Acc00500 =
      SourceJson.object (fuel + 419) (SourceJson.white tail) fragment0180173Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_005"
  err.flush

noncomputable def fragment0180173Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0180173Field006Value00 : SourceJson := .str (String.ofList ['5', '2', '0', '6', '6', '0', '0', '9', '9', '2', '2', '9', '2', '4', '0', '7', '7', '5', '4', '5', '5', '3', '7', '9', '0', '8', '3', '9', '6', '5', '2', '1', '8', '5', '1', '8', '2', '7', '7', '0', '4', '3', '5', '0', '8', '1', '0', '9', '9', '5', '2', '0', '0', '0', '0', '0', '/', '7', '0', '5', '7', '5', '8', '4', '2', '4', '4', '0', '6', '4', '9', '6', '1', '4', '9', '9', '0', '4', '4', '9', '7', '6', '0', '7', '9', '4', '2', '6', '0', '1', '3', '1', '5', '6', '1', '2', '4', '4', '9', '6', '8', '0', '5', '8', '2', '6', '0', '8', '0', '1', '0', '6', '3', '7', '8', '6', '2', '3', '2', '9', '4', '0', '1', '7', '7'])
noncomputable def fragment0180173Acc00700 : List (String × SourceJson) := (fragment0180173Field006Key00, fragment0180173Field006Value00) :: fragment0180173Acc00600
noncomputable def fragment0180173Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '2', '0', '6', '6', '0', '0', '9', '9', '2', '2', '9', '2', '4', '0', '7', '7', '5', '4', '5', '5', '3', '7', '9', '0', '8', '3', '9', '6', '5', '2', '1', '8', '5', '1', '8', '2', '7', '7', '0', '4', '3', '5', '0', '8', '1', '0', '9', '9', '5', '2', '0', '0', '0', '0', '0', '/', '7', '0', '5', '7', '5', '8', '4', '2', '4', '4', '0', '6', '4', '9', '6', '1', '4', '9', '9', '0', '4', '4', '9', '7', '6', '0', '7', '9', '4', '2', '6', '0', '1', '3', '1', '5', '6', '1', '2', '4', '4', '9', '6', '8', '0', '5', '8', '2', '6', '0', '8', '0', '1', '0', '6', '3', '7', '8', '6', '2', '3', '2', '9', '4', '0', '1', '7', '7', '"', ',']

theorem object_fragment0180173_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 419) (SourceJson.white (fragment0180173Field006Chars00 ++ tail)) fragment0180173Acc00600 =
      SourceJson.object (fuel + 418) (SourceJson.white tail) fragment0180173Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_006"
  err.flush

noncomputable def fragment0180173Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0180173Field007Value00 : SourceJson := .str (String.ofList ['8', '7', '2', '4', '7', '2', '3', '1', '3', '3', '4', '2', '5', '2', '9', '6', '4', '6', '1', '1', '0', '6', '6', '1', '3', '0', '9', '8', '0', '1', '2', '3', '3', '2', '5', '9', '2', '9', '7', '2', '1', '7', '7', '2', '5', '9', '3', '9', '9', '0', '7', '0', '7', '9', '9', '9', '3', '9', '8', '5', '8', '5', '8', '6', '4', '4', '1', '4', '9', '5', '6', '5', '4', '0', '8', '8', '3', '3', '3', '6', '2', '4', '8', '8', '1', '0', '1', '3', '6', '1', '8', '0', '3', '5', '1', '6', '2', '8', '0', '7', '5', '5', '5', '1', '8', '3', '5', '7', '0', '7', '0', '0', '8', '5', '7', '0', '4', '9', '3', '9', '0', '6', '3', '6', '1', '3', '1', '2', '4', '0', '4', '9', '8', '4', '7', '3', '8', '3', '3', '9', '0', '3', '9', '7', '5', '0', '4', '2', '2', '2', '6', '2', '2', '6', '6', '1', '2', '6', '3', '3', '8', '3', '2', '5', '6', '6', '6', '6', '6', '6', '3', '3', '5', '3', '9', '2', '6', '8', '3', '7', '8', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '0', '0', '9', '2', '3', '3', '3', '6', '3', '9', '9', '2', '7', '6', '6', '1', '2', '2', '7', '5', '8', '4', '7', '9', '9', '3', '7', '1', '7', '4', '7', '9', '2', '1', '2', '9', '8', '7', '5', '7', '1', '6', '5', '9', '2', '2', '9', '8', '7', '2', '5', '9', '7', '0', '6', '4', '3', '1', '8', '5', '2', '4', '8', '3', '2', '4', '6', '5', '2', '6', '6', '0', '5', '4', '1', '1', '0', '7', '2', '4', '5', '1', '0', '6', '6', '0', '0', '7', '6', '1', '8', '6', '7', '4', '2', '9', '5', '2', '7', '5', '7', '1', '4', '9', '9', '5', '3', '4', '5', '3', '8', '0', '6', '3', '2', '0', '1', '0', '6', '3', '9', '2', '0', '0', '2', '0', '3', '7', '1', '8', '2', '9', '0', '2', '0', '2', '9', '2', '2', '3', '8', '6', '0', '7', '2', '5', '0', '5', '8', '6', '4', '7', '1', '8', '2', '7', '9', '0', '4', '6', '8', '9', '2', '2', '8', '0', '6', '2', '2', '4', '2', '6', '5', '7', '5', '4', '0', '2', '5', '8', '9', '0', '6', '6', '4', '1', '3', '8', '2', '8', '8', '2', '9', '3', '2', '9', '1', '3', '0', '3', '0', '0', '6', '2', '1', '4', '5', '7', '7', '5', '8', '7'])
noncomputable def fragment0180173Acc00800 : List (String × SourceJson) := (fragment0180173Field007Key00, fragment0180173Field007Value00) :: fragment0180173Acc00700
noncomputable def fragment0180173Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '7', '2', '4', '7', '2', '3', '1', '3', '3', '4', '2', '5', '2', '9', '6', '4', '6', '1', '1', '0', '6', '6', '1', '3', '0', '9', '8', '0', '1', '2', '3', '3', '2', '5', '9', '2', '9', '7', '2', '1', '7', '7', '2', '5', '9', '3', '9', '9', '0', '7', '0', '7', '9', '9', '9', '3', '9', '8', '5', '8', '5', '8', '6', '4', '4', '1', '4', '9', '5', '6', '5', '4', '0', '8', '8', '3', '3', '3', '6', '2', '4', '8', '8', '1', '0', '1', '3', '6', '1', '8', '0', '3', '5', '1', '6', '2', '8', '0', '7', '5', '5', '5', '1', '8', '3', '5', '7', '0', '7', '0', '0', '8', '5', '7', '0', '4', '9', '3', '9', '0', '6', '3', '6', '1', '3', '1', '2', '4', '0', '4', '9', '8', '4', '7', '3', '8', '3', '3', '9', '0', '3', '9', '7', '5', '0', '4', '2', '2', '2', '6', '2', '2', '6', '6', '1', '2', '6', '3', '3', '8', '3', '2', '5', '6', '6', '6', '6', '6', '6', '3', '3', '5', '3', '9', '2', '6', '8', '3', '7', '8', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '0', '0', '9', '2', '3', '3', '3', '6', '3', '9', '9', '2', '7', '6', '6', '1', '2', '2', '7', '5', '8', '4', '7', '9', '9', '3', '7', '1', '7', '4', '7', '9', '2', '1', '2', '9', '8', '7', '5', '7', '1', '6', '5', '9', '2', '2', '9', '8', '7', '2', '5', '9', '7', '0', '6', '4', '3', '1', '8', '5', '2', '4', '8', '3', '2', '4', '6', '5', '2', '6', '6', '0', '5', '4', '1', '1', '0', '7', '2', '4', '5', '1', '0', '6', '6', '0', '0', '7', '6', '1', '8', '6', '7', '4', '2', '9', '5', '2', '7', '5', '7', '1', '4', '9', '9', '5', '3', '4', '5', '3', '8', '0', '6', '3', '2', '0', '1', '0', '6', '3', '9', '2', '0', '0', '2', '0', '3', '7', '1', '8', '2', '9', '0', '2', '0', '2', '9', '2', '2', '3', '8', '6', '0', '7', '2', '5', '0', '5', '8', '6', '4', '7', '1', '8', '2', '7', '9', '0', '4', '6', '8', '9', '2', '2', '8', '0', '6', '2', '2', '4', '2', '6', '5', '7', '5', '4', '0', '2', '5', '8', '9', '0', '6', '6', '4', '1', '3', '8', '2', '8', '8', '2', '9', '3', '2', '9', '1', '3', '0', '3', '0', '0', '6', '2', '1', '4', '5', '7', '7', '5', '8', '7', '"', ',']

theorem object_fragment0180173_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 418) (SourceJson.white (fragment0180173Field007Chars00 ++ tail)) fragment0180173Acc00700 =
      SourceJson.object (fuel + 417) (SourceJson.white tail) fragment0180173Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_007"
  err.flush

noncomputable def fragment0180173Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0180173Field008Value00 : SourceJson := .str (String.ofList ['5', '8', '4', '4', '9', '0', '9', '7', '4', '9', '5', '5', '3', '0', '4', '9', '7'])
noncomputable def fragment0180173Acc00900 : List (String × SourceJson) := (fragment0180173Field008Key00, fragment0180173Field008Value00) :: fragment0180173Acc00800
noncomputable def fragment0180173Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '8', '4', '4', '9', '0', '9', '7', '4', '9', '5', '5', '3', '0', '4', '9', '7', '"', ',']

theorem object_fragment0180173_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 417) (SourceJson.white (fragment0180173Field008Chars00 ++ tail)) fragment0180173Acc00800 =
      SourceJson.object (fuel + 416) (SourceJson.white tail) fragment0180173Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_008"
  err.flush

noncomputable def fragment0180173Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0180173Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '9', '7', '0', '7', '6', '0', '2', '7', '9', '9', '4', '7', '5', '8', '8', '7'])
noncomputable def fragment0180173Acc01000 : List (String × SourceJson) := (fragment0180173Field009Key00, fragment0180173Field009Value00) :: fragment0180173Acc00900
noncomputable def fragment0180173Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '9', '7', '0', '7', '6', '0', '2', '7', '9', '9', '4', '7', '5', '8', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0180173_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 416) (SourceJson.white (fragment0180173Field009Chars00 ++ tail)) fragment0180173Acc00900 =
      .ok (.obj (fragment0180173Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0180173_object_field_009"
  err.flush

noncomputable def fragment0180173Chars : List Char := '{' :: (fragment0180173Field000Chars00 ++ fragment0180173Field001Chars00 ++ fragment0180173Field002Chars00 ++ fragment0180173Field003Chars00 ++ fragment0180173Field004Chars00 ++ fragment0180173Field005Chars00 ++ fragment0180173Field006Chars00 ++ fragment0180173Field007Chars00 ++ fragment0180173Field008Chars00 ++ fragment0180173Field009Chars00)
noncomputable def fragment0180173Value : SourceJson := .obj (fragment0180173Acc01000.reverse)

theorem value_fragment0180173 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 426) (fragment0180173Chars ++ tail) =
      .ok (fragment0180173Value, tail) := by
  have hinput : fragment0180173Chars ++ tail = '{' :: (fragment0180173Field000Chars00 ++ (fragment0180173Field001Chars00 ++ (fragment0180173Field002Chars00 ++ (fragment0180173Field003Chars00 ++ (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0180173Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 426) (fragment0180173Chars ++ tail) =
        SourceJson.value (fuel + 426) ('{' :: (fragment0180173Field000Chars00 ++ (fragment0180173Field001Chars00 ++ (fragment0180173Field002Chars00 ++ (fragment0180173Field003Chars00 ++ (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 426)) hinput
    _ = SourceJson.object (fuel + 425) (SourceJson.white (fragment0180173Field000Chars00 ++ (fragment0180173Field001Chars00 ++ (fragment0180173Field002Chars00 ++ (fragment0180173Field003Chars00 ++ (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))))))))))) fragment0180173Acc00000 := by rfl
    _ = SourceJson.object (fuel + 424) (SourceJson.white (fragment0180173Field001Chars00 ++ (fragment0180173Field002Chars00 ++ (fragment0180173Field003Chars00 ++ (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail))))))))))) fragment0180173Acc00100 := object_fragment0180173_field_000 fuel (fragment0180173Field001Chars00 ++ (fragment0180173Field002Chars00 ++ (fragment0180173Field003Chars00 ++ (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 423) (SourceJson.white (fragment0180173Field002Chars00 ++ (fragment0180173Field003Chars00 ++ (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))))))))) fragment0180173Acc00200 := object_fragment0180173_field_001 fuel (fragment0180173Field002Chars00 ++ (fragment0180173Field003Chars00 ++ (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 422) (SourceJson.white (fragment0180173Field003Chars00 ++ (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail))))))))) fragment0180173Acc00300 := object_fragment0180173_field_002 fuel (fragment0180173Field003Chars00 ++ (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))))))) fragment0180173Acc00400 := object_fragment0180173_field_003 fuel (fragment0180173Field004Chars00 ++ (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail))))))) fragment0180173Acc00500 := object_fragment0180173_field_004 fuel (fragment0180173Field005Chars00 ++ (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 419) (SourceJson.white (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))))) fragment0180173Acc00600 := object_fragment0180173_field_005 fuel (fragment0180173Field006Chars00 ++ (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 418) (SourceJson.white (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail))))) fragment0180173Acc00700 := object_fragment0180173_field_006 fuel (fragment0180173Field007Chars00 ++ (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 417) (SourceJson.white (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))) fragment0180173Acc00800 := object_fragment0180173_field_007 fuel (fragment0180173Field008Chars00 ++ (fragment0180173Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 416) (SourceJson.white (fragment0180173Field009Chars00 ++ (tail))) fragment0180173Acc00900 := object_fragment0180173_field_008 fuel (fragment0180173Field009Chars00 ++ (tail))
    _ = .ok (fragment0180173Value, tail) := object_fragment0180173_field_009 fuel (tail)

noncomputable def fragment0182177Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0182177Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0182177Field000Value00 : SourceJson := .number (String.ofList ['3', '0'])
noncomputable def fragment0182177Acc00100 : List (String × SourceJson) := (fragment0182177Field000Key00, fragment0182177Field000Value00) :: fragment0182177Acc00000
noncomputable def fragment0182177Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '0', ',']

theorem object_fragment0182177_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0182177Field000Chars00 ++ tail)) fragment0182177Acc00000 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0182177Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_000"
  err.flush

noncomputable def fragment0182177Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0182177Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0182177Acc00200 : List (String × SourceJson) := (fragment0182177Field001Key00, fragment0182177Field001Value00) :: fragment0182177Acc00100
noncomputable def fragment0182177Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0182177_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0182177Field001Chars00 ++ tail)) fragment0182177Acc00100 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0182177Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_001"
  err.flush

noncomputable def fragment0182177Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0182177Field002Value00 : SourceJson := .str (String.ofList ['7', '8', '0', '1', '7', '1', '8', '9', '7', '7', '8', '6', '8', '6', '0', '7', '4', '9', '2', '8', '0', '5', '3', '7', '4', '7', '2', '8', '6', '6', '4', '5', '6', '6', '4', '1', '2', '2', '3', '2', '7', '4', '4', '9', '1', '/', '4', '5', '4', '5', '4', '4', '8', '3', '0', '3', '6', '5', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0182177Acc00300 : List (String × SourceJson) := (fragment0182177Field002Key00, fragment0182177Field002Value00) :: fragment0182177Acc00200
noncomputable def fragment0182177Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '8', '0', '1', '7', '1', '8', '9', '7', '7', '8', '6', '8', '6', '0', '7', '4', '9', '2', '8', '0', '5', '3', '7', '4', '7', '2', '8', '6', '6', '4', '5', '6', '6', '4', '1', '2', '2', '3', '2', '7', '4', '4', '9', '1', '/', '4', '5', '4', '5', '4', '4', '8', '3', '0', '3', '6', '5', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0182177_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0182177Field002Chars00 ++ tail)) fragment0182177Acc00200 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0182177Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_002"
  err.flush

noncomputable def fragment0182177Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0182177Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0182177Acc00400 : List (String × SourceJson) := (fragment0182177Field003Key00, fragment0182177Field003Value00) :: fragment0182177Acc00300
noncomputable def fragment0182177Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0182177_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0182177Field003Chars00 ++ tail)) fragment0182177Acc00300 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0182177Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_003"
  err.flush

noncomputable def fragment0182177Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0182177Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0182177Acc00500 : List (String × SourceJson) := (fragment0182177Field004Key00, fragment0182177Field004Value00) :: fragment0182177Acc00400
noncomputable def fragment0182177Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0182177_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0182177Field004Chars00 ++ tail)) fragment0182177Acc00400 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0182177Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_004"
  err.flush

noncomputable def fragment0182177Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0182177Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '5', '2', '5', '1', '9', '6', '4', '1', '3', '7', '9', '9', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '9', '4', '1', '1', '0', '5', '2', '9', '4', '6', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '4', '1', '7', '6', '9', '5', '9', '3', '8', '4', '4', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '5', '0', '2', '5', '2', '9', '9', '9', '5', '6', '7', '7', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '2', '9', '6', '7', '0', '7', '2', '2', '3', '3', '6', '7', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '5', '1', '7', '2', '9', '5', '9', '6', '4', '0', '9', '/', '4', '6', '5', '9', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '5', '0', '4', '2', '7', '9', '2', '7', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '5', '9', '5', '4', '9', '9', '2', '1', '2', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '3', '8', '1', '2', '5', '3', '1', '0', '7', '3', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '5', '8', '3', '9', '6', '2', '0', '8', '8', '9', '8', '7', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0182177Acc00600 : List (String × SourceJson) := (fragment0182177Field005Key00, fragment0182177Field005Value00) :: fragment0182177Acc00500
noncomputable def fragment0182177Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '2', '5', '1', '9', '6', '4', '1', '3', '7', '9', '9', '/', '1', '7', '0', '8', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '9', '4', '1', '1', '0', '5', '2', '9', '4', '6', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '4', '1', '7', '6', '9', '5', '9', '3', '8', '4', '4', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '5', '0', '2', '5', '2', '9', '9', '9', '5', '6', '7', '7', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '2', '9', '6', '7', '0', '7', '2', '2', '3', '3', '6', '7', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '5', '1', '7', '2', '9', '5', '9', '6', '4', '0', '9', '/', '4', '6', '5', '9', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '5', '0', '4', '2', '7', '9', '2', '7', '/', '8', '3', '2', '1', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '5', '9', '5', '4', '9', '9', '2', '1', '2', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '3', '8', '1', '2', '5', '3', '1', '0', '7', '3', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '8', '3', '9', '6', '2', '0', '8', '8', '9', '8', '7', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0182177_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0182177Field005Chars00 ++ tail)) fragment0182177Acc00500 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0182177Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_005"
  err.flush

noncomputable def fragment0182177Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0182177Field006Value00 : SourceJson := .str (String.ofList ['5', '4', '4', '0', '7', '8', '5', '2', '4', '9', '7', '3', '6', '6', '6', '5', '7', '5', '4', '9', '2', '2', '1', '9', '1', '5', '0', '7', '7', '5', '5', '3', '1', '3', '8', '7', '8', '5', '1', '4', '1', '3', '8', '8', '7', '5', '6', '4', '1', '1', '4', '0', '8', '0', '0', '/', '3', '8', '6', '1', '9', '1', '0', '6', '6', '7', '6', '9', '7', '7', '9', '7', '6', '3', '5', '5', '4', '5', '1', '9', '3', '5', '7', '1', '1', '2', '0', '7', '0', '6', '0', '3', '0', '1', '2', '8', '0', '2', '1', '5', '8', '4', '8', '7', '1', '5', '9', '1', '9', '8', '7', '4', '2', '6', '8', '8', '5', '4', '0', '7', '9', '3', '1'])
noncomputable def fragment0182177Acc00700 : List (String × SourceJson) := (fragment0182177Field006Key00, fragment0182177Field006Value00) :: fragment0182177Acc00600
noncomputable def fragment0182177Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '4', '4', '0', '7', '8', '5', '2', '4', '9', '7', '3', '6', '6', '6', '5', '7', '5', '4', '9', '2', '2', '1', '9', '1', '5', '0', '7', '7', '5', '5', '3', '1', '3', '8', '7', '8', '5', '1', '4', '1', '3', '8', '8', '7', '5', '6', '4', '1', '1', '4', '0', '8', '0', '0', '/', '3', '8', '6', '1', '9', '1', '0', '6', '6', '7', '6', '9', '7', '7', '9', '7', '6', '3', '5', '5', '4', '5', '1', '9', '3', '5', '7', '1', '1', '2', '0', '7', '0', '6', '0', '3', '0', '1', '2', '8', '0', '2', '1', '5', '8', '4', '8', '7', '1', '5', '9', '1', '9', '8', '7', '4', '2', '6', '8', '8', '5', '4', '0', '7', '9', '3', '1', '"', ',']

theorem object_fragment0182177_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0182177Field006Chars00 ++ tail)) fragment0182177Acc00600 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0182177Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_006"
  err.flush

noncomputable def fragment0182177Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0182177Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '9', '2', '9', '1', '7', '0', '8', '5', '1', '2', '4', '5', '6', '2', '6', '9', '7', '8', '1', '1', '1', '2', '1', '6', '5', '5', '2', '4', '4', '6', '3', '8', '4', '5', '6', '8', '4', '4', '0', '8', '9', '0', '9', '8', '4', '4', '5', '2', '6', '8', '4', '3', '6', '3', '4', '9', '1', '6', '7', '2', '8', '8', '8', '9', '3', '4', '8', '9', '0', '9', '2', '3', '8', '1', '2', '2', '7', '7', '5', '1', '8', '0', '9', '3', '7', '2', '8', '2', '4', '0', '3', '2', '1', '4', '4', '6', '5', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '2', '6', '4', '4', '7', '5', '2', '1', '7', '9', '5', '8', '6', '4', '0', '1', '0', '1', '8', '8', '4', '9', '9', '7', '6', '0', '5', '4', '7', '4', '1', '2', '2', '7', '9', '9', '8', '3', '0', '4', '7', '6', '4', '5', '1', '7', '5', '3', '1', '0', '8', '8', '4', '6', '9', '6', '7', '3', '3', '9', '8', '6', '2', '8', '6', '8', '5', '4', '1', '0', '1', '3', '0', '9', '8', '2', '7', '2', '7', '0', '3', '6', '5', '7', '2', '5', '4', '0', '8', '7', '6', '2', '9', '9', '0', '1', '3', '2', '8', '0', '8', '1', '8', '1', '9', '7', '7', '2', '1', '4', '1', '3', '3', '4', '6', '0', '5', '7', '0', '6', '9', '4', '8', '9', '2', '9', '1'])
noncomputable def fragment0182177Acc00800 : List (String × SourceJson) := (fragment0182177Field007Key00, fragment0182177Field007Value00) :: fragment0182177Acc00700
noncomputable def fragment0182177Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '9', '2', '9', '1', '7', '0', '8', '5', '1', '2', '4', '5', '6', '2', '6', '9', '7', '8', '1', '1', '1', '2', '1', '6', '5', '5', '2', '4', '4', '6', '3', '8', '4', '5', '6', '8', '4', '4', '0', '8', '9', '0', '9', '8', '4', '4', '5', '2', '6', '8', '4', '3', '6', '3', '4', '9', '1', '6', '7', '2', '8', '8', '8', '9', '3', '4', '8', '9', '0', '9', '2', '3', '8', '1', '2', '2', '7', '7', '5', '1', '8', '0', '9', '3', '7', '2', '8', '2', '4', '0', '3', '2', '1', '4', '4', '6', '5', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '9', '2', '6', '4', '4', '7', '5', '2', '1', '7', '9', '5', '8', '6', '4', '0', '1', '0', '1', '8', '8', '4', '9', '9', '7', '6', '0', '5', '4', '7', '4', '1', '2', '2', '7', '9', '9', '8', '3', '0', '4', '7', '6', '4', '5', '1', '7', '5', '3', '1', '0', '8', '8', '4', '6', '9', '6', '7', '3', '3', '9', '8', '6', '2', '8', '6', '8', '5', '4', '1', '0', '1', '3', '0', '9', '8', '2', '7', '2', '7', '0', '3', '6', '5', '7', '2', '5', '4', '0', '8', '7', '6', '2', '9', '9', '0', '1', '3', '2', '8', '0', '8', '1', '8', '1', '9', '7', '7', '2', '1', '4', '1', '3', '3', '4', '6', '0', '5', '7', '0', '6', '9', '4', '8', '9', '2', '9', '1', '"', ',']

theorem object_fragment0182177_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0182177Field007Chars00 ++ tail)) fragment0182177Acc00700 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0182177Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_007"
  err.flush

noncomputable def fragment0182177Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0182177Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '1', '6', '1', '9', '2', '1', '0', '0', '3', '9', '4', '4', '8', '9', '0', '4'])
noncomputable def fragment0182177Acc00900 : List (String × SourceJson) := (fragment0182177Field008Key00, fragment0182177Field008Value00) :: fragment0182177Acc00800
noncomputable def fragment0182177Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '1', '6', '1', '9', '2', '1', '0', '0', '3', '9', '4', '4', '8', '9', '0', '4', '"', ',']

theorem object_fragment0182177_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0182177Field008Chars00 ++ tail)) fragment0182177Acc00800 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0182177Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_008"
  err.flush

noncomputable def fragment0182177Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0182177Field009Value00 : SourceJson := .str (String.ofList ['4', '9', '0', '6', '0', '5', '7', '7', '8', '8', '5', '9', '6', '5', '5', '7', '8', '7'])
noncomputable def fragment0182177Acc01000 : List (String × SourceJson) := (fragment0182177Field009Key00, fragment0182177Field009Value00) :: fragment0182177Acc00900
noncomputable def fragment0182177Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '9', '0', '6', '0', '5', '7', '7', '8', '8', '5', '9', '6', '5', '5', '7', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0182177_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0182177Field009Chars00 ++ tail)) fragment0182177Acc00900 =
      .ok (.obj (fragment0182177Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0182177_object_field_009"
  err.flush

noncomputable def fragment0182177Chars : List Char := '{' :: (fragment0182177Field000Chars00 ++ fragment0182177Field001Chars00 ++ fragment0182177Field002Chars00 ++ fragment0182177Field003Chars00 ++ fragment0182177Field004Chars00 ++ fragment0182177Field005Chars00 ++ fragment0182177Field006Chars00 ++ fragment0182177Field007Chars00 ++ fragment0182177Field008Chars00 ++ fragment0182177Field009Chars00)
noncomputable def fragment0182177Value : SourceJson := .obj (fragment0182177Acc01000.reverse)

theorem value_fragment0182177 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 259) (fragment0182177Chars ++ tail) =
      .ok (fragment0182177Value, tail) := by
  have hinput : fragment0182177Chars ++ tail = '{' :: (fragment0182177Field000Chars00 ++ (fragment0182177Field001Chars00 ++ (fragment0182177Field002Chars00 ++ (fragment0182177Field003Chars00 ++ (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0182177Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 259) (fragment0182177Chars ++ tail) =
        SourceJson.value (fuel + 259) ('{' :: (fragment0182177Field000Chars00 ++ (fragment0182177Field001Chars00 ++ (fragment0182177Field002Chars00 ++ (fragment0182177Field003Chars00 ++ (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 259)) hinput
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0182177Field000Chars00 ++ (fragment0182177Field001Chars00 ++ (fragment0182177Field002Chars00 ++ (fragment0182177Field003Chars00 ++ (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))))))))))) fragment0182177Acc00000 := by rfl
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0182177Field001Chars00 ++ (fragment0182177Field002Chars00 ++ (fragment0182177Field003Chars00 ++ (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail))))))))))) fragment0182177Acc00100 := object_fragment0182177_field_000 fuel (fragment0182177Field001Chars00 ++ (fragment0182177Field002Chars00 ++ (fragment0182177Field003Chars00 ++ (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0182177Field002Chars00 ++ (fragment0182177Field003Chars00 ++ (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))))))))) fragment0182177Acc00200 := object_fragment0182177_field_001 fuel (fragment0182177Field002Chars00 ++ (fragment0182177Field003Chars00 ++ (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0182177Field003Chars00 ++ (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail))))))))) fragment0182177Acc00300 := object_fragment0182177_field_002 fuel (fragment0182177Field003Chars00 ++ (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))))))) fragment0182177Acc00400 := object_fragment0182177_field_003 fuel (fragment0182177Field004Chars00 ++ (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail))))))) fragment0182177Acc00500 := object_fragment0182177_field_004 fuel (fragment0182177Field005Chars00 ++ (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))))) fragment0182177Acc00600 := object_fragment0182177_field_005 fuel (fragment0182177Field006Chars00 ++ (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail))))) fragment0182177Acc00700 := object_fragment0182177_field_006 fuel (fragment0182177Field007Chars00 ++ (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))) fragment0182177Acc00800 := object_fragment0182177_field_007 fuel (fragment0182177Field008Chars00 ++ (fragment0182177Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0182177Field009Chars00 ++ (tail))) fragment0182177Acc00900 := object_fragment0182177_field_008 fuel (fragment0182177Field009Chars00 ++ (tail))
    _ = .ok (fragment0182177Value, tail) := object_fragment0182177_field_009 fuel (tail)

noncomputable def fragment0183845Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0183845Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0183845Field000Value00 : SourceJson := .number (String.ofList ['3', '1'])
noncomputable def fragment0183845Acc00100 : List (String × SourceJson) := (fragment0183845Field000Key00, fragment0183845Field000Value00) :: fragment0183845Acc00000
noncomputable def fragment0183845Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '1', ',']

theorem object_fragment0183845_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 451) (SourceJson.white (fragment0183845Field000Chars00 ++ tail)) fragment0183845Acc00000 =
      SourceJson.object (fuel + 450) (SourceJson.white tail) fragment0183845Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_000"
  err.flush

noncomputable def fragment0183845Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0183845Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['3'])]
noncomputable def fragment0183845Acc00200 : List (String × SourceJson) := (fragment0183845Field001Key00, fragment0183845Field001Value00) :: fragment0183845Acc00100
noncomputable def fragment0183845Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0183845_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 450) (SourceJson.white (fragment0183845Field001Chars00 ++ tail)) fragment0183845Acc00100 =
      SourceJson.object (fuel + 449) (SourceJson.white tail) fragment0183845Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_001"
  err.flush

noncomputable def fragment0183845Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0183845Field002Value00 : SourceJson := .str (String.ofList ['2', '7', '0', '2', '3', '4', '7', '7', '7', '2', '8', '3', '2', '7', '2', '2', '8', '4', '5', '1', '7', '0', '9', '2', '5', '9', '5', '9', '4', '3', '9', '7', '9', '7', '8', '9', '5', '5', '0', '4', '3', '8', '1', '9', '/', '9', '6', '5', '2', '0', '6', '3', '0', '6', '4', '5', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0183845Acc00300 : List (String × SourceJson) := (fragment0183845Field002Key00, fragment0183845Field002Value00) :: fragment0183845Acc00200
noncomputable def fragment0183845Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '7', '0', '2', '3', '4', '7', '7', '7', '2', '8', '3', '2', '7', '2', '2', '8', '4', '5', '1', '7', '0', '9', '2', '5', '9', '5', '9', '4', '3', '9', '7', '9', '7', '8', '9', '5', '5', '0', '4', '3', '8', '1', '9', '/', '9', '6', '5', '2', '0', '6', '3', '0', '6', '4', '5', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0183845_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 449) (SourceJson.white (fragment0183845Field002Chars00 ++ tail)) fragment0183845Acc00200 =
      SourceJson.object (fuel + 448) (SourceJson.white tail) fragment0183845Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_002"
  err.flush

noncomputable def fragment0183845Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0183845Field003Value00 : SourceJson := .str (String.ofList ['4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0183845Acc00400 : List (String × SourceJson) := (fragment0183845Field003Key00, fragment0183845Field003Value00) :: fragment0183845Acc00300
noncomputable def fragment0183845Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0183845_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 448) (SourceJson.white (fragment0183845Field003Chars00 ++ tail)) fragment0183845Acc00300 =
      SourceJson.object (fuel + 447) (SourceJson.white tail) fragment0183845Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_003"
  err.flush

noncomputable def fragment0183845Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0183845Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0183845Acc00500 : List (String × SourceJson) := (fragment0183845Field004Key00, fragment0183845Field004Value00) :: fragment0183845Acc00400
noncomputable def fragment0183845Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0183845_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 447) (SourceJson.white (fragment0183845Field004Chars00 ++ tail)) fragment0183845Acc00400 =
      SourceJson.object (fuel + 446) (SourceJson.white tail) fragment0183845Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_004"
  err.flush

noncomputable def fragment0183845Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0183845Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '3', '5', '1', '8', '8', '0', '8', '5', '2', '0', '6', '5', '7', '5', '0', '2', '2', '3', '1', '8', '9', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '1', '2', '2', '1', '1', '4', '3', '2', '3', '8', '4', '0', '4', '0', '9', '0', '7', '8', '2', '7', '9', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '0', '6', '1', '0', '5', '1', '1', '8', '7', '9', '1', '7', '9', '5', '1', '8', '6', '2', '8', '0', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '9', '8', '0', '6', '8', '5', '0', '2', '7', '6', '7', '7', '8', '7', '1', '4', '8', '9', '3', '7', '0', '1', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '3', '9', '0', '8', '7', '5', '9', '5', '7', '1', '8', '2', '6', '6', '1', '1', '3', '6', '3', '3', '1', '/', '6', '0', '3', '5', '7', '7', '9', '2', '9', '2', '7', '8', '2', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '7', '7', '4', '4', '3', '9', '4', '4', '5', '8', '5', '0', '1', '8', '4', '8', '8', '5', '5', '1', '3', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '5', '0', '8', '5', '4', '1', '9', '9', '0', '3', '1', '0', '3', '2', '0', '9', '1', '7', '7', '3', '/', '6', '4', '6', '6', '9', '0', '6', '3', '8', '5', '1', '2', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '3', '5', '9', '7', '0', '9', '8', '6', '6', '4', '2', '3', '2', '8', '6', '4', '5', '0', '7', '3', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '5', '7', '7', '3', '3', '5', '0', '8', '0', '6', '8', '9', '3', '1', '7', '7', '6', '1', '3', '7', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '5', '6', '4', '5', '9', '3', '7', '7', '6', '3', '5', '5', '9', '0', '2', '6', '5', '7', '1', '1', '/', '3', '0', '1', '7', '8', '8', '9', '6', '4', '6', '3', '9', '1', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0183845Acc00600 : List (String × SourceJson) := (fragment0183845Field005Key00, fragment0183845Field005Value00) :: fragment0183845Acc00500
noncomputable def fragment0183845Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '3', '5', '1', '8', '8', '0', '8', '5', '2', '0', '6', '5', '7', '5', '0', '2', '2', '3', '1', '8', '9', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '1', '2', '2', '1', '1', '4', '3', '2', '3', '8', '4', '0', '4', '0', '9', '0', '7', '8', '2', '7', '9', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '0', '0', '6', '1', '0', '5', '1', '1', '8', '7', '9', '1', '7', '9', '5', '1', '8', '6', '2', '8', '0', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '8', '0', '6', '8', '5', '0', '2', '7', '6', '7', '7', '8', '7', '1', '4', '8', '9', '3', '7', '0', '1', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '2', '3', '9', '0', '8', '7', '5', '9', '5', '7', '1', '8', '2', '6', '6', '1', '1', '3', '6', '3', '3', '1', '/', '6', '0', '3', '5', '7', '7', '9', '2', '9', '2', '7', '8', '2', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '5', '7', '7', '4', '4', '3', '9', '4', '4', '5', '8', '5', '0', '1', '8', '4', '8', '8', '5', '5', '1', '3', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '5', '0', '8', '5', '4', '1', '9', '9', '0', '3', '1', '0', '3', '2', '0', '9', '1', '7', '7', '3', '/', '6', '4', '6', '6', '9', '0', '6', '3', '8', '5', '1', '2', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '3', '5', '9', '7', '0', '9', '8', '6', '6', '4', '2', '3', '2', '8', '6', '4', '5', '0', '7', '3', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '8', '5', '7', '7', '3', '3', '5', '0', '8', '0', '6', '8', '9', '3', '1', '7', '7', '6', '1', '3', '7', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '5', '6', '4', '5', '9', '3', '7', '7', '6', '3', '5', '5', '9', '0', '2', '6', '5', '7', '1', '1', '/', '3', '0', '1', '7', '8', '8', '9', '6', '4', '6', '3', '9', '1', '0', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0183845_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 446) (SourceJson.white (fragment0183845Field005Chars00 ++ tail)) fragment0183845Acc00500 =
      SourceJson.object (fuel + 445) (SourceJson.white tail) fragment0183845Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_005"
  err.flush

noncomputable def fragment0183845Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0183845Field006Value00 : SourceJson := .str (String.ofList ['1', '3', '3', '1', '9', '9', '1', '7', '3', '0', '1', '5', '0', '0', '2', '9', '7', '2', '1', '0', '3', '1', '9', '0', '0', '8', '4', '0', '8', '5', '4', '2', '2', '8', '6', '4', '7', '1', '5', '6', '5', '9', '5', '3', '3', '0', '8', '2', '7', '7', '7', '3', '0', '0', '0', '0', '0', '/', '2', '5', '8', '7', '7', '8', '0', '8', '8', '9', '4', '9', '0', '4', '8', '5', '8', '8', '2', '9', '8', '3', '1', '5', '7', '8', '9', '5', '7', '8', '9', '5', '3', '8', '1', '5', '7', '2', '4', '5', '6', '4', '8', '8', '2', '8', '8', '0', '2', '8', '9', '6', '0', '3', '9', '0', '0', '5', '4', '9', '5', '2', '0', '7', '8', '0', '6', '4', '9'])
noncomputable def fragment0183845Acc00700 : List (String × SourceJson) := (fragment0183845Field006Key00, fragment0183845Field006Value00) :: fragment0183845Acc00600
noncomputable def fragment0183845Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '3', '3', '1', '9', '9', '1', '7', '3', '0', '1', '5', '0', '0', '2', '9', '7', '2', '1', '0', '3', '1', '9', '0', '0', '8', '4', '0', '8', '5', '4', '2', '2', '8', '6', '4', '7', '1', '5', '6', '5', '9', '5', '3', '3', '0', '8', '2', '7', '7', '7', '3', '0', '0', '0', '0', '0', '/', '2', '5', '8', '7', '7', '8', '0', '8', '8', '9', '4', '9', '0', '4', '8', '5', '8', '8', '2', '9', '8', '3', '1', '5', '7', '8', '9', '5', '7', '8', '9', '5', '3', '8', '1', '5', '7', '2', '4', '5', '6', '4', '8', '8', '2', '8', '8', '0', '2', '8', '9', '6', '0', '3', '9', '0', '0', '5', '4', '9', '5', '2', '0', '7', '8', '0', '6', '4', '9', '"', ',']

theorem object_fragment0183845_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 445) (SourceJson.white (fragment0183845Field006Chars00 ++ tail)) fragment0183845Acc00600 =
      SourceJson.object (fuel + 444) (SourceJson.white tail) fragment0183845Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_006"
  err.flush

noncomputable def fragment0183845Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0183845Field007Value00 : SourceJson := .str (String.ofList ['2', '7', '2', '0', '1', '0', '2', '2', '9', '1', '2', '0', '9', '9', '1', '2', '8', '7', '4', '8', '3', '8', '4', '9', '5', '2', '4', '5', '2', '3', '4', '0', '4', '8', '4', '1', '5', '0', '3', '9', '5', '8', '7', '0', '3', '2', '9', '5', '2', '7', '1', '3', '7', '4', '7', '2', '8', '9', '4', '6', '4', '4', '4', '9', '9', '4', '6', '1', '7', '7', '0', '8', '3', '6', '5', '5', '6', '2', '9', '3', '9', '7', '7', '4', '5', '9', '8', '4', '3', '7', '9', '8', '2', '7', '0', '4', '5', '4', '7', '8', '3', '9', '8', '2', '5', '9', '0', '5', '3', '4', '3', '4', '5', '1', '2', '2', '0', '3', '8', '3', '3', '7', '5', '4', '1', '7', '5', '9', '7', '0', '8', '9', '8', '4', '9', '8', '6', '6', '9', '0', '1', '6', '5', '8', '3', '3', '8', '1', '9', '1', '9', '5', '7', '2', '1', '9', '1', '3', '5', '4', '2', '8', '0', '1', '7', '6', '5', '7', '8', '2', '8', '0', '2', '1', '6', '4', '2', '8', '7', '9', '9', '1', '4', '3', '2', '3', '4', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '4', '4', '5', '6', '2', '4', '8', '3', '9', '3', '4', '1', '3', '0', '5', '5', '7', '3', '9', '4', '4', '7', '7', '0', '5', '0', '7', '5', '4', '6', '1', '8', '8', '8', '3', '1', '1', '1', '1', '6', '0', '3', '1', '2', '9', '7', '1', '3', '7', '9', '4', '7', '2', '7', '8', '0', '1', '2', '5', '2', '9', '0', '3', '8', '3', '5', '8', '8', '8', '7', '0', '8', '6', '0', '6', '0', '3', '6', '1', '9', '1', '1', '9', '8', '5', '0', '3', '0', '2', '3', '2', '5', '6', '0', '9', '3', '5', '6', '7', '5', '9', '6', '2', '2', '0', '4', '9', '7', '6', '1', '2', '9', '5', '9', '2', '3', '7', '0', '7', '6', '9', '1', '0', '1', '7', '6', '2', '5', '3', '2', '3', '8', '8', '5', '4', '3', '6', '1', '9', '6', '9', '6', '2', '7', '8', '2', '0', '5', '7', '0', '8', '2', '0', '8', '1', '4', '3', '7', '4', '0', '7', '0', '5', '4', '6', '3', '3', '2', '6', '6', '3', '1', '9', '4', '6', '6', '4', '7', '0', '2', '1', '0', '2', '1', '5', '3', '4', '4', '3', '2', '7', '6', '5', '9', '3', '5', '1', '5', '5', '8', '7', '8', '6', '7', '3', '6', '2', '6', '7', '6', '1', '2', '7', '9', '0', '8', '5', '9', '1', '4', '7', '6', '7', '9'])
noncomputable def fragment0183845Acc00800 : List (String × SourceJson) := (fragment0183845Field007Key00, fragment0183845Field007Value00) :: fragment0183845Acc00700
noncomputable def fragment0183845Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '7', '2', '0', '1', '0', '2', '2', '9', '1', '2', '0', '9', '9', '1', '2', '8', '7', '4', '8', '3', '8', '4', '9', '5', '2', '4', '5', '2', '3', '4', '0', '4', '8', '4', '1', '5', '0', '3', '9', '5', '8', '7', '0', '3', '2', '9', '5', '2', '7', '1', '3', '7', '4', '7', '2', '8', '9', '4', '6', '4', '4', '4', '9', '9', '4', '6', '1', '7', '7', '0', '8', '3', '6', '5', '5', '6', '2', '9', '3', '9', '7', '7', '4', '5', '9', '8', '4', '3', '7', '9', '8', '2', '7', '0', '4', '5', '4', '7', '8', '3', '9', '8', '2', '5', '9', '0', '5', '3', '4', '3', '4', '5', '1', '2', '2', '0', '3', '8', '3', '3', '7', '5', '4', '1', '7', '5', '9', '7', '0', '8', '9', '8', '4', '9', '8', '6', '6', '9', '0', '1', '6', '5', '8', '3', '3', '8', '1', '9', '1', '9', '5', '7', '2', '1', '9', '1', '3', '5', '4', '2', '8', '0', '1', '7', '6', '5', '7', '8', '2', '8', '0', '2', '1', '6', '4', '2', '8', '7', '9', '9', '1', '4', '3', '2', '3', '4', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '4', '4', '5', '6', '2', '4', '8', '3', '9', '3', '4', '1', '3', '0', '5', '5', '7', '3', '9', '4', '4', '7', '7', '0', '5', '0', '7', '5', '4', '6', '1', '8', '8', '8', '3', '1', '1', '1', '1', '6', '0', '3', '1', '2', '9', '7', '1', '3', '7', '9', '4', '7', '2', '7', '8', '0', '1', '2', '5', '2', '9', '0', '3', '8', '3', '5', '8', '8', '8', '7', '0', '8', '6', '0', '6', '0', '3', '6', '1', '9', '1', '1', '9', '8', '5', '0', '3', '0', '2', '3', '2', '5', '6', '0', '9', '3', '5', '6', '7', '5', '9', '6', '2', '2', '0', '4', '9', '7', '6', '1', '2', '9', '5', '9', '2', '3', '7', '0', '7', '6', '9', '1', '0', '1', '7', '6', '2', '5', '3', '2', '3', '8', '8', '5', '4', '3', '6', '1', '9', '6', '9', '6', '2', '7', '8', '2', '0', '5', '7', '0', '8', '2', '0', '8', '1', '4', '3', '7', '4', '0', '7', '0', '5', '4', '6', '3', '3', '2', '6', '6', '3', '1', '9', '4', '6', '6', '4', '7', '0', '2', '1', '0', '2', '1', '5', '3', '4', '4', '3', '2', '7', '6', '5', '9', '3', '5', '1', '5', '5', '8', '7', '8', '6', '7', '3', '6', '2', '6', '7', '6', '1', '2', '7', '9', '0', '8', '5', '9', '1', '4', '7', '6', '7', '9', '"', ',']

theorem object_fragment0183845_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 444) (SourceJson.white (fragment0183845Field007Chars00 ++ tail)) fragment0183845Acc00700 =
      SourceJson.object (fuel + 443) (SourceJson.white tail) fragment0183845Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_007"
  err.flush

noncomputable def fragment0183845Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0183845Field008Value00 : SourceJson := .str (String.ofList ['4', '0', '7', '8', '0', '5', '9', '9', '9', '6', '9', '8', '6', '8', '7', '6', '8'])
noncomputable def fragment0183845Acc00900 : List (String × SourceJson) := (fragment0183845Field008Key00, fragment0183845Field008Value00) :: fragment0183845Acc00800
noncomputable def fragment0183845Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '7', '8', '0', '5', '9', '9', '9', '6', '9', '8', '6', '8', '7', '6', '8', '"', ',']

theorem object_fragment0183845_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 443) (SourceJson.white (fragment0183845Field008Chars00 ++ tail)) fragment0183845Acc00800 =
      SourceJson.object (fuel + 442) (SourceJson.white tail) fragment0183845Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_008"
  err.flush

noncomputable def fragment0183845Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0183845Field009Value00 : SourceJson := .str (String.ofList ['1', '6', '0', '2', '8', '1', '6', '5', '9', '6', '1', '6', '7', '6', '4', '5', '4', '1'])
noncomputable def fragment0183845Acc01000 : List (String × SourceJson) := (fragment0183845Field009Key00, fragment0183845Field009Value00) :: fragment0183845Acc00900
noncomputable def fragment0183845Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '6', '0', '2', '8', '1', '6', '5', '9', '6', '1', '6', '7', '6', '4', '5', '4', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0183845_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 442) (SourceJson.white (fragment0183845Field009Chars00 ++ tail)) fragment0183845Acc00900 =
      .ok (.obj (fragment0183845Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0183845_object_field_009"
  err.flush

noncomputable def fragment0183845Chars : List Char := '{' :: (fragment0183845Field000Chars00 ++ fragment0183845Field001Chars00 ++ fragment0183845Field002Chars00 ++ fragment0183845Field003Chars00 ++ fragment0183845Field004Chars00 ++ fragment0183845Field005Chars00 ++ fragment0183845Field006Chars00 ++ fragment0183845Field007Chars00 ++ fragment0183845Field008Chars00 ++ fragment0183845Field009Chars00)
noncomputable def fragment0183845Value : SourceJson := .obj (fragment0183845Acc01000.reverse)

theorem value_fragment0183845 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 452) (fragment0183845Chars ++ tail) =
      .ok (fragment0183845Value, tail) := by
  have hinput : fragment0183845Chars ++ tail = '{' :: (fragment0183845Field000Chars00 ++ (fragment0183845Field001Chars00 ++ (fragment0183845Field002Chars00 ++ (fragment0183845Field003Chars00 ++ (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0183845Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 452) (fragment0183845Chars ++ tail) =
        SourceJson.value (fuel + 452) ('{' :: (fragment0183845Field000Chars00 ++ (fragment0183845Field001Chars00 ++ (fragment0183845Field002Chars00 ++ (fragment0183845Field003Chars00 ++ (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 452)) hinput
    _ = SourceJson.object (fuel + 451) (SourceJson.white (fragment0183845Field000Chars00 ++ (fragment0183845Field001Chars00 ++ (fragment0183845Field002Chars00 ++ (fragment0183845Field003Chars00 ++ (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))))))))))) fragment0183845Acc00000 := by rfl
    _ = SourceJson.object (fuel + 450) (SourceJson.white (fragment0183845Field001Chars00 ++ (fragment0183845Field002Chars00 ++ (fragment0183845Field003Chars00 ++ (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail))))))))))) fragment0183845Acc00100 := object_fragment0183845_field_000 fuel (fragment0183845Field001Chars00 ++ (fragment0183845Field002Chars00 ++ (fragment0183845Field003Chars00 ++ (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 449) (SourceJson.white (fragment0183845Field002Chars00 ++ (fragment0183845Field003Chars00 ++ (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))))))))) fragment0183845Acc00200 := object_fragment0183845_field_001 fuel (fragment0183845Field002Chars00 ++ (fragment0183845Field003Chars00 ++ (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 448) (SourceJson.white (fragment0183845Field003Chars00 ++ (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail))))))))) fragment0183845Acc00300 := object_fragment0183845_field_002 fuel (fragment0183845Field003Chars00 ++ (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 447) (SourceJson.white (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))))))) fragment0183845Acc00400 := object_fragment0183845_field_003 fuel (fragment0183845Field004Chars00 ++ (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 446) (SourceJson.white (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail))))))) fragment0183845Acc00500 := object_fragment0183845_field_004 fuel (fragment0183845Field005Chars00 ++ (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 445) (SourceJson.white (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))))) fragment0183845Acc00600 := object_fragment0183845_field_005 fuel (fragment0183845Field006Chars00 ++ (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 444) (SourceJson.white (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail))))) fragment0183845Acc00700 := object_fragment0183845_field_006 fuel (fragment0183845Field007Chars00 ++ (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 443) (SourceJson.white (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))) fragment0183845Acc00800 := object_fragment0183845_field_007 fuel (fragment0183845Field008Chars00 ++ (fragment0183845Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 442) (SourceJson.white (fragment0183845Field009Chars00 ++ (tail))) fragment0183845Acc00900 := object_fragment0183845_field_008 fuel (fragment0183845Field009Chars00 ++ (tail))
    _ = .ok (fragment0183845Value, tail) := object_fragment0183845_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_before_reader"
  err.flush

noncomputable def chunk0024LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0024SuffixChars00 : List Char := [',']
noncomputable def chunk0024Chars00 : List Char := chunk0024LeadChars00 ++ fragment0170831Chars ++ chunk0024SuffixChars00
noncomputable def chunk0024Push00 (acc : List SourceJson) : List SourceJson := fragment0170831Value :: acc

noncomputable def chunk0024AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0024_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 633)
      (SourceJson.white (chunk0024LeadChars00 ++ (fragment0170831Chars ++ rest))) acc =
      (SourceJson.value (fuel + 632) (fragment0170831Chars ++ rest)).bind
        (chunk0024AfterValue00 (fuel + 632) acc) := by rfl

theorem array_chunk0024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 633) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 632) (SourceJson.white tail) (chunk0024Push00 acc) := by
  have hinput : chunk0024Chars00 ++ tail = chunk0024LeadChars00 ++ (fragment0170831Chars ++ (chunk0024SuffixChars00 ++ tail)) := by
    simp only [chunk0024Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 633) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 633)
          (SourceJson.white (chunk0024LeadChars00 ++ (fragment0170831Chars ++ (chunk0024SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 633) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 632) (fragment0170831Chars ++ (chunk0024SuffixChars00 ++ tail))).bind
        (chunk0024AfterValue00 (fuel + 632) acc) := array_chunk0024_head fuel (chunk0024SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0170831Value, chunk0024SuffixChars00 ++ tail)).bind
        (chunk0024AfterValue00 (fuel + 632) acc) :=
      congrArg (fun result => result.bind (chunk0024AfterValue00 (fuel + 632) acc))
        (value_fragment0170831 (fuel + 429) (chunk0024SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 632) (SourceJson.white tail) (chunk0024Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_before_reader"
  err.flush

noncomputable def chunk0025LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0025SuffixChars00 : List Char := [',']
noncomputable def chunk0025Chars00 : List Char := chunk0025LeadChars00 ++ fragment0172379Chars ++ chunk0025SuffixChars00
noncomputable def chunk0025Push00 (acc : List SourceJson) : List SourceJson := fragment0172379Value :: acc

noncomputable def chunk0025AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0025_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 632)
      (SourceJson.white (chunk0025LeadChars00 ++ (fragment0172379Chars ++ rest))) acc =
      (SourceJson.value (fuel + 631) (fragment0172379Chars ++ rest)).bind
        (chunk0025AfterValue00 (fuel + 631) acc) := by rfl

theorem array_chunk0025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 632) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 631) (SourceJson.white tail) (chunk0025Push00 acc) := by
  have hinput : chunk0025Chars00 ++ tail = chunk0025LeadChars00 ++ (fragment0172379Chars ++ (chunk0025SuffixChars00 ++ tail)) := by
    simp only [chunk0025Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 632) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 632)
          (SourceJson.white (chunk0025LeadChars00 ++ (fragment0172379Chars ++ (chunk0025SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 632) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 631) (fragment0172379Chars ++ (chunk0025SuffixChars00 ++ tail))).bind
        (chunk0025AfterValue00 (fuel + 631) acc) := array_chunk0025_head fuel (chunk0025SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0172379Value, chunk0025SuffixChars00 ++ tail)).bind
        (chunk0025AfterValue00 (fuel + 631) acc) :=
      congrArg (fun result => result.bind (chunk0025AfterValue00 (fuel + 631) acc))
        (value_fragment0172379 (fuel + 163) (chunk0025SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 631) (SourceJson.white tail) (chunk0025Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_before_reader"
  err.flush

noncomputable def chunk0026LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0026SuffixChars00 : List Char := [',']
noncomputable def chunk0026Chars00 : List Char := chunk0026LeadChars00 ++ fragment0174476Chars ++ chunk0026SuffixChars00
noncomputable def chunk0026Push00 (acc : List SourceJson) : List SourceJson := fragment0174476Value :: acc

noncomputable def chunk0026AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0026_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 631)
      (SourceJson.white (chunk0026LeadChars00 ++ (fragment0174476Chars ++ rest))) acc =
      (SourceJson.value (fuel + 630) (fragment0174476Chars ++ rest)).bind
        (chunk0026AfterValue00 (fuel + 630) acc) := by rfl

theorem array_chunk0026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 631) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 630) (SourceJson.white tail) (chunk0026Push00 acc) := by
  have hinput : chunk0026Chars00 ++ tail = chunk0026LeadChars00 ++ (fragment0174476Chars ++ (chunk0026SuffixChars00 ++ tail)) := by
    simp only [chunk0026Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 631) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 631)
          (SourceJson.white (chunk0026LeadChars00 ++ (fragment0174476Chars ++ (chunk0026SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 631) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 630) (fragment0174476Chars ++ (chunk0026SuffixChars00 ++ tail))).bind
        (chunk0026AfterValue00 (fuel + 630) acc) := array_chunk0026_head fuel (chunk0026SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0174476Value, chunk0026SuffixChars00 ++ tail)).bind
        (chunk0026AfterValue00 (fuel + 630) acc) :=
      congrArg (fun result => result.bind (chunk0026AfterValue00 (fuel + 630) acc))
        (value_fragment0174476 (fuel + 163) (chunk0026SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 630) (SourceJson.white tail) (chunk0026Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_before_reader"
  err.flush

noncomputable def chunk0027LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0027SuffixChars00 : List Char := [',']
noncomputable def chunk0027Chars00 : List Char := chunk0027LeadChars00 ++ fragment0176562Chars ++ chunk0027SuffixChars00
noncomputable def chunk0027Push00 (acc : List SourceJson) : List SourceJson := fragment0176562Value :: acc

noncomputable def chunk0027AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0027_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 630)
      (SourceJson.white (chunk0027LeadChars00 ++ (fragment0176562Chars ++ rest))) acc =
      (SourceJson.value (fuel + 629) (fragment0176562Chars ++ rest)).bind
        (chunk0027AfterValue00 (fuel + 629) acc) := by rfl

theorem array_chunk0027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 630) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 629) (SourceJson.white tail) (chunk0027Push00 acc) := by
  have hinput : chunk0027Chars00 ++ tail = chunk0027LeadChars00 ++ (fragment0176562Chars ++ (chunk0027SuffixChars00 ++ tail)) := by
    simp only [chunk0027Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 630) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 630)
          (SourceJson.white (chunk0027LeadChars00 ++ (fragment0176562Chars ++ (chunk0027SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 630) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 629) (fragment0176562Chars ++ (chunk0027SuffixChars00 ++ tail))).bind
        (chunk0027AfterValue00 (fuel + 629) acc) := array_chunk0027_head fuel (chunk0027SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0176562Value, chunk0027SuffixChars00 ++ tail)).bind
        (chunk0027AfterValue00 (fuel + 629) acc) :=
      congrArg (fun result => result.bind (chunk0027AfterValue00 (fuel + 629) acc))
        (value_fragment0176562 (fuel + 217) (chunk0027SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 629) (SourceJson.white tail) (chunk0027Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_before_reader"
  err.flush

noncomputable def chunk0028LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0028SuffixChars00 : List Char := [',']
noncomputable def chunk0028Chars00 : List Char := chunk0028LeadChars00 ++ fragment0178519Chars ++ chunk0028SuffixChars00
noncomputable def chunk0028Push00 (acc : List SourceJson) : List SourceJson := fragment0178519Value :: acc

noncomputable def chunk0028AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0028_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 629)
      (SourceJson.white (chunk0028LeadChars00 ++ (fragment0178519Chars ++ rest))) acc =
      (SourceJson.value (fuel + 628) (fragment0178519Chars ++ rest)).bind
        (chunk0028AfterValue00 (fuel + 628) acc) := by rfl

theorem array_chunk0028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 629) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 628) (SourceJson.white tail) (chunk0028Push00 acc) := by
  have hinput : chunk0028Chars00 ++ tail = chunk0028LeadChars00 ++ (fragment0178519Chars ++ (chunk0028SuffixChars00 ++ tail)) := by
    simp only [chunk0028Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 629) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 629)
          (SourceJson.white (chunk0028LeadChars00 ++ (fragment0178519Chars ++ (chunk0028SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 629) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 628) (fragment0178519Chars ++ (chunk0028SuffixChars00 ++ tail))).bind
        (chunk0028AfterValue00 (fuel + 628) acc) := array_chunk0028_head fuel (chunk0028SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0178519Value, chunk0028SuffixChars00 ++ tail)).bind
        (chunk0028AfterValue00 (fuel + 628) acc) :=
      congrArg (fun result => result.bind (chunk0028AfterValue00 (fuel + 628) acc))
        (value_fragment0178519 (fuel + 367) (chunk0028SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 628) (SourceJson.white tail) (chunk0028Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_before_reader"
  err.flush

noncomputable def chunk0029LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0029SuffixChars00 : List Char := [',']
noncomputable def chunk0029Chars00 : List Char := chunk0029LeadChars00 ++ fragment0180173Chars ++ chunk0029SuffixChars00
noncomputable def chunk0029Push00 (acc : List SourceJson) : List SourceJson := fragment0180173Value :: acc

noncomputable def chunk0029AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0029_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 628)
      (SourceJson.white (chunk0029LeadChars00 ++ (fragment0180173Chars ++ rest))) acc =
      (SourceJson.value (fuel + 627) (fragment0180173Chars ++ rest)).bind
        (chunk0029AfterValue00 (fuel + 627) acc) := by rfl

theorem array_chunk0029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 628) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 627) (SourceJson.white tail) (chunk0029Push00 acc) := by
  have hinput : chunk0029Chars00 ++ tail = chunk0029LeadChars00 ++ (fragment0180173Chars ++ (chunk0029SuffixChars00 ++ tail)) := by
    simp only [chunk0029Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 628) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 628)
          (SourceJson.white (chunk0029LeadChars00 ++ (fragment0180173Chars ++ (chunk0029SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 628) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 627) (fragment0180173Chars ++ (chunk0029SuffixChars00 ++ tail))).bind
        (chunk0029AfterValue00 (fuel + 627) acc) := array_chunk0029_head fuel (chunk0029SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0180173Value, chunk0029SuffixChars00 ++ tail)).bind
        (chunk0029AfterValue00 (fuel + 627) acc) :=
      congrArg (fun result => result.bind (chunk0029AfterValue00 (fuel + 627) acc))
        (value_fragment0180173 (fuel + 201) (chunk0029SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 627) (SourceJson.white tail) (chunk0029Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_before_reader"
  err.flush

noncomputable def chunk0030LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0030SuffixChars00 : List Char := [',']
noncomputable def chunk0030Chars00 : List Char := chunk0030LeadChars00 ++ fragment0182177Chars ++ chunk0030SuffixChars00
noncomputable def chunk0030Push00 (acc : List SourceJson) : List SourceJson := fragment0182177Value :: acc

noncomputable def chunk0030AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0030_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 627)
      (SourceJson.white (chunk0030LeadChars00 ++ (fragment0182177Chars ++ rest))) acc =
      (SourceJson.value (fuel + 626) (fragment0182177Chars ++ rest)).bind
        (chunk0030AfterValue00 (fuel + 626) acc) := by rfl

theorem array_chunk0030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 627) (SourceJson.white (chunk0030Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 626) (SourceJson.white tail) (chunk0030Push00 acc) := by
  have hinput : chunk0030Chars00 ++ tail = chunk0030LeadChars00 ++ (fragment0182177Chars ++ (chunk0030SuffixChars00 ++ tail)) := by
    simp only [chunk0030Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 627) (SourceJson.white (chunk0030Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 627)
          (SourceJson.white (chunk0030LeadChars00 ++ (fragment0182177Chars ++ (chunk0030SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 627) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 626) (fragment0182177Chars ++ (chunk0030SuffixChars00 ++ tail))).bind
        (chunk0030AfterValue00 (fuel + 626) acc) := array_chunk0030_head fuel (chunk0030SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0182177Value, chunk0030SuffixChars00 ++ tail)).bind
        (chunk0030AfterValue00 (fuel + 626) acc) :=
      congrArg (fun result => result.bind (chunk0030AfterValue00 (fuel + 626) acc))
        (value_fragment0182177 (fuel + 367) (chunk0030SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 626) (SourceJson.white tail) (chunk0030Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_before_reader"
  err.flush

noncomputable def chunk0031LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0031SuffixChars00 : List Char := [',']
noncomputable def chunk0031Chars00 : List Char := chunk0031LeadChars00 ++ fragment0183845Chars ++ chunk0031SuffixChars00
noncomputable def chunk0031Push00 (acc : List SourceJson) : List SourceJson := fragment0183845Value :: acc

noncomputable def chunk0031AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0031_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 626)
      (SourceJson.white (chunk0031LeadChars00 ++ (fragment0183845Chars ++ rest))) acc =
      (SourceJson.value (fuel + 625) (fragment0183845Chars ++ rest)).bind
        (chunk0031AfterValue00 (fuel + 625) acc) := by rfl

theorem array_chunk0031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 626) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 625) (SourceJson.white tail) (chunk0031Push00 acc) := by
  have hinput : chunk0031Chars00 ++ tail = chunk0031LeadChars00 ++ (fragment0183845Chars ++ (chunk0031SuffixChars00 ++ tail)) := by
    simp only [chunk0031Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 626) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 626)
          (SourceJson.white (chunk0031LeadChars00 ++ (fragment0183845Chars ++ (chunk0031SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 626) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 625) (fragment0183845Chars ++ (chunk0031SuffixChars00 ++ tail))).bind
        (chunk0031AfterValue00 (fuel + 625) acc) := array_chunk0031_head fuel (chunk0031SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0183845Value, chunk0031SuffixChars00 ++ tail)).bind
        (chunk0031AfterValue00 (fuel + 625) acc) :=
      congrArg (fun result => result.bind (chunk0031AfterValue00 (fuel + 625) acc))
        (value_fragment0183845 (fuel + 173) (chunk0031SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 625) (SourceJson.white tail) (chunk0031Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0024Chars00 ++ chunk0025Chars00 ++ chunk0026Chars00 ++ chunk0027Chars00 ++ chunk0028Chars00 ++ chunk0029Chars00 ++ chunk0030Chars00 ++ chunk0031Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0031Push00 (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 633) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 625) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 633) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 633) (SourceJson.white (chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 633) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 632) (SourceJson.white (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))))) (chunk0024Push00 (acc)) := array_chunk0024 fuel (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 631) (SourceJson.white (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (chunk0025Push00 (chunk0024Push00 (acc))) := array_chunk0025 fuel (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0024Push00 (acc))
    _ = SourceJson.array (fuel + 630) (SourceJson.white (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))) := array_chunk0026 fuel (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0025Push00 (chunk0024Push00 (acc)))
    _ = SourceJson.array (fuel + 629) (SourceJson.white (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))) := array_chunk0027 fuel (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))
    _ = SourceJson.array (fuel + 628) (SourceJson.white (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))) := array_chunk0028 fuel (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))
    _ = SourceJson.array (fuel + 627) (SourceJson.white (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))) := array_chunk0029 fuel (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))
    _ = SourceJson.array (fuel + 626) (SourceJson.white (chunk0031Chars00 ++ (tail))) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))) := array_chunk0030 fuel (chunk0031Chars00 ++ (tail)) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))
    _ = SourceJson.array (fuel + 625) (SourceJson.white tail) (blockPush acc) := array_chunk0031 fuel (tail) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 170825).take 15066 = blockChars := by rfl

theorem block_original_split : sourceRest 170825 = blockChars ++ sourceRest 185891 := by
  calc
    sourceRest 170825 = (sourceRest 170825).take 15066 ++ (sourceRest 170825).drop 15066 :=
      (List.take_append_drop 15066 (sourceRest 170825)).symm
    _ = blockChars ++ (sourceRest 170825).drop 15066 :=
      congrArg (fun part => part ++ (sourceRest 170825).drop 15066) block_original_prefix
    _ = blockChars ++ sourceRest 185891 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 170825 15066)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 633) (SourceJson.white (sourceRest 170825)) acc =
      SourceJson.array (fuel + 625) (SourceJson.white (sourceRest 185891)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 633) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 185891) acc)

#print axioms object_fragment0170831_field_000
#print axioms object_fragment0170831_field_001
#print axioms object_fragment0170831_field_002
#print axioms object_fragment0170831_field_003
#print axioms object_fragment0170831_field_004
#print axioms object_fragment0170831_field_005
#print axioms object_fragment0170831_field_006
#print axioms object_fragment0170831_field_007
#print axioms object_fragment0170831_field_008
#print axioms object_fragment0170831_field_009
#print axioms value_fragment0170831
#print axioms object_fragment0172379_field_000
#print axioms object_fragment0172379_field_001
#print axioms object_fragment0172379_field_002
#print axioms object_fragment0172379_field_003
#print axioms object_fragment0172379_field_004
#print axioms object_fragment0172379_field_005
#print axioms object_fragment0172379_field_006
#print axioms object_fragment0172379_field_007
#print axioms object_fragment0172379_field_008
#print axioms object_fragment0172379_field_009
#print axioms value_fragment0172379
#print axioms object_fragment0174476_field_000
#print axioms object_fragment0174476_field_001
#print axioms object_fragment0174476_field_002
#print axioms object_fragment0174476_field_003
#print axioms object_fragment0174476_field_004
#print axioms object_fragment0174476_field_005
#print axioms object_fragment0174476_field_006
#print axioms object_fragment0174476_field_007
#print axioms object_fragment0174476_field_008
#print axioms object_fragment0174476_field_009
#print axioms value_fragment0174476
#print axioms object_fragment0176562_field_000
#print axioms object_fragment0176562_field_001
#print axioms object_fragment0176562_field_002
#print axioms object_fragment0176562_field_003
#print axioms object_fragment0176562_field_004
#print axioms object_fragment0176562_field_005
#print axioms object_fragment0176562_field_006
#print axioms object_fragment0176562_field_007
#print axioms object_fragment0176562_field_008
#print axioms object_fragment0176562_field_009
#print axioms value_fragment0176562
#print axioms object_fragment0178519_field_000
#print axioms object_fragment0178519_field_001
#print axioms object_fragment0178519_field_002
#print axioms object_fragment0178519_field_003
#print axioms object_fragment0178519_field_004
#print axioms object_fragment0178519_field_005
#print axioms object_fragment0178519_field_006
#print axioms object_fragment0178519_field_007
#print axioms object_fragment0178519_field_008
#print axioms object_fragment0178519_field_009
#print axioms value_fragment0178519
#print axioms object_fragment0180173_field_000
#print axioms object_fragment0180173_field_001
#print axioms object_fragment0180173_field_002
#print axioms object_fragment0180173_field_003
#print axioms object_fragment0180173_field_004
#print axioms object_fragment0180173_field_005
#print axioms object_fragment0180173_field_006
#print axioms object_fragment0180173_field_007
#print axioms object_fragment0180173_field_008
#print axioms object_fragment0180173_field_009
#print axioms value_fragment0180173
#print axioms object_fragment0182177_field_000
#print axioms object_fragment0182177_field_001
#print axioms object_fragment0182177_field_002
#print axioms object_fragment0182177_field_003
#print axioms object_fragment0182177_field_004
#print axioms object_fragment0182177_field_005
#print axioms object_fragment0182177_field_006
#print axioms object_fragment0182177_field_007
#print axioms object_fragment0182177_field_008
#print axioms object_fragment0182177_field_009
#print axioms value_fragment0182177
#print axioms object_fragment0183845_field_000
#print axioms object_fragment0183845_field_001
#print axioms object_fragment0183845_field_002
#print axioms object_fragment0183845_field_003
#print axioms object_fragment0183845_field_004
#print axioms object_fragment0183845_field_005
#print axioms object_fragment0183845_field_006
#print axioms object_fragment0183845_field_007
#print axioms object_fragment0183845_field_008
#print axioms object_fragment0183845_field_009
#print axioms value_fragment0183845
#print axioms array_chunk0024_head
#print axioms array_chunk0024
#print axioms array_chunk0025_head
#print axioms array_chunk0025
#print axioms array_chunk0026_head
#print axioms array_chunk0026
#print axioms array_chunk0027_head
#print axioms array_chunk0027
#print axioms array_chunk0028_head
#print axioms array_chunk0028
#print axioms array_chunk0029_head
#print axioms array_chunk0029
#print axioms array_chunk0030_head
#print axioms array_chunk0030
#print axioms array_chunk0031_head
#print axioms array_chunk0031
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock003

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
