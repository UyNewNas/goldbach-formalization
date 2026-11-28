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

namespace SimplicesBlock005

noncomputable def fragment0201524Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0201524Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0201524Field000Value00 : SourceJson := .number (String.ofList ['4', '0'])
noncomputable def fragment0201524Acc00100 : List (String × SourceJson) := (fragment0201524Field000Key00, fragment0201524Field000Value00) :: fragment0201524Acc00000
noncomputable def fragment0201524Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '0', ',']

theorem object_fragment0201524_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 207) (SourceJson.white (fragment0201524Field000Chars00 ++ tail)) fragment0201524Acc00000 =
      SourceJson.object (fuel + 206) (SourceJson.white tail) fragment0201524Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_000"
  err.flush

noncomputable def fragment0201524Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0201524Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0201524Acc00200 : List (String × SourceJson) := (fragment0201524Field001Key00, fragment0201524Field001Value00) :: fragment0201524Acc00100
noncomputable def fragment0201524Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0201524_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0201524Field001Chars00 ++ tail)) fragment0201524Acc00100 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0201524Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_001"
  err.flush

noncomputable def fragment0201524Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0201524Field002Value00 : SourceJson := .str (String.ofList ['2', '1', '2', '1', '2', '4', '3', '3', '1', '2', '0', '0', '6', '1', '5', '9', '9', '8', '3', '8', '7', '9', '3', '6', '2', '1', '8', '8', '8', '7', '1', '7', '9', '2', '8', '3', '5', '2', '1', '9', '/', '2', '3', '0', '3', '9', '9', '5', '3', '0', '9', '7', '0', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0201524Acc00300 : List (String × SourceJson) := (fragment0201524Field002Key00, fragment0201524Field002Value00) :: fragment0201524Acc00200
noncomputable def fragment0201524Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '1', '2', '1', '2', '4', '3', '3', '1', '2', '0', '0', '6', '1', '5', '9', '9', '8', '3', '8', '7', '9', '3', '6', '2', '1', '8', '8', '8', '7', '1', '7', '9', '2', '8', '3', '5', '2', '1', '9', '/', '2', '3', '0', '3', '9', '9', '5', '3', '0', '9', '7', '0', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0201524_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0201524Field002Chars00 ++ tail)) fragment0201524Acc00200 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0201524Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_002"
  err.flush

noncomputable def fragment0201524Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0201524Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0201524Acc00400 : List (String × SourceJson) := (fragment0201524Field003Key00, fragment0201524Field003Value00) :: fragment0201524Acc00300
noncomputable def fragment0201524Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0201524_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0201524Field003Chars00 ++ tail)) fragment0201524Acc00300 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0201524Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_003"
  err.flush

noncomputable def fragment0201524Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0201524Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0201524Acc00500 : List (String × SourceJson) := (fragment0201524Field004Key00, fragment0201524Field004Value00) :: fragment0201524Acc00400
noncomputable def fragment0201524Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0201524_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0201524Field004Chars00 ++ tail)) fragment0201524Acc00400 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0201524Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_004"
  err.flush

noncomputable def fragment0201524Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0201524Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '1', '4', '5', '5', '4', '3', '2', '7', '7', '1', '/', '7', '9', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '0', '1', '6', '0', '9', '0', '1', '1', '1', '/', '1', '5', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '4', '8', '4', '2', '8', '7', '2', '8', '3', '/', '1', '6', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '7', '9', '1', '0', '9', '5', '3', '7', '9', '7', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '7', '5', '1', '7', '1', '7', '3', '4', '7', '7', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '4', '2', '7', '4', '6', '4', '1', '6', '9', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '2', '4', '1', '5', '9', '0', '3', '/', '2', '7', '1', '6', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '3', '9', '9', '1', '8', '8', '2', '3', '/', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '7', '2', '4', '0', '1', '9', '0', '3', '/', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '3', '3', '6', '4', '3', '1', '7', '5', '1', '/', '4', '7', '8', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0201524Acc00600 : List (String × SourceJson) := (fragment0201524Field005Key00, fragment0201524Field005Value00) :: fragment0201524Acc00500
noncomputable def fragment0201524Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '4', '5', '5', '4', '3', '2', '7', '7', '1', '/', '7', '9', '6', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '5', '0', '1', '6', '0', '9', '0', '1', '1', '1', '/', '1', '5', '9', '3', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '8', '4', '2', '8', '7', '2', '8', '3', '/', '1', '6', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '7', '9', '1', '0', '9', '5', '3', '7', '9', '7', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '7', '5', '1', '7', '1', '7', '3', '4', '7', '7', '/', '1', '9', '1', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '4', '2', '7', '4', '6', '4', '1', '6', '9', '/', '1', '7', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '2', '4', '1', '5', '9', '0', '3', '/', '2', '7', '1', '6', '8', '7', '5', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '3', '9', '9', '1', '8', '8', '2', '3', '/', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '7', '2', '4', '0', '1', '9', '0', '3', '/', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '3', '3', '6', '4', '3', '1', '7', '5', '1', '/', '4', '7', '8', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0201524_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0201524Field005Chars00 ++ tail)) fragment0201524Acc00500 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0201524Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_005"
  err.flush

noncomputable def fragment0201524Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0201524Field006Value00 : SourceJson := .str (String.ofList ['3', '3', '2', '1', '9', '7', '8', '9', '9', '2', '5', '2', '2', '3', '1', '7', '3', '1', '0', '4', '2', '4', '7', '9', '8', '7', '1', '0', '6', '5', '4', '9', '1', '0', '5', '1', '3', '8', '2', '6', '5', '6', '3', '7', '0', '6', '8', '8', '0', '0', '0', '/', '4', '3', '9', '5', '8', '6', '8', '0', '6', '2', '3', '0', '7', '8', '6', '6', '3', '1', '0', '7', '1', '5', '5', '1', '8', '6', '4', '6', '9', '7', '4', '8', '8', '3', '2', '6', '6', '1', '0', '6', '2', '6', '8', '6', '8', '4', '1', '5', '2', '8', '0', '0', '9', '3', '4', '2', '6', '4', '5', '0', '3', '7', '7', '5', '0', '9', '1'])
noncomputable def fragment0201524Acc00700 : List (String × SourceJson) := (fragment0201524Field006Key00, fragment0201524Field006Value00) :: fragment0201524Acc00600
noncomputable def fragment0201524Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '2', '1', '9', '7', '8', '9', '9', '2', '5', '2', '2', '3', '1', '7', '3', '1', '0', '4', '2', '4', '7', '9', '8', '7', '1', '0', '6', '5', '4', '9', '1', '0', '5', '1', '3', '8', '2', '6', '5', '6', '3', '7', '0', '6', '8', '8', '0', '0', '0', '/', '4', '3', '9', '5', '8', '6', '8', '0', '6', '2', '3', '0', '7', '8', '6', '6', '3', '1', '0', '7', '1', '5', '5', '1', '8', '6', '4', '6', '9', '7', '4', '8', '8', '3', '2', '6', '6', '1', '0', '6', '2', '6', '8', '6', '8', '4', '1', '5', '2', '8', '0', '0', '9', '3', '4', '2', '6', '4', '5', '0', '3', '7', '7', '5', '0', '9', '1', '"', ',']

theorem object_fragment0201524_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0201524Field006Chars00 ++ tail)) fragment0201524Acc00600 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0201524Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_006"
  err.flush

noncomputable def fragment0201524Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0201524Field007Value00 : SourceJson := .str (String.ofList ['9', '4', '5', '1', '6', '8', '1', '4', '6', '7', '6', '1', '5', '8', '5', '7', '5', '7', '7', '4', '8', '2', '5', '5', '0', '6', '5', '4', '2', '1', '7', '4', '4', '4', '9', '8', '4', '6', '8', '5', '8', '8', '4', '4', '5', '2', '4', '9', '1', '2', '2', '7', '1', '1', '1', '9', '2', '9', '0', '2', '2', '3', '1', '6', '8', '8', '9', '4', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '7', '0', '1', '6', '3', '6', '3', '3', '4', '1', '0', '0', '7', '5', '4', '7', '2', '2', '9', '7', '9', '0', '1', '6', '2', '2', '9', '1', '9', '1', '9', '1', '9', '3', '2', '9', '4', '6', '4', '9', '8', '0', '9', '1', '1', '0', '9', '1', '2', '6', '8', '9', '9', '1', '1', '1', '5', '9', '3', '7', '3', '4', '6', '2', '8', '9', '2', '2', '2', '0', '8', '5', '6', '8', '6', '5', '7', '6', '5', '3', '7', '9', '3', '0', '3', '4', '0', '0', '1', '3', '7', '8', '6', '6', '8', '3', '5', '8', '3', '2', '1', '8', '7', '2', '3'])
noncomputable def fragment0201524Acc00800 : List (String × SourceJson) := (fragment0201524Field007Key00, fragment0201524Field007Value00) :: fragment0201524Acc00700
noncomputable def fragment0201524Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '4', '5', '1', '6', '8', '1', '4', '6', '7', '6', '1', '5', '8', '5', '7', '5', '7', '7', '4', '8', '2', '5', '5', '0', '6', '5', '4', '2', '1', '7', '4', '4', '4', '9', '8', '4', '6', '8', '5', '8', '8', '4', '4', '5', '2', '4', '9', '1', '2', '2', '7', '1', '1', '1', '9', '2', '9', '0', '2', '2', '3', '1', '6', '8', '8', '9', '4', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '7', '0', '1', '6', '3', '6', '3', '3', '4', '1', '0', '0', '7', '5', '4', '7', '2', '2', '9', '7', '9', '0', '1', '6', '2', '2', '9', '1', '9', '1', '9', '1', '9', '3', '2', '9', '4', '6', '4', '9', '8', '0', '9', '1', '1', '0', '9', '1', '2', '6', '8', '9', '9', '1', '1', '1', '5', '9', '3', '7', '3', '4', '6', '2', '8', '9', '2', '2', '2', '0', '8', '5', '6', '8', '6', '5', '7', '6', '5', '3', '7', '9', '3', '0', '3', '4', '0', '0', '1', '3', '7', '8', '6', '6', '8', '3', '5', '8', '3', '2', '1', '8', '7', '2', '3', '"', ',']

theorem object_fragment0201524_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0201524Field007Chars00 ++ tail)) fragment0201524Acc00700 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0201524Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_007"
  err.flush

noncomputable def fragment0201524Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0201524Field008Value00 : SourceJson := .str (String.ofList ['5', '9', '8', '7', '3', '1', '0', '9', '8', '7', '4', '5', '3'])
noncomputable def fragment0201524Acc00900 : List (String × SourceJson) := (fragment0201524Field008Key00, fragment0201524Field008Value00) :: fragment0201524Acc00800
noncomputable def fragment0201524Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '8', '7', '3', '1', '0', '9', '8', '7', '4', '5', '3', '"', ',']

theorem object_fragment0201524_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0201524Field008Chars00 ++ tail)) fragment0201524Acc00800 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0201524Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_008"
  err.flush

noncomputable def fragment0201524Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0201524Field009Value00 : SourceJson := .str (String.ofList ['2', '7', '7', '1', '7', '9', '9', '2', '4', '5', '8', '7', '6', '6'])
noncomputable def fragment0201524Acc01000 : List (String × SourceJson) := (fragment0201524Field009Key00, fragment0201524Field009Value00) :: fragment0201524Acc00900
noncomputable def fragment0201524Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '7', '1', '7', '9', '9', '2', '4', '5', '8', '7', '6', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0201524_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0201524Field009Chars00 ++ tail)) fragment0201524Acc00900 =
      .ok (.obj (fragment0201524Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0201524_object_field_009"
  err.flush

noncomputable def fragment0201524Chars : List Char := '{' :: (fragment0201524Field000Chars00 ++ fragment0201524Field001Chars00 ++ fragment0201524Field002Chars00 ++ fragment0201524Field003Chars00 ++ fragment0201524Field004Chars00 ++ fragment0201524Field005Chars00 ++ fragment0201524Field006Chars00 ++ fragment0201524Field007Chars00 ++ fragment0201524Field008Chars00 ++ fragment0201524Field009Chars00)
noncomputable def fragment0201524Value : SourceJson := .obj (fragment0201524Acc01000.reverse)

theorem value_fragment0201524 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 208) (fragment0201524Chars ++ tail) =
      .ok (fragment0201524Value, tail) := by
  have hinput : fragment0201524Chars ++ tail = '{' :: (fragment0201524Field000Chars00 ++ (fragment0201524Field001Chars00 ++ (fragment0201524Field002Chars00 ++ (fragment0201524Field003Chars00 ++ (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0201524Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 208) (fragment0201524Chars ++ tail) =
        SourceJson.value (fuel + 208) ('{' :: (fragment0201524Field000Chars00 ++ (fragment0201524Field001Chars00 ++ (fragment0201524Field002Chars00 ++ (fragment0201524Field003Chars00 ++ (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 208)) hinput
    _ = SourceJson.object (fuel + 207) (SourceJson.white (fragment0201524Field000Chars00 ++ (fragment0201524Field001Chars00 ++ (fragment0201524Field002Chars00 ++ (fragment0201524Field003Chars00 ++ (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))))))))))) fragment0201524Acc00000 := by rfl
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0201524Field001Chars00 ++ (fragment0201524Field002Chars00 ++ (fragment0201524Field003Chars00 ++ (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail))))))))))) fragment0201524Acc00100 := object_fragment0201524_field_000 fuel (fragment0201524Field001Chars00 ++ (fragment0201524Field002Chars00 ++ (fragment0201524Field003Chars00 ++ (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0201524Field002Chars00 ++ (fragment0201524Field003Chars00 ++ (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))))))))) fragment0201524Acc00200 := object_fragment0201524_field_001 fuel (fragment0201524Field002Chars00 ++ (fragment0201524Field003Chars00 ++ (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0201524Field003Chars00 ++ (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail))))))))) fragment0201524Acc00300 := object_fragment0201524_field_002 fuel (fragment0201524Field003Chars00 ++ (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))))))) fragment0201524Acc00400 := object_fragment0201524_field_003 fuel (fragment0201524Field004Chars00 ++ (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail))))))) fragment0201524Acc00500 := object_fragment0201524_field_004 fuel (fragment0201524Field005Chars00 ++ (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))))) fragment0201524Acc00600 := object_fragment0201524_field_005 fuel (fragment0201524Field006Chars00 ++ (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail))))) fragment0201524Acc00700 := object_fragment0201524_field_006 fuel (fragment0201524Field007Chars00 ++ (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))) fragment0201524Acc00800 := object_fragment0201524_field_007 fuel (fragment0201524Field008Chars00 ++ (fragment0201524Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0201524Field009Chars00 ++ (tail))) fragment0201524Acc00900 := object_fragment0201524_field_008 fuel (fragment0201524Field009Chars00 ++ (tail))
    _ = .ok (fragment0201524Value, tail) := object_fragment0201524_field_009 fuel (tail)

noncomputable def fragment0203081Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0203081Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0203081Field000Value00 : SourceJson := .number (String.ofList ['4', '1'])
noncomputable def fragment0203081Acc00100 : List (String × SourceJson) := (fragment0203081Field000Key00, fragment0203081Field000Value00) :: fragment0203081Acc00000
noncomputable def fragment0203081Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '1', ',']

theorem object_fragment0203081_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 477) (SourceJson.white (fragment0203081Field000Chars00 ++ tail)) fragment0203081Acc00000 =
      SourceJson.object (fuel + 476) (SourceJson.white tail) fragment0203081Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_000"
  err.flush

noncomputable def fragment0203081Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0203081Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0203081Acc00200 : List (String × SourceJson) := (fragment0203081Field001Key00, fragment0203081Field001Value00) :: fragment0203081Acc00100
noncomputable def fragment0203081Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0203081_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment0203081Field001Chars00 ++ tail)) fragment0203081Acc00100 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment0203081Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_001"
  err.flush

noncomputable def fragment0203081Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0203081Field002Value00 : SourceJson := .str (String.ofList ['5', '8', '6', '4', '6', '3', '5', '7', '7', '9', '3', '6', '6', '7', '1', '9', '3', '2', '4', '6', '3', '5', '9', '1', '5', '2', '1', '6', '3', '7', '5', '7', '1', '0', '7', '8', '9', '3', '8', '3', '1', '1', '/', '2', '3', '8', '3', '2', '3', '0', '1', '0', '2', '7', '7', '5', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0203081Acc00300 : List (String × SourceJson) := (fragment0203081Field002Key00, fragment0203081Field002Value00) :: fragment0203081Acc00200
noncomputable def fragment0203081Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '8', '6', '4', '6', '3', '5', '7', '7', '9', '3', '6', '6', '7', '1', '9', '3', '2', '4', '6', '3', '5', '9', '1', '5', '2', '1', '6', '3', '7', '5', '7', '1', '0', '7', '8', '9', '3', '8', '3', '1', '1', '/', '2', '3', '8', '3', '2', '3', '0', '1', '0', '2', '7', '7', '5', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0203081_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment0203081Field002Chars00 ++ tail)) fragment0203081Acc00200 =
      SourceJson.object (fuel + 474) (SourceJson.white tail) fragment0203081Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_002"
  err.flush

noncomputable def fragment0203081Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0203081Field003Value00 : SourceJson := .str (String.ofList ['1', '5', '4', '4', '2', '3', '4', '4', '5', '9', '/', '5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0'])
noncomputable def fragment0203081Acc00400 : List (String × SourceJson) := (fragment0203081Field003Key00, fragment0203081Field003Value00) :: fragment0203081Acc00300
noncomputable def fragment0203081Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '5', '4', '4', '2', '3', '4', '4', '5', '9', '/', '5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0203081_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 474) (SourceJson.white (fragment0203081Field003Chars00 ++ tail)) fragment0203081Acc00300 =
      SourceJson.object (fuel + 473) (SourceJson.white tail) fragment0203081Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_003"
  err.flush

noncomputable def fragment0203081Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0203081Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0203081Acc00500 : List (String × SourceJson) := (fragment0203081Field004Key00, fragment0203081Field004Value00) :: fragment0203081Acc00400
noncomputable def fragment0203081Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0203081_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 473) (SourceJson.white (fragment0203081Field004Chars00 ++ tail)) fragment0203081Acc00400 =
      SourceJson.object (fuel + 472) (SourceJson.white tail) fragment0203081Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_004"
  err.flush

noncomputable def fragment0203081Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0203081Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '5', '2', '4', '0', '6', '7', '0', '9', '2', '7', '2', '4', '8', '2', '8', '4', '3', '8', '4', '8', '5', '8', '6', '6', '3', '/', '3', '9', '7', '1', '0', '5', '2', '1', '9', '3', '5', '8', '4', '2', '7', '3', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '2', '9', '2', '2', '2', '7', '8', '1', '7', '0', '9', '9', '9', '6', '4', '5', '6', '4', '2', '2', '9', '9', '/', '7', '0', '9', '1', '1', '6', '4', '6', '3', '1', '4', '0', '0', '4', '8', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '1', '4', '6', '1', '8', '8', '5', '6', '7', '0', '6', '2', '5', '7', '3', '8', '9', '5', '5', '4', '5', '7', '/', '9', '9', '2', '7', '6', '3', '0', '4', '8', '3', '9', '6', '0', '6', '8', '3', '3', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '4', '0', '2', '6', '6', '0', '7', '1', '7', '9', '6', '3', '7', '8', '7', '9', '2', '3', '6', '3', '3', '7', '9', '/', '6', '6', '1', '8', '4', '2', '0', '3', '2', '2', '6', '4', '0', '4', '5', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '0', '1', '4', '3', '3', '5', '3', '8', '8', '5', '7', '2', '6', '6', '4', '8', '3', '1', '7', '9', '3', '1', '3', '/', '2', '2', '0', '6', '1', '4', '0', '1', '0', '7', '5', '4', '6', '8', '1', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '2', '9', '7', '1', '6', '2', '6', '3', '9', '4', '8', '8', '5', '7', '6', '9', '8', '8', '4', '2', '6', '9', '/', '1', '8', '0', '5', '0', '2', '3', '7', '2', '4', '3', '5', '6', '4', '8', '7', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '0', '1', '5', '5', '3', '4', '4', '0', '7', '7', '9', '9', '2', '0', '5', '3', '3', '4', '8', '2', '6', '3', '/', '7', '2', '2', '0', '0', '9', '4', '8', '9', '7', '4', '2', '5', '9', '5', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '3', '9', '3', '8', '2', '9', '9', '1', '9', '5', '7', '5', '0', '2', '1', '3', '8', '2', '9', '4', '3', '/', '1', '1', '8', '3', '6', '2', '2', '1', '1', '4', '3', '3', '2', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '1', '4', '5', '9', '1', '1', '0', '7', '3', '1', '0', '2', '5', '5', '7', '7', '7', '0', '5', '2', '6', '4', '9', '/', '3', '6', '1', '0', '0', '4', '7', '4', '4', '8', '7', '1', '2', '9', '7', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '2', '5', '6', '4', '7', '5', '9', '0', '5', '6', '0', '8', '6', '8', '7', '8', '5', '8', '7', '9', '5', '3', '/', '7', '0', '9', '1', '1', '6', '4', '6', '3', '1', '4', '0', '0', '4', '8', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0203081Acc00600 : List (String × SourceJson) := (fragment0203081Field005Key00, fragment0203081Field005Value00) :: fragment0203081Acc00500
noncomputable def fragment0203081Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '4', '0', '6', '7', '0', '9', '2', '7', '2', '4', '8', '2', '8', '4', '3', '8', '4', '8', '5', '8', '6', '6', '3', '/', '3', '9', '7', '1', '0', '5', '2', '1', '9', '3', '5', '8', '4', '2', '7', '3', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '2', '9', '2', '2', '2', '7', '8', '1', '7', '0', '9', '9', '9', '6', '4', '5', '6', '4', '2', '2', '9', '9', '/', '7', '0', '9', '1', '1', '6', '4', '6', '3', '1', '4', '0', '0', '4', '8', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '1', '4', '6', '1', '8', '8', '5', '6', '7', '0', '6', '2', '5', '7', '3', '8', '9', '5', '5', '4', '5', '7', '/', '9', '9', '2', '7', '6', '3', '0', '4', '8', '3', '9', '6', '0', '6', '8', '3', '3', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '4', '0', '2', '6', '6', '0', '7', '1', '7', '9', '6', '3', '7', '8', '7', '9', '2', '3', '6', '3', '3', '7', '9', '/', '6', '6', '1', '8', '4', '2', '0', '3', '2', '2', '6', '4', '0', '4', '5', '5', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '1', '4', '3', '3', '5', '3', '8', '8', '5', '7', '2', '6', '6', '4', '8', '3', '1', '7', '9', '3', '1', '3', '/', '2', '2', '0', '6', '1', '4', '0', '1', '0', '7', '5', '4', '6', '8', '1', '8', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '2', '9', '7', '1', '6', '2', '6', '3', '9', '4', '8', '8', '5', '7', '6', '9', '8', '8', '4', '2', '6', '9', '/', '1', '8', '0', '5', '0', '2', '3', '7', '2', '4', '3', '5', '6', '4', '8', '7', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '4', '0', '1', '5', '5', '3', '4', '4', '0', '7', '7', '9', '9', '2', '0', '5', '3', '3', '4', '8', '2', '6', '3', '/', '7', '2', '2', '0', '0', '9', '4', '8', '9', '7', '4', '2', '5', '9', '5', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '3', '9', '3', '8', '2', '9', '9', '1', '9', '5', '7', '5', '0', '2', '1', '3', '8', '2', '9', '4', '3', '/', '1', '1', '8', '3', '6', '2', '2', '1', '1', '4', '3', '3', '2', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '4', '5', '9', '1', '1', '0', '7', '3', '1', '0', '2', '5', '5', '7', '7', '7', '0', '5', '2', '6', '4', '9', '/', '3', '6', '1', '0', '0', '4', '7', '4', '4', '8', '7', '1', '2', '9', '7', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '2', '5', '6', '4', '7', '5', '9', '0', '5', '6', '0', '8', '6', '8', '7', '8', '5', '8', '7', '9', '5', '3', '/', '7', '0', '9', '1', '1', '6', '4', '6', '3', '1', '4', '0', '0', '4', '8', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0203081_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment0203081Field005Chars00 ++ tail)) fragment0203081Acc00500 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment0203081Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_005"
  err.flush

noncomputable def fragment0203081Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0203081Field006Value00 : SourceJson := .str (String.ofList ['1', '6', '7', '5', '3', '1', '1', '7', '3', '2', '7', '8', '7', '0', '8', '2', '4', '2', '2', '7', '3', '7', '4', '6', '9', '3', '7', '6', '2', '5', '0', '4', '1', '5', '9', '2', '3', '6', '1', '9', '9', '3', '1', '1', '6', '1', '5', '5', '9', '5', '8', '4', '0', '0', '0', '/', '1', '1', '7', '1', '2', '0', '8', '2', '9', '6', '0', '8', '5', '9', '6', '3', '5', '1', '6', '1', '2', '7', '2', '8', '2', '3', '5', '5', '6', '8', '9', '3', '1', '4', '9', '3', '9', '1', '7', '3', '4', '2', '3', '9', '0', '8', '8', '0', '1', '0', '3', '7', '5', '0', '5', '2', '1', '3', '1', '2', '2', '7', '5', '9', '7', '7', '6', '0', '3'])
noncomputable def fragment0203081Acc00700 : List (String × SourceJson) := (fragment0203081Field006Key00, fragment0203081Field006Value00) :: fragment0203081Acc00600
noncomputable def fragment0203081Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '7', '5', '3', '1', '1', '7', '3', '2', '7', '8', '7', '0', '8', '2', '4', '2', '2', '7', '3', '7', '4', '6', '9', '3', '7', '6', '2', '5', '0', '4', '1', '5', '9', '2', '3', '6', '1', '9', '9', '3', '1', '1', '6', '1', '5', '5', '9', '5', '8', '4', '0', '0', '0', '/', '1', '1', '7', '1', '2', '0', '8', '2', '9', '6', '0', '8', '5', '9', '6', '3', '5', '1', '6', '1', '2', '7', '2', '8', '2', '3', '5', '5', '6', '8', '9', '3', '1', '4', '9', '3', '9', '1', '7', '3', '4', '2', '3', '9', '0', '8', '8', '0', '1', '0', '3', '7', '5', '0', '5', '2', '1', '3', '1', '2', '2', '7', '5', '9', '7', '7', '6', '0', '3', '"', ',']

theorem object_fragment0203081_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment0203081Field006Chars00 ++ tail)) fragment0203081Acc00600 =
      SourceJson.object (fuel + 470) (SourceJson.white tail) fragment0203081Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_006"
  err.flush

noncomputable def fragment0203081Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0203081Field007Value00 : SourceJson := .str (String.ofList ['8', '2', '4', '2', '5', '0', '6', '1', '0', '8', '2', '4', '6', '8', '9', '0', '5', '7', '6', '5', '6', '8', '9', '0', '3', '7', '7', '9', '0', '9', '2', '0', '0', '0', '6', '9', '6', '5', '4', '2', '5', '7', '8', '7', '8', '7', '6', '8', '8', '2', '4', '3', '5', '3', '7', '9', '5', '9', '5', '5', '2', '7', '1', '3', '1', '9', '7', '6', '1', '6', '2', '1', '4', '1', '7', '3', '2', '1', '1', '7', '3', '1', '4', '6', '3', '5', '3', '3', '5', '0', '1', '3', '5', '9', '4', '6', '2', '7', '8', '0', '6', '5', '7', '0', '7', '1', '7', '3', '5', '9', '1', '9', '0', '9', '8', '7', '4', '1', '3', '0', '0', '0', '7', '2', '2', '1', '8', '3', '5', '0', '2', '9', '2', '1', '5', '0', '2', '5', '8', '7', '3', '9', '8', '7', '9', '1', '2', '7', '8', '1', '8', '3', '9', '3', '9', '0', '7', '0', '9', '6', '1', '0', '1', '9', '7', '1', '7', '3', '5', '6', '0', '2', '5', '1', '7', '5', '0', '4', '6', '4', '8', '5', '6', '7', '0', '7', '7', '6', '4', '7', '0', '5', '4', '0', '6', '9', '5', '0', '2', '7', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '8', '1', '1', '0', '9', '5', '9', '7', '6', '7', '3', '9', '6', '8', '2', '9', '2', '1', '5', '6', '5', '6', '5', '5', '1', '3', '1', '5', '0', '3', '2', '3', '5', '1', '5', '2', '4', '8', '4', '7', '6', '3', '3', '8', '2', '7', '8', '2', '3', '2', '3', '8', '8', '7', '3', '6', '7', '1', '9', '3', '7', '9', '7', '7', '6', '1', '8', '9', '9', '0', '2', '8', '8', '7', '4', '0', '5', '3', '0', '3', '0', '5', '0', '5', '1', '3', '8', '0', '3', '1', '5', '8', '2', '2', '6', '3', '6', '5', '3', '2', '6', '7', '7', '4', '8', '1', '2', '2', '4', '6', '4', '4', '0', '9', '6', '0', '6', '1', '2', '6', '8', '8', '1', '7', '8', '2', '4', '1', '7', '3', '9', '4', '0', '8', '5', '8', '5', '1', '3', '5', '9', '2', '4', '3', '9', '8', '5', '4', '2', '7', '7', '0', '8', '0', '4', '4', '1', '7', '9', '7', '1', '8', '5', '1', '9', '2', '4', '0', '8', '3', '2', '8', '5', '8', '8', '8', '5', '5', '4', '2', '5', '4', '7', '2', '3', '8', '4', '4', '3', '1', '2', '1', '1', '7', '2', '0', '3', '3', '1', '9', '9', '4', '0', '9', '7', '7', '5', '8', '3', '0', '0', '5', '8', '6', '7', '4', '5', '0', '2', '3', '3', '5', '9', '4', '8', '6', '3', '3', '0', '0', '1', '9', '7', '3', '6', '5', '6', '3'])
noncomputable def fragment0203081Acc00800 : List (String × SourceJson) := (fragment0203081Field007Key00, fragment0203081Field007Value00) :: fragment0203081Acc00700
noncomputable def fragment0203081Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '2', '4', '2', '5', '0', '6', '1', '0', '8', '2', '4', '6', '8', '9', '0', '5', '7', '6', '5', '6', '8', '9', '0', '3', '7', '7', '9', '0', '9', '2', '0', '0', '0', '6', '9', '6', '5', '4', '2', '5', '7', '8', '7', '8', '7', '6', '8', '8', '2', '4', '3', '5', '3', '7', '9', '5', '9', '5', '5', '2', '7', '1', '3', '1', '9', '7', '6', '1', '6', '2', '1', '4', '1', '7', '3', '2', '1', '1', '7', '3', '1', '4', '6', '3', '5', '3', '3', '5', '0', '1', '3', '5', '9', '4', '6', '2', '7', '8', '0', '6', '5', '7', '0', '7', '1', '7', '3', '5', '9', '1', '9', '0', '9', '8', '7', '4', '1', '3', '0', '0', '0', '7', '2', '2', '1', '8', '3', '5', '0', '2', '9', '2', '1', '5', '0', '2', '5', '8', '7', '3', '9', '8', '7', '9', '1', '2', '7', '8', '1', '8', '3', '9', '3', '9', '0', '7', '0', '9', '6', '1', '0', '1', '9', '7', '1', '7', '3', '5', '6', '0', '2', '5', '1', '7', '5', '0', '4', '6', '4', '8', '5', '6', '7', '0', '7', '7', '6', '4', '7', '0', '5', '4', '0', '6', '9', '5', '0', '2', '7', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '8', '1', '1', '0', '9', '5', '9', '7', '6', '7', '3', '9', '6', '8', '2', '9', '2', '1', '5', '6', '5', '6', '5', '5', '1', '3', '1', '5', '0', '3', '2', '3', '5', '1', '5', '2', '4', '8', '4', '7', '6', '3', '3', '8', '2', '7', '8', '2', '3', '2', '3', '8', '8', '7', '3', '6', '7', '1', '9', '3', '7', '9', '7', '7', '6', '1', '8', '9', '9', '0', '2', '8', '8', '7', '4', '0', '5', '3', '0', '3', '0', '5', '0', '5', '1', '3', '8', '0', '3', '1', '5', '8', '2', '2', '6', '3', '6', '5', '3', '2', '6', '7', '7', '4', '8', '1', '2', '2', '4', '6', '4', '4', '0', '9', '6', '0', '6', '1', '2', '6', '8', '8', '1', '7', '8', '2', '4', '1', '7', '3', '9', '4', '0', '8', '5', '8', '5', '1', '3', '5', '9', '2', '4', '3', '9', '8', '5', '4', '2', '7', '7', '0', '8', '0', '4', '4', '1', '7', '9', '7', '1', '8', '5', '1', '9', '2', '4', '0', '8', '3', '2', '8', '5', '8', '8', '8', '5', '5', '4', '2', '5', '4', '7', '2', '3', '8', '4', '4', '3', '1', '2', '1', '1', '7', '2', '0', '3', '3', '1', '9', '9', '4', '0', '9', '7', '7', '5', '8', '3', '0', '0', '5', '8', '6', '7', '4', '5', '0', '2', '3', '3', '5', '9', '4', '8', '6', '3', '3', '0', '0', '1', '9', '7', '3', '6', '5', '6', '3', '"', ',']

theorem object_fragment0203081_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment0203081Field007Chars00 ++ tail)) fragment0203081Acc00700 =
      SourceJson.object (fuel + 469) (SourceJson.white tail) fragment0203081Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_007"
  err.flush

noncomputable def fragment0203081Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0203081Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '3', '2', '9', '0', '0', '4', '4', '7', '4', '1', '6', '7', '9'])
noncomputable def fragment0203081Acc00900 : List (String × SourceJson) := (fragment0203081Field008Key00, fragment0203081Field008Value00) :: fragment0203081Acc00800
noncomputable def fragment0203081Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '3', '3', '2', '9', '0', '0', '4', '4', '7', '4', '1', '6', '7', '9', '"', ',']

theorem object_fragment0203081_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 469) (SourceJson.white (fragment0203081Field008Chars00 ++ tail)) fragment0203081Acc00800 =
      SourceJson.object (fuel + 468) (SourceJson.white tail) fragment0203081Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_008"
  err.flush

noncomputable def fragment0203081Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0203081Field009Value00 : SourceJson := .str (String.ofList ['3', '1', '3', '7', '9', '3', '4', '7', '5', '4', '6', '0', '8', '2', '8', '5'])
noncomputable def fragment0203081Acc01000 : List (String × SourceJson) := (fragment0203081Field009Key00, fragment0203081Field009Value00) :: fragment0203081Acc00900
noncomputable def fragment0203081Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '1', '3', '7', '9', '3', '4', '7', '5', '4', '6', '0', '8', '2', '8', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0203081_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 468) (SourceJson.white (fragment0203081Field009Chars00 ++ tail)) fragment0203081Acc00900 =
      .ok (.obj (fragment0203081Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0203081_object_field_009"
  err.flush

noncomputable def fragment0203081Chars : List Char := '{' :: (fragment0203081Field000Chars00 ++ fragment0203081Field001Chars00 ++ fragment0203081Field002Chars00 ++ fragment0203081Field003Chars00 ++ fragment0203081Field004Chars00 ++ fragment0203081Field005Chars00 ++ fragment0203081Field006Chars00 ++ fragment0203081Field007Chars00 ++ fragment0203081Field008Chars00 ++ fragment0203081Field009Chars00)
noncomputable def fragment0203081Value : SourceJson := .obj (fragment0203081Acc01000.reverse)

theorem value_fragment0203081 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 478) (fragment0203081Chars ++ tail) =
      .ok (fragment0203081Value, tail) := by
  have hinput : fragment0203081Chars ++ tail = '{' :: (fragment0203081Field000Chars00 ++ (fragment0203081Field001Chars00 ++ (fragment0203081Field002Chars00 ++ (fragment0203081Field003Chars00 ++ (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0203081Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 478) (fragment0203081Chars ++ tail) =
        SourceJson.value (fuel + 478) ('{' :: (fragment0203081Field000Chars00 ++ (fragment0203081Field001Chars00 ++ (fragment0203081Field002Chars00 ++ (fragment0203081Field003Chars00 ++ (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 478)) hinput
    _ = SourceJson.object (fuel + 477) (SourceJson.white (fragment0203081Field000Chars00 ++ (fragment0203081Field001Chars00 ++ (fragment0203081Field002Chars00 ++ (fragment0203081Field003Chars00 ++ (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))))))))))) fragment0203081Acc00000 := by rfl
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment0203081Field001Chars00 ++ (fragment0203081Field002Chars00 ++ (fragment0203081Field003Chars00 ++ (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail))))))))))) fragment0203081Acc00100 := object_fragment0203081_field_000 fuel (fragment0203081Field001Chars00 ++ (fragment0203081Field002Chars00 ++ (fragment0203081Field003Chars00 ++ (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment0203081Field002Chars00 ++ (fragment0203081Field003Chars00 ++ (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))))))))) fragment0203081Acc00200 := object_fragment0203081_field_001 fuel (fragment0203081Field002Chars00 ++ (fragment0203081Field003Chars00 ++ (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 474) (SourceJson.white (fragment0203081Field003Chars00 ++ (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail))))))))) fragment0203081Acc00300 := object_fragment0203081_field_002 fuel (fragment0203081Field003Chars00 ++ (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 473) (SourceJson.white (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))))))) fragment0203081Acc00400 := object_fragment0203081_field_003 fuel (fragment0203081Field004Chars00 ++ (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail))))))) fragment0203081Acc00500 := object_fragment0203081_field_004 fuel (fragment0203081Field005Chars00 ++ (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))))) fragment0203081Acc00600 := object_fragment0203081_field_005 fuel (fragment0203081Field006Chars00 ++ (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail))))) fragment0203081Acc00700 := object_fragment0203081_field_006 fuel (fragment0203081Field007Chars00 ++ (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 469) (SourceJson.white (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))) fragment0203081Acc00800 := object_fragment0203081_field_007 fuel (fragment0203081Field008Chars00 ++ (fragment0203081Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 468) (SourceJson.white (fragment0203081Field009Chars00 ++ (tail))) fragment0203081Acc00900 := object_fragment0203081_field_008 fuel (fragment0203081Field009Chars00 ++ (tail))
    _ = .ok (fragment0203081Value, tail) := object_fragment0203081_field_009 fuel (tail)

noncomputable def fragment0205178Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0205178Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0205178Field000Value00 : SourceJson := .number (String.ofList ['4', '2'])
noncomputable def fragment0205178Acc00100 : List (String × SourceJson) := (fragment0205178Field000Key00, fragment0205178Field000Value00) :: fragment0205178Acc00000
noncomputable def fragment0205178Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '2', ',']

theorem object_fragment0205178_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 480) (SourceJson.white (fragment0205178Field000Chars00 ++ tail)) fragment0205178Acc00000 =
      SourceJson.object (fuel + 479) (SourceJson.white tail) fragment0205178Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_000"
  err.flush

noncomputable def fragment0205178Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0205178Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0205178Acc00200 : List (String × SourceJson) := (fragment0205178Field001Key00, fragment0205178Field001Value00) :: fragment0205178Acc00100
noncomputable def fragment0205178Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0205178_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 479) (SourceJson.white (fragment0205178Field001Chars00 ++ tail)) fragment0205178Acc00100 =
      SourceJson.object (fuel + 478) (SourceJson.white tail) fragment0205178Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_001"
  err.flush

noncomputable def fragment0205178Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0205178Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '5', '4', '0', '1', '5', '3', '0', '0', '7', '6', '5', '7', '6', '2', '1', '8', '4', '1', '8', '0', '7', '7', '3', '6', '7', '3', '5', '5', '8', '0', '4', '9', '6', '5', '3', '7', '5', '3', '3', '/', '7', '3', '8', '9', '8', '6', '0', '7', '8', '3', '8', '0', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0205178Acc00300 : List (String × SourceJson) := (fragment0205178Field002Key00, fragment0205178Field002Value00) :: fragment0205178Acc00200
noncomputable def fragment0205178Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '5', '4', '0', '1', '5', '3', '0', '0', '7', '6', '5', '7', '6', '2', '1', '8', '4', '1', '8', '0', '7', '7', '3', '6', '7', '3', '5', '5', '8', '0', '4', '9', '6', '5', '3', '7', '5', '3', '3', '/', '7', '3', '8', '9', '8', '6', '0', '7', '8', '3', '8', '0', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0205178_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 478) (SourceJson.white (fragment0205178Field002Chars00 ++ tail)) fragment0205178Acc00200 =
      SourceJson.object (fuel + 477) (SourceJson.white tail) fragment0205178Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_002"
  err.flush

noncomputable def fragment0205178Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0205178Field003Value00 : SourceJson := .str (String.ofList ['2', '4', '2', '7', '7', '4', '2', '3', '/', '1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0'])
noncomputable def fragment0205178Acc00400 : List (String × SourceJson) := (fragment0205178Field003Key00, fragment0205178Field003Value00) :: fragment0205178Acc00300
noncomputable def fragment0205178Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '4', '2', '7', '7', '4', '2', '3', '/', '1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0', '"', ',']

theorem object_fragment0205178_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 477) (SourceJson.white (fragment0205178Field003Chars00 ++ tail)) fragment0205178Acc00300 =
      SourceJson.object (fuel + 476) (SourceJson.white tail) fragment0205178Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_003"
  err.flush

noncomputable def fragment0205178Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0205178Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0205178Acc00500 : List (String × SourceJson) := (fragment0205178Field004Key00, fragment0205178Field004Value00) :: fragment0205178Acc00400
noncomputable def fragment0205178Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0205178_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment0205178Field004Chars00 ++ tail)) fragment0205178Acc00400 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment0205178Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_004"
  err.flush

noncomputable def fragment0205178Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0205178Field005Value00 : SourceJson := .arr [.str (String.ofList ['8', '9', '2', '9', '7', '3', '6', '4', '1', '4', '6', '3', '5', '6', '2', '1', '6', '4', '3', '9', '2', '5', '0', '7', '1', '/', '9', '9', '8', '8', '8', '3', '6', '9', '4', '6', '0', '3', '2', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '6', '9', '7', '1', '6', '1', '0', '0', '9', '9', '7', '7', '1', '7', '0', '2', '9', '5', '5', '5', '4', '7', '/', '7', '1', '3', '4', '8', '8', '3', '5', '3', '2', '8', '8', '0', '3', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '5', '5', '6', '2', '5', '4', '2', '7', '1', '7', '6', '6', '2', '3', '6', '5', '0', '7', '8', '2', '1', '7', '/', '1', '9', '9', '7', '7', '6', '7', '3', '8', '9', '2', '0', '6', '5', '0', '2', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '0', '9', '5', '0', '5', '4', '0', '8', '7', '0', '8', '3', '6', '9', '4', '0', '3', '5', '9', '9', '5', '1', '1', '/', '3', '3', '2', '9', '6', '1', '2', '3', '1', '5', '3', '4', '4', '1', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '1', '4', '1', '1', '8', '1', '2', '8', '3', '4', '2', '7', '9', '7', '1', '2', '3', '4', '5', '7', '5', '1', '/', '3', '3', '2', '9', '6', '1', '2', '3', '1', '5', '3', '4', '4', '1', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '4', '0', '8', '5', '5', '8', '8', '7', '5', '8', '2', '4', '3', '5', '4', '4', '9', '5', '4', '0', '7', '1', '/', '9', '0', '8', '0', '7', '6', '0', '8', '6', '0', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '5', '3', '9', '5', '1', '1', '6', '4', '0', '1', '2', '1', '6', '3', '7', '8', '5', '7', '6', '4', '0', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '5', '8', '7', '3', '0', '5', '4', '3', '4', '3', '0', '1', '0', '4', '7', '1', '9', '6', '9', '6', '6', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '0', '7', '3', '7', '8', '2', '7', '1', '9', '2', '4', '3', '2', '0', '7', '8', '2', '3', '4', '6', '1', '3', '/', '9', '0', '8', '0', '7', '6', '0', '8', '6', '0', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '3', '9', '4', '4', '8', '9', '4', '1', '2', '3', '1', '7', '7', '7', '6', '1', '4', '0', '8', '0', '0', '9', '/', '7', '1', '3', '4', '8', '8', '3', '5', '3', '2', '8', '8', '0', '3', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0205178Acc00600 : List (String × SourceJson) := (fragment0205178Field005Key00, fragment0205178Field005Value00) :: fragment0205178Acc00500
noncomputable def fragment0205178Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '2', '9', '7', '3', '6', '4', '1', '4', '6', '3', '5', '6', '2', '1', '6', '4', '3', '9', '2', '5', '0', '7', '1', '/', '9', '9', '8', '8', '8', '3', '6', '9', '4', '6', '0', '3', '2', '5', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '6', '9', '7', '1', '6', '1', '0', '0', '9', '9', '7', '7', '1', '7', '0', '2', '9', '5', '5', '5', '4', '7', '/', '7', '1', '3', '4', '8', '8', '3', '5', '3', '2', '8', '8', '0', '3', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '2', '5', '5', '6', '2', '5', '4', '2', '7', '1', '7', '6', '6', '2', '3', '6', '5', '0', '7', '8', '2', '1', '7', '/', '1', '9', '9', '7', '7', '6', '7', '3', '8', '9', '2', '0', '6', '5', '0', '2', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '0', '9', '5', '0', '5', '4', '0', '8', '7', '0', '8', '3', '6', '9', '4', '0', '3', '5', '9', '9', '5', '1', '1', '/', '3', '3', '2', '9', '6', '1', '2', '3', '1', '5', '3', '4', '4', '1', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '9', '1', '4', '1', '1', '8', '1', '2', '8', '3', '4', '2', '7', '9', '7', '1', '2', '3', '4', '5', '7', '5', '1', '/', '3', '3', '2', '9', '6', '1', '2', '3', '1', '5', '3', '4', '4', '1', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '4', '0', '8', '5', '5', '8', '8', '7', '5', '8', '2', '4', '3', '5', '4', '4', '9', '5', '4', '0', '7', '1', '/', '9', '0', '8', '0', '7', '6', '0', '8', '6', '0', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '5', '3', '9', '5', '1', '1', '6', '4', '0', '1', '2', '1', '6', '3', '7', '8', '5', '7', '6', '4', '0', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '5', '8', '7', '3', '0', '5', '4', '3', '4', '3', '0', '1', '0', '4', '7', '1', '9', '6', '9', '6', '6', '1', '/', '1', '8', '1', '6', '1', '5', '2', '1', '7', '2', '0', '0', '5', '9', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '0', '7', '3', '7', '8', '2', '7', '1', '9', '2', '4', '3', '2', '0', '7', '8', '2', '3', '4', '6', '1', '3', '/', '9', '0', '8', '0', '7', '6', '0', '8', '6', '0', '0', '2', '9', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '9', '4', '4', '8', '9', '4', '1', '2', '3', '1', '7', '7', '7', '6', '1', '4', '0', '8', '0', '0', '9', '/', '7', '1', '3', '4', '8', '8', '3', '5', '3', '2', '8', '8', '0', '3', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0205178_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment0205178Field005Chars00 ++ tail)) fragment0205178Acc00500 =
      SourceJson.object (fuel + 474) (SourceJson.white tail) fragment0205178Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_005"
  err.flush

noncomputable def fragment0205178Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0205178Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '4', '8', '4', '6', '6', '3', '3', '9', '1', '6', '2', '0', '3', '5', '1', '9', '8', '1', '7', '5', '4', '4', '5', '1', '7', '5', '2', '5', '3', '5', '0', '5', '7', '8', '8', '2', '8', '4', '8', '1', '0', '4', '9', '7', '0', '2', '4', '0', '0', '0', '0', '0', '/', '2', '7', '1', '4', '4', '3', '8', '2', '3', '1', '2', '9', '2', '0', '7', '1', '4', '5', '7', '8', '5', '1', '1', '9', '2', '0', '9', '8', '1', '7', '5', '2', '7', '4', '6', '0', '8', '0', '7', '8', '2', '3', '1', '4', '7', '8', '0', '1', '3', '6', '1', '7', '2', '6', '3', '1', '5', '5', '7', '3', '5', '4', '5', '6', '6', '1', '7'])
noncomputable def fragment0205178Acc00700 : List (String × SourceJson) := (fragment0205178Field006Key00, fragment0205178Field006Value00) :: fragment0205178Acc00600
noncomputable def fragment0205178Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '4', '8', '4', '6', '6', '3', '3', '9', '1', '6', '2', '0', '3', '5', '1', '9', '8', '1', '7', '5', '4', '4', '5', '1', '7', '5', '2', '5', '3', '5', '0', '5', '7', '8', '8', '2', '8', '4', '8', '1', '0', '4', '9', '7', '0', '2', '4', '0', '0', '0', '0', '0', '/', '2', '7', '1', '4', '4', '3', '8', '2', '3', '1', '2', '9', '2', '0', '7', '1', '4', '5', '7', '8', '5', '1', '1', '9', '2', '0', '9', '8', '1', '7', '5', '2', '7', '4', '6', '0', '8', '0', '7', '8', '2', '3', '1', '4', '7', '8', '0', '1', '3', '6', '1', '7', '2', '6', '3', '1', '5', '5', '7', '3', '5', '4', '5', '6', '6', '1', '7', '"', ',']

theorem object_fragment0205178_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 474) (SourceJson.white (fragment0205178Field006Chars00 ++ tail)) fragment0205178Acc00600 =
      SourceJson.object (fuel + 473) (SourceJson.white tail) fragment0205178Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_006"
  err.flush

noncomputable def fragment0205178Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0205178Field007Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '7', '7', '5', '2', '7', '8', '0', '0', '0', '6', '8', '9', '9', '8', '4', '7', '0', '9', '7', '0', '8', '8', '2', '7', '2', '3', '5', '4', '5', '1', '3', '0', '4', '5', '0', '9', '4', '5', '2', '6', '2', '6', '7', '2', '3', '3', '2', '8', '9', '8', '1', '4', '6', '7', '7', '7', '9', '4', '0', '6', '9', '1', '3', '1', '6', '6', '2', '7', '3', '3', '2', '3', '2', '3', '1', '1', '5', '3', '4', '0', '0', '2', '4', '6', '4', '8', '3', '1', '3', '5', '9', '7', '9', '2', '8', '4', '4', '1', '9', '0', '3', '7', '2', '0', '1', '4', '9', '9', '3', '4', '0', '6', '0', '9', '0', '2', '5', '8', '1', '9', '8', '7', '1', '9', '6', '8', '5', '0', '7', '6', '0', '9', '1', '4', '7', '7', '7', '0', '6', '2', '6', '2', '0', '9', '3', '4', '0', '5', '0', '8', '6', '6', '2', '9', '0', '5', '4', '0', '6', '2', '8', '7', '4', '1', '4', '3', '9', '1', '2', '0', '3', '7', '9', '6', '4', '0', '7', '8', '1', '7', '7', '2', '3', '3', '0', '7', '0', '1', '9', '4', '4', '7', '9', '2', '9', '1', '4', '3', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '8', '7', '7', '2', '4', '5', '9', '1', '3', '1', '0', '2', '3', '0', '0', '1', '3', '3', '6', '9', '2', '8', '2', '2', '3', '2', '5', '4', '4', '0', '6', '3', '6', '9', '2', '5', '2', '9', '3', '4', '4', '9', '2', '5', '8', '0', '8', '2', '1', '2', '0', '4', '1', '7', '0', '7', '0', '0', '0', '9', '7', '9', '9', '9', '5', '8', '5', '4', '1', '0', '2', '2', '9', '0', '9', '6', '4', '0', '2', '2', '4', '5', '4', '5', '4', '9', '3', '7', '0', '0', '8', '0', '3', '8', '0', '6', '2', '8', '5', '8', '7', '2', '6', '0', '4', '4', '7', '8', '3', '7', '2', '8', '3', '2', '4', '9', '6', '9', '5', '3', '3', '3', '5', '3', '7', '2', '4', '7', '2', '9', '2', '9', '8', '7', '6', '9', '5', '7', '8', '6', '9', '1', '6', '5', '6', '6', '5', '5', '0', '6', '4', '2', '6', '7', '6', '4', '0', '0', '8', '3', '3', '3', '1', '9', '9', '7', '8', '7', '0', '8', '9', '3', '9', '5', '9', '6', '9', '7', '5', '8', '1', '5', '9', '1', '0', '7', '2', '5', '5', '1', '3', '3', '4', '5', '2', '9', '1', '2', '7', '4', '6', '7', '3', '3', '5', '4', '3', '6', '2', '3', '4', '9', '9', '2', '7', '2', '8', '8', '3', '7', '1', '3', '3', '9', '3', '5', '0', '7', '7', '0', '5', '6', '5', '6', '1', '0', '9', '6', '3'])
noncomputable def fragment0205178Acc00800 : List (String × SourceJson) := (fragment0205178Field007Key00, fragment0205178Field007Value00) :: fragment0205178Acc00700
noncomputable def fragment0205178Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '7', '5', '7', '7', '5', '2', '7', '8', '0', '0', '0', '6', '8', '9', '9', '8', '4', '7', '0', '9', '7', '0', '8', '8', '2', '7', '2', '3', '5', '4', '5', '1', '3', '0', '4', '5', '0', '9', '4', '5', '2', '6', '2', '6', '7', '2', '3', '3', '2', '8', '9', '8', '1', '4', '6', '7', '7', '7', '9', '4', '0', '6', '9', '1', '3', '1', '6', '6', '2', '7', '3', '3', '2', '3', '2', '3', '1', '1', '5', '3', '4', '0', '0', '2', '4', '6', '4', '8', '3', '1', '3', '5', '9', '7', '9', '2', '8', '4', '4', '1', '9', '0', '3', '7', '2', '0', '1', '4', '9', '9', '3', '4', '0', '6', '0', '9', '0', '2', '5', '8', '1', '9', '8', '7', '1', '9', '6', '8', '5', '0', '7', '6', '0', '9', '1', '4', '7', '7', '7', '0', '6', '2', '6', '2', '0', '9', '3', '4', '0', '5', '0', '8', '6', '6', '2', '9', '0', '5', '4', '0', '6', '2', '8', '7', '4', '1', '4', '3', '9', '1', '2', '0', '3', '7', '9', '6', '4', '0', '7', '8', '1', '7', '7', '2', '3', '3', '0', '7', '0', '1', '9', '4', '4', '7', '9', '2', '9', '1', '4', '3', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '8', '7', '7', '2', '4', '5', '9', '1', '3', '1', '0', '2', '3', '0', '0', '1', '3', '3', '6', '9', '2', '8', '2', '2', '3', '2', '5', '4', '4', '0', '6', '3', '6', '9', '2', '5', '2', '9', '3', '4', '4', '9', '2', '5', '8', '0', '8', '2', '1', '2', '0', '4', '1', '7', '0', '7', '0', '0', '0', '9', '7', '9', '9', '9', '5', '8', '5', '4', '1', '0', '2', '2', '9', '0', '9', '6', '4', '0', '2', '2', '4', '5', '4', '5', '4', '9', '3', '7', '0', '0', '8', '0', '3', '8', '0', '6', '2', '8', '5', '8', '7', '2', '6', '0', '4', '4', '7', '8', '3', '7', '2', '8', '3', '2', '4', '9', '6', '9', '5', '3', '3', '3', '5', '3', '7', '2', '4', '7', '2', '9', '2', '9', '8', '7', '6', '9', '5', '7', '8', '6', '9', '1', '6', '5', '6', '6', '5', '5', '0', '6', '4', '2', '6', '7', '6', '4', '0', '0', '8', '3', '3', '3', '1', '9', '9', '7', '8', '7', '0', '8', '9', '3', '9', '5', '9', '6', '9', '7', '5', '8', '1', '5', '9', '1', '0', '7', '2', '5', '5', '1', '3', '3', '4', '5', '2', '9', '1', '2', '7', '4', '6', '7', '3', '3', '5', '4', '3', '6', '2', '3', '4', '9', '9', '2', '7', '2', '8', '8', '3', '7', '1', '3', '3', '9', '3', '5', '0', '7', '7', '0', '5', '6', '5', '6', '1', '0', '9', '6', '3', '"', ',']

theorem object_fragment0205178_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 473) (SourceJson.white (fragment0205178Field007Chars00 ++ tail)) fragment0205178Acc00700 =
      SourceJson.object (fuel + 472) (SourceJson.white tail) fragment0205178Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_007"
  err.flush

noncomputable def fragment0205178Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0205178Field008Value00 : SourceJson := .str (String.ofList ['5', '3', '9', '5', '2', '4', '4', '9', '4', '7', '2', '9', '6', '7', '5', '8'])
noncomputable def fragment0205178Acc00900 : List (String × SourceJson) := (fragment0205178Field008Key00, fragment0205178Field008Value00) :: fragment0205178Acc00800
noncomputable def fragment0205178Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '3', '9', '5', '2', '4', '4', '9', '4', '7', '2', '9', '6', '7', '5', '8', '"', ',']

theorem object_fragment0205178_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment0205178Field008Chars00 ++ tail)) fragment0205178Acc00800 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment0205178Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_008"
  err.flush

noncomputable def fragment0205178Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0205178Field009Value00 : SourceJson := .str (String.ofList ['1', '9', '9', '4', '0', '1', '7', '0', '0', '1', '4', '5', '2', '4', '4', '2', '5'])
noncomputable def fragment0205178Acc01000 : List (String × SourceJson) := (fragment0205178Field009Key00, fragment0205178Field009Value00) :: fragment0205178Acc00900
noncomputable def fragment0205178Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '9', '4', '0', '1', '7', '0', '0', '1', '4', '5', '2', '4', '4', '2', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0205178_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment0205178Field009Chars00 ++ tail)) fragment0205178Acc00900 =
      .ok (.obj (fragment0205178Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0205178_object_field_009"
  err.flush

noncomputable def fragment0205178Chars : List Char := '{' :: (fragment0205178Field000Chars00 ++ fragment0205178Field001Chars00 ++ fragment0205178Field002Chars00 ++ fragment0205178Field003Chars00 ++ fragment0205178Field004Chars00 ++ fragment0205178Field005Chars00 ++ fragment0205178Field006Chars00 ++ fragment0205178Field007Chars00 ++ fragment0205178Field008Chars00 ++ fragment0205178Field009Chars00)
noncomputable def fragment0205178Value : SourceJson := .obj (fragment0205178Acc01000.reverse)

theorem value_fragment0205178 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 481) (fragment0205178Chars ++ tail) =
      .ok (fragment0205178Value, tail) := by
  have hinput : fragment0205178Chars ++ tail = '{' :: (fragment0205178Field000Chars00 ++ (fragment0205178Field001Chars00 ++ (fragment0205178Field002Chars00 ++ (fragment0205178Field003Chars00 ++ (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0205178Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 481) (fragment0205178Chars ++ tail) =
        SourceJson.value (fuel + 481) ('{' :: (fragment0205178Field000Chars00 ++ (fragment0205178Field001Chars00 ++ (fragment0205178Field002Chars00 ++ (fragment0205178Field003Chars00 ++ (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 481)) hinput
    _ = SourceJson.object (fuel + 480) (SourceJson.white (fragment0205178Field000Chars00 ++ (fragment0205178Field001Chars00 ++ (fragment0205178Field002Chars00 ++ (fragment0205178Field003Chars00 ++ (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))))))))))) fragment0205178Acc00000 := by rfl
    _ = SourceJson.object (fuel + 479) (SourceJson.white (fragment0205178Field001Chars00 ++ (fragment0205178Field002Chars00 ++ (fragment0205178Field003Chars00 ++ (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail))))))))))) fragment0205178Acc00100 := object_fragment0205178_field_000 fuel (fragment0205178Field001Chars00 ++ (fragment0205178Field002Chars00 ++ (fragment0205178Field003Chars00 ++ (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 478) (SourceJson.white (fragment0205178Field002Chars00 ++ (fragment0205178Field003Chars00 ++ (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))))))))) fragment0205178Acc00200 := object_fragment0205178_field_001 fuel (fragment0205178Field002Chars00 ++ (fragment0205178Field003Chars00 ++ (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 477) (SourceJson.white (fragment0205178Field003Chars00 ++ (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail))))))))) fragment0205178Acc00300 := object_fragment0205178_field_002 fuel (fragment0205178Field003Chars00 ++ (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))))))) fragment0205178Acc00400 := object_fragment0205178_field_003 fuel (fragment0205178Field004Chars00 ++ (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail))))))) fragment0205178Acc00500 := object_fragment0205178_field_004 fuel (fragment0205178Field005Chars00 ++ (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 474) (SourceJson.white (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))))) fragment0205178Acc00600 := object_fragment0205178_field_005 fuel (fragment0205178Field006Chars00 ++ (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 473) (SourceJson.white (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail))))) fragment0205178Acc00700 := object_fragment0205178_field_006 fuel (fragment0205178Field007Chars00 ++ (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))) fragment0205178Acc00800 := object_fragment0205178_field_007 fuel (fragment0205178Field008Chars00 ++ (fragment0205178Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment0205178Field009Chars00 ++ (tail))) fragment0205178Acc00900 := object_fragment0205178_field_008 fuel (fragment0205178Field009Chars00 ++ (tail))
    _ = .ok (fragment0205178Value, tail) := object_fragment0205178_field_009 fuel (tail)

noncomputable def fragment0207270Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0207270Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0207270Field000Value00 : SourceJson := .number (String.ofList ['4', '3'])
noncomputable def fragment0207270Acc00100 : List (String × SourceJson) := (fragment0207270Field000Key00, fragment0207270Field000Value00) :: fragment0207270Acc00000
noncomputable def fragment0207270Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '3', ',']

theorem object_fragment0207270_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0207270Field000Chars00 ++ tail)) fragment0207270Acc00000 =
      SourceJson.object (fuel + 428) (SourceJson.white tail) fragment0207270Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_000"
  err.flush

noncomputable def fragment0207270Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0207270Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0207270Acc00200 : List (String × SourceJson) := (fragment0207270Field001Key00, fragment0207270Field001Value00) :: fragment0207270Acc00100
noncomputable def fragment0207270Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0207270_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 428) (SourceJson.white (fragment0207270Field001Chars00 ++ tail)) fragment0207270Acc00100 =
      SourceJson.object (fuel + 427) (SourceJson.white tail) fragment0207270Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_001"
  err.flush

noncomputable def fragment0207270Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0207270Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '3', '3', '8', '4', '1', '2', '1', '1', '0', '7', '4', '9', '8', '5', '5', '0', '4', '3', '5', '2', '3', '7', '7', '9', '9', '5', '8', '9', '3', '9', '8', '2', '3', '9', '/', '1', '6', '1', '1', '1', '6', '1', '5', '0', '8', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0207270Acc00300 : List (String × SourceJson) := (fragment0207270Field002Key00, fragment0207270Field002Value00) :: fragment0207270Acc00200
noncomputable def fragment0207270Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '8', '3', '3', '8', '4', '1', '2', '1', '1', '0', '7', '4', '9', '8', '5', '5', '0', '4', '3', '5', '2', '3', '7', '7', '9', '9', '5', '8', '9', '3', '9', '8', '2', '3', '9', '/', '1', '6', '1', '1', '1', '6', '1', '5', '0', '8', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0207270_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 427) (SourceJson.white (fragment0207270Field002Chars00 ++ tail)) fragment0207270Acc00200 =
      SourceJson.object (fuel + 426) (SourceJson.white tail) fragment0207270Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_002"
  err.flush

noncomputable def fragment0207270Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0207270Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0207270Acc00400 : List (String × SourceJson) := (fragment0207270Field003Key00, fragment0207270Field003Value00) :: fragment0207270Acc00300
noncomputable def fragment0207270Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0207270_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 426) (SourceJson.white (fragment0207270Field003Chars00 ++ tail)) fragment0207270Acc00300 =
      SourceJson.object (fuel + 425) (SourceJson.white tail) fragment0207270Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_003"
  err.flush

noncomputable def fragment0207270Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0207270Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0207270Acc00500 : List (String × SourceJson) := (fragment0207270Field004Key00, fragment0207270Field004Value00) :: fragment0207270Acc00400
noncomputable def fragment0207270Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '2', '0', '3', '1', '/', '8', '3', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0207270_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 425) (SourceJson.white (fragment0207270Field004Chars00 ++ tail)) fragment0207270Acc00400 =
      SourceJson.object (fuel + 424) (SourceJson.white tail) fragment0207270Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_004"
  err.flush

noncomputable def fragment0207270Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0207270Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '8', '5', '1', '4', '9', '8', '2', '2', '3', '5', '7', '7', '7', '0', '1', '6', '0', '6', '3', '0', '1', '3', '/', '4', '2', '8', '6', '9', '0', '4', '3', '7', '3', '4', '4', '6', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '2', '4', '3', '1', '3', '2', '4', '5', '9', '7', '0', '4', '9', '0', '3', '6', '9', '3', '2', '7', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '0', '3', '2', '8', '4', '0', '8', '1', '4', '8', '2', '8', '5', '5', '2', '1', '1', '0', '7', '6', '9', '/', '1', '7', '1', '4', '7', '6', '1', '7', '4', '9', '3', '7', '8', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '8', '1', '5', '3', '7', '6', '8', '4', '8', '8', '3', '3', '9', '9', '6', '1', '8', '2', '6', '1', '/', '2', '8', '5', '7', '9', '3', '6', '2', '4', '8', '9', '6', '4', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '7', '5', '4', '1', '1', '0', '9', '5', '7', '2', '6', '0', '3', '2', '5', '0', '1', '7', '6', '7', '/', '9', '5', '2', '6', '4', '5', '4', '1', '6', '3', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '7', '4', '5', '9', '7', '6', '5', '8', '6', '4', '8', '7', '4', '9', '9', '8', '9', '0', '8', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '5', '0', '7', '0', '6', '7', '9', '4', '1', '3', '9', '5', '5', '0', '5', '3', '5', '7', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '2', '3', '0', '3', '9', '9', '2', '1', '1', '0', '0', '5', '8', '2', '7', '6', '4', '2', '2', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '0', '6', '4', '4', '9', '9', '3', '6', '6', '4', '0', '9', '6', '9', '5', '6', '5', '4', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '1', '7', '2', '9', '6', '2', '6', '6', '0', '9', '3', '4', '0', '0', '4', '4', '6', '4', '6', '9', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0207270Acc00600 : List (String × SourceJson) := (fragment0207270Field005Key00, fragment0207270Field005Value00) :: fragment0207270Acc00500
noncomputable def fragment0207270Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '5', '1', '4', '9', '8', '2', '2', '3', '5', '7', '7', '7', '0', '1', '6', '0', '6', '3', '0', '1', '3', '/', '4', '2', '8', '6', '9', '0', '4', '3', '7', '3', '4', '4', '6', '1', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '2', '4', '3', '1', '3', '2', '4', '5', '9', '7', '0', '4', '9', '0', '3', '6', '9', '3', '2', '7', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '0', '3', '2', '8', '4', '0', '8', '1', '4', '8', '2', '8', '5', '5', '2', '1', '1', '0', '7', '6', '9', '/', '1', '7', '1', '4', '7', '6', '1', '7', '4', '9', '3', '7', '8', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '5', '8', '1', '5', '3', '7', '6', '8', '4', '8', '8', '3', '3', '9', '9', '6', '1', '8', '2', '6', '1', '/', '2', '8', '5', '7', '9', '3', '6', '2', '4', '8', '9', '6', '4', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '7', '5', '4', '1', '1', '0', '9', '5', '7', '2', '6', '0', '3', '2', '5', '0', '1', '7', '6', '7', '/', '9', '5', '2', '6', '4', '5', '4', '1', '6', '3', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '7', '4', '5', '9', '7', '6', '5', '8', '6', '4', '8', '7', '4', '9', '9', '8', '9', '0', '8', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '5', '0', '7', '0', '6', '7', '9', '4', '1', '3', '9', '5', '5', '0', '5', '3', '5', '7', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '2', '3', '0', '3', '9', '9', '2', '1', '1', '0', '0', '5', '8', '2', '7', '6', '4', '2', '2', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '0', '6', '4', '4', '9', '9', '3', '6', '6', '4', '0', '9', '6', '9', '5', '6', '5', '4', '9', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '1', '7', '2', '9', '6', '2', '6', '6', '0', '9', '3', '4', '0', '0', '4', '4', '6', '4', '6', '9', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0207270_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 424) (SourceJson.white (fragment0207270Field005Chars00 ++ tail)) fragment0207270Acc00500 =
      SourceJson.object (fuel + 423) (SourceJson.white tail) fragment0207270Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_005"
  err.flush

noncomputable def fragment0207270Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0207270Field006Value00 : SourceJson := .str (String.ofList ['2', '9', '4', '9', '5', '8', '0', '7', '5', '2', '8', '1', '2', '2', '4', '5', '4', '6', '3', '0', '9', '9', '4', '0', '2', '2', '1', '0', '1', '5', '2', '5', '6', '2', '1', '0', '5', '6', '3', '9', '7', '2', '0', '9', '6', '0', '/', '1', '8', '7', '5', '3', '3', '7', '7', '3', '3', '9', '1', '7', '1', '1', '6', '4', '1', '7', '5', '3', '5', '3', '3', '3', '8', '1', '0', '5', '7', '5', '2', '8', '3', '6', '5', '0', '6', '4', '2', '6', '4', '6', '4', '7', '8', '8', '2', '1', '3', '7', '8', '6', '1', '6', '4', '5', '5', '7', '6', '2', '7', '7'])
noncomputable def fragment0207270Acc00700 : List (String × SourceJson) := (fragment0207270Field006Key00, fragment0207270Field006Value00) :: fragment0207270Acc00600
noncomputable def fragment0207270Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '9', '4', '9', '5', '8', '0', '7', '5', '2', '8', '1', '2', '2', '4', '5', '4', '6', '3', '0', '9', '9', '4', '0', '2', '2', '1', '0', '1', '5', '2', '5', '6', '2', '1', '0', '5', '6', '3', '9', '7', '2', '0', '9', '6', '0', '/', '1', '8', '7', '5', '3', '3', '7', '7', '3', '3', '9', '1', '7', '1', '1', '6', '4', '1', '7', '5', '3', '5', '3', '3', '3', '8', '1', '0', '5', '7', '5', '2', '8', '3', '6', '5', '0', '6', '4', '2', '6', '4', '6', '4', '7', '8', '8', '2', '1', '3', '7', '8', '6', '1', '6', '4', '5', '5', '7', '6', '2', '7', '7', '"', ',']

theorem object_fragment0207270_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 423) (SourceJson.white (fragment0207270Field006Chars00 ++ tail)) fragment0207270Acc00600 =
      SourceJson.object (fuel + 422) (SourceJson.white tail) fragment0207270Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_006"
  err.flush

noncomputable def fragment0207270Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0207270Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '7', '0', '5', '1', '3', '9', '8', '5', '0', '1', '6', '6', '2', '6', '9', '7', '2', '3', '3', '6', '2', '0', '1', '6', '4', '6', '2', '5', '6', '4', '6', '6', '3', '7', '0', '9', '6', '7', '5', '7', '5', '9', '7', '0', '3', '8', '8', '4', '8', '7', '7', '2', '2', '2', '4', '6', '0', '1', '6', '8', '9', '1', '8', '5', '7', '2', '3', '5', '2', '3', '4', '1', '3', '3', '2', '6', '5', '3', '2', '9', '2', '8', '9', '7', '0', '6', '9', '9', '1', '2', '4', '3', '5', '2', '4', '6', '2', '9', '9', '1', '3', '1', '6', '5', '2', '4', '8', '7', '0', '6', '8', '0', '0', '1', '4', '7', '3', '0', '6', '6', '8', '2', '6', '1', '6', '5', '3', '0', '0', '6', '4', '4', '7', '2', '8', '5', '9', '8', '2', '4', '9', '4', '8', '5', '1', '2', '2', '0', '6', '0', '0', '8', '8', '6', '0', '0', '8', '6', '7', '4', '0', '6', '2', '3', '2', '3', '6', '9', '7', '1', '7', '0', '5', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '9', '1', '2', '3', '6', '9', '2', '5', '1', '5', '4', '9', '4', '8', '3', '6', '9', '8', '2', '4', '6', '4', '0', '9', '9', '0', '3', '0', '5', '1', '0', '9', '6', '6', '9', '2', '7', '1', '5', '0', '7', '9', '0', '4', '4', '0', '7', '9', '4', '8', '8', '6', '1', '9', '8', '0', '9', '5', '3', '0', '6', '5', '4', '5', '8', '4', '3', '4', '8', '6', '5', '0', '9', '9', '3', '9', '5', '3', '7', '1', '7', '4', '0', '6', '1', '2', '8', '4', '6', '7', '6', '7', '8', '8', '5', '3', '0', '1', '0', '4', '1', '8', '2', '5', '9', '5', '6', '9', '3', '8', '2', '1', '2', '4', '0', '3', '8', '7', '3', '2', '0', '6', '0', '6', '4', '7', '4', '9', '1', '7', '6', '6', '0', '2', '4', '8', '8', '0', '5', '3', '6', '4', '2', '2', '0', '1', '0', '7', '9', '7', '0', '7', '1', '2', '5', '5', '9', '6', '7', '2', '5', '7', '9', '1', '8', '6', '8', '0', '1', '9', '6', '6', '4', '5', '0', '2', '2', '6', '7', '4', '3', '6', '5', '8', '3', '8', '1', '5', '4', '6', '8', '7', '0', '4', '7', '9', '0', '3', '4', '8', '7', '5', '2', '4', '8', '7', '4', '1', '1', '6', '0', '6', '6', '7', '6', '7'])
noncomputable def fragment0207270Acc00800 : List (String × SourceJson) := (fragment0207270Field007Key00, fragment0207270Field007Value00) :: fragment0207270Acc00700
noncomputable def fragment0207270Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '7', '0', '5', '1', '3', '9', '8', '5', '0', '1', '6', '6', '2', '6', '9', '7', '2', '3', '3', '6', '2', '0', '1', '6', '4', '6', '2', '5', '6', '4', '6', '6', '3', '7', '0', '9', '6', '7', '5', '7', '5', '9', '7', '0', '3', '8', '8', '4', '8', '7', '7', '2', '2', '2', '4', '6', '0', '1', '6', '8', '9', '1', '8', '5', '7', '2', '3', '5', '2', '3', '4', '1', '3', '3', '2', '6', '5', '3', '2', '9', '2', '8', '9', '7', '0', '6', '9', '9', '1', '2', '4', '3', '5', '2', '4', '6', '2', '9', '9', '1', '3', '1', '6', '5', '2', '4', '8', '7', '0', '6', '8', '0', '0', '1', '4', '7', '3', '0', '6', '6', '8', '2', '6', '1', '6', '5', '3', '0', '0', '6', '4', '4', '7', '2', '8', '5', '9', '8', '2', '4', '9', '4', '8', '5', '1', '2', '2', '0', '6', '0', '0', '8', '8', '6', '0', '0', '8', '6', '7', '4', '0', '6', '2', '3', '2', '3', '6', '9', '7', '1', '7', '0', '5', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '9', '1', '2', '3', '6', '9', '2', '5', '1', '5', '4', '9', '4', '8', '3', '6', '9', '8', '2', '4', '6', '4', '0', '9', '9', '0', '3', '0', '5', '1', '0', '9', '6', '6', '9', '2', '7', '1', '5', '0', '7', '9', '0', '4', '4', '0', '7', '9', '4', '8', '8', '6', '1', '9', '8', '0', '9', '5', '3', '0', '6', '5', '4', '5', '8', '4', '3', '4', '8', '6', '5', '0', '9', '9', '3', '9', '5', '3', '7', '1', '7', '4', '0', '6', '1', '2', '8', '4', '6', '7', '6', '7', '8', '8', '5', '3', '0', '1', '0', '4', '1', '8', '2', '5', '9', '5', '6', '9', '3', '8', '2', '1', '2', '4', '0', '3', '8', '7', '3', '2', '0', '6', '0', '6', '4', '7', '4', '9', '1', '7', '6', '6', '0', '2', '4', '8', '8', '0', '5', '3', '6', '4', '2', '2', '0', '1', '0', '7', '9', '7', '0', '7', '1', '2', '5', '5', '9', '6', '7', '2', '5', '7', '9', '1', '8', '6', '8', '0', '1', '9', '6', '6', '4', '5', '0', '2', '2', '6', '7', '4', '3', '6', '5', '8', '3', '8', '1', '5', '4', '6', '8', '7', '0', '4', '7', '9', '0', '3', '4', '8', '7', '5', '2', '4', '8', '7', '4', '1', '1', '6', '0', '6', '6', '7', '6', '7', '"', ',']

theorem object_fragment0207270_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 422) (SourceJson.white (fragment0207270Field007Chars00 ++ tail)) fragment0207270Acc00700 =
      SourceJson.object (fuel + 421) (SourceJson.white tail) fragment0207270Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_007"
  err.flush

noncomputable def fragment0207270Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0207270Field008Value00 : SourceJson := .str (String.ofList ['1', '2', '4', '6', '1', '2', '1', '4', '7', '9', '9', '1', '4'])
noncomputable def fragment0207270Acc00900 : List (String × SourceJson) := (fragment0207270Field008Key00, fragment0207270Field008Value00) :: fragment0207270Acc00800
noncomputable def fragment0207270Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '4', '6', '1', '2', '1', '4', '7', '9', '9', '1', '4', '"', ',']

theorem object_fragment0207270_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0207270Field008Chars00 ++ tail)) fragment0207270Acc00800 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0207270Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_008"
  err.flush

noncomputable def fragment0207270Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0207270Field009Value00 : SourceJson := .str (String.ofList ['4', '5', '4', '4', '4', '7', '0', '2', '2', '5', '2', '9', '2'])
noncomputable def fragment0207270Acc01000 : List (String × SourceJson) := (fragment0207270Field009Key00, fragment0207270Field009Value00) :: fragment0207270Acc00900
noncomputable def fragment0207270Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '5', '4', '4', '4', '7', '0', '2', '2', '5', '2', '9', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0207270_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0207270Field009Chars00 ++ tail)) fragment0207270Acc00900 =
      .ok (.obj (fragment0207270Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0207270_object_field_009"
  err.flush

noncomputable def fragment0207270Chars : List Char := '{' :: (fragment0207270Field000Chars00 ++ fragment0207270Field001Chars00 ++ fragment0207270Field002Chars00 ++ fragment0207270Field003Chars00 ++ fragment0207270Field004Chars00 ++ fragment0207270Field005Chars00 ++ fragment0207270Field006Chars00 ++ fragment0207270Field007Chars00 ++ fragment0207270Field008Chars00 ++ fragment0207270Field009Chars00)
noncomputable def fragment0207270Value : SourceJson := .obj (fragment0207270Acc01000.reverse)

theorem value_fragment0207270 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 430) (fragment0207270Chars ++ tail) =
      .ok (fragment0207270Value, tail) := by
  have hinput : fragment0207270Chars ++ tail = '{' :: (fragment0207270Field000Chars00 ++ (fragment0207270Field001Chars00 ++ (fragment0207270Field002Chars00 ++ (fragment0207270Field003Chars00 ++ (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0207270Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 430) (fragment0207270Chars ++ tail) =
        SourceJson.value (fuel + 430) ('{' :: (fragment0207270Field000Chars00 ++ (fragment0207270Field001Chars00 ++ (fragment0207270Field002Chars00 ++ (fragment0207270Field003Chars00 ++ (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 430)) hinput
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0207270Field000Chars00 ++ (fragment0207270Field001Chars00 ++ (fragment0207270Field002Chars00 ++ (fragment0207270Field003Chars00 ++ (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))))))))))) fragment0207270Acc00000 := by rfl
    _ = SourceJson.object (fuel + 428) (SourceJson.white (fragment0207270Field001Chars00 ++ (fragment0207270Field002Chars00 ++ (fragment0207270Field003Chars00 ++ (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail))))))))))) fragment0207270Acc00100 := object_fragment0207270_field_000 fuel (fragment0207270Field001Chars00 ++ (fragment0207270Field002Chars00 ++ (fragment0207270Field003Chars00 ++ (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 427) (SourceJson.white (fragment0207270Field002Chars00 ++ (fragment0207270Field003Chars00 ++ (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))))))))) fragment0207270Acc00200 := object_fragment0207270_field_001 fuel (fragment0207270Field002Chars00 ++ (fragment0207270Field003Chars00 ++ (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 426) (SourceJson.white (fragment0207270Field003Chars00 ++ (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail))))))))) fragment0207270Acc00300 := object_fragment0207270_field_002 fuel (fragment0207270Field003Chars00 ++ (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 425) (SourceJson.white (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))))))) fragment0207270Acc00400 := object_fragment0207270_field_003 fuel (fragment0207270Field004Chars00 ++ (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 424) (SourceJson.white (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail))))))) fragment0207270Acc00500 := object_fragment0207270_field_004 fuel (fragment0207270Field005Chars00 ++ (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 423) (SourceJson.white (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))))) fragment0207270Acc00600 := object_fragment0207270_field_005 fuel (fragment0207270Field006Chars00 ++ (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 422) (SourceJson.white (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail))))) fragment0207270Acc00700 := object_fragment0207270_field_006 fuel (fragment0207270Field007Chars00 ++ (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))) fragment0207270Acc00800 := object_fragment0207270_field_007 fuel (fragment0207270Field008Chars00 ++ (fragment0207270Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0207270Field009Chars00 ++ (tail))) fragment0207270Acc00900 := object_fragment0207270_field_008 fuel (fragment0207270Field009Chars00 ++ (tail))
    _ = .ok (fragment0207270Value, tail) := object_fragment0207270_field_009 fuel (tail)

noncomputable def fragment0209244Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0209244Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0209244Field000Value00 : SourceJson := .number (String.ofList ['4', '4'])
noncomputable def fragment0209244Acc00100 : List (String × SourceJson) := (fragment0209244Field000Key00, fragment0209244Field000Value00) :: fragment0209244Acc00000
noncomputable def fragment0209244Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '4', ',']

theorem object_fragment0209244_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0209244Field000Chars00 ++ tail)) fragment0209244Acc00000 =
      SourceJson.object (fuel + 250) (SourceJson.white tail) fragment0209244Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_000"
  err.flush

noncomputable def fragment0209244Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0209244Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0209244Acc00200 : List (String × SourceJson) := (fragment0209244Field001Key00, fragment0209244Field001Value00) :: fragment0209244Acc00100
noncomputable def fragment0209244Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0209244_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 250) (SourceJson.white (fragment0209244Field001Chars00 ++ tail)) fragment0209244Acc00100 =
      SourceJson.object (fuel + 249) (SourceJson.white tail) fragment0209244Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_001"
  err.flush

noncomputable def fragment0209244Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0209244Field002Value00 : SourceJson := .str (String.ofList ['2', '6', '1', '8', '6', '9', '1', '1', '9', '3', '9', '0', '4', '0', '8', '3', '9', '3', '3', '5', '0', '3', '2', '7', '8', '7', '6', '1', '4', '8', '1', '3', '5', '4', '8', '9', '7', '9', '/', '3', '5', '5', '1', '1', '3', '1', '4', '8', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0209244Acc00300 : List (String × SourceJson) := (fragment0209244Field002Key00, fragment0209244Field002Value00) :: fragment0209244Acc00200
noncomputable def fragment0209244Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '6', '1', '8', '6', '9', '1', '1', '9', '3', '9', '0', '4', '0', '8', '3', '9', '3', '3', '5', '0', '3', '2', '7', '8', '7', '6', '1', '4', '8', '1', '3', '5', '4', '8', '9', '7', '9', '/', '3', '5', '5', '1', '1', '3', '1', '4', '8', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0209244_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 249) (SourceJson.white (fragment0209244Field002Chars00 ++ tail)) fragment0209244Acc00200 =
      SourceJson.object (fuel + 248) (SourceJson.white tail) fragment0209244Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_002"
  err.flush

noncomputable def fragment0209244Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0209244Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0209244Acc00400 : List (String × SourceJson) := (fragment0209244Field003Key00, fragment0209244Field003Value00) :: fragment0209244Acc00300
noncomputable def fragment0209244Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0209244_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 248) (SourceJson.white (fragment0209244Field003Chars00 ++ tail)) fragment0209244Acc00300 =
      SourceJson.object (fuel + 247) (SourceJson.white tail) fragment0209244Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_003"
  err.flush

noncomputable def fragment0209244Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0209244Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0209244Acc00500 : List (String × SourceJson) := (fragment0209244Field004Key00, fragment0209244Field004Value00) :: fragment0209244Acc00400
noncomputable def fragment0209244Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0209244_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 247) (SourceJson.white (fragment0209244Field004Chars00 ++ tail)) fragment0209244Acc00400 =
      SourceJson.object (fuel + 246) (SourceJson.white tail) fragment0209244Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_004"
  err.flush

noncomputable def fragment0209244Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0209244Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '4', '4', '0', '3', '2', '3', '0', '9', '9', '1', '7', '3', '/', '6', '1', '0', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '2', '0', '9', '2', '3', '1', '2', '5', '5', '2', '9', '/', '6', '1', '0', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '9', '9', '8', '3', '4', '0', '8', '6', '7', '8', '3', '7', '/', '5', '1', '2', '5', '9', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '7', '6', '9', '4', '6', '0', '5', '6', '5', '9', '0', '4', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '3', '0', '1', '8', '3', '9', '0', '9', '6', '1', '6', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '2', '4', '6', '4', '7', '2', '1', '8', '3', '4', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '9', '0', '3', '1', '4', '8', '3', '9', '2', '5', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '6', '4', '6', '9', '9', '0', '2', '0', '9', '7', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '8', '3', '6', '5', '2', '9', '1', '8', '5', '7', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '4', '8', '0', '4', '4', '7', '7', '6', '8', '8', '9', '/', '1', '8', '3', '0', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0209244Acc00600 : List (String × SourceJson) := (fragment0209244Field005Key00, fragment0209244Field005Value00) :: fragment0209244Acc00500
noncomputable def fragment0209244Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '4', '0', '3', '2', '3', '0', '9', '9', '1', '7', '3', '/', '6', '1', '0', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '2', '0', '9', '2', '3', '1', '2', '5', '5', '2', '9', '/', '6', '1', '0', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '9', '9', '8', '3', '4', '0', '8', '6', '7', '8', '3', '7', '/', '5', '1', '2', '5', '9', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '7', '6', '9', '4', '6', '0', '5', '6', '5', '9', '0', '4', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '3', '0', '1', '8', '3', '9', '0', '9', '6', '1', '6', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '2', '4', '6', '4', '7', '2', '1', '8', '3', '4', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '9', '0', '3', '1', '4', '8', '3', '9', '2', '5', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '6', '4', '6', '9', '9', '0', '2', '0', '9', '7', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '8', '3', '6', '5', '2', '9', '1', '8', '5', '7', '/', '1', '6', '6', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '4', '8', '0', '4', '4', '7', '7', '6', '8', '8', '9', '/', '1', '8', '3', '0', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0209244_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 246) (SourceJson.white (fragment0209244Field005Chars00 ++ tail)) fragment0209244Acc00500 =
      SourceJson.object (fuel + 245) (SourceJson.white tail) fragment0209244Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_005"
  err.flush

noncomputable def fragment0209244Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0209244Field006Value00 : SourceJson := .str (String.ofList ['3', '6', '9', '0', '9', '0', '7', '7', '6', '9', '2', '0', '0', '1', '0', '4', '7', '5', '2', '4', '5', '4', '5', '5', '8', '3', '8', '0', '7', '1', '5', '1', '8', '3', '8', '5', '5', '1', '5', '7', '1', '0', '2', '3', '8', '7', '2', '0', '0', '0', '/', '6', '0', '9', '7', '7', '8', '7', '9', '9', '5', '3', '3', '3', '8', '9', '3', '2', '2', '6', '0', '4', '4', '3', '0', '1', '2', '2', '8', '7', '2', '2', '9', '2', '2', '9', '5', '7', '1', '2', '4', '6', '3', '7', '7', '1', '9', '2', '1', '8', '1', '7', '1', '0', '6', '8', '2', '3', '4', '4', '0', '4', '8', '2', '2', '5', '9'])
noncomputable def fragment0209244Acc00700 : List (String × SourceJson) := (fragment0209244Field006Key00, fragment0209244Field006Value00) :: fragment0209244Acc00600
noncomputable def fragment0209244Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '6', '9', '0', '9', '0', '7', '7', '6', '9', '2', '0', '0', '1', '0', '4', '7', '5', '2', '4', '5', '4', '5', '5', '8', '3', '8', '0', '7', '1', '5', '1', '8', '3', '8', '5', '5', '1', '5', '7', '1', '0', '2', '3', '8', '7', '2', '0', '0', '0', '/', '6', '0', '9', '7', '7', '8', '7', '9', '9', '5', '3', '3', '3', '8', '9', '3', '2', '2', '6', '0', '4', '4', '3', '0', '1', '2', '2', '8', '7', '2', '2', '9', '2', '2', '9', '5', '7', '1', '2', '4', '6', '3', '7', '7', '1', '9', '2', '1', '8', '1', '7', '1', '0', '6', '8', '2', '3', '4', '4', '0', '4', '8', '2', '2', '5', '9', '"', ',']

theorem object_fragment0209244_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0209244Field006Chars00 ++ tail)) fragment0209244Acc00600 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0209244Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_006"
  err.flush

noncomputable def fragment0209244Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0209244Field007Value00 : SourceJson := .str (String.ofList ['4', '0', '1', '2', '4', '5', '7', '2', '7', '4', '6', '1', '8', '0', '2', '9', '7', '1', '4', '1', '9', '5', '2', '1', '8', '2', '0', '5', '4', '6', '0', '7', '8', '9', '3', '7', '3', '1', '7', '4', '5', '3', '3', '5', '9', '6', '9', '3', '4', '3', '5', '1', '6', '5', '1', '0', '1', '9', '8', '2', '9', '0', '4', '7', '5', '2', '3', '6', '3', '9', '4', '6', '1', '7', '7', '1', '0', '5', '5', '2', '6', '0', '3', '4', '2', '0', '2', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '2', '6', '8', '7', '5', '3', '5', '9', '2', '3', '6', '4', '2', '4', '3', '9', '5', '8', '3', '6', '1', '6', '1', '4', '0', '2', '4', '1', '6', '2', '3', '9', '5', '9', '8', '2', '0', '0', '8', '8', '2', '1', '3', '7', '6', '3', '2', '5', '4', '8', '1', '4', '5', '3', '4', '2', '8', '0', '4', '8', '1', '7', '5', '4', '5', '0', '7', '3', '9', '4', '8', '3', '8', '7', '2', '1', '1', '9', '5', '3', '6', '9', '2', '0', '7', '1', '9', '7', '6', '9', '5', '4', '2', '4', '3', '0', '6', '3', '4', '8', '3', '7', '0', '6', '4', '6', '9', '7', '9', '3', '2', '2', '5', '0', '5', '4', '6', '4', '7', '6', '0', '8', '2', '7', '0', '9'])
noncomputable def fragment0209244Acc00800 : List (String × SourceJson) := (fragment0209244Field007Key00, fragment0209244Field007Value00) :: fragment0209244Acc00700
noncomputable def fragment0209244Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '0', '1', '2', '4', '5', '7', '2', '7', '4', '6', '1', '8', '0', '2', '9', '7', '1', '4', '1', '9', '5', '2', '1', '8', '2', '0', '5', '4', '6', '0', '7', '8', '9', '3', '7', '3', '1', '7', '4', '5', '3', '3', '5', '9', '6', '9', '3', '4', '3', '5', '1', '6', '5', '1', '0', '1', '9', '8', '2', '9', '0', '4', '7', '5', '2', '3', '6', '3', '9', '4', '6', '1', '7', '7', '1', '0', '5', '5', '2', '6', '0', '3', '4', '2', '0', '2', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '2', '6', '8', '7', '5', '3', '5', '9', '2', '3', '6', '4', '2', '4', '3', '9', '5', '8', '3', '6', '1', '6', '1', '4', '0', '2', '4', '1', '6', '2', '3', '9', '5', '9', '8', '2', '0', '0', '8', '8', '2', '1', '3', '7', '6', '3', '2', '5', '4', '8', '1', '4', '5', '3', '4', '2', '8', '0', '4', '8', '1', '7', '5', '4', '5', '0', '7', '3', '9', '4', '8', '3', '8', '7', '2', '1', '1', '9', '5', '3', '6', '9', '2', '0', '7', '1', '9', '7', '6', '9', '5', '4', '2', '4', '3', '0', '6', '3', '4', '8', '3', '7', '0', '6', '4', '6', '9', '7', '9', '3', '2', '2', '5', '0', '5', '4', '6', '4', '7', '6', '0', '8', '2', '7', '0', '9', '"', ',']

theorem object_fragment0209244_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0209244Field007Chars00 ++ tail)) fragment0209244Acc00700 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0209244Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_007"
  err.flush

noncomputable def fragment0209244Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0209244Field008Value00 : SourceJson := .str (String.ofList ['4', '7', '9', '5', '5', '7', '2', '4', '4', '0', '1', '5', '5'])
noncomputable def fragment0209244Acc00900 : List (String × SourceJson) := (fragment0209244Field008Key00, fragment0209244Field008Value00) :: fragment0209244Acc00800
noncomputable def fragment0209244Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '7', '9', '5', '5', '7', '2', '4', '4', '0', '1', '5', '5', '"', ',']

theorem object_fragment0209244_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0209244Field008Chars00 ++ tail)) fragment0209244Acc00800 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0209244Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_008"
  err.flush

noncomputable def fragment0209244Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0209244Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '2', '7', '9', '4', '2', '4', '4', '0', '6', '4', '2', '4'])
noncomputable def fragment0209244Acc01000 : List (String × SourceJson) := (fragment0209244Field009Key00, fragment0209244Field009Value00) :: fragment0209244Acc00900
noncomputable def fragment0209244Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '2', '7', '9', '4', '2', '4', '4', '0', '6', '4', '2', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0209244_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0209244Field009Chars00 ++ tail)) fragment0209244Acc00900 =
      .ok (.obj (fragment0209244Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0209244_object_field_009"
  err.flush

noncomputable def fragment0209244Chars : List Char := '{' :: (fragment0209244Field000Chars00 ++ fragment0209244Field001Chars00 ++ fragment0209244Field002Chars00 ++ fragment0209244Field003Chars00 ++ fragment0209244Field004Chars00 ++ fragment0209244Field005Chars00 ++ fragment0209244Field006Chars00 ++ fragment0209244Field007Chars00 ++ fragment0209244Field008Chars00 ++ fragment0209244Field009Chars00)
noncomputable def fragment0209244Value : SourceJson := .obj (fragment0209244Acc01000.reverse)

theorem value_fragment0209244 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 252) (fragment0209244Chars ++ tail) =
      .ok (fragment0209244Value, tail) := by
  have hinput : fragment0209244Chars ++ tail = '{' :: (fragment0209244Field000Chars00 ++ (fragment0209244Field001Chars00 ++ (fragment0209244Field002Chars00 ++ (fragment0209244Field003Chars00 ++ (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0209244Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 252) (fragment0209244Chars ++ tail) =
        SourceJson.value (fuel + 252) ('{' :: (fragment0209244Field000Chars00 ++ (fragment0209244Field001Chars00 ++ (fragment0209244Field002Chars00 ++ (fragment0209244Field003Chars00 ++ (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 252)) hinput
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0209244Field000Chars00 ++ (fragment0209244Field001Chars00 ++ (fragment0209244Field002Chars00 ++ (fragment0209244Field003Chars00 ++ (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))))))))))) fragment0209244Acc00000 := by rfl
    _ = SourceJson.object (fuel + 250) (SourceJson.white (fragment0209244Field001Chars00 ++ (fragment0209244Field002Chars00 ++ (fragment0209244Field003Chars00 ++ (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail))))))))))) fragment0209244Acc00100 := object_fragment0209244_field_000 fuel (fragment0209244Field001Chars00 ++ (fragment0209244Field002Chars00 ++ (fragment0209244Field003Chars00 ++ (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 249) (SourceJson.white (fragment0209244Field002Chars00 ++ (fragment0209244Field003Chars00 ++ (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))))))))) fragment0209244Acc00200 := object_fragment0209244_field_001 fuel (fragment0209244Field002Chars00 ++ (fragment0209244Field003Chars00 ++ (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 248) (SourceJson.white (fragment0209244Field003Chars00 ++ (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail))))))))) fragment0209244Acc00300 := object_fragment0209244_field_002 fuel (fragment0209244Field003Chars00 ++ (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 247) (SourceJson.white (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))))))) fragment0209244Acc00400 := object_fragment0209244_field_003 fuel (fragment0209244Field004Chars00 ++ (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 246) (SourceJson.white (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail))))))) fragment0209244Acc00500 := object_fragment0209244_field_004 fuel (fragment0209244Field005Chars00 ++ (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))))) fragment0209244Acc00600 := object_fragment0209244_field_005 fuel (fragment0209244Field006Chars00 ++ (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail))))) fragment0209244Acc00700 := object_fragment0209244_field_006 fuel (fragment0209244Field007Chars00 ++ (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))) fragment0209244Acc00800 := object_fragment0209244_field_007 fuel (fragment0209244Field008Chars00 ++ (fragment0209244Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0209244Field009Chars00 ++ (tail))) fragment0209244Acc00900 := object_fragment0209244_field_008 fuel (fragment0209244Field009Chars00 ++ (tail))
    _ = .ok (fragment0209244Value, tail) := object_fragment0209244_field_009 fuel (tail)

noncomputable def fragment0210881Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0210881Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0210881Field000Value00 : SourceJson := .number (String.ofList ['4', '5'])
noncomputable def fragment0210881Acc00100 : List (String × SourceJson) := (fragment0210881Field000Key00, fragment0210881Field000Value00) :: fragment0210881Acc00000
noncomputable def fragment0210881Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '5', ',']

theorem object_fragment0210881_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 438) (SourceJson.white (fragment0210881Field000Chars00 ++ tail)) fragment0210881Acc00000 =
      SourceJson.object (fuel + 437) (SourceJson.white tail) fragment0210881Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_000"
  err.flush

noncomputable def fragment0210881Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0210881Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['3']), .number (String.ofList ['0'])]
noncomputable def fragment0210881Acc00200 : List (String × SourceJson) := (fragment0210881Field001Key00, fragment0210881Field001Value00) :: fragment0210881Acc00100
noncomputable def fragment0210881Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0210881_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0210881Field001Chars00 ++ tail)) fragment0210881Acc00100 =
      SourceJson.object (fuel + 436) (SourceJson.white tail) fragment0210881Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_001"
  err.flush

noncomputable def fragment0210881Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0210881Field002Value00 : SourceJson := .str (String.ofList ['8', '6', '2', '7', '8', '2', '2', '2', '1', '1', '4', '5', '1', '0', '5', '5', '2', '1', '9', '7', '6', '8', '8', '5', '0', '6', '6', '5', '8', '8', '3', '3', '9', '6', '8', '1', '2', '6', '4', '1', '/', '3', '5', '1', '8', '9', '8', '1', '3', '2', '5', '6', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0210881Acc00300 : List (String × SourceJson) := (fragment0210881Field002Key00, fragment0210881Field002Value00) :: fragment0210881Acc00200
noncomputable def fragment0210881Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '8', '6', '2', '7', '8', '2', '2', '2', '1', '1', '4', '5', '1', '0', '5', '5', '2', '1', '9', '7', '6', '8', '8', '5', '0', '6', '6', '5', '8', '8', '3', '3', '9', '6', '8', '1', '2', '6', '4', '1', '/', '3', '5', '1', '8', '9', '8', '1', '3', '2', '5', '6', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0210881_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0210881Field002Chars00 ++ tail)) fragment0210881Acc00200 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0210881Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_002"
  err.flush

noncomputable def fragment0210881Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0210881Field003Value00 : SourceJson := .str (String.ofList ['3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0210881Acc00400 : List (String × SourceJson) := (fragment0210881Field003Key00, fragment0210881Field003Value00) :: fragment0210881Acc00300
noncomputable def fragment0210881Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0210881_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0210881Field003Chars00 ++ tail)) fragment0210881Acc00300 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0210881Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_003"
  err.flush

noncomputable def fragment0210881Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0210881Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0210881Acc00500 : List (String × SourceJson) := (fragment0210881Field004Key00, fragment0210881Field004Value00) :: fragment0210881Acc00400
noncomputable def fragment0210881Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0210881_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0210881Field004Chars00 ++ tail)) fragment0210881Acc00400 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0210881Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_004"
  err.flush

noncomputable def fragment0210881Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0210881Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '6', '2', '4', '7', '6', '5', '3', '5', '5', '7', '6', '0', '2', '1', '9', '4', '8', '7', '7', '5', '6', '3', '/', '2', '9', '1', '4', '0', '4', '3', '3', '3', '7', '9', '0', '2', '4', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '6', '6', '8', '2', '6', '5', '6', '6', '8', '9', '9', '2', '6', '5', '8', '9', '1', '0', '1', '7', '3', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '2', '4', '1', '6', '9', '8', '3', '2', '5', '8', '0', '7', '7', '4', '0', '6', '5', '6', '4', '2', '9', '/', '2', '3', '3', '1', '2', '3', '4', '6', '7', '0', '3', '2', '1', '9', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '9', '0', '4', '9', '1', '7', '6', '5', '6', '0', '0', '3', '1', '5', '4', '4', '3', '7', '1', '9', '/', '1', '2', '9', '5', '1', '3', '0', '3', '7', '2', '4', '0', '1', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '5', '6', '0', '3', '3', '7', '5', '1', '2', '4', '9', '0', '5', '0', '0', '5', '2', '6', '0', '3', '7', '/', '3', '8', '8', '5', '3', '9', '1', '1', '1', '7', '2', '0', '3', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '4', '3', '7', '5', '7', '3', '7', '6', '7', '1', '6', '5', '4', '1', '3', '4', '1', '3', '7', '7', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '1', '7', '6', '9', '0', '3', '3', '4', '4', '9', '9', '4', '4', '8', '7', '6', '7', '5', '4', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '1', '0', '7', '5', '2', '7', '6', '3', '6', '5', '9', '3', '9', '2', '4', '3', '9', '4', '8', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '2', '6', '8', '8', '6', '1', '6', '6', '7', '6', '6', '2', '7', '6', '6', '7', '5', '0', '7', '/', '1', '3', '2', '4', '5', '6', '5', '1', '5', '3', '5', '9', '2', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '2', '9', '4', '1', '1', '5', '5', '9', '4', '2', '2', '9', '6', '3', '1', '4', '4', '0', '8', '3', '1', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0210881Acc00600 : List (String × SourceJson) := (fragment0210881Field005Key00, fragment0210881Field005Value00) :: fragment0210881Acc00500
noncomputable def fragment0210881Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '2', '4', '7', '6', '5', '3', '5', '5', '7', '6', '0', '2', '1', '9', '4', '8', '7', '7', '5', '6', '3', '/', '2', '9', '1', '4', '0', '4', '3', '3', '3', '7', '9', '0', '2', '4', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '6', '6', '8', '2', '6', '5', '6', '6', '8', '9', '9', '2', '6', '5', '8', '9', '1', '0', '1', '7', '3', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '2', '4', '1', '6', '9', '8', '3', '2', '5', '8', '0', '7', '7', '4', '0', '6', '5', '6', '4', '2', '9', '/', '2', '3', '3', '1', '2', '3', '4', '6', '7', '0', '3', '2', '1', '9', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '9', '0', '4', '9', '1', '7', '6', '5', '6', '0', '0', '3', '1', '5', '4', '4', '3', '7', '1', '9', '/', '1', '2', '9', '5', '1', '3', '0', '3', '7', '2', '4', '0', '1', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '5', '6', '0', '3', '3', '7', '5', '1', '2', '4', '9', '0', '5', '0', '0', '5', '2', '6', '0', '3', '7', '/', '3', '8', '8', '5', '3', '9', '1', '1', '1', '7', '2', '0', '3', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '4', '3', '7', '5', '7', '3', '7', '6', '7', '1', '6', '5', '4', '1', '3', '4', '1', '3', '7', '7', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '1', '7', '6', '9', '0', '3', '3', '4', '4', '9', '9', '4', '4', '8', '7', '6', '7', '5', '4', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '1', '0', '7', '5', '2', '7', '6', '3', '6', '5', '9', '3', '9', '2', '4', '3', '9', '4', '8', '1', '/', '1', '0', '5', '9', '6', '5', '2', '1', '2', '2', '8', '7', '3', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '2', '6', '8', '8', '6', '1', '6', '6', '7', '6', '6', '2', '7', '6', '6', '7', '5', '0', '7', '/', '1', '3', '2', '4', '5', '6', '5', '1', '5', '3', '5', '9', '2', '0', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '2', '9', '4', '1', '1', '5', '5', '9', '4', '2', '2', '9', '6', '3', '1', '4', '4', '0', '8', '3', '1', '/', '5', '8', '2', '8', '0', '8', '6', '6', '7', '5', '8', '0', '4', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0210881_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0210881Field005Chars00 ++ tail)) fragment0210881Acc00500 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0210881Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_005"
  err.flush

noncomputable def fragment0210881Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0210881Field006Value00 : SourceJson := .str (String.ofList ['2', '6', '8', '2', '5', '4', '2', '0', '3', '0', '1', '6', '5', '2', '6', '5', '0', '2', '7', '0', '7', '6', '0', '7', '5', '5', '5', '2', '5', '6', '2', '4', '3', '5', '6', '1', '9', '2', '0', '6', '5', '1', '9', '1', '1', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '/', '5', '4', '3', '1', '5', '3', '6', '0', '0', '1', '3', '5', '7', '5', '1', '4', '0', '1', '2', '2', '8', '1', '0', '3', '7', '6', '1', '4', '4', '9', '9', '5', '4', '1', '2', '7', '0', '1', '1', '0', '8', '7', '5', '4', '6', '5', '6', '9', '2', '3', '8', '5', '9', '8', '9', '0', '5', '9', '7', '0', '3', '8', '6', '4', '2', '9', '1'])
noncomputable def fragment0210881Acc00700 : List (String × SourceJson) := (fragment0210881Field006Key00, fragment0210881Field006Value00) :: fragment0210881Acc00600
noncomputable def fragment0210881Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '8', '2', '5', '4', '2', '0', '3', '0', '1', '6', '5', '2', '6', '5', '0', '2', '7', '0', '7', '6', '0', '7', '5', '5', '5', '2', '5', '6', '2', '4', '3', '5', '6', '1', '9', '2', '0', '6', '5', '1', '9', '1', '1', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '/', '5', '4', '3', '1', '5', '3', '6', '0', '0', '1', '3', '5', '7', '5', '1', '4', '0', '1', '2', '2', '8', '1', '0', '3', '7', '6', '1', '4', '4', '9', '9', '5', '4', '1', '2', '7', '0', '1', '1', '0', '8', '7', '5', '4', '6', '5', '6', '9', '2', '3', '8', '5', '9', '8', '9', '0', '5', '9', '7', '0', '3', '8', '6', '4', '2', '9', '1', '"', ',']

theorem object_fragment0210881_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0210881Field006Chars00 ++ tail)) fragment0210881Acc00600 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0210881Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_006"
  err.flush

noncomputable def fragment0210881Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0210881Field007Value00 : SourceJson := .str (String.ofList ['1', '4', '0', '8', '0', '6', '9', '6', '5', '9', '9', '3', '7', '5', '5', '1', '1', '0', '4', '6', '5', '8', '6', '8', '7', '1', '9', '9', '3', '7', '6', '7', '0', '4', '8', '2', '2', '9', '9', '3', '7', '2', '6', '5', '4', '7', '9', '5', '4', '5', '3', '1', '7', '2', '7', '0', '2', '2', '8', '9', '0', '6', '1', '6', '0', '4', '5', '1', '1', '4', '3', '3', '8', '1', '9', '2', '4', '8', '4', '2', '4', '4', '1', '1', '3', '8', '8', '7', '6', '0', '6', '3', '3', '2', '7', '5', '1', '1', '5', '9', '1', '1', '5', '3', '6', '2', '1', '1', '1', '4', '8', '0', '5', '9', '9', '8', '8', '0', '0', '1', '9', '1', '0', '0', '6', '9', '2', '9', '2', '4', '7', '0', '2', '8', '0', '5', '9', '3', '7', '9', '6', '9', '4', '0', '3', '2', '5', '8', '1', '0', '3', '4', '9', '8', '8', '5', '9', '6', '4', '1', '7', '1', '3', '1', '7', '8', '8', '5', '3', '5', '7', '3', '9', '1', '2', '7', '4', '2', '1', '8', '2', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '3', '0', '2', '5', '0', '1', '0', '3', '6', '3', '0', '2', '6', '1', '3', '4', '8', '3', '4', '2', '2', '1', '9', '6', '7', '0', '7', '6', '2', '8', '1', '3', '8', '8', '8', '5', '3', '8', '2', '8', '2', '0', '2', '0', '9', '5', '3', '6', '1', '9', '8', '2', '3', '7', '7', '3', '3', '7', '9', '0', '5', '7', '6', '2', '5', '5', '4', '1', '2', '7', '3', '2', '4', '5', '0', '0', '0', '8', '5', '3', '1', '7', '6', '2', '1', '1', '2', '8', '3', '0', '8', '5', '5', '7', '5', '0', '6', '5', '1', '2', '8', '3', '2', '1', '2', '1', '9', '8', '0', '8', '0', '0', '3', '4', '6', '8', '7', '7', '8', '1', '3', '0', '9', '7', '2', '3', '0', '3', '4', '7', '4', '1', '6', '9', '8', '3', '9', '0', '8', '8', '2', '1', '5', '9', '0', '0', '6', '7', '5', '4', '9', '9', '9', '1', '5', '8', '4', '4', '8', '7', '8', '1', '5', '7', '1', '2', '1', '1', '9', '6', '5', '8', '1', '6', '0', '7', '7', '4', '2', '7', '3', '2', '5', '5', '2', '5', '5', '0', '3', '8', '8', '5', '8', '8', '8', '3', '9', '7', '0', '5', '9', '9', '6', '7', '8', '1', '5', '5', '3', '7', '0', '7', '5', '1', '1', '8', '0', '3'])
noncomputable def fragment0210881Acc00800 : List (String × SourceJson) := (fragment0210881Field007Key00, fragment0210881Field007Value00) :: fragment0210881Acc00700
noncomputable def fragment0210881Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '0', '8', '0', '6', '9', '6', '5', '9', '9', '3', '7', '5', '5', '1', '1', '0', '4', '6', '5', '8', '6', '8', '7', '1', '9', '9', '3', '7', '6', '7', '0', '4', '8', '2', '2', '9', '9', '3', '7', '2', '6', '5', '4', '7', '9', '5', '4', '5', '3', '1', '7', '2', '7', '0', '2', '2', '8', '9', '0', '6', '1', '6', '0', '4', '5', '1', '1', '4', '3', '3', '8', '1', '9', '2', '4', '8', '4', '2', '4', '4', '1', '1', '3', '8', '8', '7', '6', '0', '6', '3', '3', '2', '7', '5', '1', '1', '5', '9', '1', '1', '5', '3', '6', '2', '1', '1', '1', '4', '8', '0', '5', '9', '9', '8', '8', '0', '0', '1', '9', '1', '0', '0', '6', '9', '2', '9', '2', '4', '7', '0', '2', '8', '0', '5', '9', '3', '7', '9', '6', '9', '4', '0', '3', '2', '5', '8', '1', '0', '3', '4', '9', '8', '8', '5', '9', '6', '4', '1', '7', '1', '3', '1', '7', '8', '8', '5', '3', '5', '7', '3', '9', '1', '2', '7', '4', '2', '1', '8', '2', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '3', '0', '2', '5', '0', '1', '0', '3', '6', '3', '0', '2', '6', '1', '3', '4', '8', '3', '4', '2', '2', '1', '9', '6', '7', '0', '7', '6', '2', '8', '1', '3', '8', '8', '8', '5', '3', '8', '2', '8', '2', '0', '2', '0', '9', '5', '3', '6', '1', '9', '8', '2', '3', '7', '7', '3', '3', '7', '9', '0', '5', '7', '6', '2', '5', '5', '4', '1', '2', '7', '3', '2', '4', '5', '0', '0', '0', '8', '5', '3', '1', '7', '6', '2', '1', '1', '2', '8', '3', '0', '8', '5', '5', '7', '5', '0', '6', '5', '1', '2', '8', '3', '2', '1', '2', '1', '9', '8', '0', '8', '0', '0', '3', '4', '6', '8', '7', '7', '8', '1', '3', '0', '9', '7', '2', '3', '0', '3', '4', '7', '4', '1', '6', '9', '8', '3', '9', '0', '8', '8', '2', '1', '5', '9', '0', '0', '6', '7', '5', '4', '9', '9', '9', '1', '5', '8', '4', '4', '8', '7', '8', '1', '5', '7', '1', '2', '1', '1', '9', '6', '5', '8', '1', '6', '0', '7', '7', '4', '2', '7', '3', '2', '5', '5', '2', '5', '5', '0', '3', '8', '8', '5', '8', '8', '8', '3', '9', '7', '0', '5', '9', '9', '6', '7', '8', '1', '5', '5', '3', '7', '0', '7', '5', '1', '1', '8', '0', '3', '"', ',']

theorem object_fragment0210881_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0210881Field007Chars00 ++ tail)) fragment0210881Acc00700 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0210881Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_007"
  err.flush

noncomputable def fragment0210881Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0210881Field008Value00 : SourceJson := .str (String.ofList ['3', '9', '1', '2', '9', '4', '2', '4', '1', '3', '7', '8', '7', '9', '1', '3', '0'])
noncomputable def fragment0210881Acc00900 : List (String × SourceJson) := (fragment0210881Field008Key00, fragment0210881Field008Value00) :: fragment0210881Acc00800
noncomputable def fragment0210881Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '1', '2', '9', '4', '2', '4', '1', '3', '7', '8', '7', '9', '1', '3', '0', '"', ',']

theorem object_fragment0210881_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0210881Field008Chars00 ++ tail)) fragment0210881Acc00800 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0210881Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_008"
  err.flush

noncomputable def fragment0210881Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0210881Field009Value00 : SourceJson := .str (String.ofList ['1', '5', '2', '7', '6', '7', '8', '9', '5', '9', '5', '0', '0', '9', '9', '6', '0', '5'])
noncomputable def fragment0210881Acc01000 : List (String × SourceJson) := (fragment0210881Field009Key00, fragment0210881Field009Value00) :: fragment0210881Acc00900
noncomputable def fragment0210881Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '2', '7', '6', '7', '8', '9', '5', '9', '5', '0', '0', '9', '9', '6', '0', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0210881_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0210881Field009Chars00 ++ tail)) fragment0210881Acc00900 =
      .ok (.obj (fragment0210881Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0210881_object_field_009"
  err.flush

noncomputable def fragment0210881Chars : List Char := '{' :: (fragment0210881Field000Chars00 ++ fragment0210881Field001Chars00 ++ fragment0210881Field002Chars00 ++ fragment0210881Field003Chars00 ++ fragment0210881Field004Chars00 ++ fragment0210881Field005Chars00 ++ fragment0210881Field006Chars00 ++ fragment0210881Field007Chars00 ++ fragment0210881Field008Chars00 ++ fragment0210881Field009Chars00)
noncomputable def fragment0210881Value : SourceJson := .obj (fragment0210881Acc01000.reverse)

theorem value_fragment0210881 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 439) (fragment0210881Chars ++ tail) =
      .ok (fragment0210881Value, tail) := by
  have hinput : fragment0210881Chars ++ tail = '{' :: (fragment0210881Field000Chars00 ++ (fragment0210881Field001Chars00 ++ (fragment0210881Field002Chars00 ++ (fragment0210881Field003Chars00 ++ (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0210881Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 439) (fragment0210881Chars ++ tail) =
        SourceJson.value (fuel + 439) ('{' :: (fragment0210881Field000Chars00 ++ (fragment0210881Field001Chars00 ++ (fragment0210881Field002Chars00 ++ (fragment0210881Field003Chars00 ++ (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 439)) hinput
    _ = SourceJson.object (fuel + 438) (SourceJson.white (fragment0210881Field000Chars00 ++ (fragment0210881Field001Chars00 ++ (fragment0210881Field002Chars00 ++ (fragment0210881Field003Chars00 ++ (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))))))))))) fragment0210881Acc00000 := by rfl
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0210881Field001Chars00 ++ (fragment0210881Field002Chars00 ++ (fragment0210881Field003Chars00 ++ (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail))))))))))) fragment0210881Acc00100 := object_fragment0210881_field_000 fuel (fragment0210881Field001Chars00 ++ (fragment0210881Field002Chars00 ++ (fragment0210881Field003Chars00 ++ (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0210881Field002Chars00 ++ (fragment0210881Field003Chars00 ++ (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))))))))) fragment0210881Acc00200 := object_fragment0210881_field_001 fuel (fragment0210881Field002Chars00 ++ (fragment0210881Field003Chars00 ++ (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0210881Field003Chars00 ++ (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail))))))))) fragment0210881Acc00300 := object_fragment0210881_field_002 fuel (fragment0210881Field003Chars00 ++ (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))))))) fragment0210881Acc00400 := object_fragment0210881_field_003 fuel (fragment0210881Field004Chars00 ++ (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail))))))) fragment0210881Acc00500 := object_fragment0210881_field_004 fuel (fragment0210881Field005Chars00 ++ (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))))) fragment0210881Acc00600 := object_fragment0210881_field_005 fuel (fragment0210881Field006Chars00 ++ (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail))))) fragment0210881Acc00700 := object_fragment0210881_field_006 fuel (fragment0210881Field007Chars00 ++ (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))) fragment0210881Acc00800 := object_fragment0210881_field_007 fuel (fragment0210881Field008Chars00 ++ (fragment0210881Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0210881Field009Chars00 ++ (tail))) fragment0210881Acc00900 := object_fragment0210881_field_008 fuel (fragment0210881Field009Chars00 ++ (tail))
    _ = .ok (fragment0210881Value, tail) := object_fragment0210881_field_009 fuel (tail)

noncomputable def fragment0212901Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0212901Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0212901Field000Value00 : SourceJson := .number (String.ofList ['4', '6'])
noncomputable def fragment0212901Acc00100 : List (String × SourceJson) := (fragment0212901Field000Key00, fragment0212901Field000Value00) :: fragment0212901Acc00000
noncomputable def fragment0212901Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '6', ',']

theorem object_fragment0212901_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0212901Field000Chars00 ++ tail)) fragment0212901Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0212901Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_000"
  err.flush

noncomputable def fragment0212901Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0212901Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0212901Acc00200 : List (String × SourceJson) := (fragment0212901Field001Key00, fragment0212901Field001Value00) :: fragment0212901Acc00100
noncomputable def fragment0212901Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0212901_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0212901Field001Chars00 ++ tail)) fragment0212901Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0212901Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_001"
  err.flush

noncomputable def fragment0212901Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0212901Field002Value00 : SourceJson := .str (String.ofList ['4', '7', '7', '3', '2', '7', '1', '7', '4', '2', '4', '0', '4', '3', '4', '1', '6', '2', '1', '6', '0', '5', '5', '0', '2', '9', '9', '0', '5', '8', '9', '2', '6', '2', '2', '2', '3', '7', '1', '2', '7', '0', '3', '/', '4', '4', '1', '9', '1', '8', '5', '8', '5', '0', '7', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0212901Acc00300 : List (String × SourceJson) := (fragment0212901Field002Key00, fragment0212901Field002Value00) :: fragment0212901Acc00200
noncomputable def fragment0212901Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '7', '7', '3', '2', '7', '1', '7', '4', '2', '4', '0', '4', '3', '4', '1', '6', '2', '1', '6', '0', '5', '5', '0', '2', '9', '9', '0', '5', '8', '9', '2', '6', '2', '2', '2', '3', '7', '1', '2', '7', '0', '3', '/', '4', '4', '1', '9', '1', '8', '5', '8', '5', '0', '7', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0212901_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0212901Field002Chars00 ++ tail)) fragment0212901Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0212901Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_002"
  err.flush

noncomputable def fragment0212901Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0212901Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0212901Acc00400 : List (String × SourceJson) := (fragment0212901Field003Key00, fragment0212901Field003Value00) :: fragment0212901Acc00300
noncomputable def fragment0212901Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0212901_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0212901Field003Chars00 ++ tail)) fragment0212901Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0212901Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_003"
  err.flush

noncomputable def fragment0212901Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0212901Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0212901Acc00500 : List (String × SourceJson) := (fragment0212901Field004Key00, fragment0212901Field004Value00) :: fragment0212901Acc00400
noncomputable def fragment0212901Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0212901_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0212901Field004Chars00 ++ tail)) fragment0212901Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0212901Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_004"
  err.flush

noncomputable def fragment0212901Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0212901Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '8', '0', '8', '2', '2', '8', '6', '1', '0', '3', '6', '5', '1', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '4', '6', '4', '8', '6', '2', '8', '8', '1', '4', '3', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '9', '9', '3', '3', '8', '2', '9', '9', '8', '9', '/', '2', '0', '5', '0', '3', '9', '2', '9', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '7', '6', '9', '4', '5', '8', '1', '2', '4', '9', '6', '0', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '6', '3', '0', '1', '8', '1', '4', '6', '8', '6', '7', '2', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '2', '4', '6', '4', '4', '9', '9', '9', '3', '0', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '8', '8', '2', '7', '8', '2', '5', '8', '2', '2', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '7', '2', '6', '1', '6', '3', '1', '9', '9', '1', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '8', '5', '5', '1', '4', '9', '5', '3', '9', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '5', '3', '6', '3', '3', '7', '8', '4', '7', '6', '6', '3', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0212901Acc00600 : List (String × SourceJson) := (fragment0212901Field005Key00, fragment0212901Field005Value00) :: fragment0212901Acc00500
noncomputable def fragment0212901Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '0', '8', '2', '2', '8', '6', '1', '0', '3', '6', '5', '1', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '4', '6', '4', '8', '6', '2', '8', '8', '1', '4', '3', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '9', '9', '9', '3', '3', '8', '2', '9', '9', '8', '9', '/', '2', '0', '5', '0', '3', '9', '2', '9', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '7', '6', '9', '4', '5', '8', '1', '2', '4', '9', '6', '0', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '6', '3', '0', '1', '8', '1', '4', '6', '8', '6', '7', '2', '3', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '5', '2', '4', '6', '4', '4', '9', '9', '9', '3', '0', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '8', '8', '2', '7', '8', '2', '5', '8', '2', '2', '7', '/', '5', '8', '2', '4', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '7', '2', '6', '1', '6', '3', '1', '9', '9', '1', '/', '2', '9', '1', '2', '4', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '8', '5', '5', '1', '4', '9', '5', '3', '9', '9', '/', '1', '1', '6', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '3', '6', '3', '3', '7', '8', '4', '7', '6', '6', '3', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0212901_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0212901Field005Chars00 ++ tail)) fragment0212901Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0212901Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_005"
  err.flush

noncomputable def fragment0212901Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0212901Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '6', '1', '4', '3', '9', '2', '4', '0', '1', '1', '2', '2', '1', '1', '4', '0', '8', '8', '9', '3', '1', '3', '8', '6', '5', '6', '6', '2', '4', '4', '9', '5', '7', '1', '7', '0', '4', '5', '5', '4', '6', '1', '8', '9', '3', '2', '7', '2', '3', '2', '0', '0', '0', '/', '1', '4', '2', '2', '8', '0', '9', '1', '9', '3', '3', '6', '2', '3', '4', '6', '4', '9', '7', '3', '0', '6', '1', '2', '3', '9', '4', '7', '2', '5', '4', '9', '9', '6', '9', '5', '8', '4', '6', '8', '2', '1', '8', '4', '7', '8', '6', '3', '6', '9', '0', '2', '3', '1', '1', '1', '5', '7', '2', '7', '3', '5', '7', '1', '3', '4', '3'])
noncomputable def fragment0212901Acc00700 : List (String × SourceJson) := (fragment0212901Field006Key00, fragment0212901Field006Value00) :: fragment0212901Acc00600
noncomputable def fragment0212901Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '6', '1', '4', '3', '9', '2', '4', '0', '1', '1', '2', '2', '1', '1', '4', '0', '8', '8', '9', '3', '1', '3', '8', '6', '5', '6', '6', '2', '4', '4', '9', '5', '7', '1', '7', '0', '4', '5', '5', '4', '6', '1', '8', '9', '3', '2', '7', '2', '3', '2', '0', '0', '0', '/', '1', '4', '2', '2', '8', '0', '9', '1', '9', '3', '3', '6', '2', '3', '4', '6', '4', '9', '7', '3', '0', '6', '1', '2', '3', '9', '4', '7', '2', '5', '4', '9', '9', '6', '9', '5', '8', '4', '6', '8', '2', '1', '8', '4', '7', '8', '6', '3', '6', '9', '0', '2', '3', '1', '1', '1', '5', '7', '2', '7', '3', '5', '7', '1', '3', '4', '3', '"', ',']

theorem object_fragment0212901_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0212901Field006Chars00 ++ tail)) fragment0212901Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0212901Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_006"
  err.flush

noncomputable def fragment0212901Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0212901Field007Value00 : SourceJson := .str (String.ofList ['2', '2', '0', '0', '0', '3', '8', '9', '9', '5', '4', '8', '7', '5', '4', '6', '0', '4', '0', '0', '0', '4', '1', '3', '9', '2', '8', '2', '5', '2', '5', '4', '2', '0', '6', '7', '0', '2', '5', '3', '5', '7', '1', '2', '4', '4', '0', '8', '5', '0', '8', '3', '8', '1', '1', '3', '7', '5', '5', '0', '2', '6', '1', '4', '3', '5', '8', '7', '4', '5', '6', '6', '3', '7', '6', '7', '1', '0', '6', '8', '4', '5', '5', '1', '6', '7', '6', '6', '6', '5', '0', '7', '8', '0', '7', '3', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '3', '5', '2', '7', '7', '6', '4', '3', '3', '6', '5', '5', '2', '6', '1', '1', '9', '2', '1', '6', '2', '2', '3', '1', '7', '9', '4', '7', '1', '5', '6', '0', '0', '1', '4', '6', '1', '5', '3', '9', '9', '5', '0', '7', '4', '5', '9', '4', '2', '4', '1', '5', '9', '9', '4', '3', '5', '4', '8', '3', '4', '6', '7', '5', '5', '0', '9', '1', '4', '4', '6', '5', '4', '4', '8', '8', '2', '7', '8', '0', '9', '5', '4', '1', '1', '3', '7', '0', '2', '4', '8', '1', '9', '8', '8', '3', '8', '3', '1', '9', '2', '8', '6', '5', '3', '5', '3', '8', '7', '0', '9', '1', '2', '2', '0', '0', '0', '2', '8', '9', '8', '6', '7', '3', '0', '9', '5', '1', '3'])
noncomputable def fragment0212901Acc00800 : List (String × SourceJson) := (fragment0212901Field007Key00, fragment0212901Field007Value00) :: fragment0212901Acc00700
noncomputable def fragment0212901Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '2', '0', '0', '0', '3', '8', '9', '9', '5', '4', '8', '7', '5', '4', '6', '0', '4', '0', '0', '0', '4', '1', '3', '9', '2', '8', '2', '5', '2', '5', '4', '2', '0', '6', '7', '0', '2', '5', '3', '5', '7', '1', '2', '4', '4', '0', '8', '5', '0', '8', '3', '8', '1', '1', '3', '7', '5', '5', '0', '2', '6', '1', '4', '3', '5', '8', '7', '4', '5', '6', '6', '3', '7', '6', '7', '1', '0', '6', '8', '4', '5', '5', '1', '6', '7', '6', '6', '6', '5', '0', '7', '8', '0', '7', '3', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '3', '5', '2', '7', '7', '6', '4', '3', '3', '6', '5', '5', '2', '6', '1', '1', '9', '2', '1', '6', '2', '2', '3', '1', '7', '9', '4', '7', '1', '5', '6', '0', '0', '1', '4', '6', '1', '5', '3', '9', '9', '5', '0', '7', '4', '5', '9', '4', '2', '4', '1', '5', '9', '9', '4', '3', '5', '4', '8', '3', '4', '6', '7', '5', '5', '0', '9', '1', '4', '4', '6', '5', '4', '4', '8', '8', '2', '7', '8', '0', '9', '5', '4', '1', '1', '3', '7', '0', '2', '4', '8', '1', '9', '8', '8', '3', '8', '3', '1', '9', '2', '8', '6', '5', '3', '5', '3', '8', '7', '0', '9', '1', '2', '2', '0', '0', '0', '2', '8', '9', '8', '6', '7', '3', '0', '9', '5', '1', '3', '"', ',']

theorem object_fragment0212901_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0212901Field007Chars00 ++ tail)) fragment0212901Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0212901Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_007"
  err.flush

noncomputable def fragment0212901Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0212901Field008Value00 : SourceJson := .str (String.ofList ['7', '0', '2', '4', '2', '3', '8', '6', '3', '8', '8', '6', '4', '9', '3', '1', '5'])
noncomputable def fragment0212901Acc00900 : List (String × SourceJson) := (fragment0212901Field008Key00, fragment0212901Field008Value00) :: fragment0212901Acc00800
noncomputable def fragment0212901Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '0', '2', '4', '2', '3', '8', '6', '3', '8', '8', '6', '4', '9', '3', '1', '5', '"', ',']

theorem object_fragment0212901_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0212901Field008Chars00 ++ tail)) fragment0212901Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0212901Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_008"
  err.flush

noncomputable def fragment0212901Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0212901Field009Value00 : SourceJson := .str (String.ofList ['3', '2', '5', '6', '3', '4', '8', '3', '4', '9', '9', '1', '9', '3', '7', '3', '0', '7'])
noncomputable def fragment0212901Acc01000 : List (String × SourceJson) := (fragment0212901Field009Key00, fragment0212901Field009Value00) :: fragment0212901Acc00900
noncomputable def fragment0212901Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '5', '6', '3', '4', '8', '3', '4', '9', '9', '1', '9', '3', '7', '3', '0', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0212901_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0212901Field009Chars00 ++ tail)) fragment0212901Acc00900 =
      .ok (.obj (fragment0212901Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212901_object_field_009"
  err.flush

noncomputable def fragment0212901Chars : List Char := '{' :: (fragment0212901Field000Chars00 ++ fragment0212901Field001Chars00 ++ fragment0212901Field002Chars00 ++ fragment0212901Field003Chars00 ++ fragment0212901Field004Chars00 ++ fragment0212901Field005Chars00 ++ fragment0212901Field006Chars00 ++ fragment0212901Field007Chars00 ++ fragment0212901Field008Chars00 ++ fragment0212901Field009Chars00)
noncomputable def fragment0212901Value : SourceJson := .obj (fragment0212901Acc01000.reverse)

theorem value_fragment0212901 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0212901Chars ++ tail) =
      .ok (fragment0212901Value, tail) := by
  have hinput : fragment0212901Chars ++ tail = '{' :: (fragment0212901Field000Chars00 ++ (fragment0212901Field001Chars00 ++ (fragment0212901Field002Chars00 ++ (fragment0212901Field003Chars00 ++ (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0212901Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0212901Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0212901Field000Chars00 ++ (fragment0212901Field001Chars00 ++ (fragment0212901Field002Chars00 ++ (fragment0212901Field003Chars00 ++ (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0212901Field000Chars00 ++ (fragment0212901Field001Chars00 ++ (fragment0212901Field002Chars00 ++ (fragment0212901Field003Chars00 ++ (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))))))))))) fragment0212901Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0212901Field001Chars00 ++ (fragment0212901Field002Chars00 ++ (fragment0212901Field003Chars00 ++ (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail))))))))))) fragment0212901Acc00100 := object_fragment0212901_field_000 fuel (fragment0212901Field001Chars00 ++ (fragment0212901Field002Chars00 ++ (fragment0212901Field003Chars00 ++ (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0212901Field002Chars00 ++ (fragment0212901Field003Chars00 ++ (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))))))))) fragment0212901Acc00200 := object_fragment0212901_field_001 fuel (fragment0212901Field002Chars00 ++ (fragment0212901Field003Chars00 ++ (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0212901Field003Chars00 ++ (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail))))))))) fragment0212901Acc00300 := object_fragment0212901_field_002 fuel (fragment0212901Field003Chars00 ++ (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))))))) fragment0212901Acc00400 := object_fragment0212901_field_003 fuel (fragment0212901Field004Chars00 ++ (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail))))))) fragment0212901Acc00500 := object_fragment0212901_field_004 fuel (fragment0212901Field005Chars00 ++ (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))))) fragment0212901Acc00600 := object_fragment0212901_field_005 fuel (fragment0212901Field006Chars00 ++ (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail))))) fragment0212901Acc00700 := object_fragment0212901_field_006 fuel (fragment0212901Field007Chars00 ++ (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))) fragment0212901Acc00800 := object_fragment0212901_field_007 fuel (fragment0212901Field008Chars00 ++ (fragment0212901Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0212901Field009Chars00 ++ (tail))) fragment0212901Acc00900 := object_fragment0212901_field_008 fuel (fragment0212901Field009Chars00 ++ (tail))
    _ = .ok (fragment0212901Value, tail) := object_fragment0212901_field_009 fuel (tail)

noncomputable def fragment0214573Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0214573Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0214573Field000Value00 : SourceJson := .number (String.ofList ['4', '7'])
noncomputable def fragment0214573Acc00100 : List (String × SourceJson) := (fragment0214573Field000Key00, fragment0214573Field000Value00) :: fragment0214573Acc00000
noncomputable def fragment0214573Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '7', ',']

theorem object_fragment0214573_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0214573Field000Chars00 ++ tail)) fragment0214573Acc00000 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0214573Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_000"
  err.flush

noncomputable def fragment0214573Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0214573Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['3'])]
noncomputable def fragment0214573Acc00200 : List (String × SourceJson) := (fragment0214573Field001Key00, fragment0214573Field001Value00) :: fragment0214573Acc00100
noncomputable def fragment0214573Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0214573_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0214573Field001Chars00 ++ tail)) fragment0214573Acc00100 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0214573Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_001"
  err.flush

noncomputable def fragment0214573Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0214573Field002Value00 : SourceJson := .str (String.ofList ['1', '6', '5', '3', '3', '5', '8', '7', '4', '0', '4', '0', '1', '0', '4', '1', '6', '3', '8', '3', '1', '0', '4', '5', '1', '9', '7', '8', '5', '7', '7', '4', '2', '8', '9', '0', '6', '3', '6', '5', '2', '7', '/', '9', '3', '8', '3', '9', '5', '0', '2', '0', '1', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0214573Acc00300 : List (String × SourceJson) := (fragment0214573Field002Key00, fragment0214573Field002Value00) :: fragment0214573Acc00200
noncomputable def fragment0214573Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '6', '5', '3', '3', '5', '8', '7', '4', '0', '4', '0', '1', '0', '4', '1', '6', '3', '8', '3', '1', '0', '4', '5', '1', '9', '7', '8', '5', '7', '7', '4', '2', '8', '9', '0', '6', '3', '6', '5', '2', '7', '/', '9', '3', '8', '3', '9', '5', '0', '2', '0', '1', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0214573_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0214573Field002Chars00 ++ tail)) fragment0214573Acc00200 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0214573Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_002"
  err.flush

noncomputable def fragment0214573Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0214573Field003Value00 : SourceJson := .str (String.ofList ['4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0214573Acc00400 : List (String × SourceJson) := (fragment0214573Field003Key00, fragment0214573Field003Value00) :: fragment0214573Acc00300
noncomputable def fragment0214573Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0214573_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0214573Field003Chars00 ++ tail)) fragment0214573Acc00300 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0214573Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_003"
  err.flush

noncomputable def fragment0214573Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0214573Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0214573Acc00500 : List (String × SourceJson) := (fragment0214573Field004Key00, fragment0214573Field004Value00) :: fragment0214573Acc00400
noncomputable def fragment0214573Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0214573_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0214573Field004Chars00 ++ tail)) fragment0214573Acc00400 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0214573Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_004"
  err.flush

noncomputable def fragment0214573Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0214573Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '4', '5', '0', '1', '8', '8', '4', '7', '1', '8', '6', '3', '4', '1', '8', '9', '9', '9', '1', '0', '9', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '0', '4', '2', '3', '5', '1', '6', '6', '2', '1', '8', '3', '5', '0', '7', '7', '0', '1', '2', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '7', '5', '1', '8', '3', '4', '3', '1', '5', '7', '4', '4', '5', '5', '3', '0', '6', '6', '6', '3', '/', '7', '2', '4', '2', '9', '3', '5', '1', '5', '1', '3', '3', '8', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '7', '9', '5', '1', '1', '8', '1', '3', '7', '8', '1', '4', '1', '6', '6', '1', '2', '1', '7', '1', '/', '1', '2', '0', '7', '1', '5', '5', '8', '5', '8', '5', '5', '6', '4', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '7', '1', '3', '0', '4', '4', '0', '4', '9', '7', '5', '4', '0', '5', '8', '2', '1', '5', '2', '9', '/', '4', '0', '2', '3', '8', '5', '2', '8', '6', '1', '8', '5', '4', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '7', '9', '1', '1', '8', '0', '9', '6', '8', '8', '8', '1', '3', '5', '0', '8', '1', '6', '3', '4', '9', '/', '3', '6', '2', '1', '4', '6', '7', '5', '7', '5', '6', '6', '9', '2', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '6', '3', '2', '9', '7', '7', '2', '7', '7', '4', '5', '8', '8', '1', '3', '5', '1', '7', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '6', '8', '5', '1', '1', '6', '0', '7', '1', '1', '1', '8', '3', '9', '0', '7', '0', '2', '2', '7', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '9', '9', '7', '8', '1', '0', '5', '4', '9', '6', '5', '0', '1', '6', '0', '1', '5', '6', '0', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '2', '7', '1', '4', '6', '3', '9', '3', '7', '3', '1', '4', '4', '3', '8', '1', '0', '9', '1', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0214573Acc00600 : List (String × SourceJson) := (fragment0214573Field005Key00, fragment0214573Field005Value00) :: fragment0214573Acc00500
noncomputable def fragment0214573Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '4', '5', '0', '1', '8', '8', '4', '7', '1', '8', '6', '3', '4', '1', '8', '9', '9', '9', '1', '0', '9', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '0', '4', '2', '3', '5', '1', '6', '6', '2', '1', '8', '3', '5', '0', '7', '7', '0', '1', '2', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '7', '5', '1', '8', '3', '4', '3', '1', '5', '7', '4', '4', '5', '5', '3', '0', '6', '6', '6', '3', '/', '7', '2', '4', '2', '9', '3', '5', '1', '5', '1', '3', '3', '8', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '7', '9', '5', '1', '1', '8', '1', '3', '7', '8', '1', '4', '1', '6', '6', '1', '2', '1', '7', '1', '/', '1', '2', '0', '7', '1', '5', '5', '8', '5', '8', '5', '5', '6', '4', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '7', '1', '3', '0', '4', '4', '0', '4', '9', '7', '5', '4', '0', '5', '8', '2', '1', '5', '2', '9', '/', '4', '0', '2', '3', '8', '5', '2', '8', '6', '1', '8', '5', '4', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '7', '9', '1', '1', '8', '0', '9', '6', '8', '8', '8', '1', '3', '5', '0', '8', '1', '6', '3', '4', '9', '/', '3', '6', '2', '1', '4', '6', '7', '5', '7', '5', '6', '6', '9', '2', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '6', '3', '2', '9', '7', '7', '2', '7', '7', '4', '5', '8', '8', '1', '3', '5', '1', '7', '/', '2', '2', '6', '3', '4', '1', '7', '2', '3', '4', '7', '9', '3', '2', '5', '3', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '6', '8', '5', '1', '1', '6', '0', '7', '1', '1', '1', '8', '3', '9', '0', '7', '0', '2', '2', '7', '/', '9', '0', '5', '3', '6', '6', '8', '9', '3', '9', '1', '7', '3', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '9', '9', '7', '8', '1', '0', '5', '4', '9', '6', '5', '0', '1', '6', '0', '1', '5', '6', '0', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '2', '7', '1', '4', '6', '3', '9', '3', '7', '3', '1', '4', '4', '3', '8', '1', '0', '9', '1', '7', '/', '1', '8', '1', '0', '7', '3', '3', '7', '8', '7', '8', '3', '4', '6', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0214573_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0214573Field005Chars00 ++ tail)) fragment0214573Acc00500 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0214573Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_005"
  err.flush

noncomputable def fragment0214573Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0214573Field006Value00 : SourceJson := .str (String.ofList ['2', '7', '4', '5', '0', '7', '2', '1', '1', '5', '3', '7', '7', '7', '5', '1', '2', '1', '9', '4', '1', '1', '3', '9', '4', '5', '5', '5', '6', '0', '6', '2', '9', '5', '3', '5', '0', '7', '4', '9', '3', '5', '6', '5', '0', '6', '9', '5', '0', '4', '0', '0', '0', '0', '0', '/', '7', '4', '8', '5', '8', '6', '8', '4', '5', '3', '2', '7', '2', '7', '5', '3', '8', '0', '7', '2', '2', '6', '2', '3', '4', '8', '2', '2', '2', '2', '7', '9', '7', '8', '3', '8', '0', '8', '2', '2', '2', '2', '4', '7', '8', '8', '2', '1', '9', '4', '2', '0', '3', '4', '2', '3', '1', '7', '9', '7', '4', '1', '7', '4', '6', '8', '3'])
noncomputable def fragment0214573Acc00700 : List (String × SourceJson) := (fragment0214573Field006Key00, fragment0214573Field006Value00) :: fragment0214573Acc00600
noncomputable def fragment0214573Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '7', '4', '5', '0', '7', '2', '1', '1', '5', '3', '7', '7', '7', '5', '1', '2', '1', '9', '4', '1', '1', '3', '9', '4', '5', '5', '5', '6', '0', '6', '2', '9', '5', '3', '5', '0', '7', '4', '9', '3', '5', '6', '5', '0', '6', '9', '5', '0', '4', '0', '0', '0', '0', '0', '/', '7', '4', '8', '5', '8', '6', '8', '4', '5', '3', '2', '7', '2', '7', '5', '3', '8', '0', '7', '2', '2', '6', '2', '3', '4', '8', '2', '2', '2', '2', '7', '9', '7', '8', '3', '8', '0', '8', '2', '2', '2', '2', '4', '7', '8', '8', '2', '1', '9', '4', '2', '0', '3', '4', '2', '3', '1', '7', '9', '7', '4', '1', '7', '4', '6', '8', '3', '"', ',']

theorem object_fragment0214573_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0214573Field006Chars00 ++ tail)) fragment0214573Acc00600 =
      SourceJson.object (fuel + 428) (SourceJson.white tail) fragment0214573Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_006"
  err.flush

noncomputable def fragment0214573Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0214573Field007Value00 : SourceJson := .str (String.ofList ['2', '8', '6', '2', '9', '9', '3', '2', '9', '7', '8', '4', '0', '0', '4', '4', '8', '3', '4', '7', '6', '6', '9', '7', '2', '9', '1', '6', '9', '7', '7', '3', '8', '2', '5', '3', '6', '1', '3', '1', '6', '3', '2', '4', '8', '8', '7', '8', '5', '9', '3', '2', '3', '7', '2', '2', '1', '5', '4', '5', '9', '5', '2', '8', '2', '3', '0', '6', '9', '3', '6', '9', '0', '9', '4', '0', '0', '7', '5', '8', '6', '1', '5', '7', '7', '9', '6', '4', '4', '3', '1', '7', '3', '9', '1', '7', '4', '2', '8', '2', '0', '9', '4', '1', '8', '6', '4', '9', '3', '7', '2', '8', '3', '5', '0', '2', '5', '1', '5', '2', '7', '5', '8', '5', '5', '5', '0', '2', '6', '7', '6', '1', '0', '8', '5', '6', '2', '2', '2', '2', '3', '7', '4', '3', '1', '6', '5', '3', '5', '6', '8', '9', '8', '0', '4', '1', '9', '7', '5', '8', '6', '5', '0', '1', '5', '6', '9', '8', '1', '2', '0', '5', '1', '3', '0', '3', '9', '5', '0', '0', '3', '0', '5', '5', '6', '3', '2', '4', '9', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '2', '6', '8', '6', '1', '9', '3', '6', '6', '6', '8', '1', '2', '2', '8', '7', '2', '2', '8', '3', '4', '2', '6', '0', '8', '3', '2', '6', '3', '9', '2', '3', '2', '7', '5', '9', '1', '2', '6', '8', '9', '7', '9', '2', '3', '3', '3', '4', '8', '0', '7', '6', '9', '5', '3', '0', '0', '5', '1', '0', '6', '1', '4', '8', '3', '4', '0', '4', '4', '8', '1', '1', '0', '4', '7', '1', '9', '1', '0', '3', '5', '3', '7', '0', '0', '4', '4', '7', '5', '7', '4', '7', '6', '2', '1', '7', '9', '1', '6', '3', '7', '0', '8', '9', '0', '1', '2', '4', '5', '0', '0', '9', '2', '8', '4', '4', '5', '7', '7', '0', '7', '4', '4', '2', '4', '2', '9', '4', '6', '7', '3', '5', '5', '5', '2', '3', '0', '6', '4', '3', '1', '8', '9', '4', '2', '5', '0', '9', '3', '7', '3', '2', '2', '2', '6', '5', '8', '5', '4', '0', '1', '8', '0', '9', '7', '1', '0', '4', '1', '3', '4', '7', '2', '6', '8', '0', '8', '7', '0', '7', '3', '0', '9', '3', '8', '2', '8', '4', '2', '5', '3', '0', '3', '6', '4', '8', '9', '5', '0', '6', '2', '3', '4', '9', '5', '6', '8', '2', '1', '0', '9', '1', '5', '7', '9', '9'])
noncomputable def fragment0214573Acc00800 : List (String × SourceJson) := (fragment0214573Field007Key00, fragment0214573Field007Value00) :: fragment0214573Acc00700
noncomputable def fragment0214573Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '8', '6', '2', '9', '9', '3', '2', '9', '7', '8', '4', '0', '0', '4', '4', '8', '3', '4', '7', '6', '6', '9', '7', '2', '9', '1', '6', '9', '7', '7', '3', '8', '2', '5', '3', '6', '1', '3', '1', '6', '3', '2', '4', '8', '8', '7', '8', '5', '9', '3', '2', '3', '7', '2', '2', '1', '5', '4', '5', '9', '5', '2', '8', '2', '3', '0', '6', '9', '3', '6', '9', '0', '9', '4', '0', '0', '7', '5', '8', '6', '1', '5', '7', '7', '9', '6', '4', '4', '3', '1', '7', '3', '9', '1', '7', '4', '2', '8', '2', '0', '9', '4', '1', '8', '6', '4', '9', '3', '7', '2', '8', '3', '5', '0', '2', '5', '1', '5', '2', '7', '5', '8', '5', '5', '5', '0', '2', '6', '7', '6', '1', '0', '8', '5', '6', '2', '2', '2', '2', '3', '7', '4', '3', '1', '6', '5', '3', '5', '6', '8', '9', '8', '0', '4', '1', '9', '7', '5', '8', '6', '5', '0', '1', '5', '6', '9', '8', '1', '2', '0', '5', '1', '3', '0', '3', '9', '5', '0', '0', '3', '0', '5', '5', '6', '3', '2', '4', '9', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '2', '6', '8', '6', '1', '9', '3', '6', '6', '6', '8', '1', '2', '2', '8', '7', '2', '2', '8', '3', '4', '2', '6', '0', '8', '3', '2', '6', '3', '9', '2', '3', '2', '7', '5', '9', '1', '2', '6', '8', '9', '7', '9', '2', '3', '3', '3', '4', '8', '0', '7', '6', '9', '5', '3', '0', '0', '5', '1', '0', '6', '1', '4', '8', '3', '4', '0', '4', '4', '8', '1', '1', '0', '4', '7', '1', '9', '1', '0', '3', '5', '3', '7', '0', '0', '4', '4', '7', '5', '7', '4', '7', '6', '2', '1', '7', '9', '1', '6', '3', '7', '0', '8', '9', '0', '1', '2', '4', '5', '0', '0', '9', '2', '8', '4', '4', '5', '7', '7', '0', '7', '4', '4', '2', '4', '2', '9', '4', '6', '7', '3', '5', '5', '5', '2', '3', '0', '6', '4', '3', '1', '8', '9', '4', '2', '5', '0', '9', '3', '7', '3', '2', '2', '2', '6', '5', '8', '5', '4', '0', '1', '8', '0', '9', '7', '1', '0', '4', '1', '3', '4', '7', '2', '6', '8', '0', '8', '7', '0', '7', '3', '0', '9', '3', '8', '2', '8', '4', '2', '5', '3', '0', '3', '6', '4', '8', '9', '5', '0', '6', '2', '3', '4', '9', '5', '6', '8', '2', '1', '0', '9', '1', '5', '7', '9', '9', '"', ',']

theorem object_fragment0214573_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 428) (SourceJson.white (fragment0214573Field007Chars00 ++ tail)) fragment0214573Acc00700 =
      SourceJson.object (fuel + 427) (SourceJson.white tail) fragment0214573Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_007"
  err.flush

noncomputable def fragment0214573Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0214573Field008Value00 : SourceJson := .str (String.ofList ['2', '9', '0', '5', '3', '0', '1', '1', '1', '5', '4', '0', '2', '8', '5', '6', '2'])
noncomputable def fragment0214573Acc00900 : List (String × SourceJson) := (fragment0214573Field008Key00, fragment0214573Field008Value00) :: fragment0214573Acc00800
noncomputable def fragment0214573Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '9', '0', '5', '3', '0', '1', '1', '1', '5', '4', '0', '2', '8', '5', '6', '2', '"', ',']

theorem object_fragment0214573_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 427) (SourceJson.white (fragment0214573Field008Chars00 ++ tail)) fragment0214573Acc00800 =
      SourceJson.object (fuel + 426) (SourceJson.white tail) fragment0214573Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_008"
  err.flush

noncomputable def fragment0214573Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0214573Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '6', '6', '4', '9', '9', '4', '0', '1', '6', '2', '0', '1', '4', '0', '7', '5'])
noncomputable def fragment0214573Acc01000 : List (String × SourceJson) := (fragment0214573Field009Key00, fragment0214573Field009Value00) :: fragment0214573Acc00900
noncomputable def fragment0214573Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '6', '6', '4', '9', '9', '4', '0', '1', '6', '2', '0', '1', '4', '0', '7', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0214573_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 426) (SourceJson.white (fragment0214573Field009Chars00 ++ tail)) fragment0214573Acc00900 =
      .ok (.obj (fragment0214573Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0214573_object_field_009"
  err.flush

noncomputable def fragment0214573Chars : List Char := '{' :: (fragment0214573Field000Chars00 ++ fragment0214573Field001Chars00 ++ fragment0214573Field002Chars00 ++ fragment0214573Field003Chars00 ++ fragment0214573Field004Chars00 ++ fragment0214573Field005Chars00 ++ fragment0214573Field006Chars00 ++ fragment0214573Field007Chars00 ++ fragment0214573Field008Chars00 ++ fragment0214573Field009Chars00)
noncomputable def fragment0214573Value : SourceJson := .obj (fragment0214573Acc01000.reverse)

theorem value_fragment0214573 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 436) (fragment0214573Chars ++ tail) =
      .ok (fragment0214573Value, tail) := by
  have hinput : fragment0214573Chars ++ tail = '{' :: (fragment0214573Field000Chars00 ++ (fragment0214573Field001Chars00 ++ (fragment0214573Field002Chars00 ++ (fragment0214573Field003Chars00 ++ (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0214573Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 436) (fragment0214573Chars ++ tail) =
        SourceJson.value (fuel + 436) ('{' :: (fragment0214573Field000Chars00 ++ (fragment0214573Field001Chars00 ++ (fragment0214573Field002Chars00 ++ (fragment0214573Field003Chars00 ++ (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 436)) hinput
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0214573Field000Chars00 ++ (fragment0214573Field001Chars00 ++ (fragment0214573Field002Chars00 ++ (fragment0214573Field003Chars00 ++ (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))))))))))) fragment0214573Acc00000 := by rfl
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0214573Field001Chars00 ++ (fragment0214573Field002Chars00 ++ (fragment0214573Field003Chars00 ++ (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail))))))))))) fragment0214573Acc00100 := object_fragment0214573_field_000 fuel (fragment0214573Field001Chars00 ++ (fragment0214573Field002Chars00 ++ (fragment0214573Field003Chars00 ++ (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0214573Field002Chars00 ++ (fragment0214573Field003Chars00 ++ (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))))))))) fragment0214573Acc00200 := object_fragment0214573_field_001 fuel (fragment0214573Field002Chars00 ++ (fragment0214573Field003Chars00 ++ (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0214573Field003Chars00 ++ (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail))))))))) fragment0214573Acc00300 := object_fragment0214573_field_002 fuel (fragment0214573Field003Chars00 ++ (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))))))) fragment0214573Acc00400 := object_fragment0214573_field_003 fuel (fragment0214573Field004Chars00 ++ (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail))))))) fragment0214573Acc00500 := object_fragment0214573_field_004 fuel (fragment0214573Field005Chars00 ++ (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))))) fragment0214573Acc00600 := object_fragment0214573_field_005 fuel (fragment0214573Field006Chars00 ++ (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 428) (SourceJson.white (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail))))) fragment0214573Acc00700 := object_fragment0214573_field_006 fuel (fragment0214573Field007Chars00 ++ (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 427) (SourceJson.white (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))) fragment0214573Acc00800 := object_fragment0214573_field_007 fuel (fragment0214573Field008Chars00 ++ (fragment0214573Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 426) (SourceJson.white (fragment0214573Field009Chars00 ++ (tail))) fragment0214573Acc00900 := object_fragment0214573_field_008 fuel (fragment0214573Field009Chars00 ++ (tail))
    _ = .ok (fragment0214573Value, tail) := object_fragment0214573_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_before_reader"
  err.flush

noncomputable def chunk0040LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0040SuffixChars00 : List Char := [',']
noncomputable def chunk0040Chars00 : List Char := chunk0040LeadChars00 ++ fragment0201524Chars ++ chunk0040SuffixChars00
noncomputable def chunk0040Push00 (acc : List SourceJson) : List SourceJson := fragment0201524Value :: acc

noncomputable def chunk0040AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0040_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 617)
      (SourceJson.white (chunk0040LeadChars00 ++ (fragment0201524Chars ++ rest))) acc =
      (SourceJson.value (fuel + 616) (fragment0201524Chars ++ rest)).bind
        (chunk0040AfterValue00 (fuel + 616) acc) := by rfl

theorem array_chunk0040 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 617) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 616) (SourceJson.white tail) (chunk0040Push00 acc) := by
  have hinput : chunk0040Chars00 ++ tail = chunk0040LeadChars00 ++ (fragment0201524Chars ++ (chunk0040SuffixChars00 ++ tail)) := by
    simp only [chunk0040Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 617) (SourceJson.white (chunk0040Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 617)
          (SourceJson.white (chunk0040LeadChars00 ++ (fragment0201524Chars ++ (chunk0040SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 617) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 616) (fragment0201524Chars ++ (chunk0040SuffixChars00 ++ tail))).bind
        (chunk0040AfterValue00 (fuel + 616) acc) := array_chunk0040_head fuel (chunk0040SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0201524Value, chunk0040SuffixChars00 ++ tail)).bind
        (chunk0040AfterValue00 (fuel + 616) acc) :=
      congrArg (fun result => result.bind (chunk0040AfterValue00 (fuel + 616) acc))
        (value_fragment0201524 (fuel + 408) (chunk0040SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 616) (SourceJson.white tail) (chunk0040Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0040_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_before_reader"
  err.flush

noncomputable def chunk0041LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0041SuffixChars00 : List Char := [',']
noncomputable def chunk0041Chars00 : List Char := chunk0041LeadChars00 ++ fragment0203081Chars ++ chunk0041SuffixChars00
noncomputable def chunk0041Push00 (acc : List SourceJson) : List SourceJson := fragment0203081Value :: acc

noncomputable def chunk0041AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0041_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 616)
      (SourceJson.white (chunk0041LeadChars00 ++ (fragment0203081Chars ++ rest))) acc =
      (SourceJson.value (fuel + 615) (fragment0203081Chars ++ rest)).bind
        (chunk0041AfterValue00 (fuel + 615) acc) := by rfl

theorem array_chunk0041 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 616) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 615) (SourceJson.white tail) (chunk0041Push00 acc) := by
  have hinput : chunk0041Chars00 ++ tail = chunk0041LeadChars00 ++ (fragment0203081Chars ++ (chunk0041SuffixChars00 ++ tail)) := by
    simp only [chunk0041Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 616) (SourceJson.white (chunk0041Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 616)
          (SourceJson.white (chunk0041LeadChars00 ++ (fragment0203081Chars ++ (chunk0041SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 616) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 615) (fragment0203081Chars ++ (chunk0041SuffixChars00 ++ tail))).bind
        (chunk0041AfterValue00 (fuel + 615) acc) := array_chunk0041_head fuel (chunk0041SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0203081Value, chunk0041SuffixChars00 ++ tail)).bind
        (chunk0041AfterValue00 (fuel + 615) acc) :=
      congrArg (fun result => result.bind (chunk0041AfterValue00 (fuel + 615) acc))
        (value_fragment0203081 (fuel + 137) (chunk0041SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 615) (SourceJson.white tail) (chunk0041Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0041_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_before_reader"
  err.flush

noncomputable def chunk0042LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0042SuffixChars00 : List Char := [',']
noncomputable def chunk0042Chars00 : List Char := chunk0042LeadChars00 ++ fragment0205178Chars ++ chunk0042SuffixChars00
noncomputable def chunk0042Push00 (acc : List SourceJson) : List SourceJson := fragment0205178Value :: acc

noncomputable def chunk0042AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0042_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 615)
      (SourceJson.white (chunk0042LeadChars00 ++ (fragment0205178Chars ++ rest))) acc =
      (SourceJson.value (fuel + 614) (fragment0205178Chars ++ rest)).bind
        (chunk0042AfterValue00 (fuel + 614) acc) := by rfl

theorem array_chunk0042 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 615) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 614) (SourceJson.white tail) (chunk0042Push00 acc) := by
  have hinput : chunk0042Chars00 ++ tail = chunk0042LeadChars00 ++ (fragment0205178Chars ++ (chunk0042SuffixChars00 ++ tail)) := by
    simp only [chunk0042Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 615) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 615)
          (SourceJson.white (chunk0042LeadChars00 ++ (fragment0205178Chars ++ (chunk0042SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 615) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 614) (fragment0205178Chars ++ (chunk0042SuffixChars00 ++ tail))).bind
        (chunk0042AfterValue00 (fuel + 614) acc) := array_chunk0042_head fuel (chunk0042SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0205178Value, chunk0042SuffixChars00 ++ tail)).bind
        (chunk0042AfterValue00 (fuel + 614) acc) :=
      congrArg (fun result => result.bind (chunk0042AfterValue00 (fuel + 614) acc))
        (value_fragment0205178 (fuel + 133) (chunk0042SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 614) (SourceJson.white tail) (chunk0042Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_before_reader"
  err.flush

noncomputable def chunk0043LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0043SuffixChars00 : List Char := [',']
noncomputable def chunk0043Chars00 : List Char := chunk0043LeadChars00 ++ fragment0207270Chars ++ chunk0043SuffixChars00
noncomputable def chunk0043Push00 (acc : List SourceJson) : List SourceJson := fragment0207270Value :: acc

noncomputable def chunk0043AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0043_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 614)
      (SourceJson.white (chunk0043LeadChars00 ++ (fragment0207270Chars ++ rest))) acc =
      (SourceJson.value (fuel + 613) (fragment0207270Chars ++ rest)).bind
        (chunk0043AfterValue00 (fuel + 613) acc) := by rfl

theorem array_chunk0043 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 614) (SourceJson.white (chunk0043Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 613) (SourceJson.white tail) (chunk0043Push00 acc) := by
  have hinput : chunk0043Chars00 ++ tail = chunk0043LeadChars00 ++ (fragment0207270Chars ++ (chunk0043SuffixChars00 ++ tail)) := by
    simp only [chunk0043Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 614) (SourceJson.white (chunk0043Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 614)
          (SourceJson.white (chunk0043LeadChars00 ++ (fragment0207270Chars ++ (chunk0043SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 614) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 613) (fragment0207270Chars ++ (chunk0043SuffixChars00 ++ tail))).bind
        (chunk0043AfterValue00 (fuel + 613) acc) := array_chunk0043_head fuel (chunk0043SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0207270Value, chunk0043SuffixChars00 ++ tail)).bind
        (chunk0043AfterValue00 (fuel + 613) acc) :=
      congrArg (fun result => result.bind (chunk0043AfterValue00 (fuel + 613) acc))
        (value_fragment0207270 (fuel + 183) (chunk0043SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 613) (SourceJson.white tail) (chunk0043Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0043_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_before_reader"
  err.flush

noncomputable def chunk0044LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0044SuffixChars00 : List Char := [',']
noncomputable def chunk0044Chars00 : List Char := chunk0044LeadChars00 ++ fragment0209244Chars ++ chunk0044SuffixChars00
noncomputable def chunk0044Push00 (acc : List SourceJson) : List SourceJson := fragment0209244Value :: acc

noncomputable def chunk0044AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0044_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 613)
      (SourceJson.white (chunk0044LeadChars00 ++ (fragment0209244Chars ++ rest))) acc =
      (SourceJson.value (fuel + 612) (fragment0209244Chars ++ rest)).bind
        (chunk0044AfterValue00 (fuel + 612) acc) := by rfl

theorem array_chunk0044 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 613) (SourceJson.white (chunk0044Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 612) (SourceJson.white tail) (chunk0044Push00 acc) := by
  have hinput : chunk0044Chars00 ++ tail = chunk0044LeadChars00 ++ (fragment0209244Chars ++ (chunk0044SuffixChars00 ++ tail)) := by
    simp only [chunk0044Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 613) (SourceJson.white (chunk0044Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 613)
          (SourceJson.white (chunk0044LeadChars00 ++ (fragment0209244Chars ++ (chunk0044SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 613) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 612) (fragment0209244Chars ++ (chunk0044SuffixChars00 ++ tail))).bind
        (chunk0044AfterValue00 (fuel + 612) acc) := array_chunk0044_head fuel (chunk0044SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0209244Value, chunk0044SuffixChars00 ++ tail)).bind
        (chunk0044AfterValue00 (fuel + 612) acc) :=
      congrArg (fun result => result.bind (chunk0044AfterValue00 (fuel + 612) acc))
        (value_fragment0209244 (fuel + 360) (chunk0044SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 612) (SourceJson.white tail) (chunk0044Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0044_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_before_reader"
  err.flush

noncomputable def chunk0045LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0045SuffixChars00 : List Char := [',']
noncomputable def chunk0045Chars00 : List Char := chunk0045LeadChars00 ++ fragment0210881Chars ++ chunk0045SuffixChars00
noncomputable def chunk0045Push00 (acc : List SourceJson) : List SourceJson := fragment0210881Value :: acc

noncomputable def chunk0045AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0045_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 612)
      (SourceJson.white (chunk0045LeadChars00 ++ (fragment0210881Chars ++ rest))) acc =
      (SourceJson.value (fuel + 611) (fragment0210881Chars ++ rest)).bind
        (chunk0045AfterValue00 (fuel + 611) acc) := by rfl

theorem array_chunk0045 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 612) (SourceJson.white (chunk0045Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 611) (SourceJson.white tail) (chunk0045Push00 acc) := by
  have hinput : chunk0045Chars00 ++ tail = chunk0045LeadChars00 ++ (fragment0210881Chars ++ (chunk0045SuffixChars00 ++ tail)) := by
    simp only [chunk0045Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 612) (SourceJson.white (chunk0045Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 612)
          (SourceJson.white (chunk0045LeadChars00 ++ (fragment0210881Chars ++ (chunk0045SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 612) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 611) (fragment0210881Chars ++ (chunk0045SuffixChars00 ++ tail))).bind
        (chunk0045AfterValue00 (fuel + 611) acc) := array_chunk0045_head fuel (chunk0045SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0210881Value, chunk0045SuffixChars00 ++ tail)).bind
        (chunk0045AfterValue00 (fuel + 611) acc) :=
      congrArg (fun result => result.bind (chunk0045AfterValue00 (fuel + 611) acc))
        (value_fragment0210881 (fuel + 172) (chunk0045SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 611) (SourceJson.white tail) (chunk0045Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0045_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_before_reader"
  err.flush

noncomputable def chunk0046LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0046SuffixChars00 : List Char := [',']
noncomputable def chunk0046Chars00 : List Char := chunk0046LeadChars00 ++ fragment0212901Chars ++ chunk0046SuffixChars00
noncomputable def chunk0046Push00 (acc : List SourceJson) : List SourceJson := fragment0212901Value :: acc

noncomputable def chunk0046AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0046_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 611)
      (SourceJson.white (chunk0046LeadChars00 ++ (fragment0212901Chars ++ rest))) acc =
      (SourceJson.value (fuel + 610) (fragment0212901Chars ++ rest)).bind
        (chunk0046AfterValue00 (fuel + 610) acc) := by rfl

theorem array_chunk0046 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 611) (SourceJson.white (chunk0046Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 610) (SourceJson.white tail) (chunk0046Push00 acc) := by
  have hinput : chunk0046Chars00 ++ tail = chunk0046LeadChars00 ++ (fragment0212901Chars ++ (chunk0046SuffixChars00 ++ tail)) := by
    simp only [chunk0046Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 611) (SourceJson.white (chunk0046Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 611)
          (SourceJson.white (chunk0046LeadChars00 ++ (fragment0212901Chars ++ (chunk0046SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 611) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 610) (fragment0212901Chars ++ (chunk0046SuffixChars00 ++ tail))).bind
        (chunk0046AfterValue00 (fuel + 610) acc) := array_chunk0046_head fuel (chunk0046SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0212901Value, chunk0046SuffixChars00 ++ tail)).bind
        (chunk0046AfterValue00 (fuel + 610) acc) :=
      congrArg (fun result => result.bind (chunk0046AfterValue00 (fuel + 610) acc))
        (value_fragment0212901 (fuel + 349) (chunk0046SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 610) (SourceJson.white tail) (chunk0046Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0046_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_before_reader"
  err.flush

noncomputable def chunk0047LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0047SuffixChars00 : List Char := [',']
noncomputable def chunk0047Chars00 : List Char := chunk0047LeadChars00 ++ fragment0214573Chars ++ chunk0047SuffixChars00
noncomputable def chunk0047Push00 (acc : List SourceJson) : List SourceJson := fragment0214573Value :: acc

noncomputable def chunk0047AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0047_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 610)
      (SourceJson.white (chunk0047LeadChars00 ++ (fragment0214573Chars ++ rest))) acc =
      (SourceJson.value (fuel + 609) (fragment0214573Chars ++ rest)).bind
        (chunk0047AfterValue00 (fuel + 609) acc) := by rfl

theorem array_chunk0047 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 610) (SourceJson.white (chunk0047Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 609) (SourceJson.white tail) (chunk0047Push00 acc) := by
  have hinput : chunk0047Chars00 ++ tail = chunk0047LeadChars00 ++ (fragment0214573Chars ++ (chunk0047SuffixChars00 ++ tail)) := by
    simp only [chunk0047Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 610) (SourceJson.white (chunk0047Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 610)
          (SourceJson.white (chunk0047LeadChars00 ++ (fragment0214573Chars ++ (chunk0047SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 610) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 609) (fragment0214573Chars ++ (chunk0047SuffixChars00 ++ tail))).bind
        (chunk0047AfterValue00 (fuel + 609) acc) := array_chunk0047_head fuel (chunk0047SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0214573Value, chunk0047SuffixChars00 ++ tail)).bind
        (chunk0047AfterValue00 (fuel + 609) acc) :=
      congrArg (fun result => result.bind (chunk0047AfterValue00 (fuel + 609) acc))
        (value_fragment0214573 (fuel + 173) (chunk0047SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 609) (SourceJson.white tail) (chunk0047Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0047_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0040Chars00 ++ chunk0041Chars00 ++ chunk0042Chars00 ++ chunk0043Chars00 ++ chunk0044Chars00 ++ chunk0045Chars00 ++ chunk0046Chars00 ++ chunk0047Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0047Push00 (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 617) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 609) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 617) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 617) (SourceJson.white (chunk0040Chars00 ++ (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 617) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 616) (SourceJson.white (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))))) (chunk0040Push00 (acc)) := array_chunk0040 fuel (chunk0041Chars00 ++ (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 615) (SourceJson.white (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))))) (chunk0041Push00 (chunk0040Push00 (acc))) := array_chunk0041 fuel (chunk0042Chars00 ++ (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))) (chunk0040Push00 (acc))
    _ = SourceJson.array (fuel + 614) (SourceJson.white (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))))) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))) := array_chunk0042 fuel (chunk0043Chars00 ++ (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))) (chunk0041Push00 (chunk0040Push00 (acc)))
    _ = SourceJson.array (fuel + 613) (SourceJson.white (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))))) (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))) := array_chunk0043 fuel (chunk0044Chars00 ++ (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))) (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))
    _ = SourceJson.array (fuel + 612) (SourceJson.white (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))))) (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))) := array_chunk0044 fuel (chunk0045Chars00 ++ (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))
    _ = SourceJson.array (fuel + 611) (SourceJson.white (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail)))) (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))) := array_chunk0045 fuel (chunk0046Chars00 ++ (chunk0047Chars00 ++ (tail))) (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))
    _ = SourceJson.array (fuel + 610) (SourceJson.white (chunk0047Chars00 ++ (tail))) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))))) := array_chunk0046 fuel (chunk0047Chars00 ++ (tail)) (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc)))))))
    _ = SourceJson.array (fuel + 609) (SourceJson.white tail) (blockPush acc) := array_chunk0047 fuel (tail) (chunk0046Push00 (chunk0045Push00 (chunk0044Push00 (chunk0043Push00 (chunk0042Push00 (chunk0041Push00 (chunk0040Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 201518).take 15062 = blockChars := by rfl

theorem block_original_split : sourceRest 201518 = blockChars ++ sourceRest 216580 := by
  calc
    sourceRest 201518 = (sourceRest 201518).take 15062 ++ (sourceRest 201518).drop 15062 :=
      (List.take_append_drop 15062 (sourceRest 201518)).symm
    _ = blockChars ++ (sourceRest 201518).drop 15062 :=
      congrArg (fun part => part ++ (sourceRest 201518).drop 15062) block_original_prefix
    _ = blockChars ++ sourceRest 216580 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 201518 15062)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 617) (SourceJson.white (sourceRest 201518)) acc =
      SourceJson.array (fuel + 609) (SourceJson.white (sourceRest 216580)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 617) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 216580) acc)

#print axioms object_fragment0201524_field_000
#print axioms object_fragment0201524_field_001
#print axioms object_fragment0201524_field_002
#print axioms object_fragment0201524_field_003
#print axioms object_fragment0201524_field_004
#print axioms object_fragment0201524_field_005
#print axioms object_fragment0201524_field_006
#print axioms object_fragment0201524_field_007
#print axioms object_fragment0201524_field_008
#print axioms object_fragment0201524_field_009
#print axioms value_fragment0201524
#print axioms object_fragment0203081_field_000
#print axioms object_fragment0203081_field_001
#print axioms object_fragment0203081_field_002
#print axioms object_fragment0203081_field_003
#print axioms object_fragment0203081_field_004
#print axioms object_fragment0203081_field_005
#print axioms object_fragment0203081_field_006
#print axioms object_fragment0203081_field_007
#print axioms object_fragment0203081_field_008
#print axioms object_fragment0203081_field_009
#print axioms value_fragment0203081
#print axioms object_fragment0205178_field_000
#print axioms object_fragment0205178_field_001
#print axioms object_fragment0205178_field_002
#print axioms object_fragment0205178_field_003
#print axioms object_fragment0205178_field_004
#print axioms object_fragment0205178_field_005
#print axioms object_fragment0205178_field_006
#print axioms object_fragment0205178_field_007
#print axioms object_fragment0205178_field_008
#print axioms object_fragment0205178_field_009
#print axioms value_fragment0205178
#print axioms object_fragment0207270_field_000
#print axioms object_fragment0207270_field_001
#print axioms object_fragment0207270_field_002
#print axioms object_fragment0207270_field_003
#print axioms object_fragment0207270_field_004
#print axioms object_fragment0207270_field_005
#print axioms object_fragment0207270_field_006
#print axioms object_fragment0207270_field_007
#print axioms object_fragment0207270_field_008
#print axioms object_fragment0207270_field_009
#print axioms value_fragment0207270
#print axioms object_fragment0209244_field_000
#print axioms object_fragment0209244_field_001
#print axioms object_fragment0209244_field_002
#print axioms object_fragment0209244_field_003
#print axioms object_fragment0209244_field_004
#print axioms object_fragment0209244_field_005
#print axioms object_fragment0209244_field_006
#print axioms object_fragment0209244_field_007
#print axioms object_fragment0209244_field_008
#print axioms object_fragment0209244_field_009
#print axioms value_fragment0209244
#print axioms object_fragment0210881_field_000
#print axioms object_fragment0210881_field_001
#print axioms object_fragment0210881_field_002
#print axioms object_fragment0210881_field_003
#print axioms object_fragment0210881_field_004
#print axioms object_fragment0210881_field_005
#print axioms object_fragment0210881_field_006
#print axioms object_fragment0210881_field_007
#print axioms object_fragment0210881_field_008
#print axioms object_fragment0210881_field_009
#print axioms value_fragment0210881
#print axioms object_fragment0212901_field_000
#print axioms object_fragment0212901_field_001
#print axioms object_fragment0212901_field_002
#print axioms object_fragment0212901_field_003
#print axioms object_fragment0212901_field_004
#print axioms object_fragment0212901_field_005
#print axioms object_fragment0212901_field_006
#print axioms object_fragment0212901_field_007
#print axioms object_fragment0212901_field_008
#print axioms object_fragment0212901_field_009
#print axioms value_fragment0212901
#print axioms object_fragment0214573_field_000
#print axioms object_fragment0214573_field_001
#print axioms object_fragment0214573_field_002
#print axioms object_fragment0214573_field_003
#print axioms object_fragment0214573_field_004
#print axioms object_fragment0214573_field_005
#print axioms object_fragment0214573_field_006
#print axioms object_fragment0214573_field_007
#print axioms object_fragment0214573_field_008
#print axioms object_fragment0214573_field_009
#print axioms value_fragment0214573
#print axioms array_chunk0040_head
#print axioms array_chunk0040
#print axioms array_chunk0041_head
#print axioms array_chunk0041
#print axioms array_chunk0042_head
#print axioms array_chunk0042
#print axioms array_chunk0043_head
#print axioms array_chunk0043
#print axioms array_chunk0044_head
#print axioms array_chunk0044
#print axioms array_chunk0045_head
#print axioms array_chunk0045
#print axioms array_chunk0046_head
#print axioms array_chunk0046
#print axioms array_chunk0047_head
#print axioms array_chunk0047
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock005

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
