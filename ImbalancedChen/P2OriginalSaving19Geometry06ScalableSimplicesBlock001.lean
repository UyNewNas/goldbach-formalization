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

namespace SimplicesBlock001

noncomputable def fragment0140279Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0140279Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0140279Field000Value00 : SourceJson := .number (String.ofList ['8'])
noncomputable def fragment0140279Acc00100 : List (String × SourceJson) := (fragment0140279Field000Key00, fragment0140279Field000Value00) :: fragment0140279Acc00000
noncomputable def fragment0140279Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '8', ',']

theorem object_fragment0140279_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 442) (SourceJson.white (fragment0140279Field000Chars00 ++ tail)) fragment0140279Acc00000 =
      SourceJson.object (fuel + 441) (SourceJson.white tail) fragment0140279Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_000"
  err.flush

noncomputable def fragment0140279Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0140279Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0140279Acc00200 : List (String × SourceJson) := (fragment0140279Field001Key00, fragment0140279Field001Value00) :: fragment0140279Acc00100
noncomputable def fragment0140279Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0140279_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 441) (SourceJson.white (fragment0140279Field001Chars00 ++ tail)) fragment0140279Acc00100 =
      SourceJson.object (fuel + 440) (SourceJson.white tail) fragment0140279Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_001"
  err.flush

noncomputable def fragment0140279Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0140279Field002Value00 : SourceJson := .str (String.ofList ['1', '3', '4', '6', '9', '4', '3', '1', '1', '7', '7', '7', '7', '0', '9', '6', '9', '0', '0', '2', '3', '6', '2', '4', '0', '4', '5', '0', '5', '2', '0', '6', '1', '6', '5', '5', '1', '8', '8', '9', '1', '7', '9', '1', '/', '2', '6', '4', '3', '8', '2', '5', '9', '6', '9', '8', '5', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0140279Acc00300 : List (String × SourceJson) := (fragment0140279Field002Key00, fragment0140279Field002Value00) :: fragment0140279Acc00200
noncomputable def fragment0140279Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '3', '4', '6', '9', '4', '3', '1', '1', '7', '7', '7', '7', '0', '9', '6', '9', '0', '0', '2', '3', '6', '2', '4', '0', '4', '5', '0', '5', '2', '0', '6', '1', '6', '5', '5', '1', '8', '8', '9', '1', '7', '9', '1', '/', '2', '6', '4', '3', '8', '2', '5', '9', '6', '9', '8', '5', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0140279_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 440) (SourceJson.white (fragment0140279Field002Chars00 ++ tail)) fragment0140279Acc00200 =
      SourceJson.object (fuel + 439) (SourceJson.white tail) fragment0140279Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_002"
  err.flush

noncomputable def fragment0140279Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0140279Field003Value00 : SourceJson := .str (String.ofList ['2', '4', '2', '7', '7', '4', '2', '3', '/', '1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0'])
noncomputable def fragment0140279Acc00400 : List (String × SourceJson) := (fragment0140279Field003Key00, fragment0140279Field003Value00) :: fragment0140279Acc00300
noncomputable def fragment0140279Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '2', '4', '2', '7', '7', '4', '2', '3', '/', '1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0', '"', ',']

theorem object_fragment0140279_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 439) (SourceJson.white (fragment0140279Field003Chars00 ++ tail)) fragment0140279Acc00300 =
      SourceJson.object (fuel + 438) (SourceJson.white tail) fragment0140279Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_003"
  err.flush

noncomputable def fragment0140279Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0140279Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0140279Acc00500 : List (String × SourceJson) := (fragment0140279Field004Key00, fragment0140279Field004Value00) :: fragment0140279Acc00400
noncomputable def fragment0140279Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0140279_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 438) (SourceJson.white (fragment0140279Field004Chars00 ++ tail)) fragment0140279Acc00400 =
      SourceJson.object (fuel + 437) (SourceJson.white tail) fragment0140279Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_004"
  err.flush

noncomputable def fragment0140279Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0140279Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '9', '1', '2', '4', '0', '6', '8', '3', '5', '8', '1', '9', '4', '9', '5', '8', '2', '9', '7', '6', '3', '9', '3', '/', '4', '3', '4', '2', '9', '7', '2', '5', '8', '5', '2', '3', '1', '5', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '1', '1', '0', '9', '2', '2', '1', '3', '4', '6', '3', '1', '8', '6', '6', '0', '4', '2', '1', '9', '/', '4', '4', '3', '1', '6', '0', '4', '6', '7', '8', '8', '0', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '3', '2', '7', '9', '8', '7', '8', '3', '0', '5', '3', '9', '4', '0', '3', '2', '5', '8', '7', '7', '9', '/', '4', '3', '4', '2', '9', '7', '2', '5', '8', '5', '2', '3', '1', '5', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '6', '7', '1', '9', '9', '2', '5', '5', '8', '6', '8', '4', '9', '2', '3', '4', '0', '2', '1', '5', '1', '/', '8', '6', '8', '5', '9', '4', '5', '1', '7', '0', '4', '6', '3', '0', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '8', '0', '0', '6', '3', '9', '9', '7', '7', '4', '1', '1', '6', '3', '2', '5', '1', '6', '6', '0', '9', '/', '1', '4', '4', '7', '6', '5', '7', '5', '2', '8', '4', '1', '0', '5', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '1', '2', '2', '9', '4', '3', '4', '7', '1', '4', '0', '6', '5', '0', '3', '7', '5', '2', '3', '3', '/', '3', '9', '4', '8', '1', '5', '6', '8', '9', '5', '6', '6', '5', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '1', '2', '1', '7', '0', '2', '9', '7', '8', '5', '1', '5', '5', '8', '1', '2', '2', '6', '2', '6', '3', '/', '7', '8', '9', '6', '3', '1', '3', '7', '9', '1', '3', '3', '0', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '4', '0', '3', '3', '5', '2', '4', '5', '4', '2', '4', '5', '7', '5', '9', '1', '9', '9', '8', '8', '3', '/', '7', '8', '9', '6', '3', '1', '3', '7', '9', '1', '3', '3', '0', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '8', '5', '8', '9', '9', '1', '7', '6', '9', '3', '2', '0', '7', '2', '1', '5', '0', '0', '9', '9', '/', '3', '9', '4', '8', '1', '5', '6', '8', '9', '5', '6', '6', '5', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '0', '5', '0', '8', '2', '2', '3', '3', '2', '3', '7', '0', '9', '7', '2', '0', '3', '2', '3', '/', '1', '4', '7', '7', '2', '0', '1', '5', '5', '9', '6', '0', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0140279Acc00600 : List (String × SourceJson) := (fragment0140279Field005Key00, fragment0140279Field005Value00) :: fragment0140279Acc00500
noncomputable def fragment0140279Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '1', '2', '4', '0', '6', '8', '3', '5', '8', '1', '9', '4', '9', '5', '8', '2', '9', '7', '6', '3', '9', '3', '/', '4', '3', '4', '2', '9', '7', '2', '5', '8', '5', '2', '3', '1', '5', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '1', '1', '0', '9', '2', '2', '1', '3', '4', '6', '3', '1', '8', '6', '6', '0', '4', '2', '1', '9', '/', '4', '4', '3', '1', '6', '0', '4', '6', '7', '8', '8', '0', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '6', '3', '2', '7', '9', '8', '7', '8', '3', '0', '5', '3', '9', '4', '0', '3', '2', '5', '8', '7', '7', '9', '/', '4', '3', '4', '2', '9', '7', '2', '5', '8', '5', '2', '3', '1', '5', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '6', '7', '1', '9', '9', '2', '5', '5', '8', '6', '8', '4', '9', '2', '3', '4', '0', '2', '1', '5', '1', '/', '8', '6', '8', '5', '9', '4', '5', '1', '7', '0', '4', '6', '3', '0', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '4', '8', '0', '0', '6', '3', '9', '9', '7', '7', '4', '1', '1', '6', '3', '2', '5', '1', '6', '6', '0', '9', '/', '1', '4', '4', '7', '6', '5', '7', '5', '2', '8', '4', '1', '0', '5', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '7', '1', '2', '2', '9', '4', '3', '4', '7', '1', '4', '0', '6', '5', '0', '3', '7', '5', '2', '3', '3', '/', '3', '9', '4', '8', '1', '5', '6', '8', '9', '5', '6', '6', '5', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '1', '2', '1', '7', '0', '2', '9', '7', '8', '5', '1', '5', '5', '8', '1', '2', '2', '6', '2', '6', '3', '/', '7', '8', '9', '6', '3', '1', '3', '7', '9', '1', '3', '3', '0', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '4', '0', '3', '3', '5', '2', '4', '5', '4', '2', '4', '5', '7', '5', '9', '1', '9', '9', '8', '8', '3', '/', '7', '8', '9', '6', '3', '1', '3', '7', '9', '1', '3', '3', '0', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '8', '5', '8', '9', '9', '1', '7', '6', '9', '3', '2', '0', '7', '2', '1', '5', '0', '0', '9', '9', '/', '3', '9', '4', '8', '1', '5', '6', '8', '9', '5', '6', '6', '5', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '0', '5', '0', '8', '2', '2', '3', '3', '2', '3', '7', '0', '9', '7', '2', '0', '3', '2', '3', '/', '1', '4', '7', '7', '2', '0', '1', '5', '5', '9', '6', '0', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0140279_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0140279Field005Chars00 ++ tail)) fragment0140279Acc00500 =
      SourceJson.object (fuel + 436) (SourceJson.white tail) fragment0140279Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_005"
  err.flush

noncomputable def fragment0140279Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0140279Field006Value00 : SourceJson := .str (String.ofList ['2', '0', '1', '2', '3', '2', '6', '6', '3', '5', '5', '2', '0', '8', '2', '4', '6', '8', '6', '7', '0', '9', '1', '6', '9', '8', '0', '5', '9', '6', '9', '2', '0', '4', '8', '1', '5', '4', '4', '7', '0', '8', '0', '0', '0', '8', '2', '1', '2', '8', '8', '0', '0', '0', '0', '0', '0', '/', '1', '4', '5', '9', '6', '7', '5', '1', '4', '2', '0', '4', '1', '4', '1', '0', '5', '0', '9', '7', '2', '5', '0', '6', '4', '5', '4', '7', '9', '6', '5', '0', '6', '3', '4', '5', '4', '0', '0', '4', '2', '2', '2', '0', '7', '2', '3', '5', '9', '9', '1', '2', '8', '0', '2', '0', '1', '9', '7', '4', '5', '9', '3', '3', '4', '8', '3', '0', '3', '3'])
noncomputable def fragment0140279Acc00700 : List (String × SourceJson) := (fragment0140279Field006Key00, fragment0140279Field006Value00) :: fragment0140279Acc00600
noncomputable def fragment0140279Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '0', '1', '2', '3', '2', '6', '6', '3', '5', '5', '2', '0', '8', '2', '4', '6', '8', '6', '7', '0', '9', '1', '6', '9', '8', '0', '5', '9', '6', '9', '2', '0', '4', '8', '1', '5', '4', '4', '7', '0', '8', '0', '0', '0', '8', '2', '1', '2', '8', '8', '0', '0', '0', '0', '0', '0', '/', '1', '4', '5', '9', '6', '7', '5', '1', '4', '2', '0', '4', '1', '4', '1', '0', '5', '0', '9', '7', '2', '5', '0', '6', '4', '5', '4', '7', '9', '6', '5', '0', '6', '3', '4', '5', '4', '0', '0', '4', '2', '2', '2', '0', '7', '2', '3', '5', '9', '9', '1', '2', '8', '0', '2', '0', '1', '9', '7', '4', '5', '9', '3', '3', '4', '8', '3', '0', '3', '3', '"', ',']

theorem object_fragment0140279_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0140279Field006Chars00 ++ tail)) fragment0140279Acc00600 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0140279Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_006"
  err.flush

noncomputable def fragment0140279Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0140279Field007Value00 : SourceJson := .str (String.ofList ['6', '9', '6', '7', '3', '3', '8', '2', '9', '6', '1', '4', '5', '2', '7', '9', '0', '8', '9', '3', '2', '8', '0', '8', '1', '3', '6', '3', '0', '0', '0', '1', '0', '7', '5', '3', '6', '1', '4', '4', '4', '0', '6', '9', '1', '3', '9', '2', '2', '6', '2', '5', '9', '0', '7', '8', '8', '5', '1', '7', '3', '6', '7', '2', '3', '9', '5', '4', '5', '1', '6', '5', '8', '7', '2', '5', '1', '9', '6', '6', '1', '7', '3', '9', '4', '4', '4', '7', '8', '3', '2', '7', '6', '2', '5', '7', '7', '5', '5', '3', '9', '4', '0', '5', '2', '0', '8', '7', '2', '3', '4', '5', '5', '3', '4', '9', '6', '6', '8', '3', '5', '4', '1', '4', '2', '1', '1', '1', '1', '9', '0', '1', '7', '2', '7', '5', '3', '5', '5', '0', '7', '4', '7', '0', '5', '8', '0', '5', '3', '4', '9', '7', '2', '3', '2', '8', '6', '5', '7', '2', '8', '3', '8', '8', '3', '8', '8', '0', '1', '9', '9', '1', '7', '0', '8', '8', '6', '6', '0', '6', '4', '1', '5', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '9', '6', '5', '0', '1', '6', '9', '1', '2', '3', '1', '1', '3', '4', '7', '1', '6', '4', '1', '5', '1', '5', '2', '5', '0', '1', '3', '5', '5', '8', '3', '4', '3', '3', '3', '4', '3', '7', '6', '7', '7', '1', '2', '7', '4', '2', '5', '9', '6', '6', '7', '4', '1', '8', '6', '0', '8', '7', '6', '4', '6', '6', '3', '6', '8', '9', '3', '2', '4', '6', '6', '2', '6', '8', '7', '8', '9', '1', '5', '7', '1', '8', '7', '7', '9', '1', '9', '6', '0', '7', '3', '5', '8', '9', '5', '3', '1', '8', '7', '8', '9', '2', '0', '4', '1', '3', '7', '7', '8', '5', '2', '6', '4', '2', '4', '4', '4', '8', '5', '7', '0', '5', '3', '7', '7', '6', '6', '8', '2', '5', '9', '8', '2', '1', '6', '3', '4', '1', '7', '5', '3', '0', '9', '5', '8', '8', '6', '3', '2', '5', '5', '1', '2', '2', '1', '6', '7', '4', '6', '3', '7', '3', '4', '7', '7', '4', '0', '3', '6', '4', '8', '6', '8', '4', '5', '0', '3', '1', '6', '7', '6', '5', '4', '5', '8', '5', '8', '0', '1', '1', '7', '0', '8', '3', '9', '8', '3', '9', '4', '5', '3', '0', '1', '4', '6', '2', '3', '0', '5', '5', '7', '0', '3', '3', '2', '4', '3', '0', '6', '1'])
noncomputable def fragment0140279Acc00800 : List (String × SourceJson) := (fragment0140279Field007Key00, fragment0140279Field007Value00) :: fragment0140279Acc00700
noncomputable def fragment0140279Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '9', '6', '7', '3', '3', '8', '2', '9', '6', '1', '4', '5', '2', '7', '9', '0', '8', '9', '3', '2', '8', '0', '8', '1', '3', '6', '3', '0', '0', '0', '1', '0', '7', '5', '3', '6', '1', '4', '4', '4', '0', '6', '9', '1', '3', '9', '2', '2', '6', '2', '5', '9', '0', '7', '8', '8', '5', '1', '7', '3', '6', '7', '2', '3', '9', '5', '4', '5', '1', '6', '5', '8', '7', '2', '5', '1', '9', '6', '6', '1', '7', '3', '9', '4', '4', '4', '7', '8', '3', '2', '7', '6', '2', '5', '7', '7', '5', '5', '3', '9', '4', '0', '5', '2', '0', '8', '7', '2', '3', '4', '5', '5', '3', '4', '9', '6', '6', '8', '3', '5', '4', '1', '4', '2', '1', '1', '1', '1', '9', '0', '1', '7', '2', '7', '5', '3', '5', '5', '0', '7', '4', '7', '0', '5', '8', '0', '5', '3', '4', '9', '7', '2', '3', '2', '8', '6', '5', '7', '2', '8', '3', '8', '8', '3', '8', '8', '0', '1', '9', '9', '1', '7', '0', '8', '8', '6', '6', '0', '6', '4', '1', '5', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '9', '6', '5', '0', '1', '6', '9', '1', '2', '3', '1', '1', '3', '4', '7', '1', '6', '4', '1', '5', '1', '5', '2', '5', '0', '1', '3', '5', '5', '8', '3', '4', '3', '3', '3', '4', '3', '7', '6', '7', '7', '1', '2', '7', '4', '2', '5', '9', '6', '6', '7', '4', '1', '8', '6', '0', '8', '7', '6', '4', '6', '6', '3', '6', '8', '9', '3', '2', '4', '6', '6', '2', '6', '8', '7', '8', '9', '1', '5', '7', '1', '8', '7', '7', '9', '1', '9', '6', '0', '7', '3', '5', '8', '9', '5', '3', '1', '8', '7', '8', '9', '2', '0', '4', '1', '3', '7', '7', '8', '5', '2', '6', '4', '2', '4', '4', '4', '8', '5', '7', '0', '5', '3', '7', '7', '6', '6', '8', '2', '5', '9', '8', '2', '1', '6', '3', '4', '1', '7', '5', '3', '0', '9', '5', '8', '8', '6', '3', '2', '5', '5', '1', '2', '2', '1', '6', '7', '4', '6', '3', '7', '3', '4', '7', '7', '4', '0', '3', '6', '4', '8', '6', '8', '4', '5', '0', '3', '1', '6', '7', '6', '5', '4', '5', '8', '5', '8', '0', '1', '1', '7', '0', '8', '3', '9', '8', '3', '9', '4', '5', '3', '0', '1', '4', '6', '2', '3', '0', '5', '5', '7', '0', '3', '3', '2', '4', '3', '0', '6', '1', '"', ',']

theorem object_fragment0140279_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0140279Field007Chars00 ++ tail)) fragment0140279Acc00700 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0140279Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_007"
  err.flush

noncomputable def fragment0140279Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0140279Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '9', '2', '2', '4', '9', '4', '8', '1', '5', '3', '7', '7', '4', '6', '2'])
noncomputable def fragment0140279Acc00900 : List (String × SourceJson) := (fragment0140279Field008Key00, fragment0140279Field008Value00) :: fragment0140279Acc00800
noncomputable def fragment0140279Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '9', '2', '2', '4', '9', '4', '8', '1', '5', '3', '7', '7', '4', '6', '2', '"', ',']

theorem object_fragment0140279_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0140279Field008Chars00 ++ tail)) fragment0140279Acc00800 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0140279Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_008"
  err.flush

noncomputable def fragment0140279Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0140279Field009Value00 : SourceJson := .str (String.ofList ['4', '2', '5', '7', '6', '8', '3', '6', '9', '2', '6', '0', '4', '1', '9', '1', '9'])
noncomputable def fragment0140279Acc01000 : List (String × SourceJson) := (fragment0140279Field009Key00, fragment0140279Field009Value00) :: fragment0140279Acc00900
noncomputable def fragment0140279Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '5', '7', '6', '8', '3', '6', '9', '2', '6', '0', '4', '1', '9', '1', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0140279_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0140279Field009Chars00 ++ tail)) fragment0140279Acc00900 =
      .ok (.obj (fragment0140279Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0140279_object_field_009"
  err.flush

noncomputable def fragment0140279Chars : List Char := '{' :: (fragment0140279Field000Chars00 ++ fragment0140279Field001Chars00 ++ fragment0140279Field002Chars00 ++ fragment0140279Field003Chars00 ++ fragment0140279Field004Chars00 ++ fragment0140279Field005Chars00 ++ fragment0140279Field006Chars00 ++ fragment0140279Field007Chars00 ++ fragment0140279Field008Chars00 ++ fragment0140279Field009Chars00)
noncomputable def fragment0140279Value : SourceJson := .obj (fragment0140279Acc01000.reverse)

theorem value_fragment0140279 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 443) (fragment0140279Chars ++ tail) =
      .ok (fragment0140279Value, tail) := by
  have hinput : fragment0140279Chars ++ tail = '{' :: (fragment0140279Field000Chars00 ++ (fragment0140279Field001Chars00 ++ (fragment0140279Field002Chars00 ++ (fragment0140279Field003Chars00 ++ (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0140279Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 443) (fragment0140279Chars ++ tail) =
        SourceJson.value (fuel + 443) ('{' :: (fragment0140279Field000Chars00 ++ (fragment0140279Field001Chars00 ++ (fragment0140279Field002Chars00 ++ (fragment0140279Field003Chars00 ++ (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 443)) hinput
    _ = SourceJson.object (fuel + 442) (SourceJson.white (fragment0140279Field000Chars00 ++ (fragment0140279Field001Chars00 ++ (fragment0140279Field002Chars00 ++ (fragment0140279Field003Chars00 ++ (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))))))))))) fragment0140279Acc00000 := by rfl
    _ = SourceJson.object (fuel + 441) (SourceJson.white (fragment0140279Field001Chars00 ++ (fragment0140279Field002Chars00 ++ (fragment0140279Field003Chars00 ++ (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail))))))))))) fragment0140279Acc00100 := object_fragment0140279_field_000 fuel (fragment0140279Field001Chars00 ++ (fragment0140279Field002Chars00 ++ (fragment0140279Field003Chars00 ++ (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 440) (SourceJson.white (fragment0140279Field002Chars00 ++ (fragment0140279Field003Chars00 ++ (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))))))))) fragment0140279Acc00200 := object_fragment0140279_field_001 fuel (fragment0140279Field002Chars00 ++ (fragment0140279Field003Chars00 ++ (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 439) (SourceJson.white (fragment0140279Field003Chars00 ++ (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail))))))))) fragment0140279Acc00300 := object_fragment0140279_field_002 fuel (fragment0140279Field003Chars00 ++ (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 438) (SourceJson.white (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))))))) fragment0140279Acc00400 := object_fragment0140279_field_003 fuel (fragment0140279Field004Chars00 ++ (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail))))))) fragment0140279Acc00500 := object_fragment0140279_field_004 fuel (fragment0140279Field005Chars00 ++ (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))))) fragment0140279Acc00600 := object_fragment0140279_field_005 fuel (fragment0140279Field006Chars00 ++ (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail))))) fragment0140279Acc00700 := object_fragment0140279_field_006 fuel (fragment0140279Field007Chars00 ++ (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))) fragment0140279Acc00800 := object_fragment0140279_field_007 fuel (fragment0140279Field008Chars00 ++ (fragment0140279Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0140279Field009Chars00 ++ (tail))) fragment0140279Acc00900 := object_fragment0140279_field_008 fuel (fragment0140279Field009Chars00 ++ (tail))
    _ = .ok (fragment0140279Value, tail) := object_fragment0140279_field_009 fuel (tail)

noncomputable def fragment0142316Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0142316Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0142316Field000Value00 : SourceJson := .number (String.ofList ['9'])
noncomputable def fragment0142316Acc00100 : List (String × SourceJson) := (fragment0142316Field000Key00, fragment0142316Field000Value00) :: fragment0142316Acc00000
noncomputable def fragment0142316Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', ',']

theorem object_fragment0142316_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0142316Field000Chars00 ++ tail)) fragment0142316Acc00000 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0142316Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_000"
  err.flush

noncomputable def fragment0142316Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0142316Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0142316Acc00200 : List (String × SourceJson) := (fragment0142316Field001Key00, fragment0142316Field001Value00) :: fragment0142316Acc00100
noncomputable def fragment0142316Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0142316_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0142316Field001Chars00 ++ tail)) fragment0142316Acc00100 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0142316Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_001"
  err.flush

noncomputable def fragment0142316Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0142316Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '2', '8', '2', '6', '8', '3', '0', '3', '7', '3', '5', '2', '9', '9', '7', '0', '6', '1', '7', '2', '2', '1', '7', '6', '7', '9', '8', '1', '7', '0', '2', '1', '5', '1', '5', '6', '1', '8', '3', '/', '6', '3', '4', '0', '5', '7', '1', '0', '0', '3', '2', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0142316Acc00300 : List (String × SourceJson) := (fragment0142316Field002Key00, fragment0142316Field002Value00) :: fragment0142316Acc00200
noncomputable def fragment0142316Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '2', '8', '2', '6', '8', '3', '0', '3', '7', '3', '5', '2', '9', '9', '7', '0', '6', '1', '7', '2', '2', '1', '7', '6', '7', '9', '8', '1', '7', '0', '2', '1', '5', '1', '5', '6', '1', '8', '3', '/', '6', '3', '4', '0', '5', '7', '1', '0', '0', '3', '2', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0142316_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0142316Field002Chars00 ++ tail)) fragment0142316Acc00200 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0142316Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_002"
  err.flush

noncomputable def fragment0142316Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0142316Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0142316Acc00400 : List (String × SourceJson) := (fragment0142316Field003Key00, fragment0142316Field003Value00) :: fragment0142316Acc00300
noncomputable def fragment0142316Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0142316_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0142316Field003Chars00 ++ tail)) fragment0142316Acc00300 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0142316Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_003"
  err.flush

noncomputable def fragment0142316Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0142316Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0142316Acc00500 : List (String × SourceJson) := (fragment0142316Field004Key00, fragment0142316Field004Value00) :: fragment0142316Acc00400
noncomputable def fragment0142316Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0142316_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0142316Field004Chars00 ++ tail)) fragment0142316Acc00400 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0142316Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_004"
  err.flush

noncomputable def fragment0142316Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0142316Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '8', '7', '4', '0', '2', '0', '8', '2', '4', '2', '2', '0', '3', '7', '5', '7', '9', '0', '9', '9', '/', '1', '8', '6', '3', '8', '7', '1', '4', '6', '6', '7', '1', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '3', '6', '9', '3', '0', '6', '7', '1', '8', '7', '7', '8', '1', '4', '1', '8', '7', '3', '/', '2', '6', '6', '2', '6', '7', '3', '5', '2', '3', '8', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '7', '5', '7', '4', '8', '5', '4', '0', '2', '8', '0', '6', '6', '7', '5', '2', '2', '1', '7', '9', '/', '3', '7', '2', '7', '7', '4', '2', '9', '3', '3', '4', '3', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '2', '9', '9', '4', '7', '2', '0', '0', '6', '5', '4', '2', '8', '1', '9', '1', '0', '5', '7', '/', '7', '4', '5', '5', '4', '8', '5', '8', '6', '6', '8', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '0', '3', '3', '3', '3', '9', '1', '0', '3', '4', '3', '8', '0', '5', '5', '2', '6', '9', '9', '/', '1', '2', '4', '2', '5', '8', '0', '9', '7', '7', '8', '1', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '8', '2', '7', '0', '9', '9', '5', '6', '2', '3', '8', '0', '8', '9', '2', '2', '6', '2', '3', '/', '3', '3', '8', '8', '8', '5', '7', '2', '1', '2', '2', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '1', '2', '5', '0', '2', '6', '0', '4', '6', '6', '0', '4', '0', '2', '7', '6', '9', '7', '/', '1', '6', '9', '4', '4', '2', '8', '6', '0', '6', '1', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '0', '8', '0', '2', '1', '0', '4', '6', '7', '7', '6', '1', '7', '5', '4', '2', '4', '7', '/', '1', '6', '9', '4', '4', '2', '8', '6', '0', '6', '1', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '1', '5', '7', '9', '5', '5', '7', '3', '8', '4', '3', '9', '9', '6', '9', '9', '2', '7', '/', '1', '6', '9', '4', '4', '2', '8', '6', '0', '6', '1', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '9', '9', '5', '6', '5', '5', '5', '3', '5', '6', '7', '4', '4', '8', '8', '5', '1', '/', '8', '8', '7', '5', '5', '7', '8', '4', '1', '2', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0142316Acc00600 : List (String × SourceJson) := (fragment0142316Field005Key00, fragment0142316Field005Value00) :: fragment0142316Acc00500
noncomputable def fragment0142316Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '7', '4', '0', '2', '0', '8', '2', '4', '2', '2', '0', '3', '7', '5', '7', '9', '0', '9', '9', '/', '1', '8', '6', '3', '8', '7', '1', '4', '6', '6', '7', '1', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '3', '6', '9', '3', '0', '6', '7', '1', '8', '7', '7', '8', '1', '4', '1', '8', '7', '3', '/', '2', '6', '6', '2', '6', '7', '3', '5', '2', '3', '8', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '7', '5', '7', '4', '8', '5', '4', '0', '2', '8', '0', '6', '6', '7', '5', '2', '2', '1', '7', '9', '/', '3', '7', '2', '7', '7', '4', '2', '9', '3', '3', '4', '3', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '2', '9', '9', '4', '7', '2', '0', '0', '6', '5', '4', '2', '8', '1', '9', '1', '0', '5', '7', '/', '7', '4', '5', '5', '4', '8', '5', '8', '6', '6', '8', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '0', '3', '3', '3', '3', '9', '1', '0', '3', '4', '3', '8', '0', '5', '5', '2', '6', '9', '9', '/', '1', '2', '4', '2', '5', '8', '0', '9', '7', '7', '8', '1', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '8', '2', '7', '0', '9', '9', '5', '6', '2', '3', '8', '0', '8', '9', '2', '2', '6', '2', '3', '/', '3', '3', '8', '8', '8', '5', '7', '2', '1', '2', '2', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '1', '2', '5', '0', '2', '6', '0', '4', '6', '6', '0', '4', '0', '2', '7', '6', '9', '7', '/', '1', '6', '9', '4', '4', '2', '8', '6', '0', '6', '1', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '0', '0', '8', '0', '2', '1', '0', '4', '6', '7', '7', '6', '1', '7', '5', '4', '2', '4', '7', '/', '1', '6', '9', '4', '4', '2', '8', '6', '0', '6', '1', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '1', '5', '7', '9', '5', '5', '7', '3', '8', '4', '3', '9', '9', '6', '9', '9', '2', '7', '/', '1', '6', '9', '4', '4', '2', '8', '6', '0', '6', '1', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '9', '9', '5', '6', '5', '5', '5', '3', '5', '6', '7', '4', '4', '8', '8', '5', '1', '/', '8', '8', '7', '5', '5', '7', '8', '4', '1', '2', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0142316_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0142316Field005Chars00 ++ tail)) fragment0142316Acc00500 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0142316Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_005"
  err.flush

noncomputable def fragment0142316Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0142316Field006Value00 : SourceJson := .str (String.ofList ['8', '7', '5', '6', '6', '1', '6', '0', '9', '5', '1', '3', '3', '7', '9', '7', '7', '6', '3', '4', '8', '3', '7', '1', '9', '1', '4', '9', '7', '4', '6', '1', '7', '5', '6', '6', '1', '1', '3', '8', '4', '5', '6', '0', '0', '/', '2', '7', '5', '0', '0', '7', '6', '8', '5', '4', '4', '6', '2', '1', '9', '1', '8', '7', '6', '2', '1', '6', '8', '4', '2', '2', '4', '1', '5', '7', '5', '1', '1', '5', '4', '5', '3', '6', '8', '4', '3', '4', '1', '3', '0', '5', '6', '3', '8', '5', '1', '1', '9', '5', '1', '6', '6', '0', '2', '1', '1', '9'])
noncomputable def fragment0142316Acc00700 : List (String × SourceJson) := (fragment0142316Field006Key00, fragment0142316Field006Value00) :: fragment0142316Acc00600
noncomputable def fragment0142316Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '7', '5', '6', '6', '1', '6', '0', '9', '5', '1', '3', '3', '7', '9', '7', '7', '6', '3', '4', '8', '3', '7', '1', '9', '1', '4', '9', '7', '4', '6', '1', '7', '5', '6', '6', '1', '1', '3', '8', '4', '5', '6', '0', '0', '/', '2', '7', '5', '0', '0', '7', '6', '8', '5', '4', '4', '6', '2', '1', '9', '1', '8', '7', '6', '2', '1', '6', '8', '4', '2', '2', '4', '1', '5', '7', '5', '1', '1', '5', '4', '5', '3', '6', '8', '4', '3', '4', '1', '3', '0', '5', '6', '3', '8', '5', '1', '1', '9', '5', '1', '6', '6', '0', '2', '1', '1', '9', '"', ',']

theorem object_fragment0142316_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0142316Field006Chars00 ++ tail)) fragment0142316Acc00600 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0142316Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_006"
  err.flush

noncomputable def fragment0142316Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0142316Field007Value00 : SourceJson := .str (String.ofList ['1', '8', '4', '4', '5', '7', '7', '2', '1', '5', '8', '8', '5', '8', '9', '4', '6', '3', '2', '5', '5', '0', '2', '7', '7', '0', '7', '5', '7', '7', '7', '6', '2', '9', '8', '9', '1', '0', '6', '5', '4', '9', '5', '1', '5', '3', '5', '2', '8', '4', '1', '6', '9', '5', '7', '5', '6', '3', '8', '4', '0', '6', '3', '9', '3', '2', '0', '6', '3', '0', '7', '1', '9', '2', '8', '9', '8', '6', '7', '7', '3', '7', '3', '0', '2', '2', '5', '5', '4', '2', '3', '5', '4', '5', '3', '4', '1', '7', '8', '7', '4', '4', '2', '3', '6', '7', '0', '6', '7', '6', '1', '8', '2', '8', '4', '2', '5', '3', '0', '6', '1', '2', '8', '5', '4', '8', '3', '0', '4', '6', '2', '1', '1', '8', '1', '7', '2', '4', '2', '1', '9', '7', '5', '8', '6', '1', '8', '9', '5', '8', '0', '2', '6', '0', '1', '6', '4', '3', '4', '7', '2', '9', '3', '2', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '0', '3', '9', '0', '9', '8', '0', '0', '2', '1', '7', '2', '5', '4', '4', '7', '5', '1', '4', '3', '1', '6', '1', '2', '5', '5', '9', '4', '1', '2', '5', '0', '1', '9', '0', '5', '5', '6', '1', '2', '2', '7', '3', '2', '4', '0', '1', '9', '9', '8', '5', '3', '1', '1', '4', '4', '5', '7', '6', '1', '6', '5', '9', '1', '6', '4', '5', '5', '7', '3', '4', '7', '2', '4', '3', '6', '9', '4', '0', '4', '6', '8', '3', '8', '9', '3', '9', '7', '7', '0', '5', '7', '6', '4', '7', '6', '6', '4', '5', '1', '5', '5', '5', '8', '2', '1', '4', '2', '0', '5', '3', '9', '9', '2', '9', '1', '7', '2', '0', '6', '7', '8', '2', '7', '2', '3', '9', '1', '2', '8', '9', '5', '7', '7', '7', '9', '3', '6', '5', '8', '3', '8', '2', '4', '2', '2', '4', '3', '7', '9', '8', '8', '4', '1', '7', '0', '3', '2', '9', '3', '6', '3', '2', '7', '0', '2', '2', '0', '7', '1', '0', '0', '7', '8', '0', '5', '4', '3', '3', '7', '8', '3', '4', '4', '8', '3', '3', '2', '8', '2', '2', '7', '4', '8', '6', '1', '3', '3', '5', '3', '7'])
noncomputable def fragment0142316Acc00800 : List (String × SourceJson) := (fragment0142316Field007Key00, fragment0142316Field007Value00) :: fragment0142316Acc00700
noncomputable def fragment0142316Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '4', '4', '5', '7', '7', '2', '1', '5', '8', '8', '5', '8', '9', '4', '6', '3', '2', '5', '5', '0', '2', '7', '7', '0', '7', '5', '7', '7', '7', '6', '2', '9', '8', '9', '1', '0', '6', '5', '4', '9', '5', '1', '5', '3', '5', '2', '8', '4', '1', '6', '9', '5', '7', '5', '6', '3', '8', '4', '0', '6', '3', '9', '3', '2', '0', '6', '3', '0', '7', '1', '9', '2', '8', '9', '8', '6', '7', '7', '3', '7', '3', '0', '2', '2', '5', '5', '4', '2', '3', '5', '4', '5', '3', '4', '1', '7', '8', '7', '4', '4', '2', '3', '6', '7', '0', '6', '7', '6', '1', '8', '2', '8', '4', '2', '5', '3', '0', '6', '1', '2', '8', '5', '4', '8', '3', '0', '4', '6', '2', '1', '1', '8', '1', '7', '2', '4', '2', '1', '9', '7', '5', '8', '6', '1', '8', '9', '5', '8', '0', '2', '6', '0', '1', '6', '4', '3', '4', '7', '2', '9', '3', '2', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '0', '3', '9', '0', '9', '8', '0', '0', '2', '1', '7', '2', '5', '4', '4', '7', '5', '1', '4', '3', '1', '6', '1', '2', '5', '5', '9', '4', '1', '2', '5', '0', '1', '9', '0', '5', '5', '6', '1', '2', '2', '7', '3', '2', '4', '0', '1', '9', '9', '8', '5', '3', '1', '1', '4', '4', '5', '7', '6', '1', '6', '5', '9', '1', '6', '4', '5', '5', '7', '3', '4', '7', '2', '4', '3', '6', '9', '4', '0', '4', '6', '8', '3', '8', '9', '3', '9', '7', '7', '0', '5', '7', '6', '4', '7', '6', '6', '4', '5', '1', '5', '5', '5', '8', '2', '1', '4', '2', '0', '5', '3', '9', '9', '2', '9', '1', '7', '2', '0', '6', '7', '8', '2', '7', '2', '3', '9', '1', '2', '8', '9', '5', '7', '7', '7', '9', '3', '6', '5', '8', '3', '8', '2', '4', '2', '2', '4', '3', '7', '9', '8', '8', '4', '1', '7', '0', '3', '2', '9', '3', '6', '3', '2', '7', '0', '2', '2', '0', '7', '1', '0', '0', '7', '8', '0', '5', '4', '3', '3', '7', '8', '3', '4', '4', '8', '3', '3', '2', '8', '2', '2', '7', '4', '8', '6', '1', '3', '3', '5', '3', '7', '"', ',']

theorem object_fragment0142316_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0142316Field007Chars00 ++ tail)) fragment0142316Acc00700 =
      SourceJson.object (fuel + 393) (SourceJson.white tail) fragment0142316Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_007"
  err.flush

noncomputable def fragment0142316Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0142316Field008Value00 : SourceJson := .str (String.ofList ['2', '5', '2', '2', '7', '3', '1', '6', '8', '9', '9', '6', '9'])
noncomputable def fragment0142316Acc00900 : List (String × SourceJson) := (fragment0142316Field008Key00, fragment0142316Field008Value00) :: fragment0142316Acc00800
noncomputable def fragment0142316Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '2', '2', '7', '3', '1', '6', '8', '9', '9', '6', '9', '"', ',']

theorem object_fragment0142316_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 393) (SourceJson.white (fragment0142316Field008Chars00 ++ tail)) fragment0142316Acc00800 =
      SourceJson.object (fuel + 392) (SourceJson.white tail) fragment0142316Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_008"
  err.flush

noncomputable def fragment0142316Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0142316Field009Value00 : SourceJson := .str (String.ofList ['9', '7', '1', '7', '5', '0', '1', '9', '0', '1', '3', '2', '4'])
noncomputable def fragment0142316Acc01000 : List (String × SourceJson) := (fragment0142316Field009Key00, fragment0142316Field009Value00) :: fragment0142316Acc00900
noncomputable def fragment0142316Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '7', '1', '7', '5', '0', '1', '9', '0', '1', '3', '2', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0142316_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 392) (SourceJson.white (fragment0142316Field009Chars00 ++ tail)) fragment0142316Acc00900 =
      .ok (.obj (fragment0142316Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0142316_object_field_009"
  err.flush

noncomputable def fragment0142316Chars : List Char := '{' :: (fragment0142316Field000Chars00 ++ fragment0142316Field001Chars00 ++ fragment0142316Field002Chars00 ++ fragment0142316Field003Chars00 ++ fragment0142316Field004Chars00 ++ fragment0142316Field005Chars00 ++ fragment0142316Field006Chars00 ++ fragment0142316Field007Chars00 ++ fragment0142316Field008Chars00 ++ fragment0142316Field009Chars00)
noncomputable def fragment0142316Value : SourceJson := .obj (fragment0142316Acc01000.reverse)

theorem value_fragment0142316 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 402) (fragment0142316Chars ++ tail) =
      .ok (fragment0142316Value, tail) := by
  have hinput : fragment0142316Chars ++ tail = '{' :: (fragment0142316Field000Chars00 ++ (fragment0142316Field001Chars00 ++ (fragment0142316Field002Chars00 ++ (fragment0142316Field003Chars00 ++ (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0142316Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 402) (fragment0142316Chars ++ tail) =
        SourceJson.value (fuel + 402) ('{' :: (fragment0142316Field000Chars00 ++ (fragment0142316Field001Chars00 ++ (fragment0142316Field002Chars00 ++ (fragment0142316Field003Chars00 ++ (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 402)) hinput
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0142316Field000Chars00 ++ (fragment0142316Field001Chars00 ++ (fragment0142316Field002Chars00 ++ (fragment0142316Field003Chars00 ++ (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))))))))))) fragment0142316Acc00000 := by rfl
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0142316Field001Chars00 ++ (fragment0142316Field002Chars00 ++ (fragment0142316Field003Chars00 ++ (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail))))))))))) fragment0142316Acc00100 := object_fragment0142316_field_000 fuel (fragment0142316Field001Chars00 ++ (fragment0142316Field002Chars00 ++ (fragment0142316Field003Chars00 ++ (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0142316Field002Chars00 ++ (fragment0142316Field003Chars00 ++ (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))))))))) fragment0142316Acc00200 := object_fragment0142316_field_001 fuel (fragment0142316Field002Chars00 ++ (fragment0142316Field003Chars00 ++ (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0142316Field003Chars00 ++ (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail))))))))) fragment0142316Acc00300 := object_fragment0142316_field_002 fuel (fragment0142316Field003Chars00 ++ (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))))))) fragment0142316Acc00400 := object_fragment0142316_field_003 fuel (fragment0142316Field004Chars00 ++ (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail))))))) fragment0142316Acc00500 := object_fragment0142316_field_004 fuel (fragment0142316Field005Chars00 ++ (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))))) fragment0142316Acc00600 := object_fragment0142316_field_005 fuel (fragment0142316Field006Chars00 ++ (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail))))) fragment0142316Acc00700 := object_fragment0142316_field_006 fuel (fragment0142316Field007Chars00 ++ (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 393) (SourceJson.white (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))) fragment0142316Acc00800 := object_fragment0142316_field_007 fuel (fragment0142316Field008Chars00 ++ (fragment0142316Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 392) (SourceJson.white (fragment0142316Field009Chars00 ++ (tail))) fragment0142316Acc00900 := object_fragment0142316_field_008 fuel (fragment0142316Field009Chars00 ++ (tail))
    _ = .ok (fragment0142316Value, tail) := object_fragment0142316_field_009 fuel (tail)

noncomputable def fragment0144241Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0144241Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0144241Field000Value00 : SourceJson := .number (String.ofList ['1', '0'])
noncomputable def fragment0144241Acc00100 : List (String × SourceJson) := (fragment0144241Field000Key00, fragment0144241Field000Value00) :: fragment0144241Acc00000
noncomputable def fragment0144241Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', ',']

theorem object_fragment0144241_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0144241Field000Chars00 ++ tail)) fragment0144241Acc00000 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0144241Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_000"
  err.flush

noncomputable def fragment0144241Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0144241Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0144241Acc00200 : List (String × SourceJson) := (fragment0144241Field001Key00, fragment0144241Field001Value00) :: fragment0144241Acc00100
noncomputable def fragment0144241Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0144241_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0144241Field001Chars00 ++ tail)) fragment0144241Acc00100 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0144241Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_001"
  err.flush

noncomputable def fragment0144241Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0144241Field002Value00 : SourceJson := .str (String.ofList ['2', '4', '9', '6', '7', '2', '6', '3', '1', '1', '1', '3', '8', '6', '0', '7', '1', '4', '9', '3', '3', '1', '3', '8', '5', '3', '7', '5', '0', '9', '4', '5', '6', '8', '9', '4', '5', '9', '7', '9', '6', '3', '/', '1', '3', '9', '7', '5', '1', '3', '6', '0', '8', '8', '8', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0144241Acc00300 : List (String × SourceJson) := (fragment0144241Field002Key00, fragment0144241Field002Value00) :: fragment0144241Acc00200
noncomputable def fragment0144241Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '4', '9', '6', '7', '2', '6', '3', '1', '1', '1', '3', '8', '6', '0', '7', '1', '4', '9', '3', '3', '1', '3', '8', '5', '3', '7', '5', '0', '9', '4', '5', '6', '8', '9', '4', '5', '9', '7', '9', '6', '3', '/', '1', '3', '9', '7', '5', '1', '3', '6', '0', '8', '8', '8', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0144241_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0144241Field002Chars00 ++ tail)) fragment0144241Acc00200 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0144241Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_002"
  err.flush

noncomputable def fragment0144241Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0144241Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0144241Acc00400 : List (String × SourceJson) := (fragment0144241Field003Key00, fragment0144241Field003Value00) :: fragment0144241Acc00300
noncomputable def fragment0144241Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0144241_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0144241Field003Chars00 ++ tail)) fragment0144241Acc00300 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0144241Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_003"
  err.flush

noncomputable def fragment0144241Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0144241Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0144241Acc00500 : List (String × SourceJson) := (fragment0144241Field004Key00, fragment0144241Field004Value00) :: fragment0144241Acc00400
noncomputable def fragment0144241Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0144241_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0144241Field004Chars00 ++ tail)) fragment0144241Acc00400 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0144241Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_004"
  err.flush

noncomputable def fragment0144241Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0144241Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '6', '8', '5', '4', '2', '4', '7', '0', '8', '1', '3', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '3', '0', '7', '2', '9', '1', '3', '6', '1', '7', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '0', '6', '3', '1', '2', '5', '5', '3', '9', '5', '9', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '0', '7', '1', '6', '3', '7', '7', '0', '6', '2', '1', '/', '2', '2', '2', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '3', '4', '2', '6', '1', '1', '9', '3', '5', '1', '7', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '3', '4', '6', '8', '9', '1', '3', '0', '4', '3', '/', '1', '0', '1', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '2', '8', '7', '3', '9', '9', '7', '0', '5', '7', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '0', '9', '0', '2', '7', '8', '5', '9', '7', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '3', '3', '3', '3', '5', '8', '2', '7', '7', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '2', '5', '4', '0', '9', '4', '1', '6', '5', '1', '/', '5', '5', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0144241Acc00600 : List (String × SourceJson) := (fragment0144241Field005Key00, fragment0144241Field005Value00) :: fragment0144241Acc00500
noncomputable def fragment0144241Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '8', '5', '4', '2', '4', '7', '0', '8', '1', '3', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '3', '0', '7', '2', '9', '1', '3', '6', '1', '7', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '0', '6', '3', '1', '2', '5', '5', '3', '9', '5', '9', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '0', '7', '1', '6', '3', '7', '7', '0', '6', '2', '1', '/', '2', '2', '2', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '3', '4', '2', '6', '1', '1', '9', '3', '5', '1', '7', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '3', '4', '6', '8', '9', '1', '3', '0', '4', '3', '/', '1', '0', '1', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '2', '8', '7', '3', '9', '9', '7', '0', '5', '7', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '3', '0', '9', '0', '2', '7', '8', '5', '9', '7', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '3', '3', '3', '3', '5', '8', '2', '7', '7', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '2', '5', '4', '0', '9', '4', '1', '6', '5', '1', '/', '5', '5', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0144241_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0144241Field005Chars00 ++ tail)) fragment0144241Acc00500 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0144241Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_005"
  err.flush

noncomputable def fragment0144241Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0144241Field006Value00 : SourceJson := .str (String.ofList ['5', '7', '8', '3', '0', '9', '4', '8', '1', '0', '1', '2', '8', '9', '2', '8', '9', '6', '5', '6', '8', '7', '8', '9', '5', '6', '0', '0', '0', '8', '4', '1', '3', '3', '0', '0', '0', '8', '8', '2', '9', '5', '0', '6', '8', '0', '0', '/', '4', '3', '4', '3', '6', '3', '6', '9', '6', '5', '4', '4', '3', '5', '8', '4', '4', '3', '4', '2', '5', '7', '0', '6', '9', '1', '3', '9', '0', '9', '2', '8', '2', '0', '9', '6', '9', '0', '1', '2', '1', '4', '1', '7', '5', '4', '1', '3', '0', '1', '8', '9', '4', '1', '2', '1', '5', '9', '7', '0', '1', '8', '1'])
noncomputable def fragment0144241Acc00700 : List (String × SourceJson) := (fragment0144241Field006Key00, fragment0144241Field006Value00) :: fragment0144241Acc00600
noncomputable def fragment0144241Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '7', '8', '3', '0', '9', '4', '8', '1', '0', '1', '2', '8', '9', '2', '8', '9', '6', '5', '6', '8', '7', '8', '9', '5', '6', '0', '0', '0', '8', '4', '1', '3', '3', '0', '0', '0', '8', '8', '2', '9', '5', '0', '6', '8', '0', '0', '/', '4', '3', '4', '3', '6', '3', '6', '9', '6', '5', '4', '4', '3', '5', '8', '4', '4', '3', '4', '2', '5', '7', '0', '6', '9', '1', '3', '9', '0', '9', '2', '8', '2', '0', '9', '6', '9', '0', '1', '2', '1', '4', '1', '7', '5', '4', '1', '3', '0', '1', '8', '9', '4', '1', '2', '1', '5', '9', '7', '0', '1', '8', '1', '"', ',']

theorem object_fragment0144241_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0144241Field006Chars00 ++ tail)) fragment0144241Acc00600 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0144241Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_006"
  err.flush

noncomputable def fragment0144241Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0144241Field007Value00 : SourceJson := .str (String.ofList ['3', '6', '7', '1', '7', '1', '7', '8', '3', '9', '1', '0', '4', '8', '0', '1', '7', '3', '3', '7', '9', '7', '8', '1', '4', '5', '9', '3', '1', '0', '2', '5', '0', '6', '1', '3', '4', '9', '7', '8', '6', '1', '5', '1', '0', '5', '0', '4', '3', '0', '1', '8', '1', '8', '6', '4', '2', '2', '7', '4', '8', '2', '6', '3', '8', '4', '7', '0', '0', '5', '8', '9', '2', '4', '9', '9', '3', '0', '4', '4', '4', '8', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '0', '8', '9', '2', '2', '3', '7', '5', '0', '9', '7', '3', '7', '6', '6', '0', '0', '9', '0', '1', '5', '9', '5', '5', '0', '4', '3', '7', '8', '8', '9', '1', '2', '0', '9', '1', '9', '0', '1', '1', '2', '2', '0', '4', '3', '9', '3', '0', '8', '1', '9', '7', '8', '4', '8', '4', '3', '9', '7', '1', '5', '6', '5', '0', '7', '2', '4', '3', '3', '1', '7', '7', '7', '7', '2', '3', '2', '0', '7', '1', '8', '8', '7', '6', '9', '7', '6', '8', '2', '3', '3', '5', '2', '2', '5', '2', '2', '0', '8', '9', '8', '7', '8', '9', '8', '8', '9', '9', '7', '9', '0', '0', '6', '1', '8', '7', '3', '9', '8', '7'])
noncomputable def fragment0144241Acc00800 : List (String × SourceJson) := (fragment0144241Field007Key00, fragment0144241Field007Value00) :: fragment0144241Acc00700
noncomputable def fragment0144241Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '6', '7', '1', '7', '1', '7', '8', '3', '9', '1', '0', '4', '8', '0', '1', '7', '3', '3', '7', '9', '7', '8', '1', '4', '5', '9', '3', '1', '0', '2', '5', '0', '6', '1', '3', '4', '9', '7', '8', '6', '1', '5', '1', '0', '5', '0', '4', '3', '0', '1', '8', '1', '8', '6', '4', '2', '2', '7', '4', '8', '2', '6', '3', '8', '4', '7', '0', '0', '5', '8', '9', '2', '4', '9', '9', '3', '0', '4', '4', '4', '8', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '0', '8', '9', '2', '2', '3', '7', '5', '0', '9', '7', '3', '7', '6', '6', '0', '0', '9', '0', '1', '5', '9', '5', '5', '0', '4', '3', '7', '8', '8', '9', '1', '2', '0', '9', '1', '9', '0', '1', '1', '2', '2', '0', '4', '3', '9', '3', '0', '8', '1', '9', '7', '8', '4', '8', '4', '3', '9', '7', '1', '5', '6', '5', '0', '7', '2', '4', '3', '3', '1', '7', '7', '7', '7', '2', '3', '2', '0', '7', '1', '8', '8', '7', '6', '9', '7', '6', '8', '2', '3', '3', '5', '2', '2', '5', '2', '2', '0', '8', '9', '8', '7', '8', '9', '8', '8', '9', '9', '7', '9', '0', '0', '6', '1', '8', '7', '3', '9', '8', '7', '"', ',']

theorem object_fragment0144241_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0144241Field007Chars00 ++ tail)) fragment0144241Acc00700 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0144241Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_007"
  err.flush

noncomputable def fragment0144241Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0144241Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '5', '4', '8', '3', '9', '4', '7', '9', '2', '1', '3', '9'])
noncomputable def fragment0144241Acc00900 : List (String × SourceJson) := (fragment0144241Field008Key00, fragment0144241Field008Value00) :: fragment0144241Acc00800
noncomputable def fragment0144241Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '5', '4', '8', '3', '9', '4', '7', '9', '2', '1', '3', '9', '"', ',']

theorem object_fragment0144241_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0144241Field008Chars00 ++ tail)) fragment0144241Acc00800 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0144241Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_008"
  err.flush

noncomputable def fragment0144241Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0144241Field009Value00 : SourceJson := .str (String.ofList ['4', '7', '7', '7', '3', '4', '8', '7', '9', '7', '8', '1', '0', '2'])
noncomputable def fragment0144241Acc01000 : List (String × SourceJson) := (fragment0144241Field009Key00, fragment0144241Field009Value00) :: fragment0144241Acc00900
noncomputable def fragment0144241Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '7', '7', '7', '3', '4', '8', '7', '9', '7', '8', '1', '0', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0144241_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0144241Field009Chars00 ++ tail)) fragment0144241Acc00900 =
      .ok (.obj (fragment0144241Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0144241_object_field_009"
  err.flush

noncomputable def fragment0144241Chars : List Char := '{' :: (fragment0144241Field000Chars00 ++ fragment0144241Field001Chars00 ++ fragment0144241Field002Chars00 ++ fragment0144241Field003Chars00 ++ fragment0144241Field004Chars00 ++ fragment0144241Field005Chars00 ++ fragment0144241Field006Chars00 ++ fragment0144241Field007Chars00 ++ fragment0144241Field008Chars00 ++ fragment0144241Field009Chars00)
noncomputable def fragment0144241Value : SourceJson := .obj (fragment0144241Acc01000.reverse)

theorem value_fragment0144241 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 239) (fragment0144241Chars ++ tail) =
      .ok (fragment0144241Value, tail) := by
  have hinput : fragment0144241Chars ++ tail = '{' :: (fragment0144241Field000Chars00 ++ (fragment0144241Field001Chars00 ++ (fragment0144241Field002Chars00 ++ (fragment0144241Field003Chars00 ++ (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0144241Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 239) (fragment0144241Chars ++ tail) =
        SourceJson.value (fuel + 239) ('{' :: (fragment0144241Field000Chars00 ++ (fragment0144241Field001Chars00 ++ (fragment0144241Field002Chars00 ++ (fragment0144241Field003Chars00 ++ (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 239)) hinput
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0144241Field000Chars00 ++ (fragment0144241Field001Chars00 ++ (fragment0144241Field002Chars00 ++ (fragment0144241Field003Chars00 ++ (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))))))))))) fragment0144241Acc00000 := by rfl
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0144241Field001Chars00 ++ (fragment0144241Field002Chars00 ++ (fragment0144241Field003Chars00 ++ (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail))))))))))) fragment0144241Acc00100 := object_fragment0144241_field_000 fuel (fragment0144241Field001Chars00 ++ (fragment0144241Field002Chars00 ++ (fragment0144241Field003Chars00 ++ (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0144241Field002Chars00 ++ (fragment0144241Field003Chars00 ++ (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))))))))) fragment0144241Acc00200 := object_fragment0144241_field_001 fuel (fragment0144241Field002Chars00 ++ (fragment0144241Field003Chars00 ++ (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0144241Field003Chars00 ++ (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail))))))))) fragment0144241Acc00300 := object_fragment0144241_field_002 fuel (fragment0144241Field003Chars00 ++ (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))))))) fragment0144241Acc00400 := object_fragment0144241_field_003 fuel (fragment0144241Field004Chars00 ++ (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail))))))) fragment0144241Acc00500 := object_fragment0144241_field_004 fuel (fragment0144241Field005Chars00 ++ (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))))) fragment0144241Acc00600 := object_fragment0144241_field_005 fuel (fragment0144241Field006Chars00 ++ (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail))))) fragment0144241Acc00700 := object_fragment0144241_field_006 fuel (fragment0144241Field007Chars00 ++ (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))) fragment0144241Acc00800 := object_fragment0144241_field_007 fuel (fragment0144241Field008Chars00 ++ (fragment0144241Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0144241Field009Chars00 ++ (tail))) fragment0144241Acc00900 := object_fragment0144241_field_008 fuel (fragment0144241Field009Chars00 ++ (tail))
    _ = .ok (fragment0144241Value, tail) := object_fragment0144241_field_009 fuel (tail)

noncomputable def fragment0145849Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0145849Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0145849Field000Value00 : SourceJson := .number (String.ofList ['1', '1'])
noncomputable def fragment0145849Acc00100 : List (String × SourceJson) := (fragment0145849Field000Key00, fragment0145849Field000Value00) :: fragment0145849Acc00000
noncomputable def fragment0145849Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '1', ',']

theorem object_fragment0145849_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 403) (SourceJson.white (fragment0145849Field000Chars00 ++ tail)) fragment0145849Acc00000 =
      SourceJson.object (fuel + 402) (SourceJson.white tail) fragment0145849Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_000"
  err.flush

noncomputable def fragment0145849Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0145849Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['3']), .number (String.ofList ['0'])]
noncomputable def fragment0145849Acc00200 : List (String × SourceJson) := (fragment0145849Field001Key00, fragment0145849Field001Value00) :: fragment0145849Acc00100
noncomputable def fragment0145849Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0145849_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 402) (SourceJson.white (fragment0145849Field001Chars00 ++ tail)) fragment0145849Acc00100 =
      SourceJson.object (fuel + 401) (SourceJson.white tail) fragment0145849Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_001"
  err.flush

noncomputable def fragment0145849Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0145849Field002Value00 : SourceJson := .str (String.ofList ['7', '4', '7', '8', '1', '6', '6', '8', '7', '7', '3', '7', '3', '6', '4', '8', '7', '0', '5', '5', '6', '7', '1', '9', '4', '0', '5', '5', '2', '5', '9', '1', '7', '8', '6', '7', '9', '5', '5', '8', '1', '0', '7', '/', '1', '2', '5', '8', '9', '6', '4', '7', '4', '7', '5', '5', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0145849Acc00300 : List (String × SourceJson) := (fragment0145849Field002Key00, fragment0145849Field002Value00) :: fragment0145849Acc00200
noncomputable def fragment0145849Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '7', '4', '7', '8', '1', '6', '6', '8', '7', '7', '3', '7', '3', '6', '4', '8', '7', '0', '5', '5', '6', '7', '1', '9', '4', '0', '5', '5', '2', '5', '9', '1', '7', '8', '6', '7', '9', '5', '5', '8', '1', '0', '7', '/', '1', '2', '5', '8', '9', '6', '4', '7', '4', '7', '5', '5', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0145849_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 401) (SourceJson.white (fragment0145849Field002Chars00 ++ tail)) fragment0145849Acc00200 =
      SourceJson.object (fuel + 400) (SourceJson.white tail) fragment0145849Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_002"
  err.flush

noncomputable def fragment0145849Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0145849Field003Value00 : SourceJson := .str (String.ofList ['3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0145849Acc00400 : List (String × SourceJson) := (fragment0145849Field003Key00, fragment0145849Field003Value00) :: fragment0145849Acc00300
noncomputable def fragment0145849Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '3', '1', '7', '2', '9', '3', '8', '7', '/', '2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0145849_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 400) (SourceJson.white (fragment0145849Field003Chars00 ++ tail)) fragment0145849Acc00300 =
      SourceJson.object (fuel + 399) (SourceJson.white tail) fragment0145849Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_003"
  err.flush

noncomputable def fragment0145849Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0145849Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0145849Acc00500 : List (String × SourceJson) := (fragment0145849Field004Key00, fragment0145849Field004Value00) :: fragment0145849Acc00400
noncomputable def fragment0145849Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0145849_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 399) (SourceJson.white (fragment0145849Field004Chars00 ++ tail)) fragment0145849Acc00400 =
      SourceJson.object (fuel + 398) (SourceJson.white tail) fragment0145849Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_004"
  err.flush

noncomputable def fragment0145849Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0145849Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '4', '9', '9', '2', '8', '7', '7', '2', '7', '6', '8', '0', '8', '1', '3', '5', '0', '1', '2', '9', '/', '1', '2', '6', '6', '9', '7', '5', '3', '6', '4', '3', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '0', '8', '5', '5', '7', '4', '3', '5', '2', '6', '9', '5', '7', '0', '1', '1', '3', '4', '7', '/', '2', '5', '3', '3', '9', '5', '0', '7', '2', '8', '6', '1', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '1', '4', '4', '1', '2', '2', '7', '5', '8', '6', '7', '9', '8', '4', '0', '4', '3', '2', '2', '3', '/', '5', '0', '6', '7', '9', '0', '1', '4', '5', '7', '2', '2', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '3', '9', '7', '8', '2', '6', '2', '7', '7', '0', '9', '2', '5', '7', '6', '7', '8', '1', '7', '/', '1', '0', '1', '3', '5', '8', '0', '2', '9', '1', '4', '4', '4', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '0', '4', '1', '1', '5', '6', '9', '0', '1', '3', '2', '2', '0', '8', '9', '9', '1', '6', '1', '/', '5', '6', '3', '1', '0', '0', '1', '6', '1', '9', '1', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '8', '2', '3', '4', '7', '9', '9', '5', '2', '3', '9', '9', '3', '0', '8', '4', '7', '1', '/', '4', '6', '0', '7', '1', '8', '3', '1', '4', '2', '9', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '3', '2', '6', '5', '9', '6', '3', '5', '6', '3', '8', '2', '6', '3', '2', '1', '8', '9', '/', '6', '5', '8', '1', '6', '9', '0', '2', '0', '4', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '8', '8', '8', '8', '8', '8', '0', '5', '9', '8', '0', '3', '2', '4', '1', '0', '3', '/', '4', '6', '0', '7', '1', '8', '3', '1', '4', '2', '9', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '2', '4', '1', '4', '8', '9', '2', '4', '1', '4', '3', '0', '1', '5', '4', '9', '/', '8', '9', '9', '8', '4', '0', '4', '5', '7', '6', '0', '3', '2', '8', '1', '2', '5', '0', '0']), .str (String.ofList ['9', '1', '5', '8', '9', '7', '2', '8', '4', '4', '4', '7', '5', '9', '8', '2', '6', '7', '8', '3', '/', '2', '8', '1', '5', '5', '0', '0', '8', '0', '9', '5', '6', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0145849Acc00600 : List (String × SourceJson) := (fragment0145849Field005Key00, fragment0145849Field005Value00) :: fragment0145849Acc00500
noncomputable def fragment0145849Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '4', '9', '9', '2', '8', '7', '7', '2', '7', '6', '8', '0', '8', '1', '3', '5', '0', '1', '2', '9', '/', '1', '2', '6', '6', '9', '7', '5', '3', '6', '4', '3', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '0', '8', '5', '5', '7', '4', '3', '5', '2', '6', '9', '5', '7', '0', '1', '1', '3', '4', '7', '/', '2', '5', '3', '3', '9', '5', '0', '7', '2', '8', '6', '1', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '1', '4', '4', '1', '2', '2', '7', '5', '8', '6', '7', '9', '8', '4', '0', '4', '3', '2', '2', '3', '/', '5', '0', '6', '7', '9', '0', '1', '4', '5', '7', '2', '2', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '3', '9', '7', '8', '2', '6', '2', '7', '7', '0', '9', '2', '5', '7', '6', '7', '8', '1', '7', '/', '1', '0', '1', '3', '5', '8', '0', '2', '9', '1', '4', '4', '4', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '8', '0', '4', '1', '1', '5', '6', '9', '0', '1', '3', '2', '2', '0', '8', '9', '9', '1', '6', '1', '/', '5', '6', '3', '1', '0', '0', '1', '6', '1', '9', '1', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '0', '8', '2', '3', '4', '7', '9', '9', '5', '2', '3', '9', '9', '3', '0', '8', '4', '7', '1', '/', '4', '6', '0', '7', '1', '8', '3', '1', '4', '2', '9', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '5', '3', '2', '6', '5', '9', '6', '3', '5', '6', '3', '8', '2', '6', '3', '2', '1', '8', '9', '/', '6', '5', '8', '1', '6', '9', '0', '2', '0', '4', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '2', '8', '8', '8', '8', '8', '8', '0', '5', '9', '8', '0', '3', '2', '4', '1', '0', '3', '/', '4', '6', '0', '7', '1', '8', '3', '1', '4', '2', '9', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '2', '4', '1', '4', '8', '9', '2', '4', '1', '4', '3', '0', '1', '5', '4', '9', '/', '8', '9', '9', '8', '4', '0', '4', '5', '7', '6', '0', '3', '2', '8', '1', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '1', '5', '8', '9', '7', '2', '8', '4', '4', '4', '7', '5', '9', '8', '2', '6', '7', '8', '3', '/', '2', '8', '1', '5', '5', '0', '0', '8', '0', '9', '5', '6', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0145849_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 398) (SourceJson.white (fragment0145849Field005Chars00 ++ tail)) fragment0145849Acc00500 =
      SourceJson.object (fuel + 397) (SourceJson.white tail) fragment0145849Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_005"
  err.flush

noncomputable def fragment0145849Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0145849Field006Value00 : SourceJson := .str (String.ofList ['3', '6', '5', '0', '4', '2', '5', '3', '9', '8', '5', '0', '4', '1', '5', '4', '5', '1', '3', '5', '5', '3', '7', '0', '0', '8', '4', '1', '2', '8', '3', '3', '5', '1', '7', '7', '8', '8', '5', '9', '2', '0', '2', '5', '5', '3', '6', '9', '8', '6', '0', '0', '0', '0', '0', '/', '3', '5', '7', '4', '6', '9', '5', '2', '1', '0', '2', '6', '9', '3', '7', '5', '1', '7', '4', '5', '5', '7', '8', '9', '0', '4', '6', '3', '2', '5', '4', '7', '5', '0', '4', '9', '6', '3', '6', '5', '5', '7', '6', '2', '2', '6', '3', '8', '6', '8', '9', '6', '6', '3', '8', '4', '3', '6', '4', '3', '4', '7', '1', '0', '7', '4', '7'])
noncomputable def fragment0145849Acc00700 : List (String × SourceJson) := (fragment0145849Field006Key00, fragment0145849Field006Value00) :: fragment0145849Acc00600
noncomputable def fragment0145849Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '6', '5', '0', '4', '2', '5', '3', '9', '8', '5', '0', '4', '1', '5', '4', '5', '1', '3', '5', '5', '3', '7', '0', '0', '8', '4', '1', '2', '8', '3', '3', '5', '1', '7', '7', '8', '8', '5', '9', '2', '0', '2', '5', '5', '3', '6', '9', '8', '6', '0', '0', '0', '0', '0', '/', '3', '5', '7', '4', '6', '9', '5', '2', '1', '0', '2', '6', '9', '3', '7', '5', '1', '7', '4', '5', '5', '7', '8', '9', '0', '4', '6', '3', '2', '5', '4', '7', '5', '0', '4', '9', '6', '3', '6', '5', '5', '7', '6', '2', '2', '6', '3', '8', '6', '8', '9', '6', '6', '3', '8', '4', '3', '6', '4', '3', '4', '7', '1', '0', '7', '4', '7', '"', ',']

theorem object_fragment0145849_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 397) (SourceJson.white (fragment0145849Field006Chars00 ++ tail)) fragment0145849Acc00600 =
      SourceJson.object (fuel + 396) (SourceJson.white tail) fragment0145849Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_006"
  err.flush

noncomputable def fragment0145849Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0145849Field007Value00 : SourceJson := .str (String.ofList ['6', '0', '3', '1', '7', '0', '5', '9', '5', '3', '3', '2', '8', '7', '4', '1', '6', '3', '1', '7', '7', '8', '6', '3', '0', '1', '2', '1', '9', '0', '9', '0', '7', '2', '1', '4', '0', '3', '0', '7', '7', '4', '6', '2', '7', '6', '8', '5', '1', '0', '3', '0', '9', '8', '0', '3', '6', '9', '4', '8', '5', '3', '8', '7', '8', '7', '0', '1', '9', '8', '2', '1', '9', '0', '6', '4', '5', '1', '2', '1', '6', '1', '8', '0', '1', '3', '1', '8', '4', '1', '7', '6', '4', '4', '4', '2', '3', '4', '0', '4', '5', '9', '7', '5', '0', '4', '9', '5', '9', '7', '1', '3', '0', '6', '9', '1', '7', '2', '4', '5', '8', '3', '4', '3', '6', '5', '9', '7', '8', '6', '1', '1', '5', '2', '7', '9', '7', '4', '2', '0', '9', '2', '1', '6', '0', '7', '3', '0', '7', '1', '5', '5', '9', '8', '3', '1', '6', '6', '6', '8', '0', '2', '6', '2', '4', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '6', '3', '0', '4', '9', '2', '5', '0', '8', '8', '0', '1', '2', '5', '2', '8', '0', '2', '6', '3', '9', '7', '5', '8', '0', '4', '9', '2', '8', '5', '7', '0', '0', '4', '5', '0', '7', '7', '4', '0', '1', '4', '3', '4', '0', '5', '0', '8', '5', '4', '7', '7', '0', '3', '5', '0', '5', '7', '9', '7', '0', '9', '1', '9', '6', '7', '6', '7', '5', '9', '4', '7', '3', '9', '8', '3', '9', '9', '9', '5', '5', '6', '5', '7', '9', '2', '5', '5', '1', '6', '1', '3', '6', '6', '4', '2', '3', '7', '4', '4', '6', '5', '5', '6', '1', '9', '6', '2', '2', '3', '4', '7', '8', '8', '7', '7', '5', '7', '7', '7', '3', '7', '1', '4', '2', '1', '5', '0', '3', '0', '6', '5', '9', '4', '9', '7', '5', '6', '0', '5', '9', '6', '3', '4', '7', '4', '1', '1', '6', '6', '6', '1', '6', '3', '9', '3', '1', '4', '2', '8', '8', '8', '5', '5', '7', '8', '2', '0', '4', '9', '1', '2', '1', '0', '4', '7', '5', '9', '6', '2', '9', '6', '4', '5', '6', '3', '4', '1', '3', '8', '8', '0', '2', '6', '8', '5', '1', '7', '7', '9'])
noncomputable def fragment0145849Acc00800 : List (String × SourceJson) := (fragment0145849Field007Key00, fragment0145849Field007Value00) :: fragment0145849Acc00700
noncomputable def fragment0145849Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '0', '3', '1', '7', '0', '5', '9', '5', '3', '3', '2', '8', '7', '4', '1', '6', '3', '1', '7', '7', '8', '6', '3', '0', '1', '2', '1', '9', '0', '9', '0', '7', '2', '1', '4', '0', '3', '0', '7', '7', '4', '6', '2', '7', '6', '8', '5', '1', '0', '3', '0', '9', '8', '0', '3', '6', '9', '4', '8', '5', '3', '8', '7', '8', '7', '0', '1', '9', '8', '2', '1', '9', '0', '6', '4', '5', '1', '2', '1', '6', '1', '8', '0', '1', '3', '1', '8', '4', '1', '7', '6', '4', '4', '4', '2', '3', '4', '0', '4', '5', '9', '7', '5', '0', '4', '9', '5', '9', '7', '1', '3', '0', '6', '9', '1', '7', '2', '4', '5', '8', '3', '4', '3', '6', '5', '9', '7', '8', '6', '1', '1', '5', '2', '7', '9', '7', '4', '2', '0', '9', '2', '1', '6', '0', '7', '3', '0', '7', '1', '5', '5', '9', '8', '3', '1', '6', '6', '6', '8', '0', '2', '6', '2', '4', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '6', '3', '0', '4', '9', '2', '5', '0', '8', '8', '0', '1', '2', '5', '2', '8', '0', '2', '6', '3', '9', '7', '5', '8', '0', '4', '9', '2', '8', '5', '7', '0', '0', '4', '5', '0', '7', '7', '4', '0', '1', '4', '3', '4', '0', '5', '0', '8', '5', '4', '7', '7', '0', '3', '5', '0', '5', '7', '9', '7', '0', '9', '1', '9', '6', '7', '6', '7', '5', '9', '4', '7', '3', '9', '8', '3', '9', '9', '9', '5', '5', '6', '5', '7', '9', '2', '5', '5', '1', '6', '1', '3', '6', '6', '4', '2', '3', '7', '4', '4', '6', '5', '5', '6', '1', '9', '6', '2', '2', '3', '4', '7', '8', '8', '7', '7', '5', '7', '7', '7', '3', '7', '1', '4', '2', '1', '5', '0', '3', '0', '6', '5', '9', '4', '9', '7', '5', '6', '0', '5', '9', '6', '3', '4', '7', '4', '1', '1', '6', '6', '6', '1', '6', '3', '9', '3', '1', '4', '2', '8', '8', '8', '5', '5', '7', '8', '2', '0', '4', '9', '1', '2', '1', '0', '4', '7', '5', '9', '6', '2', '9', '6', '4', '5', '6', '3', '4', '1', '3', '8', '8', '0', '2', '6', '8', '5', '1', '7', '7', '9', '"', ',']

theorem object_fragment0145849_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 396) (SourceJson.white (fragment0145849Field007Chars00 ++ tail)) fragment0145849Acc00700 =
      SourceJson.object (fuel + 395) (SourceJson.white tail) fragment0145849Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_007"
  err.flush

noncomputable def fragment0145849Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0145849Field008Value00 : SourceJson := .str (String.ofList ['8', '0', '9', '0', '6', '6', '1', '7', '1', '2', '5', '8', '5', '3', '1', '0', '9'])
noncomputable def fragment0145849Acc00900 : List (String × SourceJson) := (fragment0145849Field008Key00, fragment0145849Field008Value00) :: fragment0145849Acc00800
noncomputable def fragment0145849Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '0', '9', '0', '6', '6', '1', '7', '1', '2', '5', '8', '5', '3', '1', '0', '9', '"', ',']

theorem object_fragment0145849_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 395) (SourceJson.white (fragment0145849Field008Chars00 ++ tail)) fragment0145849Acc00800 =
      SourceJson.object (fuel + 394) (SourceJson.white tail) fragment0145849Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_008"
  err.flush

noncomputable def fragment0145849Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0145849Field009Value00 : SourceJson := .str (String.ofList ['3', '2', '6', '6', '3', '3', '5', '5', '6', '0', '6', '1', '8', '3', '9', '2', '0', '1'])
noncomputable def fragment0145849Acc01000 : List (String × SourceJson) := (fragment0145849Field009Key00, fragment0145849Field009Value00) :: fragment0145849Acc00900
noncomputable def fragment0145849Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '2', '6', '6', '3', '3', '5', '5', '6', '0', '6', '1', '8', '3', '9', '2', '0', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0145849_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 394) (SourceJson.white (fragment0145849Field009Chars00 ++ tail)) fragment0145849Acc00900 =
      .ok (.obj (fragment0145849Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0145849_object_field_009"
  err.flush

noncomputable def fragment0145849Chars : List Char := '{' :: (fragment0145849Field000Chars00 ++ fragment0145849Field001Chars00 ++ fragment0145849Field002Chars00 ++ fragment0145849Field003Chars00 ++ fragment0145849Field004Chars00 ++ fragment0145849Field005Chars00 ++ fragment0145849Field006Chars00 ++ fragment0145849Field007Chars00 ++ fragment0145849Field008Chars00 ++ fragment0145849Field009Chars00)
noncomputable def fragment0145849Value : SourceJson := .obj (fragment0145849Acc01000.reverse)

theorem value_fragment0145849 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 404) (fragment0145849Chars ++ tail) =
      .ok (fragment0145849Value, tail) := by
  have hinput : fragment0145849Chars ++ tail = '{' :: (fragment0145849Field000Chars00 ++ (fragment0145849Field001Chars00 ++ (fragment0145849Field002Chars00 ++ (fragment0145849Field003Chars00 ++ (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0145849Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 404) (fragment0145849Chars ++ tail) =
        SourceJson.value (fuel + 404) ('{' :: (fragment0145849Field000Chars00 ++ (fragment0145849Field001Chars00 ++ (fragment0145849Field002Chars00 ++ (fragment0145849Field003Chars00 ++ (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 404)) hinput
    _ = SourceJson.object (fuel + 403) (SourceJson.white (fragment0145849Field000Chars00 ++ (fragment0145849Field001Chars00 ++ (fragment0145849Field002Chars00 ++ (fragment0145849Field003Chars00 ++ (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))))))))))) fragment0145849Acc00000 := by rfl
    _ = SourceJson.object (fuel + 402) (SourceJson.white (fragment0145849Field001Chars00 ++ (fragment0145849Field002Chars00 ++ (fragment0145849Field003Chars00 ++ (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail))))))))))) fragment0145849Acc00100 := object_fragment0145849_field_000 fuel (fragment0145849Field001Chars00 ++ (fragment0145849Field002Chars00 ++ (fragment0145849Field003Chars00 ++ (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 401) (SourceJson.white (fragment0145849Field002Chars00 ++ (fragment0145849Field003Chars00 ++ (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))))))))) fragment0145849Acc00200 := object_fragment0145849_field_001 fuel (fragment0145849Field002Chars00 ++ (fragment0145849Field003Chars00 ++ (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 400) (SourceJson.white (fragment0145849Field003Chars00 ++ (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail))))))))) fragment0145849Acc00300 := object_fragment0145849_field_002 fuel (fragment0145849Field003Chars00 ++ (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 399) (SourceJson.white (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))))))) fragment0145849Acc00400 := object_fragment0145849_field_003 fuel (fragment0145849Field004Chars00 ++ (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 398) (SourceJson.white (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail))))))) fragment0145849Acc00500 := object_fragment0145849_field_004 fuel (fragment0145849Field005Chars00 ++ (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 397) (SourceJson.white (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))))) fragment0145849Acc00600 := object_fragment0145849_field_005 fuel (fragment0145849Field006Chars00 ++ (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 396) (SourceJson.white (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail))))) fragment0145849Acc00700 := object_fragment0145849_field_006 fuel (fragment0145849Field007Chars00 ++ (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 395) (SourceJson.white (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))) fragment0145849Acc00800 := object_fragment0145849_field_007 fuel (fragment0145849Field008Chars00 ++ (fragment0145849Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 394) (SourceJson.white (fragment0145849Field009Chars00 ++ (tail))) fragment0145849Acc00900 := object_fragment0145849_field_008 fuel (fragment0145849Field009Chars00 ++ (tail))
    _ = .ok (fragment0145849Value, tail) := object_fragment0145849_field_009 fuel (tail)

noncomputable def fragment0147801Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0147801Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0147801Field000Value00 : SourceJson := .number (String.ofList ['1', '2'])
noncomputable def fragment0147801Acc00100 : List (String × SourceJson) := (fragment0147801Field000Key00, fragment0147801Field000Value00) :: fragment0147801Acc00000
noncomputable def fragment0147801Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '2', ',']

theorem object_fragment0147801_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0147801Field000Chars00 ++ tail)) fragment0147801Acc00000 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0147801Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_000"
  err.flush

noncomputable def fragment0147801Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0147801Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0147801Acc00200 : List (String × SourceJson) := (fragment0147801Field001Key00, fragment0147801Field001Value00) :: fragment0147801Acc00100
noncomputable def fragment0147801Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0147801_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0147801Field001Chars00 ++ tail)) fragment0147801Acc00100 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0147801Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_001"
  err.flush

noncomputable def fragment0147801Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0147801Field002Value00 : SourceJson := .str (String.ofList ['4', '5', '5', '0', '9', '5', '7', '8', '1', '3', '2', '8', '3', '8', '2', '6', '8', '8', '5', '9', '0', '3', '6', '3', '4', '5', '9', '2', '8', '7', '3', '8', '3', '8', '5', '5', '9', '5', '3', '5', '3', '6', '1', '1', '1', '9', '1', '/', '1', '7', '3', '9', '1', '2', '8', '0', '4', '6', '6', '1', '6', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0147801Acc00300 : List (String × SourceJson) := (fragment0147801Field002Key00, fragment0147801Field002Value00) :: fragment0147801Acc00200
noncomputable def fragment0147801Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '5', '5', '0', '9', '5', '7', '8', '1', '3', '2', '8', '3', '8', '2', '6', '8', '8', '5', '9', '0', '3', '6', '3', '4', '5', '9', '2', '8', '7', '3', '8', '3', '8', '5', '5', '9', '5', '3', '5', '3', '6', '1', '1', '1', '9', '1', '/', '1', '7', '3', '9', '1', '2', '8', '0', '4', '6', '6', '1', '6', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0147801_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0147801Field002Chars00 ++ tail)) fragment0147801Acc00200 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0147801Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_002"
  err.flush

noncomputable def fragment0147801Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0147801Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0147801Acc00400 : List (String × SourceJson) := (fragment0147801Field003Key00, fragment0147801Field003Value00) :: fragment0147801Acc00300
noncomputable def fragment0147801Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0147801_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0147801Field003Chars00 ++ tail)) fragment0147801Acc00300 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0147801Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_003"
  err.flush

noncomputable def fragment0147801Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0147801Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0147801Acc00500 : List (String × SourceJson) := (fragment0147801Field004Key00, fragment0147801Field004Value00) :: fragment0147801Acc00400
noncomputable def fragment0147801Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0147801_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0147801Field004Chars00 ++ tail)) fragment0147801Acc00400 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0147801Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_004"
  err.flush

noncomputable def fragment0147801Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0147801Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '6', '8', '5', '4', '3', '5', '3', '2', '0', '9', '3', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '3', '0', '7', '3', '9', '7', '4', '8', '9', '7', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '0', '6', '3', '1', '3', '6', '1', '5', '2', '3', '9', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '1', '4', '3', '2', '7', '1', '1', '6', '7', '3', '/', '4', '4', '5', '7', '3', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '3', '4', '2', '6', '0', '1', '3', '2', '2', '3', '7', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '3', '4', '6', '8', '8', '1', '6', '5', '6', '3', '/', '1', '0', '1', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '3', '7', '7', '1', '3', '0', '7', '3', '/', '3', '6', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '0', '4', '5', '3', '0', '5', '4', '9', '/', '6', '3', '3', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '3', '3', '3', '1', '1', '7', '0', '7', '7', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '2', '5', '4', '2', '0', '0', '2', '9', '3', '1', '/', '5', '5', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0147801Acc00600 : List (String × SourceJson) := (fragment0147801Field005Key00, fragment0147801Field005Value00) :: fragment0147801Acc00500
noncomputable def fragment0147801Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '6', '8', '5', '4', '3', '5', '3', '2', '0', '9', '3', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '3', '0', '7', '3', '9', '7', '4', '8', '9', '7', '/', '1', '8', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '0', '6', '3', '1', '3', '6', '1', '5', '2', '3', '9', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '1', '4', '3', '2', '7', '1', '1', '6', '7', '3', '/', '4', '4', '5', '7', '3', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '4', '3', '4', '2', '6', '0', '1', '3', '2', '2', '3', '7', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '3', '4', '6', '8', '8', '1', '6', '5', '6', '3', '/', '1', '0', '1', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '1', '3', '7', '7', '1', '3', '0', '7', '3', '/', '3', '6', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '5', '0', '4', '5', '3', '0', '5', '4', '9', '/', '6', '3', '3', '1', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '0', '3', '3', '3', '1', '1', '7', '0', '7', '7', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '8', '2', '5', '4', '2', '0', '0', '2', '9', '3', '1', '/', '5', '5', '7', '1', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0147801_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0147801Field005Chars00 ++ tail)) fragment0147801Acc00500 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0147801Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_005"
  err.flush

noncomputable def fragment0147801Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0147801Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '7', '1', '5', '3', '8', '4', '8', '8', '2', '1', '5', '6', '9', '6', '0', '9', '4', '1', '9', '5', '8', '7', '6', '6', '4', '0', '5', '6', '3', '2', '9', '5', '2', '7', '6', '9', '6', '4', '6', '7', '2', '1', '1', '5', '0', '1', '5', '2', '1', '6', '7', '5', '/', '6', '5', '2', '0', '2', '4', '5', '0', '2', '4', '7', '8', '3', '9', '8', '4', '8', '6', '6', '0', '6', '6', '5', '1', '6', '1', '0', '0', '6', '0', '8', '8', '1', '1', '6', '5', '5', '6', '3', '6', '4', '3', '4', '6', '9', '7', '8', '2', '3', '4', '0', '7', '4', '0', '2', '9', '7', '6', '6', '3', '8', '4', '5', '4', '7'])
noncomputable def fragment0147801Acc00700 : List (String × SourceJson) := (fragment0147801Field006Key00, fragment0147801Field006Value00) :: fragment0147801Acc00600
noncomputable def fragment0147801Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '7', '1', '5', '3', '8', '4', '8', '8', '2', '1', '5', '6', '9', '6', '0', '9', '4', '1', '9', '5', '8', '7', '6', '6', '4', '0', '5', '6', '3', '2', '9', '5', '2', '7', '6', '9', '6', '4', '6', '7', '2', '1', '1', '5', '0', '1', '5', '2', '1', '6', '7', '5', '/', '6', '5', '2', '0', '2', '4', '5', '0', '2', '4', '7', '8', '3', '9', '8', '4', '8', '6', '6', '0', '6', '6', '5', '1', '6', '1', '0', '0', '6', '0', '8', '8', '1', '1', '6', '5', '5', '6', '3', '6', '4', '3', '4', '6', '9', '7', '8', '2', '3', '4', '0', '7', '4', '0', '2', '9', '7', '6', '6', '3', '8', '4', '5', '4', '7', '"', ',']

theorem object_fragment0147801_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0147801Field006Chars00 ++ tail)) fragment0147801Acc00600 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0147801Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_006"
  err.flush

noncomputable def fragment0147801Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0147801Field007Value00 : SourceJson := .str (String.ofList ['6', '7', '1', '5', '8', '5', '9', '3', '7', '1', '1', '8', '7', '3', '7', '3', '7', '2', '7', '8', '1', '6', '0', '7', '0', '7', '0', '1', '6', '7', '8', '7', '1', '2', '8', '5', '9', '8', '9', '3', '1', '3', '4', '8', '2', '1', '4', '8', '3', '8', '4', '8', '4', '0', '6', '9', '6', '5', '3', '3', '8', '4', '9', '7', '7', '2', '0', '8', '1', '7', '9', '4', '8', '3', '0', '1', '3', '3', '0', '6', '2', '6', '4', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '1', '8', '9', '4', '9', '1', '6', '4', '8', '7', '7', '6', '0', '2', '4', '8', '7', '2', '2', '1', '3', '7', '4', '2', '7', '6', '6', '5', '8', '5', '1', '4', '4', '3', '8', '3', '3', '8', '4', '5', '5', '4', '3', '7', '9', '2', '7', '5', '2', '4', '8', '6', '6', '0', '7', '5', '8', '9', '7', '5', '6', '9', '1', '5', '9', '8', '6', '3', '3', '0', '7', '1', '6', '1', '6', '6', '8', '5', '7', '1', '9', '0', '2', '2', '1', '3', '8', '0', '1', '9', '6', '9', '5', '9', '3', '7', '9', '3', '5', '4', '3', '2', '3', '7', '4', '8', '4', '9', '8', '6', '4', '1', '2', '1'])
noncomputable def fragment0147801Acc00800 : List (String × SourceJson) := (fragment0147801Field007Key00, fragment0147801Field007Value00) :: fragment0147801Acc00700
noncomputable def fragment0147801Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '7', '1', '5', '8', '5', '9', '3', '7', '1', '1', '8', '7', '3', '7', '3', '7', '2', '7', '8', '1', '6', '0', '7', '0', '7', '0', '1', '6', '7', '8', '7', '1', '2', '8', '5', '9', '8', '9', '3', '1', '3', '4', '8', '2', '1', '4', '8', '3', '8', '4', '8', '4', '0', '6', '9', '6', '5', '3', '3', '8', '4', '9', '7', '7', '2', '0', '8', '1', '7', '9', '4', '8', '3', '0', '1', '3', '3', '0', '6', '2', '6', '4', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '6', '1', '8', '9', '4', '9', '1', '6', '4', '8', '7', '7', '6', '0', '2', '4', '8', '7', '2', '2', '1', '3', '7', '4', '2', '7', '6', '6', '5', '8', '5', '1', '4', '4', '3', '8', '3', '3', '8', '4', '5', '5', '4', '3', '7', '9', '2', '7', '5', '2', '4', '8', '6', '6', '0', '7', '5', '8', '9', '7', '5', '6', '9', '1', '5', '9', '8', '6', '3', '3', '0', '7', '1', '6', '1', '6', '6', '8', '5', '7', '1', '9', '0', '2', '2', '1', '3', '8', '0', '1', '9', '6', '9', '5', '9', '3', '7', '9', '3', '5', '4', '3', '2', '3', '7', '4', '8', '4', '9', '8', '6', '4', '1', '2', '1', '"', ',']

theorem object_fragment0147801_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0147801Field007Chars00 ++ tail)) fragment0147801Acc00700 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0147801Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_007"
  err.flush

noncomputable def fragment0147801Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0147801Field008Value00 : SourceJson := .str (String.ofList ['1', '5', '4', '5', '0', '5', '9', '3', '8', '9', '7', '0', '9', '5', '5', '6', '5', '2'])
noncomputable def fragment0147801Acc00900 : List (String × SourceJson) := (fragment0147801Field008Key00, fragment0147801Field008Value00) :: fragment0147801Acc00800
noncomputable def fragment0147801Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '4', '5', '0', '5', '9', '3', '8', '9', '7', '0', '9', '5', '5', '6', '5', '2', '"', ',']

theorem object_fragment0147801_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0147801Field008Chars00 ++ tail)) fragment0147801Acc00800 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0147801Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_008"
  err.flush

noncomputable def fragment0147801Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0147801Field009Value00 : SourceJson := .str (String.ofList ['6', '9', '8', '3', '7', '0', '8', '4', '6', '3', '8', '4', '2', '0', '2', '4', '2', '6'])
noncomputable def fragment0147801Acc01000 : List (String × SourceJson) := (fragment0147801Field009Key00, fragment0147801Field009Value00) :: fragment0147801Acc00900
noncomputable def fragment0147801Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '9', '8', '3', '7', '0', '8', '4', '6', '3', '8', '4', '2', '0', '2', '4', '2', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0147801_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0147801Field009Chars00 ++ tail)) fragment0147801Acc00900 =
      .ok (.obj (fragment0147801Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0147801_object_field_009"
  err.flush

noncomputable def fragment0147801Chars : List Char := '{' :: (fragment0147801Field000Chars00 ++ fragment0147801Field001Chars00 ++ fragment0147801Field002Chars00 ++ fragment0147801Field003Chars00 ++ fragment0147801Field004Chars00 ++ fragment0147801Field005Chars00 ++ fragment0147801Field006Chars00 ++ fragment0147801Field007Chars00 ++ fragment0147801Field008Chars00 ++ fragment0147801Field009Chars00)
noncomputable def fragment0147801Value : SourceJson := .obj (fragment0147801Acc01000.reverse)

theorem value_fragment0147801 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 233) (fragment0147801Chars ++ tail) =
      .ok (fragment0147801Value, tail) := by
  have hinput : fragment0147801Chars ++ tail = '{' :: (fragment0147801Field000Chars00 ++ (fragment0147801Field001Chars00 ++ (fragment0147801Field002Chars00 ++ (fragment0147801Field003Chars00 ++ (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0147801Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 233) (fragment0147801Chars ++ tail) =
        SourceJson.value (fuel + 233) ('{' :: (fragment0147801Field000Chars00 ++ (fragment0147801Field001Chars00 ++ (fragment0147801Field002Chars00 ++ (fragment0147801Field003Chars00 ++ (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 233)) hinput
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0147801Field000Chars00 ++ (fragment0147801Field001Chars00 ++ (fragment0147801Field002Chars00 ++ (fragment0147801Field003Chars00 ++ (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))))))))))) fragment0147801Acc00000 := by rfl
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0147801Field001Chars00 ++ (fragment0147801Field002Chars00 ++ (fragment0147801Field003Chars00 ++ (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail))))))))))) fragment0147801Acc00100 := object_fragment0147801_field_000 fuel (fragment0147801Field001Chars00 ++ (fragment0147801Field002Chars00 ++ (fragment0147801Field003Chars00 ++ (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0147801Field002Chars00 ++ (fragment0147801Field003Chars00 ++ (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))))))))) fragment0147801Acc00200 := object_fragment0147801_field_001 fuel (fragment0147801Field002Chars00 ++ (fragment0147801Field003Chars00 ++ (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0147801Field003Chars00 ++ (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail))))))))) fragment0147801Acc00300 := object_fragment0147801_field_002 fuel (fragment0147801Field003Chars00 ++ (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))))))) fragment0147801Acc00400 := object_fragment0147801_field_003 fuel (fragment0147801Field004Chars00 ++ (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail))))))) fragment0147801Acc00500 := object_fragment0147801_field_004 fuel (fragment0147801Field005Chars00 ++ (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))))) fragment0147801Acc00600 := object_fragment0147801_field_005 fuel (fragment0147801Field006Chars00 ++ (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail))))) fragment0147801Acc00700 := object_fragment0147801_field_006 fuel (fragment0147801Field007Chars00 ++ (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))) fragment0147801Acc00800 := object_fragment0147801_field_007 fuel (fragment0147801Field008Chars00 ++ (fragment0147801Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0147801Field009Chars00 ++ (tail))) fragment0147801Acc00900 := object_fragment0147801_field_008 fuel (fragment0147801Field009Chars00 ++ (tail))
    _ = .ok (fragment0147801Value, tail) := object_fragment0147801_field_009 fuel (tail)

noncomputable def fragment0149420Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0149420Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0149420Field000Value00 : SourceJson := .number (String.ofList ['1', '3'])
noncomputable def fragment0149420Acc00100 : List (String × SourceJson) := (fragment0149420Field000Key00, fragment0149420Field000Value00) :: fragment0149420Acc00000
noncomputable def fragment0149420Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', ',']

theorem object_fragment0149420_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 422) (SourceJson.white (fragment0149420Field000Chars00 ++ tail)) fragment0149420Acc00000 =
      SourceJson.object (fuel + 421) (SourceJson.white tail) fragment0149420Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_000"
  err.flush

noncomputable def fragment0149420Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0149420Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['3'])]
noncomputable def fragment0149420Acc00200 : List (String × SourceJson) := (fragment0149420Field001Key00, fragment0149420Field001Value00) :: fragment0149420Acc00100
noncomputable def fragment0149420Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0149420_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0149420Field001Chars00 ++ tail)) fragment0149420Acc00100 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0149420Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_001"
  err.flush

noncomputable def fragment0149420Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0149420Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '7', '6', '3', '5', '3', '9', '7', '3', '5', '1', '1', '4', '9', '6', '2', '0', '2', '9', '9', '6', '3', '8', '4', '6', '3', '7', '9', '8', '1', '1', '9', '2', '8', '8', '6', '4', '7', '7', '6', '5', '4', '1', '1', '9', '/', '3', '6', '9', '2', '9', '6', '3', '2', '5', '9', '4', '8', '2', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0149420Acc00300 : List (String × SourceJson) := (fragment0149420Field002Key00, fragment0149420Field002Value00) :: fragment0149420Acc00200
noncomputable def fragment0149420Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '7', '6', '3', '5', '3', '9', '7', '3', '5', '1', '1', '4', '9', '6', '2', '0', '2', '9', '9', '6', '3', '8', '4', '6', '3', '7', '9', '8', '1', '1', '9', '2', '8', '8', '6', '4', '7', '7', '6', '5', '4', '1', '1', '9', '/', '3', '6', '9', '2', '9', '6', '3', '2', '5', '9', '4', '8', '2', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0149420_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0149420Field002Chars00 ++ tail)) fragment0149420Acc00200 =
      SourceJson.object (fuel + 419) (SourceJson.white tail) fragment0149420Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_002"
  err.flush

noncomputable def fragment0149420Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0149420Field003Value00 : SourceJson := .str (String.ofList ['4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0149420Acc00400 : List (String × SourceJson) := (fragment0149420Field003Key00, fragment0149420Field003Value00) :: fragment0149420Acc00300
noncomputable def fragment0149420Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '9', '2', '9', '0', '1', '6', '7', '/', '3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0149420_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 419) (SourceJson.white (fragment0149420Field003Chars00 ++ tail)) fragment0149420Acc00300 =
      SourceJson.object (fuel + 418) (SourceJson.white tail) fragment0149420Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_003"
  err.flush

noncomputable def fragment0149420Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0149420Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0149420Acc00500 : List (String × SourceJson) := (fragment0149420Field004Key00, fragment0149420Field004Value00) :: fragment0149420Acc00400
noncomputable def fragment0149420Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0149420_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 418) (SourceJson.white (fragment0149420Field004Chars00 ++ tail)) fragment0149420Acc00400 =
      SourceJson.object (fuel + 417) (SourceJson.white tail) fragment0149420Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_004"
  err.flush

noncomputable def fragment0149420Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0149420Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '6', '0', '3', '2', '4', '0', '2', '0', '1', '0', '0', '7', '3', '5', '9', '0', '0', '4', '9', '5', '1', '/', '3', '9', '3', '6', '3', '7', '7', '7', '9', '9', '6', '4', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '8', '0', '2', '0', '6', '8', '7', '3', '6', '9', '3', '2', '1', '3', '7', '3', '7', '7', '8', '1', '/', '3', '9', '3', '6', '3', '7', '7', '7', '9', '9', '6', '4', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '4', '4', '8', '5', '4', '9', '5', '4', '2', '3', '0', '3', '0', '8', '4', '8', '8', '1', '5', '3', '/', '7', '8', '7', '2', '7', '5', '5', '5', '9', '9', '2', '8', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '7', '2', '9', '9', '0', '8', '8', '8', '3', '9', '2', '1', '4', '9', '6', '8', '3', '7', '8', '3', '/', '7', '8', '7', '2', '7', '5', '5', '5', '9', '9', '2', '8', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '3', '3', '7', '4', '7', '0', '5', '8', '1', '2', '4', '8', '7', '9', '6', '8', '7', '7', '6', '9', '/', '2', '6', '2', '4', '2', '5', '1', '8', '6', '6', '4', '2', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '9', '1', '4', '7', '0', '7', '2', '5', '4', '9', '8', '7', '4', '0', '9', '3', '5', '6', '8', '7', '/', '7', '8', '7', '2', '7', '5', '5', '5', '9', '9', '2', '8', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '0', '6', '7', '2', '4', '4', '7', '1', '5', '2', '0', '1', '3', '4', '0', '7', '5', '1', '/', '1', '4', '0', '5', '8', '4', '9', '2', '1', '4', '1', '5', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '8', '5', '0', '5', '0', '1', '6', '4', '5', '0', '5', '3', '3', '2', '3', '3', '4', '5', '9', '/', '1', '9', '6', '8', '1', '8', '8', '8', '9', '9', '8', '2', '0', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '1', '6', '1', '4', '3', '5', '5', '1', '0', '5', '6', '9', '8', '5', '8', '0', '9', '5', '3', '/', '3', '9', '3', '6', '3', '7', '7', '7', '9', '9', '6', '4', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '9', '9', '6', '2', '7', '3', '7', '2', '3', '1', '1', '8', '7', '7', '8', '4', '4', '3', '/', '2', '6', '2', '4', '2', '5', '1', '8', '6', '6', '4', '2', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0149420Acc00600 : List (String × SourceJson) := (fragment0149420Field005Key00, fragment0149420Field005Value00) :: fragment0149420Acc00500
noncomputable def fragment0149420Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '0', '3', '2', '4', '0', '2', '0', '1', '0', '0', '7', '3', '5', '9', '0', '0', '4', '9', '5', '1', '/', '3', '9', '3', '6', '3', '7', '7', '7', '9', '9', '6', '4', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '8', '0', '2', '0', '6', '8', '7', '3', '6', '9', '3', '2', '1', '3', '7', '3', '7', '7', '8', '1', '/', '3', '9', '3', '6', '3', '7', '7', '7', '9', '9', '6', '4', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '0', '4', '4', '8', '5', '4', '9', '5', '4', '2', '3', '0', '3', '0', '8', '4', '8', '8', '1', '5', '3', '/', '7', '8', '7', '2', '7', '5', '5', '5', '9', '9', '2', '8', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '7', '2', '9', '9', '0', '8', '8', '8', '3', '9', '2', '1', '4', '9', '6', '8', '3', '7', '8', '3', '/', '7', '8', '7', '2', '7', '5', '5', '5', '9', '9', '2', '8', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '3', '3', '7', '4', '7', '0', '5', '8', '1', '2', '4', '8', '7', '9', '6', '8', '7', '7', '6', '9', '/', '2', '6', '2', '4', '2', '5', '1', '8', '6', '6', '4', '2', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '9', '9', '1', '4', '7', '0', '7', '2', '5', '4', '9', '8', '7', '4', '0', '9', '3', '5', '6', '8', '7', '/', '7', '8', '7', '2', '7', '5', '5', '5', '9', '9', '2', '8', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '4', '0', '6', '7', '2', '4', '4', '7', '1', '5', '2', '0', '1', '3', '4', '0', '7', '5', '1', '/', '1', '4', '0', '5', '8', '4', '9', '2', '1', '4', '1', '5', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '8', '5', '0', '5', '0', '1', '6', '4', '5', '0', '5', '3', '3', '2', '3', '3', '4', '5', '9', '/', '1', '9', '6', '8', '1', '8', '8', '8', '9', '9', '8', '2', '0', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '4', '1', '6', '1', '4', '3', '5', '5', '1', '0', '5', '6', '9', '8', '5', '8', '0', '9', '5', '3', '/', '3', '9', '3', '6', '3', '7', '7', '7', '9', '9', '6', '4', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '9', '9', '6', '2', '7', '3', '7', '2', '3', '1', '1', '8', '7', '7', '8', '4', '4', '3', '/', '2', '6', '2', '4', '2', '5', '1', '8', '6', '6', '4', '2', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0149420_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 417) (SourceJson.white (fragment0149420Field005Chars00 ++ tail)) fragment0149420Acc00500 =
      SourceJson.object (fuel + 416) (SourceJson.white tail) fragment0149420Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_005"
  err.flush

noncomputable def fragment0149420Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0149420Field006Value00 : SourceJson := .str (String.ofList ['1', '8', '6', '7', '7', '5', '8', '4', '2', '8', '0', '1', '6', '7', '1', '2', '1', '2', '1', '7', '6', '8', '2', '1', '3', '9', '2', '3', '1', '3', '2', '8', '7', '3', '5', '6', '3', '3', '0', '9', '9', '9', '0', '7', '0', '4', '1', '7', '6', '6', '3', '1', '5', '6', '2', '5', '/', '2', '6', '2', '1', '4', '4', '3', '1', '5', '4', '1', '9', '7', '5', '4', '1', '7', '9', '4', '6', '7', '5', '7', '8', '6', '3', '3', '9', '7', '2', '0', '1', '5', '0', '3', '6', '4', '0', '0', '1', '4', '2', '2', '5', '6', '6', '0', '1', '7', '0', '5', '7', '5', '3', '4', '8', '5', '3', '3', '8', '5', '4', '5', '4', '5', '4', '7', '8'])
noncomputable def fragment0149420Acc00700 : List (String × SourceJson) := (fragment0149420Field006Key00, fragment0149420Field006Value00) :: fragment0149420Acc00600
noncomputable def fragment0149420Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '8', '6', '7', '7', '5', '8', '4', '2', '8', '0', '1', '6', '7', '1', '2', '1', '2', '1', '7', '6', '8', '2', '1', '3', '9', '2', '3', '1', '3', '2', '8', '7', '3', '5', '6', '3', '3', '0', '9', '9', '9', '0', '7', '0', '4', '1', '7', '6', '6', '3', '1', '5', '6', '2', '5', '/', '2', '6', '2', '1', '4', '4', '3', '1', '5', '4', '1', '9', '7', '5', '4', '1', '7', '9', '4', '6', '7', '5', '7', '8', '6', '3', '3', '9', '7', '2', '0', '1', '5', '0', '3', '6', '4', '0', '0', '1', '4', '2', '2', '5', '6', '6', '0', '1', '7', '0', '5', '7', '5', '3', '4', '8', '5', '3', '3', '8', '5', '4', '5', '4', '5', '4', '7', '8', '"', ',']

theorem object_fragment0149420_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 416) (SourceJson.white (fragment0149420Field006Chars00 ++ tail)) fragment0149420Acc00600 =
      SourceJson.object (fuel + 415) (SourceJson.white tail) fragment0149420Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_006"
  err.flush

noncomputable def fragment0149420Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0149420Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '8', '0', '7', '5', '6', '3', '3', '4', '4', '7', '4', '3', '2', '7', '0', '8', '7', '9', '0', '4', '1', '1', '5', '3', '3', '9', '7', '0', '2', '2', '6', '2', '2', '3', '5', '9', '5', '7', '1', '4', '6', '1', '7', '9', '1', '5', '6', '2', '7', '6', '3', '9', '9', '8', '5', '5', '2', '4', '3', '6', '4', '2', '5', '7', '3', '6', '7', '7', '0', '3', '4', '4', '2', '8', '4', '9', '1', '0', '1', '4', '2', '1', '7', '9', '2', '9', '5', '7', '6', '2', '8', '5', '7', '9', '5', '1', '6', '0', '9', '2', '7', '6', '6', '5', '7', '8', '4', '2', '7', '4', '2', '8', '4', '5', '4', '7', '2', '6', '5', '3', '6', '7', '0', '0', '4', '4', '5', '7', '5', '0', '9', '4', '8', '2', '4', '8', '8', '5', '3', '3', '6', '6', '8', '9', '5', '6', '6', '5', '1', '0', '1', '6', '4', '5', '4', '8', '0', '3', '6', '8', '7', '0', '3', '4', '3', '7', '9', '2', '9', '7', '0', '7', '2', '6', '3', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '4', '8', '3', '7', '4', '7', '2', '0', '9', '1', '1', '6', '9', '2', '9', '1', '2', '2', '4', '8', '6', '3', '4', '6', '6', '7', '2', '1', '3', '1', '2', '2', '6', '2', '7', '5', '5', '9', '1', '9', '8', '2', '7', '7', '2', '3', '5', '1', '9', '8', '4', '9', '6', '9', '6', '4', '0', '0', '2', '5', '7', '9', '4', '8', '2', '7', '6', '4', '8', '5', '7', '4', '7', '6', '0', '2', '4', '6', '8', '4', '1', '0', '7', '3', '2', '9', '2', '4', '1', '8', '1', '8', '2', '8', '7', '3', '7', '7', '3', '3', '4', '7', '6', '1', '3', '5', '4', '4', '2', '4', '8', '7', '8', '8', '0', '2', '5', '2', '9', '8', '7', '7', '1', '1', '2', '9', '3', '5', '2', '6', '7', '0', '4', '3', '8', '8', '7', '6', '5', '3', '4', '6', '8', '9', '4', '9', '0', '5', '5', '8', '7', '4', '9', '8', '2', '6', '1', '9', '8', '8', '8', '9', '4', '0', '6', '4', '2', '7', '2', '5', '1', '3', '9', '0', '5', '5', '1', '8', '8', '9', '2', '9', '4', '3', '4', '8', '3', '9', '4', '8', '8', '0', '1', '2', '2', '1', '3', '1', '0', '0', '3', '6', '8', '6', '4', '0', '3', '2', '9'])
noncomputable def fragment0149420Acc00800 : List (String × SourceJson) := (fragment0149420Field007Key00, fragment0149420Field007Value00) :: fragment0149420Acc00700
noncomputable def fragment0149420Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '7', '8', '0', '7', '5', '6', '3', '3', '4', '4', '7', '4', '3', '2', '7', '0', '8', '7', '9', '0', '4', '1', '1', '5', '3', '3', '9', '7', '0', '2', '2', '6', '2', '2', '3', '5', '9', '5', '7', '1', '4', '6', '1', '7', '9', '1', '5', '6', '2', '7', '6', '3', '9', '9', '8', '5', '5', '2', '4', '3', '6', '4', '2', '5', '7', '3', '6', '7', '7', '0', '3', '4', '4', '2', '8', '4', '9', '1', '0', '1', '4', '2', '1', '7', '9', '2', '9', '5', '7', '6', '2', '8', '5', '7', '9', '5', '1', '6', '0', '9', '2', '7', '6', '6', '5', '7', '8', '4', '2', '7', '4', '2', '8', '4', '5', '4', '7', '2', '6', '5', '3', '6', '7', '0', '0', '4', '4', '5', '7', '5', '0', '9', '4', '8', '2', '4', '8', '8', '5', '3', '3', '6', '6', '8', '9', '5', '6', '6', '5', '1', '0', '1', '6', '4', '5', '4', '8', '0', '3', '6', '8', '7', '0', '3', '4', '3', '7', '9', '2', '9', '7', '0', '7', '2', '6', '3', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '4', '8', '3', '7', '4', '7', '2', '0', '9', '1', '1', '6', '9', '2', '9', '1', '2', '2', '4', '8', '6', '3', '4', '6', '6', '7', '2', '1', '3', '1', '2', '2', '6', '2', '7', '5', '5', '9', '1', '9', '8', '2', '7', '7', '2', '3', '5', '1', '9', '8', '4', '9', '6', '9', '6', '4', '0', '0', '2', '5', '7', '9', '4', '8', '2', '7', '6', '4', '8', '5', '7', '4', '7', '6', '0', '2', '4', '6', '8', '4', '1', '0', '7', '3', '2', '9', '2', '4', '1', '8', '1', '8', '2', '8', '7', '3', '7', '7', '3', '3', '4', '7', '6', '1', '3', '5', '4', '4', '2', '4', '8', '7', '8', '8', '0', '2', '5', '2', '9', '8', '7', '7', '1', '1', '2', '9', '3', '5', '2', '6', '7', '0', '4', '3', '8', '8', '7', '6', '5', '3', '4', '6', '8', '9', '4', '9', '0', '5', '5', '8', '7', '4', '9', '8', '2', '6', '1', '9', '8', '8', '8', '9', '4', '0', '6', '4', '2', '7', '2', '5', '1', '3', '9', '0', '5', '5', '1', '8', '8', '9', '2', '9', '4', '3', '4', '8', '3', '9', '4', '8', '8', '0', '1', '2', '2', '1', '3', '1', '0', '0', '3', '6', '8', '6', '4', '0', '3', '2', '9', '"', ',']

theorem object_fragment0149420_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 415) (SourceJson.white (fragment0149420Field007Chars00 ++ tail)) fragment0149420Acc00700 =
      SourceJson.object (fuel + 414) (SourceJson.white tail) fragment0149420Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_007"
  err.flush

noncomputable def fragment0149420Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0149420Field008Value00 : SourceJson := .str (String.ofList ['5', '6', '4', '4', '9', '4', '6', '6', '7', '8', '9', '0', '6', '4', '6', '2', '6'])
noncomputable def fragment0149420Acc00900 : List (String × SourceJson) := (fragment0149420Field008Key00, fragment0149420Field008Value00) :: fragment0149420Acc00800
noncomputable def fragment0149420Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '4', '4', '9', '4', '6', '6', '7', '8', '9', '0', '6', '4', '6', '2', '6', '"', ',']

theorem object_fragment0149420_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 414) (SourceJson.white (fragment0149420Field008Chars00 ++ tail)) fragment0149420Acc00800 =
      SourceJson.object (fuel + 413) (SourceJson.white tail) fragment0149420Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_008"
  err.flush

noncomputable def fragment0149420Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0149420Field009Value00 : SourceJson := .str (String.ofList ['2', '2', '7', '8', '6', '9', '2', '9', '7', '6', '2', '6', '3', '2', '4', '2', '6', '0'])
noncomputable def fragment0149420Acc01000 : List (String × SourceJson) := (fragment0149420Field009Key00, fragment0149420Field009Value00) :: fragment0149420Acc00900
noncomputable def fragment0149420Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '2', '7', '8', '6', '9', '2', '9', '7', '6', '2', '6', '3', '2', '4', '2', '6', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0149420_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 413) (SourceJson.white (fragment0149420Field009Chars00 ++ tail)) fragment0149420Acc00900 =
      .ok (.obj (fragment0149420Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0149420_object_field_009"
  err.flush

noncomputable def fragment0149420Chars : List Char := '{' :: (fragment0149420Field000Chars00 ++ fragment0149420Field001Chars00 ++ fragment0149420Field002Chars00 ++ fragment0149420Field003Chars00 ++ fragment0149420Field004Chars00 ++ fragment0149420Field005Chars00 ++ fragment0149420Field006Chars00 ++ fragment0149420Field007Chars00 ++ fragment0149420Field008Chars00 ++ fragment0149420Field009Chars00)
noncomputable def fragment0149420Value : SourceJson := .obj (fragment0149420Acc01000.reverse)

theorem value_fragment0149420 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 423) (fragment0149420Chars ++ tail) =
      .ok (fragment0149420Value, tail) := by
  have hinput : fragment0149420Chars ++ tail = '{' :: (fragment0149420Field000Chars00 ++ (fragment0149420Field001Chars00 ++ (fragment0149420Field002Chars00 ++ (fragment0149420Field003Chars00 ++ (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0149420Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 423) (fragment0149420Chars ++ tail) =
        SourceJson.value (fuel + 423) ('{' :: (fragment0149420Field000Chars00 ++ (fragment0149420Field001Chars00 ++ (fragment0149420Field002Chars00 ++ (fragment0149420Field003Chars00 ++ (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 423)) hinput
    _ = SourceJson.object (fuel + 422) (SourceJson.white (fragment0149420Field000Chars00 ++ (fragment0149420Field001Chars00 ++ (fragment0149420Field002Chars00 ++ (fragment0149420Field003Chars00 ++ (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))))))))))) fragment0149420Acc00000 := by rfl
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0149420Field001Chars00 ++ (fragment0149420Field002Chars00 ++ (fragment0149420Field003Chars00 ++ (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail))))))))))) fragment0149420Acc00100 := object_fragment0149420_field_000 fuel (fragment0149420Field001Chars00 ++ (fragment0149420Field002Chars00 ++ (fragment0149420Field003Chars00 ++ (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0149420Field002Chars00 ++ (fragment0149420Field003Chars00 ++ (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))))))))) fragment0149420Acc00200 := object_fragment0149420_field_001 fuel (fragment0149420Field002Chars00 ++ (fragment0149420Field003Chars00 ++ (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 419) (SourceJson.white (fragment0149420Field003Chars00 ++ (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail))))))))) fragment0149420Acc00300 := object_fragment0149420_field_002 fuel (fragment0149420Field003Chars00 ++ (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 418) (SourceJson.white (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))))))) fragment0149420Acc00400 := object_fragment0149420_field_003 fuel (fragment0149420Field004Chars00 ++ (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 417) (SourceJson.white (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail))))))) fragment0149420Acc00500 := object_fragment0149420_field_004 fuel (fragment0149420Field005Chars00 ++ (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 416) (SourceJson.white (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))))) fragment0149420Acc00600 := object_fragment0149420_field_005 fuel (fragment0149420Field006Chars00 ++ (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 415) (SourceJson.white (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail))))) fragment0149420Acc00700 := object_fragment0149420_field_006 fuel (fragment0149420Field007Chars00 ++ (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 414) (SourceJson.white (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))) fragment0149420Acc00800 := object_fragment0149420_field_007 fuel (fragment0149420Field008Chars00 ++ (fragment0149420Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 413) (SourceJson.white (fragment0149420Field009Chars00 ++ (tail))) fragment0149420Acc00900 := object_fragment0149420_field_008 fuel (fragment0149420Field009Chars00 ++ (tail))
    _ = .ok (fragment0149420Value, tail) := object_fragment0149420_field_009 fuel (tail)

noncomputable def fragment0151413Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0151413Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0151413Field000Value00 : SourceJson := .number (String.ofList ['1', '4'])
noncomputable def fragment0151413Acc00100 : List (String × SourceJson) := (fragment0151413Field000Key00, fragment0151413Field000Value00) :: fragment0151413Acc00000
noncomputable def fragment0151413Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '4', ',']

theorem object_fragment0151413_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 489) (SourceJson.white (fragment0151413Field000Chars00 ++ tail)) fragment0151413Acc00000 =
      SourceJson.object (fuel + 488) (SourceJson.white tail) fragment0151413Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_000"
  err.flush

noncomputable def fragment0151413Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0151413Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0151413Acc00200 : List (String × SourceJson) := (fragment0151413Field001Key00, fragment0151413Field001Value00) :: fragment0151413Acc00100
noncomputable def fragment0151413Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0151413_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 488) (SourceJson.white (fragment0151413Field001Chars00 ++ tail)) fragment0151413Acc00100 =
      SourceJson.object (fuel + 487) (SourceJson.white tail) fragment0151413Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_001"
  err.flush

noncomputable def fragment0151413Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0151413Field002Value00 : SourceJson := .str (String.ofList ['3', '5', '2', '4', '3', '3', '2', '0', '9', '8', '8', '8', '7', '9', '2', '0', '9', '7', '3', '7', '5', '1', '0', '7', '5', '9', '2', '3', '0', '1', '8', '7', '3', '1', '6', '1', '1', '9', '4', '2', '4', '2', '6', '1', '/', '2', '3', '2', '0', '0', '7', '2', '5', '7', '1', '6', '5', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0151413Acc00300 : List (String × SourceJson) := (fragment0151413Field002Key00, fragment0151413Field002Value00) :: fragment0151413Acc00200
noncomputable def fragment0151413Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '5', '2', '4', '3', '3', '2', '0', '9', '8', '8', '8', '7', '9', '2', '0', '9', '7', '3', '7', '5', '1', '0', '7', '5', '9', '2', '3', '0', '1', '8', '7', '3', '1', '6', '1', '1', '9', '4', '2', '4', '2', '6', '1', '/', '2', '3', '2', '0', '0', '7', '2', '5', '7', '1', '6', '5', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0151413_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 487) (SourceJson.white (fragment0151413Field002Chars00 ++ tail)) fragment0151413Acc00200 =
      SourceJson.object (fuel + 486) (SourceJson.white tail) fragment0151413Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_002"
  err.flush

noncomputable def fragment0151413Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0151413Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0151413Acc00400 : List (String × SourceJson) := (fragment0151413Field003Key00, fragment0151413Field003Value00) :: fragment0151413Acc00300
noncomputable def fragment0151413Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0151413_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 486) (SourceJson.white (fragment0151413Field003Chars00 ++ tail)) fragment0151413Acc00300 =
      SourceJson.object (fuel + 485) (SourceJson.white tail) fragment0151413Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_003"
  err.flush

noncomputable def fragment0151413Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0151413Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0151413Acc00500 : List (String × SourceJson) := (fragment0151413Field004Key00, fragment0151413Field004Value00) :: fragment0151413Acc00400
noncomputable def fragment0151413Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0151413_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 485) (SourceJson.white (fragment0151413Field004Chars00 ++ tail)) fragment0151413Acc00400 =
      SourceJson.object (fuel + 484) (SourceJson.white tail) fragment0151413Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_004"
  err.flush

noncomputable def fragment0151413Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0151413Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '6', '2', '1', '8', '1', '4', '4', '2', '2', '6', '2', '1', '3', '5', '5', '7', '7', '3', '0', '4', '8', '8', '9', '1', '/', '5', '1', '4', '0', '9', '0', '8', '9', '6', '7', '6', '5', '2', '1', '8', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '0', '6', '6', '5', '9', '2', '0', '6', '2', '9', '0', '1', '1', '8', '3', '9', '7', '9', '3', '9', '/', '1', '7', '0', '7', '9', '4', '3', '1', '7', '8', '6', '2', '1', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '0', '4', '5', '8', '7', '3', '1', '0', '6', '4', '8', '4', '2', '4', '0', '3', '7', '2', '8', '1', '6', '5', '1', '3', '3', '/', '2', '3', '6', '4', '8', '1', '8', '1', '2', '5', '1', '2', '0', '0', '0', '4', '5', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '2', '4', '4', '8', '4', '5', '4', '0', '7', '9', '1', '8', '1', '5', '1', '8', '4', '6', '5', '4', '0', '7', '1', '9', '/', '4', '7', '2', '9', '6', '3', '6', '2', '5', '0', '2', '4', '0', '0', '0', '9', '1', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '0', '2', '3', '0', '0', '3', '1', '0', '4', '6', '1', '3', '1', '2', '5', '6', '9', '9', '5', '7', '0', '5', '3', '3', '/', '7', '8', '8', '2', '7', '2', '7', '0', '8', '3', '7', '3', '3', '3', '4', '8', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '5', '1', '1', '5', '8', '6', '7', '9', '9', '6', '3', '1', '7', '0', '4', '6', '3', '6', '1', '2', '4', '8', '1', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '6', '3', '6', '0', '3', '9', '0', '7', '5', '4', '5', '4', '7', '5', '5', '4', '1', '1', '6', '2', '0', '9', '9', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '3', '9', '5', '2', '2', '8', '6', '5', '7', '1', '8', '0', '7', '0', '4', '5', '3', '2', '3', '8', '7', '6', '9', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '8', '1', '0', '2', '3', '7', '2', '5', '5', '0', '2', '2', '7', '3', '9', '6', '1', '7', '1', '3', '8', '8', '9', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '4', '7', '7', '1', '3', '2', '6', '3', '0', '5', '8', '4', '7', '9', '2', '7', '3', '4', '3', '3', '/', '5', '6', '9', '3', '1', '4', '3', '9', '2', '8', '7', '3', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0151413Acc00600 : List (String × SourceJson) := (fragment0151413Field005Key00, fragment0151413Field005Value00) :: fragment0151413Acc00500
noncomputable def fragment0151413Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '2', '1', '8', '1', '4', '4', '2', '2', '6', '2', '1', '3', '5', '5', '7', '7', '3', '0', '4', '8', '8', '9', '1', '/', '5', '1', '4', '0', '9', '0', '8', '9', '6', '7', '6', '5', '2', '1', '8', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '0', '6', '6', '5', '9', '2', '0', '6', '2', '9', '0', '1', '1', '8', '3', '9', '7', '9', '3', '9', '/', '1', '7', '0', '7', '9', '4', '3', '1', '7', '8', '6', '2', '1', '9', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '0', '4', '5', '8', '7', '3', '1', '0', '6', '4', '8', '4', '2', '4', '0', '3', '7', '2', '8', '1', '6', '5', '1', '3', '3', '/', '2', '3', '6', '4', '8', '1', '8', '1', '2', '5', '1', '2', '0', '0', '0', '4', '5', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '2', '4', '4', '8', '4', '5', '4', '0', '7', '9', '1', '8', '1', '5', '1', '8', '4', '6', '5', '4', '0', '7', '1', '9', '/', '4', '7', '2', '9', '6', '3', '6', '2', '5', '0', '2', '4', '0', '0', '0', '9', '1', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '0', '2', '3', '0', '0', '3', '1', '0', '4', '6', '1', '3', '1', '2', '5', '6', '9', '9', '5', '7', '0', '5', '3', '3', '/', '7', '8', '8', '2', '7', '2', '7', '0', '8', '3', '7', '3', '3', '3', '4', '8', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '5', '1', '1', '5', '8', '6', '7', '9', '9', '6', '3', '1', '7', '0', '4', '6', '3', '6', '1', '2', '4', '8', '1', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '6', '3', '6', '0', '3', '9', '0', '7', '5', '4', '5', '4', '7', '5', '5', '4', '1', '1', '6', '2', '0', '9', '9', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '3', '9', '5', '2', '2', '8', '6', '5', '7', '1', '8', '0', '7', '0', '4', '5', '3', '2', '3', '8', '7', '6', '9', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '8', '1', '0', '2', '3', '7', '2', '5', '5', '0', '2', '2', '7', '3', '9', '6', '1', '7', '1', '3', '8', '8', '9', '/', '1', '0', '7', '4', '9', '1', '7', '3', '2', '9', '6', '0', '0', '0', '0', '2', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '4', '7', '7', '1', '3', '2', '6', '3', '0', '5', '8', '4', '7', '9', '2', '7', '3', '4', '3', '3', '/', '5', '6', '9', '3', '1', '4', '3', '9', '2', '8', '7', '3', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0151413_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 484) (SourceJson.white (fragment0151413Field005Chars00 ++ tail)) fragment0151413Acc00500 =
      SourceJson.object (fuel + 483) (SourceJson.white tail) fragment0151413Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_005"
  err.flush

noncomputable def fragment0151413Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0151413Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '9', '4', '4', '7', '6', '1', '5', '9', '8', '2', '4', '9', '6', '3', '8', '5', '4', '4', '6', '8', '7', '0', '4', '5', '5', '6', '9', '6', '9', '1', '9', '3', '3', '3', '8', '6', '8', '0', '0', '8', '7', '6', '8', '1', '5', '1', '0', '1', '9', '5', '1', '2', '0', '0', '0', '0', '0', '/', '3', '7', '0', '8', '6', '9', '9', '0', '5', '3', '3', '7', '1', '7', '7', '8', '7', '7', '6', '7', '8', '2', '7', '9', '5', '8', '9', '4', '3', '6', '2', '7', '3', '5', '0', '3', '1', '4', '2', '0', '0', '5', '5', '8', '9', '7', '9', '2', '8', '9', '1', '0', '7', '7', '2', '4', '4', '1', '4', '7', '6', '5', '9', '5', '0', '4', '6', '1', '3', '3', '0', '3'])
noncomputable def fragment0151413Acc00700 : List (String × SourceJson) := (fragment0151413Field006Key00, fragment0151413Field006Value00) :: fragment0151413Acc00600
noncomputable def fragment0151413Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '9', '4', '4', '7', '6', '1', '5', '9', '8', '2', '4', '9', '6', '3', '8', '5', '4', '4', '6', '8', '7', '0', '4', '5', '5', '6', '9', '6', '9', '1', '9', '3', '3', '3', '8', '6', '8', '0', '0', '8', '7', '6', '8', '1', '5', '1', '0', '1', '9', '5', '1', '2', '0', '0', '0', '0', '0', '/', '3', '7', '0', '8', '6', '9', '9', '0', '5', '3', '3', '7', '1', '7', '7', '8', '7', '7', '6', '7', '8', '2', '7', '9', '5', '8', '9', '4', '3', '6', '2', '7', '3', '5', '0', '3', '1', '4', '2', '0', '0', '5', '5', '8', '9', '7', '9', '2', '8', '9', '1', '0', '7', '7', '2', '4', '4', '1', '4', '7', '6', '5', '9', '5', '0', '4', '6', '1', '3', '3', '0', '3', '"', ',']

theorem object_fragment0151413_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 483) (SourceJson.white (fragment0151413Field006Chars00 ++ tail)) fragment0151413Acc00600 =
      SourceJson.object (fuel + 482) (SourceJson.white tail) fragment0151413Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_006"
  err.flush

noncomputable def fragment0151413Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0151413Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '7', '6', '1', '9', '0', '2', '4', '9', '4', '9', '5', '8', '4', '0', '1', '7', '1', '1', '1', '0', '0', '2', '5', '7', '9', '2', '9', '9', '5', '0', '5', '2', '1', '2', '1', '8', '0', '2', '8', '7', '0', '1', '9', '5', '4', '4', '6', '5', '3', '6', '6', '0', '2', '6', '3', '5', '5', '1', '4', '5', '8', '1', '2', '5', '4', '8', '9', '0', '0', '4', '6', '5', '0', '6', '2', '0', '5', '4', '1', '9', '8', '0', '8', '5', '7', '5', '6', '5', '5', '5', '0', '1', '2', '2', '0', '7', '6', '9', '0', '1', '6', '3', '3', '6', '9', '9', '7', '4', '1', '2', '3', '1', '5', '3', '2', '0', '4', '4', '7', '8', '0', '3', '6', '9', '9', '8', '5', '2', '0', '5', '3', '9', '5', '3', '1', '0', '5', '5', '5', '9', '0', '3', '2', '9', '3', '0', '3', '3', '0', '8', '7', '5', '2', '5', '1', '6', '5', '9', '1', '2', '9', '2', '5', '6', '2', '2', '9', '5', '0', '8', '2', '5', '3', '8', '2', '4', '3', '6', '7', '1', '6', '0', '9', '4', '0', '1', '9', '4', '0', '0', '7', '0', '9', '7', '1', '0', '1', '0', '2', '3', '4', '5', '7', '1', '9', '4', '3', '1', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '9', '6', '3', '2', '3', '1', '3', '8', '7', '8', '9', '7', '1', '3', '9', '1', '9', '3', '7', '4', '0', '7', '8', '5', '0', '0', '0', '1', '5', '6', '2', '8', '1', '0', '7', '5', '5', '3', '9', '9', '4', '5', '1', '7', '8', '1', '9', '7', '5', '4', '6', '6', '5', '3', '2', '2', '2', '7', '6', '7', '3', '3', '2', '0', '3', '8', '6', '9', '9', '1', '3', '1', '8', '4', '2', '9', '8', '0', '0', '5', '4', '7', '9', '0', '5', '9', '5', '1', '0', '5', '5', '7', '2', '2', '6', '7', '3', '3', '5', '1', '1', '5', '2', '6', '0', '9', '4', '2', '2', '8', '8', '9', '1', '1', '9', '3', '2', '1', '8', '7', '8', '3', '2', '6', '4', '2', '4', '7', '1', '7', '0', '5', '6', '2', '6', '3', '2', '7', '0', '2', '5', '1', '0', '3', '9', '7', '3', '4', '5', '4', '6', '3', '7', '5', '7', '1', '7', '6', '2', '0', '5', '2', '8', '2', '2', '2', '0', '5', '7', '1', '3', '8', '2', '8', '7', '0', '4', '4', '2', '2', '4', '5', '8', '3', '7', '3', '6', '3', '9', '4', '0', '7', '4', '5', '2', '4', '7', '8', '3', '8', '1', '3', '0', '9', '5', '8', '8', '0', '4', '5', '6', '9', '5', '0', '7', '6', '7', '8', '2', '5', '7', '4', '3', '6', '4', '4', '9', '0', '8', '5', '7', '2', '3', '3', '2', '9', '0', '9', '5', '8', '5', '4', '1', '3'])
noncomputable def fragment0151413Acc00800 : List (String × SourceJson) := (fragment0151413Field007Key00, fragment0151413Field007Value00) :: fragment0151413Acc00700
noncomputable def fragment0151413Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '7', '6', '1', '9', '0', '2', '4', '9', '4', '9', '5', '8', '4', '0', '1', '7', '1', '1', '1', '0', '0', '2', '5', '7', '9', '2', '9', '9', '5', '0', '5', '2', '1', '2', '1', '8', '0', '2', '8', '7', '0', '1', '9', '5', '4', '4', '6', '5', '3', '6', '6', '0', '2', '6', '3', '5', '5', '1', '4', '5', '8', '1', '2', '5', '4', '8', '9', '0', '0', '4', '6', '5', '0', '6', '2', '0', '5', '4', '1', '9', '8', '0', '8', '5', '7', '5', '6', '5', '5', '5', '0', '1', '2', '2', '0', '7', '6', '9', '0', '1', '6', '3', '3', '6', '9', '9', '7', '4', '1', '2', '3', '1', '5', '3', '2', '0', '4', '4', '7', '8', '0', '3', '6', '9', '9', '8', '5', '2', '0', '5', '3', '9', '5', '3', '1', '0', '5', '5', '5', '9', '0', '3', '2', '9', '3', '0', '3', '3', '0', '8', '7', '5', '2', '5', '1', '6', '5', '9', '1', '2', '9', '2', '5', '6', '2', '2', '9', '5', '0', '8', '2', '5', '3', '8', '2', '4', '3', '6', '7', '1', '6', '0', '9', '4', '0', '1', '9', '4', '0', '0', '7', '0', '9', '7', '1', '0', '1', '0', '2', '3', '4', '5', '7', '1', '9', '4', '3', '1', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '9', '6', '3', '2', '3', '1', '3', '8', '7', '8', '9', '7', '1', '3', '9', '1', '9', '3', '7', '4', '0', '7', '8', '5', '0', '0', '0', '1', '5', '6', '2', '8', '1', '0', '7', '5', '5', '3', '9', '9', '4', '5', '1', '7', '8', '1', '9', '7', '5', '4', '6', '6', '5', '3', '2', '2', '2', '7', '6', '7', '3', '3', '2', '0', '3', '8', '6', '9', '9', '1', '3', '1', '8', '4', '2', '9', '8', '0', '0', '5', '4', '7', '9', '0', '5', '9', '5', '1', '0', '5', '5', '7', '2', '2', '6', '7', '3', '3', '5', '1', '1', '5', '2', '6', '0', '9', '4', '2', '2', '8', '8', '9', '1', '1', '9', '3', '2', '1', '8', '7', '8', '3', '2', '6', '4', '2', '4', '7', '1', '7', '0', '5', '6', '2', '6', '3', '2', '7', '0', '2', '5', '1', '0', '3', '9', '7', '3', '4', '5', '4', '6', '3', '7', '5', '7', '1', '7', '6', '2', '0', '5', '2', '8', '2', '2', '2', '0', '5', '7', '1', '3', '8', '2', '8', '7', '0', '4', '4', '2', '2', '4', '5', '8', '3', '7', '3', '6', '3', '9', '4', '0', '7', '4', '5', '2', '4', '7', '8', '3', '8', '1', '3', '0', '9', '5', '8', '8', '0', '4', '5', '6', '9', '5', '0', '7', '6', '7', '8', '2', '5', '7', '4', '3', '6', '4', '4', '9', '0', '8', '5', '7', '2', '3', '3', '2', '9', '0', '9', '5', '8', '5', '4', '1', '3', '"', ',']

theorem object_fragment0151413_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 482) (SourceJson.white (fragment0151413Field007Chars00 ++ tail)) fragment0151413Acc00700 =
      SourceJson.object (fuel + 481) (SourceJson.white tail) fragment0151413Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_007"
  err.flush

noncomputable def fragment0151413Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0151413Field008Value00 : SourceJson := .str (String.ofList ['4', '2', '6', '0', '7', '5', '7', '7', '2', '2', '5', '1', '6', '5', '9', '9'])
noncomputable def fragment0151413Acc00900 : List (String × SourceJson) := (fragment0151413Field008Key00, fragment0151413Field008Value00) :: fragment0151413Acc00800
noncomputable def fragment0151413Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '2', '6', '0', '7', '5', '7', '7', '2', '2', '5', '1', '6', '5', '9', '9', '"', ',']

theorem object_fragment0151413_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 481) (SourceJson.white (fragment0151413Field008Chars00 ++ tail)) fragment0151413Acc00800 =
      SourceJson.object (fuel + 480) (SourceJson.white tail) fragment0151413Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_008"
  err.flush

noncomputable def fragment0151413Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0151413Field009Value00 : SourceJson := .str (String.ofList ['1', '2', '5', '3', '3', '9', '5', '1', '3', '2', '3', '4', '7', '8', '4', '3', '9'])
noncomputable def fragment0151413Acc01000 : List (String × SourceJson) := (fragment0151413Field009Key00, fragment0151413Field009Value00) :: fragment0151413Acc00900
noncomputable def fragment0151413Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '2', '5', '3', '3', '9', '5', '1', '3', '2', '3', '4', '7', '8', '4', '3', '9', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0151413_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 480) (SourceJson.white (fragment0151413Field009Chars00 ++ tail)) fragment0151413Acc00900 =
      .ok (.obj (fragment0151413Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0151413_object_field_009"
  err.flush

noncomputable def fragment0151413Chars : List Char := '{' :: (fragment0151413Field000Chars00 ++ fragment0151413Field001Chars00 ++ fragment0151413Field002Chars00 ++ fragment0151413Field003Chars00 ++ fragment0151413Field004Chars00 ++ fragment0151413Field005Chars00 ++ fragment0151413Field006Chars00 ++ fragment0151413Field007Chars00 ++ fragment0151413Field008Chars00 ++ fragment0151413Field009Chars00)
noncomputable def fragment0151413Value : SourceJson := .obj (fragment0151413Acc01000.reverse)

theorem value_fragment0151413 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 490) (fragment0151413Chars ++ tail) =
      .ok (fragment0151413Value, tail) := by
  have hinput : fragment0151413Chars ++ tail = '{' :: (fragment0151413Field000Chars00 ++ (fragment0151413Field001Chars00 ++ (fragment0151413Field002Chars00 ++ (fragment0151413Field003Chars00 ++ (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0151413Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 490) (fragment0151413Chars ++ tail) =
        SourceJson.value (fuel + 490) ('{' :: (fragment0151413Field000Chars00 ++ (fragment0151413Field001Chars00 ++ (fragment0151413Field002Chars00 ++ (fragment0151413Field003Chars00 ++ (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 490)) hinput
    _ = SourceJson.object (fuel + 489) (SourceJson.white (fragment0151413Field000Chars00 ++ (fragment0151413Field001Chars00 ++ (fragment0151413Field002Chars00 ++ (fragment0151413Field003Chars00 ++ (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))))))))))) fragment0151413Acc00000 := by rfl
    _ = SourceJson.object (fuel + 488) (SourceJson.white (fragment0151413Field001Chars00 ++ (fragment0151413Field002Chars00 ++ (fragment0151413Field003Chars00 ++ (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail))))))))))) fragment0151413Acc00100 := object_fragment0151413_field_000 fuel (fragment0151413Field001Chars00 ++ (fragment0151413Field002Chars00 ++ (fragment0151413Field003Chars00 ++ (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 487) (SourceJson.white (fragment0151413Field002Chars00 ++ (fragment0151413Field003Chars00 ++ (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))))))))) fragment0151413Acc00200 := object_fragment0151413_field_001 fuel (fragment0151413Field002Chars00 ++ (fragment0151413Field003Chars00 ++ (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 486) (SourceJson.white (fragment0151413Field003Chars00 ++ (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail))))))))) fragment0151413Acc00300 := object_fragment0151413_field_002 fuel (fragment0151413Field003Chars00 ++ (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 485) (SourceJson.white (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))))))) fragment0151413Acc00400 := object_fragment0151413_field_003 fuel (fragment0151413Field004Chars00 ++ (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 484) (SourceJson.white (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail))))))) fragment0151413Acc00500 := object_fragment0151413_field_004 fuel (fragment0151413Field005Chars00 ++ (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 483) (SourceJson.white (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))))) fragment0151413Acc00600 := object_fragment0151413_field_005 fuel (fragment0151413Field006Chars00 ++ (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 482) (SourceJson.white (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail))))) fragment0151413Acc00700 := object_fragment0151413_field_006 fuel (fragment0151413Field007Chars00 ++ (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 481) (SourceJson.white (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))) fragment0151413Acc00800 := object_fragment0151413_field_007 fuel (fragment0151413Field008Chars00 ++ (fragment0151413Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 480) (SourceJson.white (fragment0151413Field009Chars00 ++ (tail))) fragment0151413Acc00900 := object_fragment0151413_field_008 fuel (fragment0151413Field009Chars00 ++ (tail))
    _ = .ok (fragment0151413Value, tail) := object_fragment0151413_field_009 fuel (tail)

noncomputable def fragment0153547Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0153547Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0153547Field000Value00 : SourceJson := .number (String.ofList ['1', '5'])
noncomputable def fragment0153547Acc00100 : List (String × SourceJson) := (fragment0153547Field000Key00, fragment0153547Field000Value00) :: fragment0153547Acc00000
noncomputable def fragment0153547Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '5', ',']

theorem object_fragment0153547_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 415) (SourceJson.white (fragment0153547Field000Chars00 ++ tail)) fragment0153547Acc00000 =
      SourceJson.object (fuel + 414) (SourceJson.white tail) fragment0153547Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_000"
  err.flush

noncomputable def fragment0153547Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0153547Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0153547Acc00200 : List (String × SourceJson) := (fragment0153547Field001Key00, fragment0153547Field001Value00) :: fragment0153547Acc00100
noncomputable def fragment0153547Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0153547_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 414) (SourceJson.white (fragment0153547Field001Chars00 ++ tail)) fragment0153547Acc00100 =
      SourceJson.object (fuel + 413) (SourceJson.white tail) fragment0153547Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_001"
  err.flush

noncomputable def fragment0153547Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0153547Field002Value00 : SourceJson := .str (String.ofList ['2', '7', '7', '6', '6', '6', '0', '4', '0', '5', '9', '0', '9', '2', '1', '6', '9', '4', '4', '8', '2', '9', '0', '0', '8', '7', '8', '9', '3', '3', '0', '9', '5', '1', '8', '9', '2', '3', '0', '7', '2', '3', '3', '7', '0', '9', '9', '/', '1', '5', '3', '1', '2', '4', '7', '8', '9', '7', '2', '9', '4', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0153547Acc00300 : List (String × SourceJson) := (fragment0153547Field002Key00, fragment0153547Field002Value00) :: fragment0153547Acc00200
noncomputable def fragment0153547Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '7', '7', '6', '6', '6', '0', '4', '0', '5', '9', '0', '9', '2', '1', '6', '9', '4', '4', '8', '2', '9', '0', '0', '8', '7', '8', '9', '3', '3', '0', '9', '5', '1', '8', '9', '2', '3', '0', '7', '2', '3', '3', '7', '0', '9', '9', '/', '1', '5', '3', '1', '2', '4', '7', '8', '9', '7', '2', '9', '4', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0153547_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 413) (SourceJson.white (fragment0153547Field002Chars00 ++ tail)) fragment0153547Acc00200 =
      SourceJson.object (fuel + 412) (SourceJson.white tail) fragment0153547Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_002"
  err.flush

noncomputable def fragment0153547Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0153547Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0153547Acc00400 : List (String × SourceJson) := (fragment0153547Field003Key00, fragment0153547Field003Value00) :: fragment0153547Acc00300
noncomputable def fragment0153547Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0153547_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 412) (SourceJson.white (fragment0153547Field003Chars00 ++ tail)) fragment0153547Acc00300 =
      SourceJson.object (fuel + 411) (SourceJson.white tail) fragment0153547Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_003"
  err.flush

noncomputable def fragment0153547Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0153547Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0153547Acc00500 : List (String × SourceJson) := (fragment0153547Field004Key00, fragment0153547Field004Value00) :: fragment0153547Acc00400
noncomputable def fragment0153547Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '3', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0153547_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 411) (SourceJson.white (fragment0153547Field004Chars00 ++ tail)) fragment0153547Acc00400 =
      SourceJson.object (fuel + 410) (SourceJson.white tail) fragment0153547Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_004"
  err.flush

noncomputable def fragment0153547Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0153547Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '6', '8', '7', '4', '0', '1', '0', '1', '7', '3', '5', '2', '6', '2', '8', '0', '2', '7', '2', '5', '9', '/', '1', '8', '6', '3', '8', '7', '1', '4', '6', '6', '7', '1', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '3', '6', '9', '1', '5', '4', '5', '6', '6', '0', '0', '5', '3', '4', '8', '7', '5', '3', '/', '2', '6', '6', '2', '6', '7', '3', '5', '2', '3', '8', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '4', '1', '5', '0', '0', '8', '4', '6', '2', '1', '1', '7', '4', '9', '7', '3', '2', '0', '9', '3', '7', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '8', '0', '3', '4', '4', '0', '2', '3', '4', '8', '5', '0', '1', '3', '3', '2', '1', '5', '4', '5', '1', '/', '1', '7', '1', '4', '7', '6', '1', '7', '4', '9', '3', '7', '8', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '3', '7', '3', '1', '2', '4', '8', '3', '1', '2', '2', '0', '7', '5', '8', '0', '4', '6', '5', '9', '/', '9', '5', '2', '6', '4', '5', '4', '1', '6', '3', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '9', '3', '9', '0', '6', '2', '4', '0', '9', '0', '8', '7', '0', '9', '8', '0', '5', '7', '4', '9', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '9', '4', '2', '4', '0', '2', '1', '1', '7', '3', '9', '2', '6', '3', '3', '9', '0', '1', '4', '1', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '8', '3', '1', '6', '8', '9', '8', '8', '7', '1', '7', '0', '1', '8', '8', '7', '2', '8', '1', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '7', '1', '0', '7', '6', '3', '8', '2', '2', '1', '1', '6', '3', '5', '4', '2', '5', '6', '1', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '9', '9', '5', '4', '8', '6', '4', '7', '7', '0', '3', '8', '0', '5', '1', '7', '1', '/', '8', '8', '7', '5', '5', '7', '8', '4', '1', '2', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0153547Acc00600 : List (String × SourceJson) := (fragment0153547Field005Key00, fragment0153547Field005Value00) :: fragment0153547Acc00500
noncomputable def fragment0153547Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '8', '7', '4', '0', '1', '0', '1', '7', '3', '5', '2', '6', '2', '8', '0', '2', '7', '2', '5', '9', '/', '1', '8', '6', '3', '8', '7', '1', '4', '6', '6', '7', '1', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '3', '6', '9', '1', '5', '4', '5', '6', '6', '0', '0', '5', '3', '4', '8', '7', '5', '3', '/', '2', '6', '6', '2', '6', '7', '3', '5', '2', '3', '8', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '4', '1', '5', '0', '0', '8', '4', '6', '2', '1', '1', '7', '4', '9', '7', '3', '2', '0', '9', '3', '7', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '8', '0', '3', '4', '4', '0', '2', '3', '4', '8', '5', '0', '1', '3', '3', '2', '1', '5', '4', '5', '1', '/', '1', '7', '1', '4', '7', '6', '1', '7', '4', '9', '3', '7', '8', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '3', '7', '3', '1', '2', '4', '8', '3', '1', '2', '2', '0', '7', '5', '8', '0', '4', '6', '5', '9', '/', '9', '5', '2', '6', '4', '5', '4', '1', '6', '3', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '9', '3', '9', '0', '6', '2', '4', '0', '9', '0', '8', '7', '0', '9', '8', '0', '5', '7', '4', '9', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '9', '4', '2', '4', '0', '2', '1', '1', '7', '3', '9', '2', '6', '3', '3', '9', '0', '1', '4', '1', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '0', '8', '3', '1', '6', '8', '9', '8', '8', '7', '1', '7', '0', '1', '8', '8', '7', '2', '8', '1', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '8', '7', '1', '0', '7', '6', '3', '8', '2', '2', '1', '1', '6', '3', '5', '4', '2', '5', '6', '1', '/', '3', '8', '9', '7', '1', '8', '5', '7', '9', '4', '0', '4', '1', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '9', '9', '5', '4', '8', '6', '4', '7', '7', '0', '3', '8', '0', '5', '1', '7', '1', '/', '8', '8', '7', '5', '5', '7', '8', '4', '1', '2', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0153547_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 410) (SourceJson.white (fragment0153547Field005Chars00 ++ tail)) fragment0153547Acc00500 =
      SourceJson.object (fuel + 409) (SourceJson.white tail) fragment0153547Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_005"
  err.flush

noncomputable def fragment0153547Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0153547Field006Value00 : SourceJson := .str (String.ofList ['4', '3', '0', '9', '9', '9', '4', '1', '9', '5', '6', '3', '7', '6', '4', '9', '8', '2', '0', '9', '4', '3', '2', '0', '8', '1', '2', '0', '0', '9', '7', '6', '1', '3', '5', '4', '0', '4', '6', '8', '7', '8', '5', '8', '6', '3', '7', '9', '3', '6', '0', '0', '/', '1', '3', '2', '8', '2', '8', '7', '1', '2', '0', '7', '0', '5', '2', '3', '8', '6', '7', '6', '2', '1', '2', '7', '3', '4', '8', '0', '2', '6', '8', '0', '7', '8', '0', '7', '6', '4', '1', '2', '9', '5', '3', '6', '8', '5', '0', '6', '2', '3', '4', '0', '1', '2', '7', '2', '6', '5', '1', '8', '8', '2', '3', '4', '7', '7'])
noncomputable def fragment0153547Acc00700 : List (String × SourceJson) := (fragment0153547Field006Key00, fragment0153547Field006Value00) :: fragment0153547Acc00600
noncomputable def fragment0153547Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '3', '0', '9', '9', '9', '4', '1', '9', '5', '6', '3', '7', '6', '4', '9', '8', '2', '0', '9', '4', '3', '2', '0', '8', '1', '2', '0', '0', '9', '7', '6', '1', '3', '5', '4', '0', '4', '6', '8', '7', '8', '5', '8', '6', '3', '7', '9', '3', '6', '0', '0', '/', '1', '3', '2', '8', '2', '8', '7', '1', '2', '0', '7', '0', '5', '2', '3', '8', '6', '7', '6', '2', '1', '2', '7', '3', '4', '8', '0', '2', '6', '8', '0', '7', '8', '0', '7', '6', '4', '1', '2', '9', '5', '3', '6', '8', '5', '0', '6', '2', '3', '4', '0', '1', '2', '7', '2', '6', '5', '1', '8', '8', '2', '3', '4', '7', '7', '"', ',']

theorem object_fragment0153547_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 409) (SourceJson.white (fragment0153547Field006Chars00 ++ tail)) fragment0153547Acc00600 =
      SourceJson.object (fuel + 408) (SourceJson.white tail) fragment0153547Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_006"
  err.flush

noncomputable def fragment0153547Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0153547Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '7', '4', '7', '8', '2', '3', '9', '5', '5', '1', '1', '4', '7', '4', '0', '4', '5', '4', '4', '6', '5', '7', '6', '3', '3', '6', '6', '7', '5', '8', '3', '0', '1', '3', '2', '3', '4', '8', '0', '7', '5', '5', '7', '2', '0', '9', '8', '6', '3', '8', '1', '0', '3', '4', '7', '6', '5', '3', '4', '5', '2', '0', '3', '0', '4', '3', '1', '6', '5', '7', '3', '8', '2', '4', '1', '9', '8', '8', '3', '3', '0', '3', '4', '6', '7', '1', '8', '6', '4', '5', '6', '3', '6', '6', '0', '6', '1', '2', '2', '2', '3', '5', '4', '1', '5', '6', '1', '9', '0', '0', '7', '0', '6', '3', '1', '7', '1', '3', '2', '9', '5', '2', '1', '0', '4', '3', '6', '4', '6', '2', '6', '8', '3', '2', '9', '5', '9', '2', '5', '0', '7', '7', '2', '9', '1', '0', '7', '7', '4', '0', '9', '3', '8', '8', '8', '2', '4', '6', '9', '5', '6', '6', '4', '4', '0', '5', '3', '6', '2', '5', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '6', '0', '5', '2', '1', '7', '1', '5', '6', '4', '7', '7', '2', '6', '3', '8', '8', '1', '0', '8', '8', '6', '5', '7', '2', '0', '8', '4', '0', '2', '5', '6', '9', '0', '8', '0', '1', '0', '7', '0', '4', '2', '3', '9', '4', '6', '2', '4', '1', '0', '8', '7', '0', '5', '0', '7', '7', '0', '7', '9', '3', '7', '5', '8', '8', '0', '2', '2', '8', '3', '4', '9', '4', '5', '6', '4', '9', '6', '1', '8', '8', '0', '1', '0', '1', '1', '6', '8', '9', '2', '8', '5', '6', '9', '4', '3', '7', '5', '2', '6', '4', '9', '9', '6', '7', '1', '0', '9', '1', '7', '8', '9', '3', '0', '5', '4', '9', '3', '1', '2', '3', '7', '0', '3', '4', '8', '8', '7', '5', '1', '8', '3', '7', '2', '3', '1', '3', '5', '6', '4', '4', '3', '0', '8', '1', '4', '9', '6', '3', '1', '4', '9', '5', '8', '9', '3', '2', '4', '6', '9', '7', '6', '4', '9', '2', '8', '5', '2', '2', '5', '4', '1', '4', '9', '0', '2', '3', '4', '4', '2', '2', '7', '5', '8', '5', '1', '8', '3', '9', '0', '7', '3', '1', '2', '8', '0', '6', '2', '9', '7', '4', '8', '2', '2', '2', '9'])
noncomputable def fragment0153547Acc00800 : List (String × SourceJson) := (fragment0153547Field007Key00, fragment0153547Field007Value00) :: fragment0153547Acc00700
noncomputable def fragment0153547Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '7', '4', '7', '8', '2', '3', '9', '5', '5', '1', '1', '4', '7', '4', '0', '4', '5', '4', '4', '6', '5', '7', '6', '3', '3', '6', '6', '7', '5', '8', '3', '0', '1', '3', '2', '3', '4', '8', '0', '7', '5', '5', '7', '2', '0', '9', '8', '6', '3', '8', '1', '0', '3', '4', '7', '6', '5', '3', '4', '5', '2', '0', '3', '0', '4', '3', '1', '6', '5', '7', '3', '8', '2', '4', '1', '9', '8', '8', '3', '3', '0', '3', '4', '6', '7', '1', '8', '6', '4', '5', '6', '3', '6', '6', '0', '6', '1', '2', '2', '2', '3', '5', '4', '1', '5', '6', '1', '9', '0', '0', '7', '0', '6', '3', '1', '7', '1', '3', '2', '9', '5', '2', '1', '0', '4', '3', '6', '4', '6', '2', '6', '8', '3', '2', '9', '5', '9', '2', '5', '0', '7', '7', '2', '9', '1', '0', '7', '7', '4', '0', '9', '3', '8', '8', '8', '2', '4', '6', '9', '5', '6', '6', '4', '4', '0', '5', '3', '6', '2', '5', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '6', '0', '5', '2', '1', '7', '1', '5', '6', '4', '7', '7', '2', '6', '3', '8', '8', '1', '0', '8', '8', '6', '5', '7', '2', '0', '8', '4', '0', '2', '5', '6', '9', '0', '8', '0', '1', '0', '7', '0', '4', '2', '3', '9', '4', '6', '2', '4', '1', '0', '8', '7', '0', '5', '0', '7', '7', '0', '7', '9', '3', '7', '5', '8', '8', '0', '2', '2', '8', '3', '4', '9', '4', '5', '6', '4', '9', '6', '1', '8', '8', '0', '1', '0', '1', '1', '6', '8', '9', '2', '8', '5', '6', '9', '4', '3', '7', '5', '2', '6', '4', '9', '9', '6', '7', '1', '0', '9', '1', '7', '8', '9', '3', '0', '5', '4', '9', '3', '1', '2', '3', '7', '0', '3', '4', '8', '8', '7', '5', '1', '8', '3', '7', '2', '3', '1', '3', '5', '6', '4', '4', '3', '0', '8', '1', '4', '9', '6', '3', '1', '4', '9', '5', '8', '9', '3', '2', '4', '6', '9', '7', '6', '4', '9', '2', '8', '5', '2', '2', '5', '4', '1', '4', '9', '0', '2', '3', '4', '4', '2', '2', '7', '5', '8', '5', '1', '8', '3', '9', '0', '7', '3', '1', '2', '8', '0', '6', '2', '9', '7', '4', '8', '2', '2', '2', '9', '"', ',']

theorem object_fragment0153547_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 408) (SourceJson.white (fragment0153547Field007Chars00 ++ tail)) fragment0153547Acc00700 =
      SourceJson.object (fuel + 407) (SourceJson.white tail) fragment0153547Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_007"
  err.flush

noncomputable def fragment0153547Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0153547Field008Value00 : SourceJson := .str (String.ofList ['2', '5', '7', '0', '7', '7', '6', '4', '1', '7', '5', '7', '3', '1', '4', '2', '0'])
noncomputable def fragment0153547Acc00900 : List (String × SourceJson) := (fragment0153547Field008Key00, fragment0153547Field008Value00) :: fragment0153547Acc00800
noncomputable def fragment0153547Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '7', '0', '7', '7', '6', '4', '1', '7', '5', '7', '3', '1', '4', '2', '0', '"', ',']

theorem object_fragment0153547_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 407) (SourceJson.white (fragment0153547Field008Chars00 ++ tail)) fragment0153547Acc00800 =
      SourceJson.object (fuel + 406) (SourceJson.white tail) fragment0153547Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_008"
  err.flush

noncomputable def fragment0153547Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0153547Field009Value00 : SourceJson := .str (String.ofList ['9', '8', '9', '8', '0', '5', '3', '6', '3', '9', '8', '0', '3', '6', '7', '9', '1'])
noncomputable def fragment0153547Acc01000 : List (String × SourceJson) := (fragment0153547Field009Key00, fragment0153547Field009Value00) :: fragment0153547Acc00900
noncomputable def fragment0153547Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '8', '9', '8', '0', '5', '3', '6', '3', '9', '8', '0', '3', '6', '7', '9', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0153547_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 406) (SourceJson.white (fragment0153547Field009Chars00 ++ tail)) fragment0153547Acc00900 =
      .ok (.obj (fragment0153547Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0153547_object_field_009"
  err.flush

noncomputable def fragment0153547Chars : List Char := '{' :: (fragment0153547Field000Chars00 ++ fragment0153547Field001Chars00 ++ fragment0153547Field002Chars00 ++ fragment0153547Field003Chars00 ++ fragment0153547Field004Chars00 ++ fragment0153547Field005Chars00 ++ fragment0153547Field006Chars00 ++ fragment0153547Field007Chars00 ++ fragment0153547Field008Chars00 ++ fragment0153547Field009Chars00)
noncomputable def fragment0153547Value : SourceJson := .obj (fragment0153547Acc01000.reverse)

theorem value_fragment0153547 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 416) (fragment0153547Chars ++ tail) =
      .ok (fragment0153547Value, tail) := by
  have hinput : fragment0153547Chars ++ tail = '{' :: (fragment0153547Field000Chars00 ++ (fragment0153547Field001Chars00 ++ (fragment0153547Field002Chars00 ++ (fragment0153547Field003Chars00 ++ (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0153547Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 416) (fragment0153547Chars ++ tail) =
        SourceJson.value (fuel + 416) ('{' :: (fragment0153547Field000Chars00 ++ (fragment0153547Field001Chars00 ++ (fragment0153547Field002Chars00 ++ (fragment0153547Field003Chars00 ++ (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 416)) hinput
    _ = SourceJson.object (fuel + 415) (SourceJson.white (fragment0153547Field000Chars00 ++ (fragment0153547Field001Chars00 ++ (fragment0153547Field002Chars00 ++ (fragment0153547Field003Chars00 ++ (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))))))))))) fragment0153547Acc00000 := by rfl
    _ = SourceJson.object (fuel + 414) (SourceJson.white (fragment0153547Field001Chars00 ++ (fragment0153547Field002Chars00 ++ (fragment0153547Field003Chars00 ++ (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail))))))))))) fragment0153547Acc00100 := object_fragment0153547_field_000 fuel (fragment0153547Field001Chars00 ++ (fragment0153547Field002Chars00 ++ (fragment0153547Field003Chars00 ++ (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 413) (SourceJson.white (fragment0153547Field002Chars00 ++ (fragment0153547Field003Chars00 ++ (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))))))))) fragment0153547Acc00200 := object_fragment0153547_field_001 fuel (fragment0153547Field002Chars00 ++ (fragment0153547Field003Chars00 ++ (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 412) (SourceJson.white (fragment0153547Field003Chars00 ++ (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail))))))))) fragment0153547Acc00300 := object_fragment0153547_field_002 fuel (fragment0153547Field003Chars00 ++ (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 411) (SourceJson.white (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))))))) fragment0153547Acc00400 := object_fragment0153547_field_003 fuel (fragment0153547Field004Chars00 ++ (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 410) (SourceJson.white (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail))))))) fragment0153547Acc00500 := object_fragment0153547_field_004 fuel (fragment0153547Field005Chars00 ++ (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 409) (SourceJson.white (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))))) fragment0153547Acc00600 := object_fragment0153547_field_005 fuel (fragment0153547Field006Chars00 ++ (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 408) (SourceJson.white (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail))))) fragment0153547Acc00700 := object_fragment0153547_field_006 fuel (fragment0153547Field007Chars00 ++ (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 407) (SourceJson.white (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))) fragment0153547Acc00800 := object_fragment0153547_field_007 fuel (fragment0153547Field008Chars00 ++ (fragment0153547Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 406) (SourceJson.white (fragment0153547Field009Chars00 ++ (tail))) fragment0153547Acc00900 := object_fragment0153547_field_008 fuel (fragment0153547Field009Chars00 ++ (tail))
    _ = .ok (fragment0153547Value, tail) := object_fragment0153547_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_before_reader"
  err.flush

noncomputable def chunk0008LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0008SuffixChars00 : List Char := [',']
noncomputable def chunk0008Chars00 : List Char := chunk0008LeadChars00 ++ fragment0140279Chars ++ chunk0008SuffixChars00
noncomputable def chunk0008Push00 (acc : List SourceJson) : List SourceJson := fragment0140279Value :: acc

noncomputable def chunk0008AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0008_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 649)
      (SourceJson.white (chunk0008LeadChars00 ++ (fragment0140279Chars ++ rest))) acc =
      (SourceJson.value (fuel + 648) (fragment0140279Chars ++ rest)).bind
        (chunk0008AfterValue00 (fuel + 648) acc) := by rfl

theorem array_chunk0008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 649) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 648) (SourceJson.white tail) (chunk0008Push00 acc) := by
  have hinput : chunk0008Chars00 ++ tail = chunk0008LeadChars00 ++ (fragment0140279Chars ++ (chunk0008SuffixChars00 ++ tail)) := by
    simp only [chunk0008Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 649) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 649)
          (SourceJson.white (chunk0008LeadChars00 ++ (fragment0140279Chars ++ (chunk0008SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 649) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 648) (fragment0140279Chars ++ (chunk0008SuffixChars00 ++ tail))).bind
        (chunk0008AfterValue00 (fuel + 648) acc) := array_chunk0008_head fuel (chunk0008SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0140279Value, chunk0008SuffixChars00 ++ tail)).bind
        (chunk0008AfterValue00 (fuel + 648) acc) :=
      congrArg (fun result => result.bind (chunk0008AfterValue00 (fuel + 648) acc))
        (value_fragment0140279 (fuel + 205) (chunk0008SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 648) (SourceJson.white tail) (chunk0008Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0009_before_reader"
  err.flush

noncomputable def chunk0009LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0009SuffixChars00 : List Char := [',']
noncomputable def chunk0009Chars00 : List Char := chunk0009LeadChars00 ++ fragment0142316Chars ++ chunk0009SuffixChars00
noncomputable def chunk0009Push00 (acc : List SourceJson) : List SourceJson := fragment0142316Value :: acc

noncomputable def chunk0009AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0009_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 648)
      (SourceJson.white (chunk0009LeadChars00 ++ (fragment0142316Chars ++ rest))) acc =
      (SourceJson.value (fuel + 647) (fragment0142316Chars ++ rest)).bind
        (chunk0009AfterValue00 (fuel + 647) acc) := by rfl

theorem array_chunk0009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 648) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 647) (SourceJson.white tail) (chunk0009Push00 acc) := by
  have hinput : chunk0009Chars00 ++ tail = chunk0009LeadChars00 ++ (fragment0142316Chars ++ (chunk0009SuffixChars00 ++ tail)) := by
    simp only [chunk0009Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 648) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 648)
          (SourceJson.white (chunk0009LeadChars00 ++ (fragment0142316Chars ++ (chunk0009SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 648) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 647) (fragment0142316Chars ++ (chunk0009SuffixChars00 ++ tail))).bind
        (chunk0009AfterValue00 (fuel + 647) acc) := array_chunk0009_head fuel (chunk0009SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0142316Value, chunk0009SuffixChars00 ++ tail)).bind
        (chunk0009AfterValue00 (fuel + 647) acc) :=
      congrArg (fun result => result.bind (chunk0009AfterValue00 (fuel + 647) acc))
        (value_fragment0142316 (fuel + 245) (chunk0009SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 647) (SourceJson.white tail) (chunk0009Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0009_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_before_reader"
  err.flush

noncomputable def chunk0010LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0010SuffixChars00 : List Char := [',']
noncomputable def chunk0010Chars00 : List Char := chunk0010LeadChars00 ++ fragment0144241Chars ++ chunk0010SuffixChars00
noncomputable def chunk0010Push00 (acc : List SourceJson) : List SourceJson := fragment0144241Value :: acc

noncomputable def chunk0010AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0010_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 647)
      (SourceJson.white (chunk0010LeadChars00 ++ (fragment0144241Chars ++ rest))) acc =
      (SourceJson.value (fuel + 646) (fragment0144241Chars ++ rest)).bind
        (chunk0010AfterValue00 (fuel + 646) acc) := by rfl

theorem array_chunk0010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 647) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 646) (SourceJson.white tail) (chunk0010Push00 acc) := by
  have hinput : chunk0010Chars00 ++ tail = chunk0010LeadChars00 ++ (fragment0144241Chars ++ (chunk0010SuffixChars00 ++ tail)) := by
    simp only [chunk0010Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 647) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 647)
          (SourceJson.white (chunk0010LeadChars00 ++ (fragment0144241Chars ++ (chunk0010SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 647) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 646) (fragment0144241Chars ++ (chunk0010SuffixChars00 ++ tail))).bind
        (chunk0010AfterValue00 (fuel + 646) acc) := array_chunk0010_head fuel (chunk0010SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0144241Value, chunk0010SuffixChars00 ++ tail)).bind
        (chunk0010AfterValue00 (fuel + 646) acc) :=
      congrArg (fun result => result.bind (chunk0010AfterValue00 (fuel + 646) acc))
        (value_fragment0144241 (fuel + 407) (chunk0010SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 646) (SourceJson.white tail) (chunk0010Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_before_reader"
  err.flush

noncomputable def chunk0011LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0011SuffixChars00 : List Char := [',']
noncomputable def chunk0011Chars00 : List Char := chunk0011LeadChars00 ++ fragment0145849Chars ++ chunk0011SuffixChars00
noncomputable def chunk0011Push00 (acc : List SourceJson) : List SourceJson := fragment0145849Value :: acc

noncomputable def chunk0011AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0011_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 646)
      (SourceJson.white (chunk0011LeadChars00 ++ (fragment0145849Chars ++ rest))) acc =
      (SourceJson.value (fuel + 645) (fragment0145849Chars ++ rest)).bind
        (chunk0011AfterValue00 (fuel + 645) acc) := by rfl

theorem array_chunk0011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 646) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 645) (SourceJson.white tail) (chunk0011Push00 acc) := by
  have hinput : chunk0011Chars00 ++ tail = chunk0011LeadChars00 ++ (fragment0145849Chars ++ (chunk0011SuffixChars00 ++ tail)) := by
    simp only [chunk0011Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 646) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 646)
          (SourceJson.white (chunk0011LeadChars00 ++ (fragment0145849Chars ++ (chunk0011SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 646) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 645) (fragment0145849Chars ++ (chunk0011SuffixChars00 ++ tail))).bind
        (chunk0011AfterValue00 (fuel + 645) acc) := array_chunk0011_head fuel (chunk0011SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0145849Value, chunk0011SuffixChars00 ++ tail)).bind
        (chunk0011AfterValue00 (fuel + 645) acc) :=
      congrArg (fun result => result.bind (chunk0011AfterValue00 (fuel + 645) acc))
        (value_fragment0145849 (fuel + 241) (chunk0011SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 645) (SourceJson.white tail) (chunk0011Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_before_reader"
  err.flush

noncomputable def chunk0012LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0012SuffixChars00 : List Char := [',']
noncomputable def chunk0012Chars00 : List Char := chunk0012LeadChars00 ++ fragment0147801Chars ++ chunk0012SuffixChars00
noncomputable def chunk0012Push00 (acc : List SourceJson) : List SourceJson := fragment0147801Value :: acc

noncomputable def chunk0012AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0012_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 645)
      (SourceJson.white (chunk0012LeadChars00 ++ (fragment0147801Chars ++ rest))) acc =
      (SourceJson.value (fuel + 644) (fragment0147801Chars ++ rest)).bind
        (chunk0012AfterValue00 (fuel + 644) acc) := by rfl

theorem array_chunk0012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 645) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 644) (SourceJson.white tail) (chunk0012Push00 acc) := by
  have hinput : chunk0012Chars00 ++ tail = chunk0012LeadChars00 ++ (fragment0147801Chars ++ (chunk0012SuffixChars00 ++ tail)) := by
    simp only [chunk0012Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 645) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 645)
          (SourceJson.white (chunk0012LeadChars00 ++ (fragment0147801Chars ++ (chunk0012SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 645) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 644) (fragment0147801Chars ++ (chunk0012SuffixChars00 ++ tail))).bind
        (chunk0012AfterValue00 (fuel + 644) acc) := array_chunk0012_head fuel (chunk0012SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0147801Value, chunk0012SuffixChars00 ++ tail)).bind
        (chunk0012AfterValue00 (fuel + 644) acc) :=
      congrArg (fun result => result.bind (chunk0012AfterValue00 (fuel + 644) acc))
        (value_fragment0147801 (fuel + 411) (chunk0012SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 644) (SourceJson.white tail) (chunk0012Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_before_reader"
  err.flush

noncomputable def chunk0013LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0013SuffixChars00 : List Char := [',']
noncomputable def chunk0013Chars00 : List Char := chunk0013LeadChars00 ++ fragment0149420Chars ++ chunk0013SuffixChars00
noncomputable def chunk0013Push00 (acc : List SourceJson) : List SourceJson := fragment0149420Value :: acc

noncomputable def chunk0013AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0013_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 644)
      (SourceJson.white (chunk0013LeadChars00 ++ (fragment0149420Chars ++ rest))) acc =
      (SourceJson.value (fuel + 643) (fragment0149420Chars ++ rest)).bind
        (chunk0013AfterValue00 (fuel + 643) acc) := by rfl

theorem array_chunk0013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 644) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 643) (SourceJson.white tail) (chunk0013Push00 acc) := by
  have hinput : chunk0013Chars00 ++ tail = chunk0013LeadChars00 ++ (fragment0149420Chars ++ (chunk0013SuffixChars00 ++ tail)) := by
    simp only [chunk0013Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 644) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 644)
          (SourceJson.white (chunk0013LeadChars00 ++ (fragment0149420Chars ++ (chunk0013SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 644) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 643) (fragment0149420Chars ++ (chunk0013SuffixChars00 ++ tail))).bind
        (chunk0013AfterValue00 (fuel + 643) acc) := array_chunk0013_head fuel (chunk0013SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0149420Value, chunk0013SuffixChars00 ++ tail)).bind
        (chunk0013AfterValue00 (fuel + 643) acc) :=
      congrArg (fun result => result.bind (chunk0013AfterValue00 (fuel + 643) acc))
        (value_fragment0149420 (fuel + 220) (chunk0013SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 643) (SourceJson.white tail) (chunk0013Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_before_reader"
  err.flush

noncomputable def chunk0014LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0014SuffixChars00 : List Char := [',']
noncomputable def chunk0014Chars00 : List Char := chunk0014LeadChars00 ++ fragment0151413Chars ++ chunk0014SuffixChars00
noncomputable def chunk0014Push00 (acc : List SourceJson) : List SourceJson := fragment0151413Value :: acc

noncomputable def chunk0014AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0014_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 643)
      (SourceJson.white (chunk0014LeadChars00 ++ (fragment0151413Chars ++ rest))) acc =
      (SourceJson.value (fuel + 642) (fragment0151413Chars ++ rest)).bind
        (chunk0014AfterValue00 (fuel + 642) acc) := by rfl

theorem array_chunk0014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 643) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 642) (SourceJson.white tail) (chunk0014Push00 acc) := by
  have hinput : chunk0014Chars00 ++ tail = chunk0014LeadChars00 ++ (fragment0151413Chars ++ (chunk0014SuffixChars00 ++ tail)) := by
    simp only [chunk0014Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 643) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 643)
          (SourceJson.white (chunk0014LeadChars00 ++ (fragment0151413Chars ++ (chunk0014SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 643) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 642) (fragment0151413Chars ++ (chunk0014SuffixChars00 ++ tail))).bind
        (chunk0014AfterValue00 (fuel + 642) acc) := array_chunk0014_head fuel (chunk0014SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0151413Value, chunk0014SuffixChars00 ++ tail)).bind
        (chunk0014AfterValue00 (fuel + 642) acc) :=
      congrArg (fun result => result.bind (chunk0014AfterValue00 (fuel + 642) acc))
        (value_fragment0151413 (fuel + 152) (chunk0014SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 642) (SourceJson.white tail) (chunk0014Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_before_reader"
  err.flush

noncomputable def chunk0015LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0015SuffixChars00 : List Char := [',']
noncomputable def chunk0015Chars00 : List Char := chunk0015LeadChars00 ++ fragment0153547Chars ++ chunk0015SuffixChars00
noncomputable def chunk0015Push00 (acc : List SourceJson) : List SourceJson := fragment0153547Value :: acc

noncomputable def chunk0015AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0015_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 642)
      (SourceJson.white (chunk0015LeadChars00 ++ (fragment0153547Chars ++ rest))) acc =
      (SourceJson.value (fuel + 641) (fragment0153547Chars ++ rest)).bind
        (chunk0015AfterValue00 (fuel + 641) acc) := by rfl

theorem array_chunk0015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 642) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 641) (SourceJson.white tail) (chunk0015Push00 acc) := by
  have hinput : chunk0015Chars00 ++ tail = chunk0015LeadChars00 ++ (fragment0153547Chars ++ (chunk0015SuffixChars00 ++ tail)) := by
    simp only [chunk0015Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 642) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 642)
          (SourceJson.white (chunk0015LeadChars00 ++ (fragment0153547Chars ++ (chunk0015SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 642) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 641) (fragment0153547Chars ++ (chunk0015SuffixChars00 ++ tail))).bind
        (chunk0015AfterValue00 (fuel + 641) acc) := array_chunk0015_head fuel (chunk0015SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0153547Value, chunk0015SuffixChars00 ++ tail)).bind
        (chunk0015AfterValue00 (fuel + 641) acc) :=
      congrArg (fun result => result.bind (chunk0015AfterValue00 (fuel + 641) acc))
        (value_fragment0153547 (fuel + 225) (chunk0015SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 641) (SourceJson.white tail) (chunk0015Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0008Chars00 ++ chunk0009Chars00 ++ chunk0010Chars00 ++ chunk0011Chars00 ++ chunk0012Chars00 ++ chunk0013Chars00 ++ chunk0014Chars00 ++ chunk0015Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 649) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 641) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 649) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 649) (SourceJson.white (chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 649) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 648) (SourceJson.white (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))))) (chunk0008Push00 (acc)) := array_chunk0008 fuel (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 647) (SourceJson.white (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (chunk0009Push00 (chunk0008Push00 (acc))) := array_chunk0009 fuel (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0008Push00 (acc))
    _ = SourceJson.array (fuel + 646) (SourceJson.white (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))) := array_chunk0010 fuel (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0009Push00 (chunk0008Push00 (acc)))
    _ = SourceJson.array (fuel + 645) (SourceJson.white (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))) := array_chunk0011 fuel (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))
    _ = SourceJson.array (fuel + 644) (SourceJson.white (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))) := array_chunk0012 fuel (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))
    _ = SourceJson.array (fuel + 643) (SourceJson.white (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))) := array_chunk0013 fuel (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))
    _ = SourceJson.array (fuel + 642) (SourceJson.white (chunk0015Chars00 ++ (tail))) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))) := array_chunk0014 fuel (chunk0015Chars00 ++ (tail)) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))
    _ = SourceJson.array (fuel + 641) (SourceJson.white tail) (blockPush acc) := array_chunk0015 fuel (tail) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 140273).take 15252 = blockChars := by rfl

theorem block_original_split : sourceRest 140273 = blockChars ++ sourceRest 155525 := by
  calc
    sourceRest 140273 = (sourceRest 140273).take 15252 ++ (sourceRest 140273).drop 15252 :=
      (List.take_append_drop 15252 (sourceRest 140273)).symm
    _ = blockChars ++ (sourceRest 140273).drop 15252 :=
      congrArg (fun part => part ++ (sourceRest 140273).drop 15252) block_original_prefix
    _ = blockChars ++ sourceRest 155525 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 140273 15252)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 649) (SourceJson.white (sourceRest 140273)) acc =
      SourceJson.array (fuel + 641) (SourceJson.white (sourceRest 155525)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 649) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 155525) acc)

#print axioms object_fragment0140279_field_000
#print axioms object_fragment0140279_field_001
#print axioms object_fragment0140279_field_002
#print axioms object_fragment0140279_field_003
#print axioms object_fragment0140279_field_004
#print axioms object_fragment0140279_field_005
#print axioms object_fragment0140279_field_006
#print axioms object_fragment0140279_field_007
#print axioms object_fragment0140279_field_008
#print axioms object_fragment0140279_field_009
#print axioms value_fragment0140279
#print axioms object_fragment0142316_field_000
#print axioms object_fragment0142316_field_001
#print axioms object_fragment0142316_field_002
#print axioms object_fragment0142316_field_003
#print axioms object_fragment0142316_field_004
#print axioms object_fragment0142316_field_005
#print axioms object_fragment0142316_field_006
#print axioms object_fragment0142316_field_007
#print axioms object_fragment0142316_field_008
#print axioms object_fragment0142316_field_009
#print axioms value_fragment0142316
#print axioms object_fragment0144241_field_000
#print axioms object_fragment0144241_field_001
#print axioms object_fragment0144241_field_002
#print axioms object_fragment0144241_field_003
#print axioms object_fragment0144241_field_004
#print axioms object_fragment0144241_field_005
#print axioms object_fragment0144241_field_006
#print axioms object_fragment0144241_field_007
#print axioms object_fragment0144241_field_008
#print axioms object_fragment0144241_field_009
#print axioms value_fragment0144241
#print axioms object_fragment0145849_field_000
#print axioms object_fragment0145849_field_001
#print axioms object_fragment0145849_field_002
#print axioms object_fragment0145849_field_003
#print axioms object_fragment0145849_field_004
#print axioms object_fragment0145849_field_005
#print axioms object_fragment0145849_field_006
#print axioms object_fragment0145849_field_007
#print axioms object_fragment0145849_field_008
#print axioms object_fragment0145849_field_009
#print axioms value_fragment0145849
#print axioms object_fragment0147801_field_000
#print axioms object_fragment0147801_field_001
#print axioms object_fragment0147801_field_002
#print axioms object_fragment0147801_field_003
#print axioms object_fragment0147801_field_004
#print axioms object_fragment0147801_field_005
#print axioms object_fragment0147801_field_006
#print axioms object_fragment0147801_field_007
#print axioms object_fragment0147801_field_008
#print axioms object_fragment0147801_field_009
#print axioms value_fragment0147801
#print axioms object_fragment0149420_field_000
#print axioms object_fragment0149420_field_001
#print axioms object_fragment0149420_field_002
#print axioms object_fragment0149420_field_003
#print axioms object_fragment0149420_field_004
#print axioms object_fragment0149420_field_005
#print axioms object_fragment0149420_field_006
#print axioms object_fragment0149420_field_007
#print axioms object_fragment0149420_field_008
#print axioms object_fragment0149420_field_009
#print axioms value_fragment0149420
#print axioms object_fragment0151413_field_000
#print axioms object_fragment0151413_field_001
#print axioms object_fragment0151413_field_002
#print axioms object_fragment0151413_field_003
#print axioms object_fragment0151413_field_004
#print axioms object_fragment0151413_field_005
#print axioms object_fragment0151413_field_006
#print axioms object_fragment0151413_field_007
#print axioms object_fragment0151413_field_008
#print axioms object_fragment0151413_field_009
#print axioms value_fragment0151413
#print axioms object_fragment0153547_field_000
#print axioms object_fragment0153547_field_001
#print axioms object_fragment0153547_field_002
#print axioms object_fragment0153547_field_003
#print axioms object_fragment0153547_field_004
#print axioms object_fragment0153547_field_005
#print axioms object_fragment0153547_field_006
#print axioms object_fragment0153547_field_007
#print axioms object_fragment0153547_field_008
#print axioms object_fragment0153547_field_009
#print axioms value_fragment0153547
#print axioms array_chunk0008_head
#print axioms array_chunk0008
#print axioms array_chunk0009_head
#print axioms array_chunk0009
#print axioms array_chunk0010_head
#print axioms array_chunk0010
#print axioms array_chunk0011_head
#print axioms array_chunk0011
#print axioms array_chunk0012_head
#print axioms array_chunk0012
#print axioms array_chunk0013_head
#print axioms array_chunk0013
#print axioms array_chunk0014_head
#print axioms array_chunk0014
#print axioms array_chunk0015_head
#print axioms array_chunk0015
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock001

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
