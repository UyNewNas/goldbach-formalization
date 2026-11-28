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

namespace SimplicesBlock004

noncomputable def fragment0185897Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0185897Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0185897Field000Value00 : SourceJson := .number (String.ofList ['3', '2'])
noncomputable def fragment0185897Acc00100 : List (String × SourceJson) := (fragment0185897Field000Key00, fragment0185897Field000Value00) :: fragment0185897Acc00000
noncomputable def fragment0185897Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '2', ',']

theorem object_fragment0185897_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 484) (SourceJson.white (fragment0185897Field000Chars00 ++ tail)) fragment0185897Acc00000 =
      SourceJson.object (fuel + 483) (SourceJson.white tail) fragment0185897Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_000"
  err.flush

noncomputable def fragment0185897Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0185897Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0185897Acc00200 : List (String × SourceJson) := (fragment0185897Field001Key00, fragment0185897Field001Value00) :: fragment0185897Acc00100
noncomputable def fragment0185897Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0185897_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 483) (SourceJson.white (fragment0185897Field001Chars00 ++ tail)) fragment0185897Acc00100 =
      SourceJson.object (fuel + 482) (SourceJson.white tail) fragment0185897Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_001"
  err.flush

noncomputable def fragment0185897Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0185897Field002Value00 : SourceJson := .str (String.ofList ['6', '6', '4', '5', '9', '4', '8', '9', '8', '9', '8', '9', '0', '0', '6', '1', '9', '4', '3', '3', '3', '3', '0', '6', '8', '1', '2', '5', '4', '6', '6', '9', '8', '4', '5', '7', '0', '9', '1', '4', '1', '7', '1', '/', '6', '6', '7', '0', '2', '0', '8', '6', '4', '3', '5', '1', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0185897Acc00300 : List (String × SourceJson) := (fragment0185897Field002Key00, fragment0185897Field002Value00) :: fragment0185897Acc00200
noncomputable def fragment0185897Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '6', '4', '5', '9', '4', '8', '9', '8', '9', '8', '9', '0', '0', '6', '1', '9', '4', '3', '3', '3', '3', '0', '6', '8', '1', '2', '5', '4', '6', '6', '9', '8', '4', '5', '7', '0', '9', '1', '4', '1', '7', '1', '/', '6', '6', '7', '0', '2', '0', '8', '6', '4', '3', '5', '1', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0185897_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 482) (SourceJson.white (fragment0185897Field002Chars00 ++ tail)) fragment0185897Acc00200 =
      SourceJson.object (fuel + 481) (SourceJson.white tail) fragment0185897Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_002"
  err.flush

noncomputable def fragment0185897Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0185897Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0185897Acc00400 : List (String × SourceJson) := (fragment0185897Field003Key00, fragment0185897Field003Value00) :: fragment0185897Acc00300
noncomputable def fragment0185897Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0185897_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 481) (SourceJson.white (fragment0185897Field003Chars00 ++ tail)) fragment0185897Acc00300 =
      SourceJson.object (fuel + 480) (SourceJson.white tail) fragment0185897Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_003"
  err.flush

noncomputable def fragment0185897Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0185897Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0185897Acc00500 : List (String × SourceJson) := (fragment0185897Field004Key00, fragment0185897Field004Value00) :: fragment0185897Acc00400
noncomputable def fragment0185897Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0185897_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 480) (SourceJson.white (fragment0185897Field004Chars00 ++ tail)) fragment0185897Acc00400 =
      SourceJson.object (fuel + 479) (SourceJson.white tail) fragment0185897Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_004"
  err.flush

noncomputable def fragment0185897Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0185897Field005Value00 : SourceJson := .arr [.str (String.ofList ['4', '2', '2', '4', '7', '6', '6', '3', '6', '0', '5', '3', '8', '9', '8', '1', '0', '0', '6', '2', '1', '3', '3', '9', '3', '/', '4', '7', '2', '9', '6', '3', '6', '2', '5', '0', '2', '4', '0', '0', '0', '9', '1', '6', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '1', '2', '8', '5', '4', '7', '8', '3', '3', '3', '3', '2', '1', '7', '0', '1', '1', '4', '3', '3', '2', '9', '/', '3', '9', '2', '8', '2', '6', '9', '3', '1', '0', '8', '3', '0', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '7', '4', '3', '0', '9', '1', '5', '5', '4', '3', '1', '9', '1', '5', '4', '4', '1', '3', '3', '2', '8', '8', '3', '/', '1', '0', '2', '8', '1', '8', '1', '7', '9', '3', '5', '3', '0', '4', '3', '6', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '1', '4', '8', '4', '8', '7', '2', '7', '4', '6', '6', '4', '4', '8', '9', '7', '8', '7', '2', '3', '7', '9', '8', '7', '9', '/', '2', '3', '6', '4', '8', '1', '8', '1', '2', '5', '1', '2', '0', '0', '0', '4', '5', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '3', '4', '8', '1', '9', '2', '8', '5', '9', '6', '5', '8', '9', '5', '1', '4', '1', '0', '8', '1', '6', '1', '2', '1', '/', '7', '8', '8', '2', '7', '2', '7', '0', '8', '3', '7', '3', '3', '3', '4', '8', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '6', '2', '0', '4', '3', '0', '1', '7', '6', '2', '7', '3', '3', '1', '3', '3', '9', '5', '8', '6', '2', '9', '3', '/', '4', '2', '9', '9', '6', '6', '9', '3', '1', '8', '4', '0', '0', '0', '0', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '0', '6', '7', '3', '6', '0', '1', '9', '1', '7', '7', '6', '9', '4', '1', '9', '9', '4', '8', '3', '6', '9', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '5', '8', '5', '7', '3', '9', '3', '5', '5', '2', '2', '8', '8', '4', '0', '2', '3', '6', '3', '7', '0', '3', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '2', '4', '7', '3', '6', '1', '9', '1', '7', '7', '6', '8', '9', '6', '8', '4', '3', '0', '4', '9', '8', '3', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '0', '5', '2', '0', '7', '4', '9', '3', '0', '2', '1', '0', '7', '5', '5', '7', '2', '6', '8', '4', '1', '/', '1', '3', '0', '9', '4', '2', '3', '1', '0', '3', '6', '1', '0', '1', '9', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0185897Acc00600 : List (String × SourceJson) := (fragment0185897Field005Key00, fragment0185897Field005Value00) :: fragment0185897Acc00500
noncomputable def fragment0185897Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '2', '4', '7', '6', '6', '3', '6', '0', '5', '3', '8', '9', '8', '1', '0', '0', '6', '2', '1', '3', '3', '9', '3', '/', '4', '7', '2', '9', '6', '3', '6', '2', '5', '0', '2', '4', '0', '0', '0', '9', '1', '6', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '6', '1', '2', '8', '5', '4', '7', '8', '3', '3', '3', '3', '2', '1', '7', '0', '1', '1', '4', '3', '3', '2', '9', '/', '3', '9', '2', '8', '2', '6', '9', '3', '1', '0', '8', '3', '0', '5', '7', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '7', '4', '3', '0', '9', '1', '5', '5', '4', '3', '1', '9', '1', '5', '4', '4', '1', '3', '3', '2', '8', '8', '3', '/', '1', '0', '2', '8', '1', '8', '1', '7', '9', '3', '5', '3', '0', '4', '3', '6', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '4', '8', '4', '8', '7', '2', '7', '4', '6', '6', '4', '4', '8', '9', '7', '8', '7', '2', '3', '7', '9', '8', '7', '9', '/', '2', '3', '6', '4', '8', '1', '8', '1', '2', '5', '1', '2', '0', '0', '0', '4', '5', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '9', '3', '4', '8', '1', '9', '2', '8', '5', '9', '6', '5', '8', '9', '5', '1', '4', '1', '0', '8', '1', '6', '1', '2', '1', '/', '7', '8', '8', '2', '7', '2', '7', '0', '8', '3', '7', '3', '3', '3', '4', '8', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '6', '2', '0', '4', '3', '0', '1', '7', '6', '2', '7', '3', '3', '1', '3', '3', '9', '5', '8', '6', '2', '9', '3', '/', '4', '2', '9', '9', '6', '6', '9', '3', '1', '8', '4', '0', '0', '0', '0', '8', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '0', '6', '7', '3', '6', '0', '1', '9', '1', '7', '7', '6', '9', '4', '1', '9', '9', '4', '8', '3', '6', '9', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '5', '8', '5', '7', '3', '9', '3', '5', '5', '2', '2', '8', '8', '4', '0', '2', '3', '6', '3', '7', '0', '3', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '2', '4', '7', '3', '6', '1', '9', '1', '7', '7', '6', '8', '9', '6', '8', '4', '3', '0', '4', '9', '8', '3', '/', '2', '1', '4', '9', '8', '3', '4', '6', '5', '9', '2', '0', '0', '0', '0', '4', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '0', '5', '2', '0', '7', '4', '9', '3', '0', '2', '1', '0', '7', '5', '5', '7', '2', '6', '8', '4', '1', '/', '1', '3', '0', '9', '4', '2', '3', '1', '0', '3', '6', '1', '0', '1', '9', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0185897_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 479) (SourceJson.white (fragment0185897Field005Chars00 ++ tail)) fragment0185897Acc00500 =
      SourceJson.object (fuel + 478) (SourceJson.white tail) fragment0185897Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_005"
  err.flush

noncomputable def fragment0185897Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0185897Field006Value00 : SourceJson := .str (String.ofList ['2', '8', '4', '4', '7', '2', '0', '9', '3', '5', '0', '1', '8', '5', '5', '1', '7', '0', '5', '5', '8', '8', '3', '9', '0', '4', '8', '6', '0', '6', '4', '2', '3', '8', '8', '0', '3', '3', '0', '0', '3', '5', '2', '8', '6', '1', '6', '8', '6', '1', '7', '3', '1', '8', '4', '0', '0', '0', '0', '0', '/', '7', '3', '2', '2', '1', '5', '0', '4', '1', '1', '5', '5', '4', '3', '5', '9', '6', '4', '4', '0', '0', '3', '8', '8', '2', '1', '3', '4', '1', '8', '2', '0', '0', '9', '1', '6', '0', '6', '7', '5', '9', '2', '2', '2', '0', '1', '6', '0', '3', '9', '8', '5', '3', '1', '2', '5', '5', '6', '7', '2', '6', '9', '3', '7', '1', '5', '6', '0', '7', '8', '3', '7', '3'])
noncomputable def fragment0185897Acc00700 : List (String × SourceJson) := (fragment0185897Field006Key00, fragment0185897Field006Value00) :: fragment0185897Acc00600
noncomputable def fragment0185897Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '8', '4', '4', '7', '2', '0', '9', '3', '5', '0', '1', '8', '5', '5', '1', '7', '0', '5', '5', '8', '8', '3', '9', '0', '4', '8', '6', '0', '6', '4', '2', '3', '8', '8', '0', '3', '3', '0', '0', '3', '5', '2', '8', '6', '1', '6', '8', '6', '1', '7', '3', '1', '8', '4', '0', '0', '0', '0', '0', '/', '7', '3', '2', '2', '1', '5', '0', '4', '1', '1', '5', '5', '4', '3', '5', '9', '6', '4', '4', '0', '0', '3', '8', '8', '2', '1', '3', '4', '1', '8', '2', '0', '0', '9', '1', '6', '0', '6', '7', '5', '9', '2', '2', '2', '0', '1', '6', '0', '3', '9', '8', '5', '3', '1', '2', '5', '5', '6', '7', '2', '6', '9', '3', '7', '1', '5', '6', '0', '7', '8', '3', '7', '3', '"', ',']

theorem object_fragment0185897_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 478) (SourceJson.white (fragment0185897Field006Chars00 ++ tail)) fragment0185897Acc00600 =
      SourceJson.object (fuel + 477) (SourceJson.white tail) fragment0185897Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_006"
  err.flush

noncomputable def fragment0185897Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0185897Field007Value00 : SourceJson := .str (String.ofList ['1', '4', '4', '6', '3', '4', '2', '8', '2', '6', '0', '6', '2', '7', '4', '6', '0', '5', '1', '3', '1', '1', '4', '8', '4', '9', '6', '1', '7', '7', '2', '5', '3', '8', '3', '7', '0', '1', '9', '6', '3', '5', '2', '0', '3', '2', '5', '3', '9', '7', '3', '4', '1', '0', '0', '1', '1', '3', '2', '0', '6', '2', '7', '1', '6', '3', '0', '3', '7', '3', '1', '8', '6', '0', '2', '1', '9', '5', '0', '4', '9', '6', '3', '1', '9', '0', '0', '7', '1', '4', '7', '8', '7', '1', '9', '6', '5', '6', '5', '3', '4', '5', '5', '3', '7', '8', '0', '4', '9', '2', '1', '1', '9', '3', '9', '2', '8', '5', '2', '8', '4', '5', '9', '9', '7', '8', '1', '8', '5', '1', '2', '4', '5', '0', '0', '1', '0', '4', '6', '9', '6', '2', '5', '5', '7', '2', '8', '9', '4', '7', '8', '0', '8', '1', '7', '6', '5', '8', '6', '1', '6', '2', '7', '2', '2', '3', '0', '5', '8', '3', '8', '1', '8', '5', '5', '3', '2', '5', '1', '1', '3', '0', '4', '4', '4', '2', '6', '1', '9', '3', '0', '4', '4', '9', '7', '0', '6', '2', '7', '3', '2', '7', '3', '4', '3', '6', '1', '1', '3', '4', '6', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '9', '9', '6', '7', '9', '3', '0', '3', '3', '9', '2', '3', '2', '2', '3', '3', '7', '5', '9', '2', '1', '2', '8', '5', '0', '4', '8', '2', '9', '3', '3', '7', '8', '4', '4', '2', '8', '6', '1', '6', '6', '8', '9', '8', '2', '5', '9', '1', '8', '3', '4', '7', '3', '7', '2', '2', '9', '0', '0', '2', '1', '2', '1', '1', '6', '2', '0', '5', '6', '8', '5', '6', '6', '3', '2', '5', '6', '5', '6', '9', '5', '0', '8', '5', '4', '8', '8', '9', '0', '2', '1', '4', '1', '9', '7', '7', '6', '9', '4', '5', '3', '6', '7', '1', '6', '8', '2', '2', '6', '8', '7', '4', '4', '3', '0', '5', '0', '6', '8', '7', '1', '7', '8', '0', '8', '3', '5', '5', '5', '6', '4', '5', '8', '8', '7', '2', '9', '1', '7', '2', '5', '2', '6', '9', '7', '2', '6', '3', '3', '1', '1', '8', '4', '2', '7', '1', '0', '2', '3', '7', '8', '0', '7', '3', '5', '3', '3', '2', '9', '2', '1', '0', '5', '0', '5', '7', '9', '5', '6', '7', '5', '8', '0', '1', '0', '2', '4', '8', '4', '6', '9', '3', '2', '9', '4', '9', '2', '9', '0', '5', '8', '1', '6', '2', '4', '4', '1', '3', '7', '2', '7', '8', '2', '3', '4', '1', '9', '8', '8', '1', '4', '6', '2', '6', '1', '8', '2', '2', '9', '7', '1', '7', '5', '5', '5', '7', '5', '3', '9', '3', '7'])
noncomputable def fragment0185897Acc00800 : List (String × SourceJson) := (fragment0185897Field007Key00, fragment0185897Field007Value00) :: fragment0185897Acc00700
noncomputable def fragment0185897Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '4', '6', '3', '4', '2', '8', '2', '6', '0', '6', '2', '7', '4', '6', '0', '5', '1', '3', '1', '1', '4', '8', '4', '9', '6', '1', '7', '7', '2', '5', '3', '8', '3', '7', '0', '1', '9', '6', '3', '5', '2', '0', '3', '2', '5', '3', '9', '7', '3', '4', '1', '0', '0', '1', '1', '3', '2', '0', '6', '2', '7', '1', '6', '3', '0', '3', '7', '3', '1', '8', '6', '0', '2', '1', '9', '5', '0', '4', '9', '6', '3', '1', '9', '0', '0', '7', '1', '4', '7', '8', '7', '1', '9', '6', '5', '6', '5', '3', '4', '5', '5', '3', '7', '8', '0', '4', '9', '2', '1', '1', '9', '3', '9', '2', '8', '5', '2', '8', '4', '5', '9', '9', '7', '8', '1', '8', '5', '1', '2', '4', '5', '0', '0', '1', '0', '4', '6', '9', '6', '2', '5', '5', '7', '2', '8', '9', '4', '7', '8', '0', '8', '1', '7', '6', '5', '8', '6', '1', '6', '2', '7', '2', '2', '3', '0', '5', '8', '3', '8', '1', '8', '5', '5', '3', '2', '5', '1', '1', '3', '0', '4', '4', '4', '2', '6', '1', '9', '3', '0', '4', '4', '9', '7', '0', '6', '2', '7', '3', '2', '7', '3', '4', '3', '6', '1', '1', '3', '4', '6', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '9', '9', '6', '7', '9', '3', '0', '3', '3', '9', '2', '3', '2', '2', '3', '3', '7', '5', '9', '2', '1', '2', '8', '5', '0', '4', '8', '2', '9', '3', '3', '7', '8', '4', '4', '2', '8', '6', '1', '6', '6', '8', '9', '8', '2', '5', '9', '1', '8', '3', '4', '7', '3', '7', '2', '2', '9', '0', '0', '2', '1', '2', '1', '1', '6', '2', '0', '5', '6', '8', '5', '6', '6', '3', '2', '5', '6', '5', '6', '9', '5', '0', '8', '5', '4', '8', '8', '9', '0', '2', '1', '4', '1', '9', '7', '7', '6', '9', '4', '5', '3', '6', '7', '1', '6', '8', '2', '2', '6', '8', '7', '4', '4', '3', '0', '5', '0', '6', '8', '7', '1', '7', '8', '0', '8', '3', '5', '5', '5', '6', '4', '5', '8', '8', '7', '2', '9', '1', '7', '2', '5', '2', '6', '9', '7', '2', '6', '3', '3', '1', '1', '8', '4', '2', '7', '1', '0', '2', '3', '7', '8', '0', '7', '3', '5', '3', '3', '2', '9', '2', '1', '0', '5', '0', '5', '7', '9', '5', '6', '7', '5', '8', '0', '1', '0', '2', '4', '8', '4', '6', '9', '3', '2', '9', '4', '9', '2', '9', '0', '5', '8', '1', '6', '2', '4', '4', '1', '3', '7', '2', '7', '8', '2', '3', '4', '1', '9', '8', '8', '1', '4', '6', '2', '6', '1', '8', '2', '2', '9', '7', '1', '7', '5', '5', '5', '7', '5', '3', '9', '3', '7', '"', ',']

theorem object_fragment0185897_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 477) (SourceJson.white (fragment0185897Field007Chars00 ++ tail)) fragment0185897Acc00700 =
      SourceJson.object (fuel + 476) (SourceJson.white tail) fragment0185897Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_007"
  err.flush

noncomputable def fragment0185897Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0185897Field008Value00 : SourceJson := .str (String.ofList ['3', '0', '7', '8', '0', '8', '4', '9', '8', '7', '0', '5', '1', '4', '3', '7'])
noncomputable def fragment0185897Acc00900 : List (String × SourceJson) := (fragment0185897Field008Key00, fragment0185897Field008Value00) :: fragment0185897Acc00800
noncomputable def fragment0185897Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '0', '7', '8', '0', '8', '4', '9', '8', '7', '0', '5', '1', '4', '3', '7', '"', ',']

theorem object_fragment0185897_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment0185897Field008Chars00 ++ tail)) fragment0185897Acc00800 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment0185897Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_008"
  err.flush

noncomputable def fragment0185897Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0185897Field009Value00 : SourceJson := .str (String.ofList ['8', '8', '1', '6', '8', '7', '3', '8', '3', '7', '6', '8', '7', '7', '1', '4'])
noncomputable def fragment0185897Acc01000 : List (String × SourceJson) := (fragment0185897Field009Key00, fragment0185897Field009Value00) :: fragment0185897Acc00900
noncomputable def fragment0185897Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '8', '1', '6', '8', '7', '3', '8', '3', '7', '6', '8', '7', '7', '1', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0185897_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment0185897Field009Chars00 ++ tail)) fragment0185897Acc00900 =
      .ok (.obj (fragment0185897Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0185897_object_field_009"
  err.flush

noncomputable def fragment0185897Chars : List Char := '{' :: (fragment0185897Field000Chars00 ++ fragment0185897Field001Chars00 ++ fragment0185897Field002Chars00 ++ fragment0185897Field003Chars00 ++ fragment0185897Field004Chars00 ++ fragment0185897Field005Chars00 ++ fragment0185897Field006Chars00 ++ fragment0185897Field007Chars00 ++ fragment0185897Field008Chars00 ++ fragment0185897Field009Chars00)
noncomputable def fragment0185897Value : SourceJson := .obj (fragment0185897Acc01000.reverse)

theorem value_fragment0185897 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 485) (fragment0185897Chars ++ tail) =
      .ok (fragment0185897Value, tail) := by
  have hinput : fragment0185897Chars ++ tail = '{' :: (fragment0185897Field000Chars00 ++ (fragment0185897Field001Chars00 ++ (fragment0185897Field002Chars00 ++ (fragment0185897Field003Chars00 ++ (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0185897Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 485) (fragment0185897Chars ++ tail) =
        SourceJson.value (fuel + 485) ('{' :: (fragment0185897Field000Chars00 ++ (fragment0185897Field001Chars00 ++ (fragment0185897Field002Chars00 ++ (fragment0185897Field003Chars00 ++ (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 485)) hinput
    _ = SourceJson.object (fuel + 484) (SourceJson.white (fragment0185897Field000Chars00 ++ (fragment0185897Field001Chars00 ++ (fragment0185897Field002Chars00 ++ (fragment0185897Field003Chars00 ++ (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))))))))))) fragment0185897Acc00000 := by rfl
    _ = SourceJson.object (fuel + 483) (SourceJson.white (fragment0185897Field001Chars00 ++ (fragment0185897Field002Chars00 ++ (fragment0185897Field003Chars00 ++ (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail))))))))))) fragment0185897Acc00100 := object_fragment0185897_field_000 fuel (fragment0185897Field001Chars00 ++ (fragment0185897Field002Chars00 ++ (fragment0185897Field003Chars00 ++ (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 482) (SourceJson.white (fragment0185897Field002Chars00 ++ (fragment0185897Field003Chars00 ++ (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))))))))) fragment0185897Acc00200 := object_fragment0185897_field_001 fuel (fragment0185897Field002Chars00 ++ (fragment0185897Field003Chars00 ++ (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 481) (SourceJson.white (fragment0185897Field003Chars00 ++ (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail))))))))) fragment0185897Acc00300 := object_fragment0185897_field_002 fuel (fragment0185897Field003Chars00 ++ (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 480) (SourceJson.white (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))))))) fragment0185897Acc00400 := object_fragment0185897_field_003 fuel (fragment0185897Field004Chars00 ++ (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 479) (SourceJson.white (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail))))))) fragment0185897Acc00500 := object_fragment0185897_field_004 fuel (fragment0185897Field005Chars00 ++ (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 478) (SourceJson.white (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))))) fragment0185897Acc00600 := object_fragment0185897_field_005 fuel (fragment0185897Field006Chars00 ++ (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 477) (SourceJson.white (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail))))) fragment0185897Acc00700 := object_fragment0185897_field_006 fuel (fragment0185897Field007Chars00 ++ (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))) fragment0185897Acc00800 := object_fragment0185897_field_007 fuel (fragment0185897Field008Chars00 ++ (fragment0185897Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment0185897Field009Chars00 ++ (tail))) fragment0185897Acc00900 := object_fragment0185897_field_008 fuel (fragment0185897Field009Chars00 ++ (tail))
    _ = .ok (fragment0185897Value, tail) := object_fragment0185897_field_009 fuel (tail)

noncomputable def fragment0188025Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0188025Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0188025Field000Value00 : SourceJson := .number (String.ofList ['3', '3'])
noncomputable def fragment0188025Acc00100 : List (String × SourceJson) := (fragment0188025Field000Key00, fragment0188025Field000Value00) :: fragment0188025Acc00000
noncomputable def fragment0188025Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '3', ',']

theorem object_fragment0188025_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 424) (SourceJson.white (fragment0188025Field000Chars00 ++ tail)) fragment0188025Acc00000 =
      SourceJson.object (fuel + 423) (SourceJson.white tail) fragment0188025Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_000"
  err.flush

noncomputable def fragment0188025Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0188025Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0188025Acc00200 : List (String × SourceJson) := (fragment0188025Field001Key00, fragment0188025Field001Value00) :: fragment0188025Acc00100
noncomputable def fragment0188025Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0188025_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 423) (SourceJson.white (fragment0188025Field001Chars00 ++ tail)) fragment0188025Acc00100 =
      SourceJson.object (fuel + 422) (SourceJson.white tail) fragment0188025Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_001"
  err.flush

noncomputable def fragment0188025Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0188025Field002Value00 : SourceJson := .str (String.ofList ['4', '7', '6', '0', '0', '3', '6', '2', '5', '4', '4', '8', '8', '4', '0', '4', '8', '8', '8', '3', '0', '3', '3', '1', '2', '9', '2', '5', '4', '8', '1', '1', '7', '6', '5', '6', '0', '3', '7', '3', '0', '0', '7', '9', '9', '/', '4', '0', '0', '2', '1', '2', '5', '1', '8', '6', '1', '1', '0', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0188025Acc00300 : List (String × SourceJson) := (fragment0188025Field002Key00, fragment0188025Field002Value00) :: fragment0188025Acc00200
noncomputable def fragment0188025Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '7', '6', '0', '0', '3', '6', '2', '5', '4', '4', '8', '8', '4', '0', '4', '8', '8', '8', '3', '0', '3', '3', '1', '2', '9', '2', '5', '4', '8', '1', '1', '7', '6', '5', '6', '0', '3', '7', '3', '0', '0', '7', '9', '9', '/', '4', '0', '0', '2', '1', '2', '5', '1', '8', '6', '1', '1', '0', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0188025_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 422) (SourceJson.white (fragment0188025Field002Chars00 ++ tail)) fragment0188025Acc00200 =
      SourceJson.object (fuel + 421) (SourceJson.white tail) fragment0188025Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_002"
  err.flush

noncomputable def fragment0188025Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0188025Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0188025Acc00400 : List (String × SourceJson) := (fragment0188025Field003Key00, fragment0188025Field003Value00) :: fragment0188025Acc00300
noncomputable def fragment0188025Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0188025_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0188025Field003Chars00 ++ tail)) fragment0188025Acc00300 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0188025Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_003"
  err.flush

noncomputable def fragment0188025Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0188025Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0188025Acc00500 : List (String × SourceJson) := (fragment0188025Field004Key00, fragment0188025Field004Value00) :: fragment0188025Acc00400
noncomputable def fragment0188025Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0188025_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0188025Field004Chars00 ++ tail)) fragment0188025Acc00400 =
      SourceJson.object (fuel + 419) (SourceJson.white tail) fragment0188025Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_004"
  err.flush

noncomputable def fragment0188025Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0188025Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '7', '1', '2', '5', '5', '0', '4', '0', '5', '5', '5', '2', '7', '0', '8', '1', '1', '3', '8', '1', '3', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '3', '1', '1', '3', '7', '5', '0', '1', '9', '6', '8', '5', '6', '5', '2', '9', '8', '7', '6', '3', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '2', '0', '6', '9', '2', '2', '4', '1', '5', '9', '3', '5', '7', '3', '5', '2', '4', '2', '4', '7', '/', '3', '7', '2', '7', '7', '4', '2', '9', '3', '3', '4', '3', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '9', '2', '4', '4', '8', '4', '0', '0', '9', '1', '6', '8', '6', '1', '3', '0', '2', '1', '2', '5', '1', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '9', '7', '4', '6', '4', '6', '6', '5', '5', '4', '4', '5', '2', '4', '7', '6', '0', '7', '8', '3', '/', '9', '5', '2', '6', '4', '5', '4', '1', '6', '3', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '1', '3', '1', '0', '1', '0', '1', '0', '0', '8', '3', '8', '3', '8', '9', '3', '2', '0', '9', '/', '1', '5', '5', '8', '8', '7', '4', '3', '1', '7', '6', '1', '6', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '4', '8', '0', '2', '5', '5', '5', '5', '4', '5', '1', '3', '1', '6', '1', '0', '4', '3', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '2', '9', '5', '5', '9', '2', '9', '8', '1', '0', '0', '0', '8', '6', '0', '4', '7', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '8', '8', '1', '7', '6', '4', '6', '7', '4', '3', '2', '4', '8', '7', '7', '6', '7', '9', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '9', '8', '5', '7', '0', '0', '6', '0', '3', '0', '9', '1', '9', '5', '8', '5', '4', '2', '7', '/', '2', '0', '4', '1', '3', '8', '3', '0', '3', '4', '9', '7', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0188025Acc00600 : List (String × SourceJson) := (fragment0188025Field005Key00, fragment0188025Field005Value00) :: fragment0188025Acc00500
noncomputable def fragment0188025Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '1', '2', '5', '5', '0', '4', '0', '5', '5', '5', '2', '7', '0', '8', '1', '1', '3', '8', '1', '3', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '3', '1', '1', '3', '7', '5', '0', '1', '9', '6', '8', '5', '6', '5', '2', '9', '8', '7', '6', '3', '/', '6', '1', '2', '4', '1', '4', '9', '1', '0', '4', '9', '2', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '2', '0', '6', '9', '2', '2', '4', '1', '5', '9', '3', '5', '7', '3', '5', '2', '4', '2', '4', '7', '/', '3', '7', '2', '7', '7', '4', '2', '9', '3', '3', '4', '3', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '9', '2', '4', '4', '8', '4', '0', '0', '9', '1', '6', '8', '6', '1', '3', '0', '2', '1', '2', '5', '1', '/', '8', '5', '7', '3', '8', '0', '8', '7', '4', '6', '8', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '9', '7', '4', '6', '4', '6', '6', '5', '5', '4', '4', '5', '2', '4', '7', '6', '0', '7', '8', '3', '/', '9', '5', '2', '6', '4', '5', '4', '1', '6', '3', '2', '1', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '1', '3', '1', '0', '1', '0', '1', '0', '0', '8', '3', '8', '3', '8', '9', '3', '2', '0', '9', '/', '1', '5', '5', '8', '8', '7', '4', '3', '1', '7', '6', '1', '6', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '4', '8', '0', '2', '5', '5', '5', '5', '4', '5', '1', '3', '1', '6', '1', '0', '4', '3', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '2', '9', '5', '5', '9', '2', '9', '8', '1', '0', '0', '0', '8', '6', '0', '4', '7', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '8', '1', '7', '6', '4', '6', '7', '4', '3', '2', '4', '8', '7', '7', '6', '7', '9', '1', '/', '7', '7', '9', '4', '3', '7', '1', '5', '8', '8', '0', '8', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '9', '8', '5', '7', '0', '0', '6', '0', '3', '0', '9', '1', '9', '5', '8', '5', '4', '2', '7', '/', '2', '0', '4', '1', '3', '8', '3', '0', '3', '4', '9', '7', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0188025_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 419) (SourceJson.white (fragment0188025Field005Chars00 ++ tail)) fragment0188025Acc00500 =
      SourceJson.object (fuel + 418) (SourceJson.white tail) fragment0188025Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_005"
  err.flush

noncomputable def fragment0188025Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0188025Field006Value00 : SourceJson := .str (String.ofList ['1', '1', '8', '6', '4', '3', '7', '3', '5', '9', '4', '7', '6', '1', '1', '9', '5', '5', '1', '0', '7', '1', '7', '9', '4', '3', '9', '2', '7', '0', '2', '2', '5', '2', '3', '7', '6', '4', '4', '0', '2', '7', '1', '0', '8', '0', '8', '2', '7', '2', '7', '9', '3', '6', '0', '0', '/', '5', '0', '6', '1', '3', '4', '9', '4', '4', '8', '6', '3', '6', '2', '5', '1', '9', '8', '9', '9', '3', '5', '8', '7', '5', '3', '6', '3', '3', '4', '9', '1', '6', '6', '8', '6', '2', '7', '3', '1', '9', '2', '7', '3', '7', '0', '9', '0', '5', '9', '6', '4', '6', '9', '6', '6', '3', '4', '4', '8', '1', '5', '6', '4', '5', '1', '5', '1'])
noncomputable def fragment0188025Acc00700 : List (String × SourceJson) := (fragment0188025Field006Key00, fragment0188025Field006Value00) :: fragment0188025Acc00600
noncomputable def fragment0188025Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '8', '6', '4', '3', '7', '3', '5', '9', '4', '7', '6', '1', '1', '9', '5', '5', '1', '0', '7', '1', '7', '9', '4', '3', '9', '2', '7', '0', '2', '2', '5', '2', '3', '7', '6', '4', '4', '0', '2', '7', '1', '0', '8', '0', '8', '2', '7', '2', '7', '9', '3', '6', '0', '0', '/', '5', '0', '6', '1', '3', '4', '9', '4', '4', '8', '6', '3', '6', '2', '5', '1', '9', '8', '9', '9', '3', '5', '8', '7', '5', '3', '6', '3', '3', '4', '9', '1', '6', '6', '8', '6', '2', '7', '3', '1', '9', '2', '7', '3', '7', '0', '9', '0', '5', '9', '6', '4', '6', '9', '6', '6', '3', '4', '4', '8', '1', '5', '6', '4', '5', '1', '5', '1', '"', ',']

theorem object_fragment0188025_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 418) (SourceJson.white (fragment0188025Field006Chars00 ++ tail)) fragment0188025Acc00600 =
      SourceJson.object (fuel + 417) (SourceJson.white tail) fragment0188025Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_006"
  err.flush

noncomputable def fragment0188025Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0188025Field007Value00 : SourceJson := .str (String.ofList ['8', '9', '1', '3', '8', '2', '4', '9', '7', '5', '0', '8', '7', '0', '2', '3', '1', '8', '3', '0', '7', '6', '4', '5', '1', '1', '4', '5', '0', '9', '6', '4', '7', '8', '4', '6', '2', '8', '7', '5', '8', '9', '7', '3', '5', '3', '2', '1', '4', '3', '5', '7', '5', '8', '2', '0', '5', '2', '3', '8', '7', '0', '9', '0', '7', '0', '6', '7', '9', '5', '3', '2', '6', '3', '0', '3', '3', '8', '6', '2', '6', '7', '1', '5', '9', '3', '6', '2', '1', '0', '0', '4', '7', '2', '6', '4', '1', '3', '5', '3', '5', '6', '6', '4', '2', '0', '4', '8', '7', '8', '5', '5', '6', '2', '9', '9', '2', '2', '7', '5', '7', '6', '1', '8', '2', '5', '7', '4', '2', '9', '9', '3', '6', '9', '6', '2', '2', '9', '7', '6', '7', '9', '6', '9', '8', '8', '0', '6', '7', '4', '8', '5', '5', '1', '1', '8', '3', '5', '9', '5', '1', '8', '5', '0', '0', '9', '6', '8', '4', '5', '3', '9', '5', '2', '7', '3', '5', '5', '4', '3', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '1', '4', '8', '6', '7', '1', '5', '4', '7', '1', '2', '7', '9', '9', '7', '7', '6', '7', '2', '4', '2', '0', '3', '3', '8', '8', '4', '1', '2', '0', '1', '5', '7', '7', '3', '8', '6', '2', '6', '8', '3', '3', '7', '9', '3', '6', '3', '0', '1', '1', '2', '4', '4', '1', '8', '3', '1', '1', '1', '1', '9', '6', '6', '0', '9', '8', '8', '2', '1', '3', '9', '4', '7', '3', '0', '9', '2', '3', '7', '6', '1', '9', '6', '1', '6', '5', '9', '2', '3', '4', '7', '6', '7', '2', '3', '8', '7', '6', '4', '9', '7', '5', '3', '7', '7', '7', '3', '2', '4', '8', '6', '5', '6', '7', '2', '0', '3', '9', '5', '3', '4', '0', '2', '3', '2', '1', '0', '7', '0', '8', '8', '4', '5', '9', '8', '6', '8', '5', '9', '7', '1', '9', '8', '4', '2', '2', '0', '3', '7', '1', '6', '3', '0', '6', '9', '1', '1', '7', '6', '4', '9', '1', '7', '1', '4', '8', '5', '6', '5', '2', '9', '1', '9', '7', '3', '6', '9', '0', '8', '0', '4', '8', '1', '2', '5', '3', '2', '0', '0', '9', '7', '2', '3', '6', '0', '0', '8', '8', '9', '1', '4', '5', '6', '0', '1', '2', '4', '1', '0', '3', '9'])
noncomputable def fragment0188025Acc00800 : List (String × SourceJson) := (fragment0188025Field007Key00, fragment0188025Field007Value00) :: fragment0188025Acc00700
noncomputable def fragment0188025Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '9', '1', '3', '8', '2', '4', '9', '7', '5', '0', '8', '7', '0', '2', '3', '1', '8', '3', '0', '7', '6', '4', '5', '1', '1', '4', '5', '0', '9', '6', '4', '7', '8', '4', '6', '2', '8', '7', '5', '8', '9', '7', '3', '5', '3', '2', '1', '4', '3', '5', '7', '5', '8', '2', '0', '5', '2', '3', '8', '7', '0', '9', '0', '7', '0', '6', '7', '9', '5', '3', '2', '6', '3', '0', '3', '3', '8', '6', '2', '6', '7', '1', '5', '9', '3', '6', '2', '1', '0', '0', '4', '7', '2', '6', '4', '1', '3', '5', '3', '5', '6', '6', '4', '2', '0', '4', '8', '7', '8', '5', '5', '6', '2', '9', '9', '2', '2', '7', '5', '7', '6', '1', '8', '2', '5', '7', '4', '2', '9', '9', '3', '6', '9', '6', '2', '2', '9', '7', '6', '7', '9', '6', '9', '8', '8', '0', '6', '7', '4', '8', '5', '5', '1', '1', '8', '3', '5', '9', '5', '1', '8', '5', '0', '0', '9', '6', '8', '4', '5', '3', '9', '5', '2', '7', '3', '5', '5', '4', '3', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '1', '4', '8', '6', '7', '1', '5', '4', '7', '1', '2', '7', '9', '9', '7', '7', '6', '7', '2', '4', '2', '0', '3', '3', '8', '8', '4', '1', '2', '0', '1', '5', '7', '7', '3', '8', '6', '2', '6', '8', '3', '3', '7', '9', '3', '6', '3', '0', '1', '1', '2', '4', '4', '1', '8', '3', '1', '1', '1', '1', '9', '6', '6', '0', '9', '8', '8', '2', '1', '3', '9', '4', '7', '3', '0', '9', '2', '3', '7', '6', '1', '9', '6', '1', '6', '5', '9', '2', '3', '4', '7', '6', '7', '2', '3', '8', '7', '6', '4', '9', '7', '5', '3', '7', '7', '7', '3', '2', '4', '8', '6', '5', '6', '7', '2', '0', '3', '9', '5', '3', '4', '0', '2', '3', '2', '1', '0', '7', '0', '8', '8', '4', '5', '9', '8', '6', '8', '5', '9', '7', '1', '9', '8', '4', '2', '2', '0', '3', '7', '1', '6', '3', '0', '6', '9', '1', '1', '7', '6', '4', '9', '1', '7', '1', '4', '8', '5', '6', '5', '2', '9', '1', '9', '7', '3', '6', '9', '0', '8', '0', '4', '8', '1', '2', '5', '3', '2', '0', '0', '9', '7', '2', '3', '6', '0', '0', '8', '8', '9', '1', '4', '5', '6', '0', '1', '2', '4', '1', '0', '3', '9', '"', ',']

theorem object_fragment0188025_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 417) (SourceJson.white (fragment0188025Field007Chars00 ++ tail)) fragment0188025Acc00700 =
      SourceJson.object (fuel + 416) (SourceJson.white tail) fragment0188025Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_007"
  err.flush

noncomputable def fragment0188025Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0188025Field008Value00 : SourceJson := .str (String.ofList ['1', '8', '5', '7', '1', '9', '7', '4', '3', '0', '9', '1', '2', '3', '4', '5', '9'])
noncomputable def fragment0188025Acc00900 : List (String × SourceJson) := (fragment0188025Field008Key00, fragment0188025Field008Value00) :: fragment0188025Acc00800
noncomputable def fragment0188025Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '5', '7', '1', '9', '7', '4', '3', '0', '9', '1', '2', '3', '4', '5', '9', '"', ',']

theorem object_fragment0188025_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 416) (SourceJson.white (fragment0188025Field008Chars00 ++ tail)) fragment0188025Acc00800 =
      SourceJson.object (fuel + 415) (SourceJson.white tail) fragment0188025Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_008"
  err.flush

noncomputable def fragment0188025Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0188025Field009Value00 : SourceJson := .str (String.ofList ['6', '9', '5', '8', '8', '0', '2', '1', '4', '9', '3', '2', '9', '1', '8', '8', '6'])
noncomputable def fragment0188025Acc01000 : List (String × SourceJson) := (fragment0188025Field009Key00, fragment0188025Field009Value00) :: fragment0188025Acc00900
noncomputable def fragment0188025Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '6', '9', '5', '8', '8', '0', '2', '1', '4', '9', '3', '2', '9', '1', '8', '8', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0188025_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 415) (SourceJson.white (fragment0188025Field009Chars00 ++ tail)) fragment0188025Acc00900 =
      .ok (.obj (fragment0188025Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0188025_object_field_009"
  err.flush

noncomputable def fragment0188025Chars : List Char := '{' :: (fragment0188025Field000Chars00 ++ fragment0188025Field001Chars00 ++ fragment0188025Field002Chars00 ++ fragment0188025Field003Chars00 ++ fragment0188025Field004Chars00 ++ fragment0188025Field005Chars00 ++ fragment0188025Field006Chars00 ++ fragment0188025Field007Chars00 ++ fragment0188025Field008Chars00 ++ fragment0188025Field009Chars00)
noncomputable def fragment0188025Value : SourceJson := .obj (fragment0188025Acc01000.reverse)

theorem value_fragment0188025 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 425) (fragment0188025Chars ++ tail) =
      .ok (fragment0188025Value, tail) := by
  have hinput : fragment0188025Chars ++ tail = '{' :: (fragment0188025Field000Chars00 ++ (fragment0188025Field001Chars00 ++ (fragment0188025Field002Chars00 ++ (fragment0188025Field003Chars00 ++ (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0188025Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 425) (fragment0188025Chars ++ tail) =
        SourceJson.value (fuel + 425) ('{' :: (fragment0188025Field000Chars00 ++ (fragment0188025Field001Chars00 ++ (fragment0188025Field002Chars00 ++ (fragment0188025Field003Chars00 ++ (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 425)) hinput
    _ = SourceJson.object (fuel + 424) (SourceJson.white (fragment0188025Field000Chars00 ++ (fragment0188025Field001Chars00 ++ (fragment0188025Field002Chars00 ++ (fragment0188025Field003Chars00 ++ (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))))))))))) fragment0188025Acc00000 := by rfl
    _ = SourceJson.object (fuel + 423) (SourceJson.white (fragment0188025Field001Chars00 ++ (fragment0188025Field002Chars00 ++ (fragment0188025Field003Chars00 ++ (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail))))))))))) fragment0188025Acc00100 := object_fragment0188025_field_000 fuel (fragment0188025Field001Chars00 ++ (fragment0188025Field002Chars00 ++ (fragment0188025Field003Chars00 ++ (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 422) (SourceJson.white (fragment0188025Field002Chars00 ++ (fragment0188025Field003Chars00 ++ (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))))))))) fragment0188025Acc00200 := object_fragment0188025_field_001 fuel (fragment0188025Field002Chars00 ++ (fragment0188025Field003Chars00 ++ (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0188025Field003Chars00 ++ (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail))))))))) fragment0188025Acc00300 := object_fragment0188025_field_002 fuel (fragment0188025Field003Chars00 ++ (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))))))) fragment0188025Acc00400 := object_fragment0188025_field_003 fuel (fragment0188025Field004Chars00 ++ (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 419) (SourceJson.white (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail))))))) fragment0188025Acc00500 := object_fragment0188025_field_004 fuel (fragment0188025Field005Chars00 ++ (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 418) (SourceJson.white (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))))) fragment0188025Acc00600 := object_fragment0188025_field_005 fuel (fragment0188025Field006Chars00 ++ (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 417) (SourceJson.white (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail))))) fragment0188025Acc00700 := object_fragment0188025_field_006 fuel (fragment0188025Field007Chars00 ++ (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 416) (SourceJson.white (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))) fragment0188025Acc00800 := object_fragment0188025_field_007 fuel (fragment0188025Field008Chars00 ++ (fragment0188025Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 415) (SourceJson.white (fragment0188025Field009Chars00 ++ (tail))) fragment0188025Acc00900 := object_fragment0188025_field_008 fuel (fragment0188025Field009Chars00 ++ (tail))
    _ = .ok (fragment0188025Value, tail) := object_fragment0188025_field_009 fuel (tail)

noncomputable def fragment0190021Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0190021Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0190021Field000Value00 : SourceJson := .number (String.ofList ['3', '4'])
noncomputable def fragment0190021Acc00100 : List (String × SourceJson) := (fragment0190021Field000Key00, fragment0190021Field000Value00) :: fragment0190021Acc00000
noncomputable def fragment0190021Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '4', ',']

theorem object_fragment0190021_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0190021Field000Chars00 ++ tail)) fragment0190021Acc00000 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0190021Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_000"
  err.flush

noncomputable def fragment0190021Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0190021Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['0'])]
noncomputable def fragment0190021Acc00200 : List (String × SourceJson) := (fragment0190021Field001Key00, fragment0190021Field001Value00) :: fragment0190021Acc00100
noncomputable def fragment0190021Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0190021_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0190021Field001Chars00 ++ tail)) fragment0190021Acc00100 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0190021Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_001"
  err.flush

noncomputable def fragment0190021Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0190021Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '5', '3', '3', '4', '0', '5', '6', '7', '9', '4', '9', '0', '8', '0', '9', '2', '7', '4', '1', '7', '8', '6', '6', '0', '6', '8', '3', '8', '6', '6', '6', '2', '9', '7', '8', '3', '0', '2', '0', '6', '6', '1', '1', '3', '9', '/', '8', '8', '2', '1', '0', '1', '0', '6', '1', '4', '2', '8', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0190021Acc00300 : List (String × SourceJson) := (fragment0190021Field002Key00, fragment0190021Field002Value00) :: fragment0190021Acc00200
noncomputable def fragment0190021Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '5', '3', '3', '4', '0', '5', '6', '7', '9', '4', '9', '0', '8', '0', '9', '2', '7', '4', '1', '7', '8', '6', '6', '0', '6', '8', '3', '8', '6', '6', '6', '2', '9', '7', '8', '3', '0', '2', '0', '6', '6', '1', '1', '3', '9', '/', '8', '8', '2', '1', '0', '1', '0', '6', '1', '4', '2', '8', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0190021_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0190021Field002Chars00 ++ tail)) fragment0190021Acc00200 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0190021Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_002"
  err.flush

noncomputable def fragment0190021Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0190021Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0190021Acc00400 : List (String × SourceJson) := (fragment0190021Field003Key00, fragment0190021Field003Value00) :: fragment0190021Acc00300
noncomputable def fragment0190021Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '5', '2', '8', '8', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0190021_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0190021Field003Chars00 ++ tail)) fragment0190021Acc00300 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0190021Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_003"
  err.flush

noncomputable def fragment0190021Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0190021Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0190021Acc00500 : List (String × SourceJson) := (fragment0190021Field004Key00, fragment0190021Field004Value00) :: fragment0190021Acc00400
noncomputable def fragment0190021Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '9', '9', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0190021_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0190021Field004Chars00 ++ tail)) fragment0190021Acc00400 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0190021Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_004"
  err.flush

noncomputable def fragment0190021Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0190021Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '6', '2', '5', '9', '7', '2', '3', '0', '5', '2', '1', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '9', '4', '0', '6', '1', '7', '1', '0', '5', '8', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '4', '0', '6', '6', '3', '9', '4', '2', '4', '2', '7', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '5', '2', '4', '2', '9', '7', '2', '3', '3', '1', '9', '1', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '1', '5', '1', '4', '3', '7', '9', '5', '9', '8', '5', '0', '7', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '2', '4', '0', '3', '2', '9', '4', '0', '5', '0', '1', '/', '4', '6', '5', '9', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '7', '2', '1', '2', '6', '2', '4', '6', '7', '7', '/', '3', '3', '2', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '4', '9', '8', '5', '2', '6', '5', '5', '2', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '9', '6', '4', '1', '9', '1', '7', '8', '4', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '5', '8', '3', '9', '1', '3', '2', '7', '0', '1', '0', '7', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0190021Acc00600 : List (String × SourceJson) := (fragment0190021Field005Key00, fragment0190021Field005Value00) :: fragment0190021Acc00500
noncomputable def fragment0190021Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '2', '5', '9', '7', '2', '3', '0', '5', '2', '1', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '9', '4', '0', '6', '1', '7', '1', '0', '5', '8', '7', '/', '4', '2', '7', '1', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '4', '0', '6', '6', '3', '9', '4', '2', '4', '2', '7', '/', '1', '1', '1', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '5', '2', '4', '2', '9', '7', '2', '3', '3', '1', '9', '1', '1', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '1', '5', '1', '4', '3', '7', '9', '5', '9', '8', '5', '0', '7', '/', '2', '5', '6', '2', '9', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '4', '0', '3', '2', '9', '4', '0', '5', '0', '1', '/', '4', '6', '5', '9', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '7', '2', '1', '2', '6', '2', '4', '6', '7', '7', '/', '3', '3', '2', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '4', '9', '8', '5', '2', '6', '5', '5', '2', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '9', '6', '4', '1', '9', '1', '7', '8', '4', '1', '/', '2', '3', '2', '9', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '8', '3', '9', '1', '3', '2', '7', '0', '1', '0', '7', '/', '1', '2', '8', '1', '4', '9', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0190021_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0190021Field005Chars00 ++ tail)) fragment0190021Acc00500 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0190021Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_005"
  err.flush

noncomputable def fragment0190021Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0190021Field006Value00 : SourceJson := .str (String.ofList ['7', '8', '3', '5', '5', '3', '7', '9', '0', '8', '2', '3', '6', '4', '3', '4', '6', '7', '2', '1', '6', '7', '9', '1', '8', '9', '5', '7', '0', '7', '4', '8', '5', '8', '4', '6', '8', '2', '4', '1', '8', '3', '8', '6', '8', '2', '2', '6', '1', '2', '2', '7', '0', '0', '8', '0', '0', '/', '7', '9', '9', '4', '2', '0', '0', '0', '6', '1', '8', '8', '2', '7', '3', '4', '0', '1', '9', '3', '4', '4', '0', '7', '8', '9', '1', '0', '8', '5', '5', '7', '5', '1', '9', '9', '6', '7', '9', '0', '4', '0', '0', '0', '4', '9', '8', '9', '5', '0', '2', '2', '2', '7', '0', '4', '5', '5', '3', '0', '4', '7', '2', '2', '4', '1', '5', '4', '9'])
noncomputable def fragment0190021Acc00700 : List (String × SourceJson) := (fragment0190021Field006Key00, fragment0190021Field006Value00) :: fragment0190021Acc00600
noncomputable def fragment0190021Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '8', '3', '5', '5', '3', '7', '9', '0', '8', '2', '3', '6', '4', '3', '4', '6', '7', '2', '1', '6', '7', '9', '1', '8', '9', '5', '7', '0', '7', '4', '8', '5', '8', '4', '6', '8', '2', '4', '1', '8', '3', '8', '6', '8', '2', '2', '6', '1', '2', '2', '7', '0', '0', '8', '0', '0', '/', '7', '9', '9', '4', '2', '0', '0', '0', '6', '1', '8', '8', '2', '7', '3', '4', '0', '1', '9', '3', '4', '4', '0', '7', '8', '9', '1', '0', '8', '5', '5', '7', '5', '1', '9', '9', '6', '7', '9', '0', '4', '0', '0', '0', '4', '9', '8', '9', '5', '0', '2', '2', '2', '7', '0', '4', '5', '5', '3', '0', '4', '7', '2', '2', '4', '1', '5', '4', '9', '"', ',']

theorem object_fragment0190021_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0190021Field006Chars00 ++ tail)) fragment0190021Acc00600 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0190021Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_006"
  err.flush

noncomputable def fragment0190021Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0190021Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '1', '0', '3', '6', '2', '7', '8', '2', '2', '1', '1', '3', '8', '0', '7', '7', '9', '7', '2', '2', '0', '2', '4', '8', '9', '0', '5', '5', '2', '3', '2', '3', '9', '5', '3', '6', '9', '0', '7', '1', '6', '1', '2', '7', '3', '4', '5', '3', '2', '9', '3', '6', '1', '2', '4', '0', '5', '5', '8', '5', '6', '3', '9', '4', '6', '9', '5', '0', '0', '6', '8', '4', '5', '5', '3', '7', '4', '2', '5', '0', '7', '5', '5', '3', '8', '3', '0', '1', '0', '0', '4', '0', '1', '7', '3', '0', '3', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '4', '1', '5', '9', '3', '3', '2', '7', '2', '8', '0', '5', '0', '0', '6', '4', '2', '5', '2', '6', '0', '6', '4', '5', '8', '5', '2', '8', '0', '9', '9', '1', '4', '3', '0', '4', '4', '4', '1', '5', '0', '4', '7', '9', '4', '4', '3', '4', '4', '4', '4', '6', '1', '7', '6', '4', '7', '6', '6', '1', '1', '0', '7', '0', '8', '3', '5', '1', '5', '7', '5', '9', '8', '1', '4', '8', '7', '4', '1', '7', '6', '7', '2', '2', '7', '7', '5', '7', '8', '9', '7', '3', '8', '1', '6', '5', '6', '4', '5', '8', '6', '2', '9', '0', '5', '8', '8', '9', '4', '8', '6', '0', '5', '0', '1', '8', '8', '7', '4', '0', '0', '7', '1', '0', '7', '7', '7', '3'])
noncomputable def fragment0190021Acc00800 : List (String × SourceJson) := (fragment0190021Field007Key00, fragment0190021Field007Value00) :: fragment0190021Acc00700
noncomputable def fragment0190021Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '1', '0', '3', '6', '2', '7', '8', '2', '2', '1', '1', '3', '8', '0', '7', '7', '9', '7', '2', '2', '0', '2', '4', '8', '9', '0', '5', '5', '2', '3', '2', '3', '9', '5', '3', '6', '9', '0', '7', '1', '6', '1', '2', '7', '3', '4', '5', '3', '2', '9', '3', '6', '1', '2', '4', '0', '5', '5', '8', '5', '6', '3', '9', '4', '6', '9', '5', '0', '0', '6', '8', '4', '5', '5', '3', '7', '4', '2', '5', '0', '7', '5', '5', '3', '8', '3', '0', '1', '0', '0', '4', '0', '1', '7', '3', '0', '3', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '4', '1', '5', '9', '3', '3', '2', '7', '2', '8', '0', '5', '0', '0', '6', '4', '2', '5', '2', '6', '0', '6', '4', '5', '8', '5', '2', '8', '0', '9', '9', '1', '4', '3', '0', '4', '4', '4', '1', '5', '0', '4', '7', '9', '4', '4', '3', '4', '4', '4', '4', '6', '1', '7', '6', '4', '7', '6', '6', '1', '1', '0', '7', '0', '8', '3', '5', '1', '5', '7', '5', '9', '8', '1', '4', '8', '7', '4', '1', '7', '6', '7', '2', '2', '7', '7', '5', '7', '8', '9', '7', '3', '8', '1', '6', '5', '6', '4', '5', '8', '6', '2', '9', '0', '5', '8', '8', '9', '4', '8', '6', '0', '5', '0', '1', '8', '8', '7', '4', '0', '0', '7', '1', '0', '7', '7', '7', '3', '"', ',']

theorem object_fragment0190021_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0190021Field007Chars00 ++ tail)) fragment0190021Acc00700 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0190021Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_007"
  err.flush

noncomputable def fragment0190021Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0190021Field008Value00 : SourceJson := .str (String.ofList ['7', '7', '6', '5', '5', '7', '0', '8', '6', '3', '5', '6', '2', '1', '7', '6', '7'])
noncomputable def fragment0190021Acc00900 : List (String × SourceJson) := (fragment0190021Field008Key00, fragment0190021Field008Value00) :: fragment0190021Acc00800
noncomputable def fragment0190021Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '7', '6', '5', '5', '7', '0', '8', '6', '3', '5', '6', '2', '1', '7', '6', '7', '"', ',']

theorem object_fragment0190021_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0190021Field008Chars00 ++ tail)) fragment0190021Acc00800 =
      SourceJson.object (fuel + 251) (SourceJson.white tail) fragment0190021Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_008"
  err.flush

noncomputable def fragment0190021Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0190021Field009Value00 : SourceJson := .str (String.ofList ['3', '4', '1', '8', '5', '7', '7', '6', '7', '4', '2', '1', '8', '7', '6', '5', '3', '6'])
noncomputable def fragment0190021Acc01000 : List (String × SourceJson) := (fragment0190021Field009Key00, fragment0190021Field009Value00) :: fragment0190021Acc00900
noncomputable def fragment0190021Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '4', '1', '8', '5', '7', '7', '6', '7', '4', '2', '1', '8', '7', '6', '5', '3', '6', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0190021_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 251) (SourceJson.white (fragment0190021Field009Chars00 ++ tail)) fragment0190021Acc00900 =
      .ok (.obj (fragment0190021Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190021_object_field_009"
  err.flush

noncomputable def fragment0190021Chars : List Char := '{' :: (fragment0190021Field000Chars00 ++ fragment0190021Field001Chars00 ++ fragment0190021Field002Chars00 ++ fragment0190021Field003Chars00 ++ fragment0190021Field004Chars00 ++ fragment0190021Field005Chars00 ++ fragment0190021Field006Chars00 ++ fragment0190021Field007Chars00 ++ fragment0190021Field008Chars00 ++ fragment0190021Field009Chars00)
noncomputable def fragment0190021Value : SourceJson := .obj (fragment0190021Acc01000.reverse)

theorem value_fragment0190021 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 261) (fragment0190021Chars ++ tail) =
      .ok (fragment0190021Value, tail) := by
  have hinput : fragment0190021Chars ++ tail = '{' :: (fragment0190021Field000Chars00 ++ (fragment0190021Field001Chars00 ++ (fragment0190021Field002Chars00 ++ (fragment0190021Field003Chars00 ++ (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0190021Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 261) (fragment0190021Chars ++ tail) =
        SourceJson.value (fuel + 261) ('{' :: (fragment0190021Field000Chars00 ++ (fragment0190021Field001Chars00 ++ (fragment0190021Field002Chars00 ++ (fragment0190021Field003Chars00 ++ (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 261)) hinput
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0190021Field000Chars00 ++ (fragment0190021Field001Chars00 ++ (fragment0190021Field002Chars00 ++ (fragment0190021Field003Chars00 ++ (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))))))))))) fragment0190021Acc00000 := by rfl
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0190021Field001Chars00 ++ (fragment0190021Field002Chars00 ++ (fragment0190021Field003Chars00 ++ (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail))))))))))) fragment0190021Acc00100 := object_fragment0190021_field_000 fuel (fragment0190021Field001Chars00 ++ (fragment0190021Field002Chars00 ++ (fragment0190021Field003Chars00 ++ (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0190021Field002Chars00 ++ (fragment0190021Field003Chars00 ++ (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))))))))) fragment0190021Acc00200 := object_fragment0190021_field_001 fuel (fragment0190021Field002Chars00 ++ (fragment0190021Field003Chars00 ++ (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0190021Field003Chars00 ++ (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail))))))))) fragment0190021Acc00300 := object_fragment0190021_field_002 fuel (fragment0190021Field003Chars00 ++ (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))))))) fragment0190021Acc00400 := object_fragment0190021_field_003 fuel (fragment0190021Field004Chars00 ++ (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail))))))) fragment0190021Acc00500 := object_fragment0190021_field_004 fuel (fragment0190021Field005Chars00 ++ (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))))) fragment0190021Acc00600 := object_fragment0190021_field_005 fuel (fragment0190021Field006Chars00 ++ (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail))))) fragment0190021Acc00700 := object_fragment0190021_field_006 fuel (fragment0190021Field007Chars00 ++ (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))) fragment0190021Acc00800 := object_fragment0190021_field_007 fuel (fragment0190021Field008Chars00 ++ (fragment0190021Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 251) (SourceJson.white (fragment0190021Field009Chars00 ++ (tail))) fragment0190021Acc00900 := object_fragment0190021_field_008 fuel (fragment0190021Field009Chars00 ++ (tail))
    _ = .ok (fragment0190021Value, tail) := object_fragment0190021_field_009 fuel (tail)

noncomputable def fragment0191697Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0191697Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0191697Field000Value00 : SourceJson := .number (String.ofList ['3', '5'])
noncomputable def fragment0191697Acc00100 : List (String × SourceJson) := (fragment0191697Field000Key00, fragment0191697Field000Value00) :: fragment0191697Acc00000
noncomputable def fragment0191697Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '5', ',']

theorem object_fragment0191697_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0191697Field000Chars00 ++ tail)) fragment0191697Acc00000 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0191697Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_000"
  err.flush

noncomputable def fragment0191697Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0191697Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7'])]
noncomputable def fragment0191697Acc00200 : List (String × SourceJson) := (fragment0191697Field001Key00, fragment0191697Field001Value00) :: fragment0191697Acc00100
noncomputable def fragment0191697Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0191697_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0191697Field001Chars00 ++ tail)) fragment0191697Acc00100 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0191697Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_001"
  err.flush

noncomputable def fragment0191697Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0191697Field002Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '7', '5', '0', '8', '5', '4', '2', '0', '1', '5', '4', '4', '0', '9', '1', '4', '6', '7', '6', '1', '9', '0', '3', '9', '0', '9', '1', '4', '1', '6', '4', '0', '8', '3', '8', '3', '4', '0', '9', '2', '7', '/', '1', '4', '9', '6', '4', '4', '3', '8', '8', '5', '9', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0191697Acc00300 : List (String × SourceJson) := (fragment0191697Field002Key00, fragment0191697Field002Value00) :: fragment0191697Acc00200
noncomputable def fragment0191697Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '0', '8', '7', '5', '0', '8', '5', '4', '2', '0', '1', '5', '4', '4', '0', '9', '1', '4', '6', '7', '6', '1', '9', '0', '3', '9', '0', '9', '1', '4', '1', '6', '4', '0', '8', '3', '8', '3', '4', '0', '9', '2', '7', '/', '1', '4', '9', '6', '4', '4', '3', '8', '8', '5', '9', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0191697_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0191697Field002Chars00 ++ tail)) fragment0191697Acc00200 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0191697Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_002"
  err.flush

noncomputable def fragment0191697Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0191697Field003Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0191697Acc00400 : List (String × SourceJson) := (fragment0191697Field003Key00, fragment0191697Field003Value00) :: fragment0191697Acc00300
noncomputable def fragment0191697Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '8', '2', '2', '6', '9', '/', '2', '6', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0191697_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0191697Field003Chars00 ++ tail)) fragment0191697Acc00300 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0191697Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_003"
  err.flush

noncomputable def fragment0191697Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0191697Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0191697Acc00500 : List (String × SourceJson) := (fragment0191697Field004Key00, fragment0191697Field004Value00) :: fragment0191697Acc00400
noncomputable def fragment0191697Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '9', '6', '8', '3', '9', '/', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0191697_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0191697Field004Chars00 ++ tail)) fragment0191697Acc00400 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0191697Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_004"
  err.flush

noncomputable def fragment0191697Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0191697Field005Value00 : SourceJson := .arr [.str (String.ofList ['7', '8', '5', '1', '4', '4', '5', '7', '9', '5', '4', '8', '3', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '5', '7', '6', '1', '7', '1', '2', '3', '4', '4', '5', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '8', '4', '0', '3', '1', '9', '5', '5', '3', '5', '3', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '7', '1', '1', '7', '0', '7', '4', '9', '7', '2', '7', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '1', '1', '3', '3', '3', '5', '9', '3', '7', '8', '6', '9', '/', '9', '4', '9', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '5', '4', '7', '3', '2', '9', '2', '0', '5', '5', '0', '1', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '5', '0', '4', '4', '6', '1', '8', '1', '2', '1', '/', '3', '0', '5', '1', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '6', '9', '1', '0', '5', '3', '4', '0', '6', '4', '1', '/', '1', '0', '6', '7', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '9', '7', '3', '4', '7', '4', '1', '8', '7', '2', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '1', '3', '1', '8', '0', '5', '3', '1', '6', '1', '1', '/', '9', '4', '9', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0191697Acc00600 : List (String × SourceJson) := (fragment0191697Field005Key00, fragment0191697Field005Value00) :: fragment0191697Acc00500
noncomputable def fragment0191697Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '5', '1', '4', '4', '5', '7', '9', '5', '4', '8', '3', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '9', '5', '7', '6', '1', '7', '1', '2', '3', '4', '4', '5', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '8', '4', '0', '3', '1', '9', '5', '5', '3', '5', '3', '9', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '1', '1', '7', '0', '7', '4', '9', '7', '2', '7', '/', '2', '1', '3', '5', '8', '2', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '1', '1', '3', '3', '3', '5', '9', '3', '7', '8', '6', '9', '/', '9', '4', '9', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '5', '4', '7', '3', '2', '9', '2', '0', '5', '5', '0', '1', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '5', '0', '4', '4', '6', '1', '8', '1', '2', '1', '/', '3', '0', '5', '1', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '6', '9', '1', '0', '5', '3', '4', '0', '6', '4', '1', '/', '1', '0', '6', '7', '9', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '9', '7', '3', '4', '7', '4', '1', '8', '7', '2', '7', '/', '8', '5', '4', '3', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '1', '3', '1', '8', '0', '5', '3', '1', '6', '1', '1', '/', '9', '4', '9', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0191697_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0191697Field005Chars00 ++ tail)) fragment0191697Acc00500 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0191697Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_005"
  err.flush

noncomputable def fragment0191697Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0191697Field006Value00 : SourceJson := .str (String.ofList ['9', '9', '1', '0', '9', '5', '4', '7', '2', '2', '2', '3', '0', '6', '2', '0', '0', '0', '3', '8', '5', '5', '7', '2', '7', '3', '1', '8', '0', '7', '6', '6', '8', '8', '6', '6', '9', '8', '1', '7', '8', '1', '2', '1', '1', '6', '8', '1', '5', '0', '0', '0', '/', '1', '5', '5', '5', '0', '6', '3', '3', '3', '1', '2', '2', '4', '3', '7', '7', '0', '7', '0', '4', '7', '8', '4', '3', '1', '5', '2', '2', '0', '1', '7', '6', '3', '0', '0', '4', '4', '6', '1', '6', '0', '9', '8', '0', '8', '8', '3', '3', '7', '7', '7', '7', '8', '0', '1', '2', '1', '7', '1', '7', '1', '5', '6', '8', '9'])
noncomputable def fragment0191697Acc00700 : List (String × SourceJson) := (fragment0191697Field006Key00, fragment0191697Field006Value00) :: fragment0191697Acc00600
noncomputable def fragment0191697Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '9', '1', '0', '9', '5', '4', '7', '2', '2', '2', '3', '0', '6', '2', '0', '0', '0', '3', '8', '5', '5', '7', '2', '7', '3', '1', '8', '0', '7', '6', '6', '8', '8', '6', '6', '9', '8', '1', '7', '8', '1', '2', '1', '1', '6', '8', '1', '5', '0', '0', '0', '/', '1', '5', '5', '5', '0', '6', '3', '3', '3', '1', '2', '2', '4', '3', '7', '7', '0', '7', '0', '4', '7', '8', '4', '3', '1', '5', '2', '2', '0', '1', '7', '6', '3', '0', '0', '4', '4', '6', '1', '6', '0', '9', '8', '0', '8', '8', '3', '3', '7', '7', '7', '7', '8', '0', '1', '2', '1', '7', '1', '7', '1', '5', '6', '8', '9', '"', ',']

theorem object_fragment0191697_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0191697Field006Chars00 ++ tail)) fragment0191697Acc00600 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0191697Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_006"
  err.flush

noncomputable def fragment0191697Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0191697Field007Value00 : SourceJson := .str (String.ofList ['6', '3', '6', '4', '4', '9', '8', '3', '9', '4', '2', '4', '1', '4', '1', '0', '3', '6', '5', '0', '2', '7', '0', '9', '6', '7', '4', '0', '1', '1', '3', '1', '0', '5', '4', '8', '7', '4', '3', '7', '1', '0', '0', '9', '3', '8', '2', '5', '6', '8', '1', '4', '7', '2', '4', '4', '0', '6', '3', '8', '4', '4', '5', '6', '1', '8', '0', '8', '6', '1', '0', '9', '6', '1', '2', '1', '6', '2', '6', '1', '7', '0', '3', '2', '0', '1', '3', '2', '8', '5', '3', '7', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '7', '3', '5', '2', '5', '4', '0', '8', '7', '3', '4', '1', '5', '1', '9', '2', '2', '0', '4', '1', '0', '0', '8', '8', '0', '4', '5', '9', '0', '7', '5', '2', '9', '9', '2', '1', '7', '1', '7', '4', '5', '2', '2', '1', '7', '6', '7', '9', '6', '3', '7', '0', '6', '3', '1', '5', '9', '3', '0', '5', '6', '4', '8', '9', '5', '7', '8', '0', '5', '1', '2', '9', '4', '4', '6', '4', '7', '1', '5', '8', '4', '0', '5', '5', '6', '8', '0', '7', '3', '5', '8', '9', '6', '3', '5', '9', '8', '4', '8', '7', '6', '1', '3', '4', '3', '3', '3', '5', '5', '3', '3', '1', '1', '5', '7', '9', '5', '2', '3', '0', '4', '3', '3', '1', '6', '1', '8', '6', '9'])
noncomputable def fragment0191697Acc00800 : List (String × SourceJson) := (fragment0191697Field007Key00, fragment0191697Field007Value00) :: fragment0191697Acc00700
noncomputable def fragment0191697Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '6', '3', '6', '4', '4', '9', '8', '3', '9', '4', '2', '4', '1', '4', '1', '0', '3', '6', '5', '0', '2', '7', '0', '9', '6', '7', '4', '0', '1', '1', '3', '1', '0', '5', '4', '8', '7', '4', '3', '7', '1', '0', '0', '9', '3', '8', '2', '5', '6', '8', '1', '4', '7', '2', '4', '4', '0', '6', '3', '8', '4', '4', '5', '6', '1', '8', '0', '8', '6', '1', '0', '9', '6', '1', '2', '1', '6', '2', '6', '1', '7', '0', '3', '2', '0', '1', '3', '2', '8', '5', '3', '7', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '5', '7', '3', '5', '2', '5', '4', '0', '8', '7', '3', '4', '1', '5', '1', '9', '2', '2', '0', '4', '1', '0', '0', '8', '8', '0', '4', '5', '9', '0', '7', '5', '2', '9', '9', '2', '1', '7', '1', '7', '4', '5', '2', '2', '1', '7', '6', '7', '9', '6', '3', '7', '0', '6', '3', '1', '5', '9', '3', '0', '5', '6', '4', '8', '9', '5', '7', '8', '0', '5', '1', '2', '9', '4', '4', '6', '4', '7', '1', '5', '8', '4', '0', '5', '5', '6', '8', '0', '7', '3', '5', '8', '9', '6', '3', '5', '9', '8', '4', '8', '7', '6', '1', '3', '4', '3', '3', '3', '5', '5', '3', '3', '1', '1', '5', '7', '9', '5', '2', '3', '0', '4', '3', '3', '1', '6', '1', '8', '6', '9', '"', ',']

theorem object_fragment0191697_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0191697Field007Chars00 ++ tail)) fragment0191697Acc00700 =
      SourceJson.object (fuel + 253) (SourceJson.white tail) fragment0191697Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_007"
  err.flush

noncomputable def fragment0191697Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0191697Field008Value00 : SourceJson := .str (String.ofList ['5', '0', '4', '9', '4', '8', '3', '9', '3', '8', '2', '9', '1', '7', '9', '8', '6'])
noncomputable def fragment0191697Acc00900 : List (String × SourceJson) := (fragment0191697Field008Key00, fragment0191697Field008Value00) :: fragment0191697Acc00800
noncomputable def fragment0191697Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '0', '4', '9', '4', '8', '3', '9', '3', '8', '2', '9', '1', '7', '9', '8', '6', '"', ',']

theorem object_fragment0191697_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 253) (SourceJson.white (fragment0191697Field008Chars00 ++ tail)) fragment0191697Acc00800 =
      SourceJson.object (fuel + 252) (SourceJson.white tail) fragment0191697Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_008"
  err.flush

noncomputable def fragment0191697Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0191697Field009Value00 : SourceJson := .str (String.ofList ['1', '9', '5', '9', '3', '6', '4', '8', '1', '2', '9', '1', '1', '4', '7', '8', '8', '7'])
noncomputable def fragment0191697Acc01000 : List (String × SourceJson) := (fragment0191697Field009Key00, fragment0191697Field009Value00) :: fragment0191697Acc00900
noncomputable def fragment0191697Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '9', '5', '9', '3', '6', '4', '8', '1', '2', '9', '1', '1', '4', '7', '8', '8', '7', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0191697_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 252) (SourceJson.white (fragment0191697Field009Chars00 ++ tail)) fragment0191697Acc00900 =
      .ok (.obj (fragment0191697Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0191697_object_field_009"
  err.flush

noncomputable def fragment0191697Chars : List Char := '{' :: (fragment0191697Field000Chars00 ++ fragment0191697Field001Chars00 ++ fragment0191697Field002Chars00 ++ fragment0191697Field003Chars00 ++ fragment0191697Field004Chars00 ++ fragment0191697Field005Chars00 ++ fragment0191697Field006Chars00 ++ fragment0191697Field007Chars00 ++ fragment0191697Field008Chars00 ++ fragment0191697Field009Chars00)
noncomputable def fragment0191697Value : SourceJson := .obj (fragment0191697Acc01000.reverse)

theorem value_fragment0191697 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 262) (fragment0191697Chars ++ tail) =
      .ok (fragment0191697Value, tail) := by
  have hinput : fragment0191697Chars ++ tail = '{' :: (fragment0191697Field000Chars00 ++ (fragment0191697Field001Chars00 ++ (fragment0191697Field002Chars00 ++ (fragment0191697Field003Chars00 ++ (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0191697Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 262) (fragment0191697Chars ++ tail) =
        SourceJson.value (fuel + 262) ('{' :: (fragment0191697Field000Chars00 ++ (fragment0191697Field001Chars00 ++ (fragment0191697Field002Chars00 ++ (fragment0191697Field003Chars00 ++ (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 262)) hinput
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0191697Field000Chars00 ++ (fragment0191697Field001Chars00 ++ (fragment0191697Field002Chars00 ++ (fragment0191697Field003Chars00 ++ (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))))))))))) fragment0191697Acc00000 := by rfl
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0191697Field001Chars00 ++ (fragment0191697Field002Chars00 ++ (fragment0191697Field003Chars00 ++ (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail))))))))))) fragment0191697Acc00100 := object_fragment0191697_field_000 fuel (fragment0191697Field001Chars00 ++ (fragment0191697Field002Chars00 ++ (fragment0191697Field003Chars00 ++ (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0191697Field002Chars00 ++ (fragment0191697Field003Chars00 ++ (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))))))))) fragment0191697Acc00200 := object_fragment0191697_field_001 fuel (fragment0191697Field002Chars00 ++ (fragment0191697Field003Chars00 ++ (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0191697Field003Chars00 ++ (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail))))))))) fragment0191697Acc00300 := object_fragment0191697_field_002 fuel (fragment0191697Field003Chars00 ++ (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))))))) fragment0191697Acc00400 := object_fragment0191697_field_003 fuel (fragment0191697Field004Chars00 ++ (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail))))))) fragment0191697Acc00500 := object_fragment0191697_field_004 fuel (fragment0191697Field005Chars00 ++ (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))))) fragment0191697Acc00600 := object_fragment0191697_field_005 fuel (fragment0191697Field006Chars00 ++ (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail))))) fragment0191697Acc00700 := object_fragment0191697_field_006 fuel (fragment0191697Field007Chars00 ++ (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 253) (SourceJson.white (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))) fragment0191697Acc00800 := object_fragment0191697_field_007 fuel (fragment0191697Field008Chars00 ++ (fragment0191697Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 252) (SourceJson.white (fragment0191697Field009Chars00 ++ (tail))) fragment0191697Acc00900 := object_fragment0191697_field_008 fuel (fragment0191697Field009Chars00 ++ (tail))
    _ = .ok (fragment0191697Value, tail) := object_fragment0191697_field_009 fuel (tail)

noncomputable def fragment0193356Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0193356Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0193356Field000Value00 : SourceJson := .number (String.ofList ['3', '6'])
noncomputable def fragment0193356Acc00100 : List (String × SourceJson) := (fragment0193356Field000Key00, fragment0193356Field000Value00) :: fragment0193356Acc00000
noncomputable def fragment0193356Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '6', ',']

theorem object_fragment0193356_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 495) (SourceJson.white (fragment0193356Field000Chars00 ++ tail)) fragment0193356Acc00000 =
      SourceJson.object (fuel + 494) (SourceJson.white tail) fragment0193356Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_000"
  err.flush

noncomputable def fragment0193356Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0193356Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0193356Acc00200 : List (String × SourceJson) := (fragment0193356Field001Key00, fragment0193356Field001Value00) :: fragment0193356Acc00100
noncomputable def fragment0193356Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0193356_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 494) (SourceJson.white (fragment0193356Field001Chars00 ++ tail)) fragment0193356Acc00100 =
      SourceJson.object (fuel + 493) (SourceJson.white tail) fragment0193356Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_001"
  err.flush

noncomputable def fragment0193356Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0193356Field002Value00 : SourceJson := .str (String.ofList ['3', '1', '8', '0', '9', '8', '2', '1', '3', '1', '2', '5', '3', '5', '1', '1', '5', '7', '3', '8', '0', '6', '0', '7', '0', '8', '2', '5', '5', '8', '5', '1', '8', '5', '0', '7', '5', '2', '8', '0', '5', '9', '9', '/', '1', '3', '0', '8', '9', '9', '8', '0', '2', '6', '5', '9', '9', '1', '3', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0193356Acc00300 : List (String × SourceJson) := (fragment0193356Field002Key00, fragment0193356Field002Value00) :: fragment0193356Acc00200
noncomputable def fragment0193356Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '1', '8', '0', '9', '8', '2', '1', '3', '1', '2', '5', '3', '5', '1', '1', '5', '7', '3', '8', '0', '6', '0', '7', '0', '8', '2', '5', '5', '8', '5', '1', '8', '5', '0', '7', '5', '2', '8', '0', '5', '9', '9', '/', '1', '3', '0', '8', '9', '9', '8', '0', '2', '6', '5', '9', '9', '1', '3', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0193356_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 493) (SourceJson.white (fragment0193356Field002Chars00 ++ tail)) fragment0193356Acc00200 =
      SourceJson.object (fuel + 492) (SourceJson.white tail) fragment0193356Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_002"
  err.flush

noncomputable def fragment0193356Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0193356Field003Value00 : SourceJson := .str (String.ofList ['4', '7', '4', '8', '0', '4', '7', '7', '4', '1', '3', '3', '/', '1', '2', '7', '9', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0193356Acc00400 : List (String × SourceJson) := (fragment0193356Field003Key00, fragment0193356Field003Value00) :: fragment0193356Acc00300
noncomputable def fragment0193356Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '4', '7', '4', '8', '0', '4', '7', '7', '4', '1', '3', '3', '/', '1', '2', '7', '9', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0193356_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 492) (SourceJson.white (fragment0193356Field003Chars00 ++ tail)) fragment0193356Acc00300 =
      SourceJson.object (fuel + 491) (SourceJson.white tail) fragment0193356Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_003"
  err.flush

noncomputable def fragment0193356Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0193356Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '2', '8', '2', '3', '3', '/', '1', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0193356Acc00500 : List (String × SourceJson) := (fragment0193356Field004Key00, fragment0193356Field004Value00) :: fragment0193356Acc00400
noncomputable def fragment0193356Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '8', '6', '4', '4', '1', '/', '1', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '2', '8', '2', '3', '3', '/', '1', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0193356_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 491) (SourceJson.white (fragment0193356Field004Chars00 ++ tail)) fragment0193356Acc00400 =
      SourceJson.object (fuel + 490) (SourceJson.white tail) fragment0193356Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_004"
  err.flush

noncomputable def fragment0193356Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0193356Field005Value00 : SourceJson := .arr [.str (String.ofList ['9', '9', '8', '7', '7', '0', '9', '2', '3', '6', '9', '9', '5', '3', '7', '9', '7', '8', '5', '6', '1', '7', '7', '0', '3', '/', '1', '1', '3', '8', '9', '7', '0', '9', '5', '0', '8', '8', '3', '3', '3', '5', '9', '9', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '9', '3', '6', '2', '7', '5', '1', '7', '8', '9', '2', '4', '0', '4', '5', '6', '6', '9', '2', '3', '8', '3', '0', '1', '/', '1', '3', '0', '1', '6', '8', '1', '0', '8', '6', '7', '2', '3', '8', '1', '2', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '0', '6', '1', '0', '8', '5', '2', '8', '4', '2', '8', '2', '0', '0', '3', '6', '3', '9', '0', '1', '6', '1', '7', '1', '/', '3', '6', '4', '4', '7', '0', '7', '0', '4', '2', '8', '2', '6', '6', '7', '5', '1', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '6', '6', '1', '1', '1', '6', '4', '1', '8', '3', '7', '6', '5', '4', '9', '9', '1', '7', '1', '9', '5', '8', '8', '1', '/', '2', '0', '2', '4', '8', '3', '7', '2', '4', '6', '0', '1', '4', '8', '1', '9', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '6', '5', '3', '2', '5', '1', '4', '8', '3', '6', '4', '4', '1', '1', '3', '8', '0', '5', '0', '9', '1', '9', '6', '3', '/', '6', '0', '7', '4', '5', '1', '1', '7', '3', '8', '0', '4', '4', '4', '5', '8', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '9', '9', '2', '2', '7', '5', '4', '8', '8', '1', '1', '5', '4', '1', '7', '9', '2', '2', '4', '1', '0', '2', '3', '/', '1', '6', '5', '6', '6', '8', '5', '0', '1', '9', '4', '6', '6', '6', '7', '0', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '9', '4', '5', '3', '6', '3', '8', '7', '9', '8', '4', '3', '6', '8', '6', '3', '5', '6', '4', '3', '5', '7', '7', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '7', '8', '8', '0', '5', '6', '6', '8', '8', '8', '6', '8', '4', '7', '8', '9', '6', '5', '3', '1', '6', '7', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '1', '3', '8', '1', '5', '4', '6', '2', '4', '0', '7', '3', '0', '6', '4', '5', '6', '1', '0', '3', '6', '5', '7', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '6', '9', '1', '4', '5', '1', '9', '9', '2', '2', '0', '3', '5', '8', '6', '5', '8', '1', '7', '1', '6', '4', '7', '/', '1', '3', '0', '1', '6', '8', '1', '0', '8', '6', '7', '2', '3', '8', '1', '2', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0193356Acc00600 : List (String × SourceJson) := (fragment0193356Field005Key00, fragment0193356Field005Value00) :: fragment0193356Acc00500
noncomputable def fragment0193356Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '8', '7', '7', '0', '9', '2', '3', '6', '9', '9', '5', '3', '7', '9', '7', '8', '5', '6', '1', '7', '7', '0', '3', '/', '1', '1', '3', '8', '9', '7', '0', '9', '5', '0', '8', '8', '3', '3', '3', '5', '9', '9', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '9', '3', '6', '2', '7', '5', '1', '7', '8', '9', '2', '4', '0', '4', '5', '6', '6', '9', '2', '3', '8', '3', '0', '1', '/', '1', '3', '0', '1', '6', '8', '1', '0', '8', '6', '7', '2', '3', '8', '1', '2', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '0', '6', '1', '0', '8', '5', '2', '8', '4', '2', '8', '2', '0', '0', '3', '6', '3', '9', '0', '1', '6', '1', '7', '1', '/', '3', '6', '4', '4', '7', '0', '7', '0', '4', '2', '8', '2', '6', '6', '7', '5', '1', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '6', '6', '1', '1', '1', '6', '4', '1', '8', '3', '7', '6', '5', '4', '9', '9', '1', '7', '1', '9', '5', '8', '8', '1', '/', '2', '0', '2', '4', '8', '3', '7', '2', '4', '6', '0', '1', '4', '8', '1', '9', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '6', '5', '3', '2', '5', '1', '4', '8', '3', '6', '4', '4', '1', '1', '3', '8', '0', '5', '0', '9', '1', '9', '6', '3', '/', '6', '0', '7', '4', '5', '1', '1', '7', '3', '8', '0', '4', '4', '4', '5', '8', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '8', '9', '9', '2', '2', '7', '5', '4', '8', '8', '1', '1', '5', '4', '1', '7', '9', '2', '2', '4', '1', '0', '2', '3', '/', '1', '6', '5', '6', '6', '8', '5', '0', '1', '9', '4', '6', '6', '6', '7', '0', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '9', '4', '5', '3', '6', '3', '8', '7', '9', '8', '4', '3', '6', '8', '6', '3', '5', '6', '4', '3', '5', '7', '7', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '7', '7', '8', '8', '0', '5', '6', '6', '8', '8', '8', '6', '8', '4', '7', '8', '9', '6', '5', '3', '1', '6', '7', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '3', '8', '1', '5', '4', '6', '2', '4', '0', '7', '3', '0', '6', '4', '5', '6', '1', '0', '3', '6', '5', '7', '/', '8', '2', '8', '3', '4', '2', '5', '0', '9', '7', '3', '3', '3', '3', '5', '2', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '6', '9', '1', '4', '5', '1', '9', '9', '2', '2', '0', '3', '5', '8', '6', '5', '8', '1', '7', '1', '6', '4', '7', '/', '1', '3', '0', '1', '6', '8', '1', '0', '8', '6', '7', '2', '3', '8', '1', '2', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0193356_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 490) (SourceJson.white (fragment0193356Field005Chars00 ++ tail)) fragment0193356Acc00500 =
      SourceJson.object (fuel + 489) (SourceJson.white tail) fragment0193356Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_005"
  err.flush

noncomputable def fragment0193356Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0193356Field006Value00 : SourceJson := .str (String.ofList ['2', '5', '4', '3', '7', '3', '9', '7', '9', '3', '4', '3', '3', '1', '4', '9', '5', '1', '2', '3', '6', '0', '5', '7', '7', '3', '7', '6', '8', '1', '8', '8', '2', '0', '4', '4', '1', '6', '3', '3', '0', '2', '3', '0', '0', '5', '9', '6', '5', '3', '8', '2', '1', '7', '6', '0', '0', '0', '0', '0', '/', '1', '3', '4', '8', '5', '9', '2', '7', '9', '8', '0', '5', '6', '2', '3', '0', '7', '5', '3', '6', '2', '5', '2', '0', '3', '6', '1', '8', '2', '6', '4', '9', '6', '8', '3', '3', '6', '3', '2', '8', '5', '5', '5', '0', '5', '2', '3', '9', '5', '7', '8', '6', '0', '8', '3', '7', '2', '1', '7', '7', '3', '0', '6', '1', '0', '6', '1', '6', '3', '9', '5', '7', '0', '4', '7'])
noncomputable def fragment0193356Acc00700 : List (String × SourceJson) := (fragment0193356Field006Key00, fragment0193356Field006Value00) :: fragment0193356Acc00600
noncomputable def fragment0193356Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '5', '4', '3', '7', '3', '9', '7', '9', '3', '4', '3', '3', '1', '4', '9', '5', '1', '2', '3', '6', '0', '5', '7', '7', '3', '7', '6', '8', '1', '8', '8', '2', '0', '4', '4', '1', '6', '3', '3', '0', '2', '3', '0', '0', '5', '9', '6', '5', '3', '8', '2', '1', '7', '6', '0', '0', '0', '0', '0', '/', '1', '3', '4', '8', '5', '9', '2', '7', '9', '8', '0', '5', '6', '2', '3', '0', '7', '5', '3', '6', '2', '5', '2', '0', '3', '6', '1', '8', '2', '6', '4', '9', '6', '8', '3', '3', '6', '3', '2', '8', '5', '5', '5', '0', '5', '2', '3', '9', '5', '7', '8', '6', '0', '8', '3', '7', '2', '1', '7', '7', '3', '0', '6', '1', '0', '6', '1', '6', '3', '9', '5', '7', '0', '4', '7', '"', ',']

theorem object_fragment0193356_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 489) (SourceJson.white (fragment0193356Field006Chars00 ++ tail)) fragment0193356Acc00600 =
      SourceJson.object (fuel + 488) (SourceJson.white tail) fragment0193356Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_006"
  err.flush

noncomputable def fragment0193356Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0193356Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '8', '4', '1', '1', '1', '8', '6', '1', '4', '2', '2', '6', '5', '8', '1', '1', '1', '4', '5', '7', '2', '7', '4', '4', '7', '3', '4', '2', '7', '9', '4', '0', '3', '4', '9', '2', '2', '7', '3', '1', '8', '8', '0', '2', '6', '3', '4', '2', '2', '2', '9', '9', '8', '3', '3', '8', '6', '3', '8', '3', '0', '5', '5', '5', '6', '5', '3', '2', '9', '6', '1', '3', '7', '5', '5', '9', '5', '2', '4', '0', '4', '2', '3', '4', '6', '0', '5', '3', '7', '3', '4', '6', '1', '4', '6', '9', '4', '1', '4', '8', '7', '8', '3', '4', '1', '1', '7', '5', '8', '9', '2', '8', '3', '3', '1', '0', '9', '9', '4', '7', '3', '1', '9', '5', '8', '8', '9', '3', '2', '8', '7', '1', '7', '0', '1', '8', '5', '9', '0', '1', '0', '8', '7', '0', '9', '1', '3', '4', '0', '8', '4', '6', '1', '0', '4', '7', '3', '3', '0', '5', '0', '1', '9', '0', '5', '3', '2', '6', '5', '2', '6', '5', '3', '5', '8', '7', '3', '7', '0', '3', '2', '0', '7', '9', '0', '3', '3', '1', '4', '7', '6', '8', '8', '6', '4', '6', '1', '1', '9', '5', '4', '8', '2', '1', '5', '0', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '8', '9', '0', '1', '6', '0', '0', '4', '8', '4', '5', '3', '2', '5', '0', '0', '0', '4', '2', '1', '7', '1', '3', '5', '7', '8', '0', '2', '6', '4', '8', '0', '0', '4', '2', '6', '0', '4', '3', '4', '7', '8', '5', '0', '7', '3', '3', '8', '5', '2', '4', '9', '0', '3', '4', '6', '9', '8', '5', '2', '5', '5', '9', '7', '4', '5', '2', '0', '7', '8', '7', '0', '5', '1', '3', '9', '4', '0', '7', '1', '7', '1', '4', '8', '7', '3', '4', '3', '5', '3', '5', '9', '5', '6', '7', '6', '2', '9', '3', '7', '1', '9', '9', '7', '6', '1', '7', '2', '7', '5', '4', '2', '4', '2', '1', '5', '6', '2', '0', '3', '7', '5', '9', '6', '5', '1', '2', '3', '0', '9', '3', '4', '2', '8', '9', '0', '3', '7', '7', '5', '4', '8', '7', '3', '9', '5', '7', '7', '5', '1', '3', '0', '1', '6', '8', '7', '4', '7', '8', '7', '9', '9', '6', '3', '5', '2', '9', '8', '9', '6', '9', '9', '9', '2', '0', '6', '0', '7', '7', '4', '0', '2', '0', '7', '3', '7', '4', '9', '1', '7', '7', '9', '3', '7', '2', '1', '6', '8', '4', '1', '2', '0', '7', '6', '1', '1', '6', '1', '0', '8', '7', '7', '2', '4', '4', '3', '9', '5', '4', '6', '9', '4', '1', '8', '2', '6', '6', '2', '8', '3', '6', '4', '7', '1', '8', '7', '7', '5', '9', '1', '0', '6', '3', '2', '2', '7', '1'])
noncomputable def fragment0193356Acc00800 : List (String × SourceJson) := (fragment0193356Field007Key00, fragment0193356Field007Value00) :: fragment0193356Acc00700
noncomputable def fragment0193356Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '8', '8', '4', '1', '1', '1', '8', '6', '1', '4', '2', '2', '6', '5', '8', '1', '1', '1', '4', '5', '7', '2', '7', '4', '4', '7', '3', '4', '2', '7', '9', '4', '0', '3', '4', '9', '2', '2', '7', '3', '1', '8', '8', '0', '2', '6', '3', '4', '2', '2', '2', '9', '9', '8', '3', '3', '8', '6', '3', '8', '3', '0', '5', '5', '5', '6', '5', '3', '2', '9', '6', '1', '3', '7', '5', '5', '9', '5', '2', '4', '0', '4', '2', '3', '4', '6', '0', '5', '3', '7', '3', '4', '6', '1', '4', '6', '9', '4', '1', '4', '8', '7', '8', '3', '4', '1', '1', '7', '5', '8', '9', '2', '8', '3', '3', '1', '0', '9', '9', '4', '7', '3', '1', '9', '5', '8', '8', '9', '3', '2', '8', '7', '1', '7', '0', '1', '8', '5', '9', '0', '1', '0', '8', '7', '0', '9', '1', '3', '4', '0', '8', '4', '6', '1', '0', '4', '7', '3', '3', '0', '5', '0', '1', '9', '0', '5', '3', '2', '6', '5', '2', '6', '5', '3', '5', '8', '7', '3', '7', '0', '3', '2', '0', '7', '9', '0', '3', '3', '1', '4', '7', '6', '8', '8', '6', '4', '6', '1', '1', '9', '5', '4', '8', '2', '1', '5', '0', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '8', '9', '0', '1', '6', '0', '0', '4', '8', '4', '5', '3', '2', '5', '0', '0', '0', '4', '2', '1', '7', '1', '3', '5', '7', '8', '0', '2', '6', '4', '8', '0', '0', '4', '2', '6', '0', '4', '3', '4', '7', '8', '5', '0', '7', '3', '3', '8', '5', '2', '4', '9', '0', '3', '4', '6', '9', '8', '5', '2', '5', '5', '9', '7', '4', '5', '2', '0', '7', '8', '7', '0', '5', '1', '3', '9', '4', '0', '7', '1', '7', '1', '4', '8', '7', '3', '4', '3', '5', '3', '5', '9', '5', '6', '7', '6', '2', '9', '3', '7', '1', '9', '9', '7', '6', '1', '7', '2', '7', '5', '4', '2', '4', '2', '1', '5', '6', '2', '0', '3', '7', '5', '9', '6', '5', '1', '2', '3', '0', '9', '3', '4', '2', '8', '9', '0', '3', '7', '7', '5', '4', '8', '7', '3', '9', '5', '7', '7', '5', '1', '3', '0', '1', '6', '8', '7', '4', '7', '8', '7', '9', '9', '6', '3', '5', '2', '9', '8', '9', '6', '9', '9', '9', '2', '0', '6', '0', '7', '7', '4', '0', '2', '0', '7', '3', '7', '4', '9', '1', '7', '7', '9', '3', '7', '2', '1', '6', '8', '4', '1', '2', '0', '7', '6', '1', '1', '6', '1', '0', '8', '7', '7', '2', '4', '4', '3', '9', '5', '4', '6', '9', '4', '1', '8', '2', '6', '6', '2', '8', '3', '6', '4', '7', '1', '8', '7', '7', '5', '9', '1', '0', '6', '3', '2', '2', '7', '1', '"', ',']

theorem object_fragment0193356_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 488) (SourceJson.white (fragment0193356Field007Chars00 ++ tail)) fragment0193356Acc00700 =
      SourceJson.object (fuel + 487) (SourceJson.white tail) fragment0193356Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_007"
  err.flush

noncomputable def fragment0193356Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0193356Field008Value00 : SourceJson := .str (String.ofList ['1', '4', '9', '4', '4', '1', '5', '7', '3', '4', '9', '6', '9', '0', '9'])
noncomputable def fragment0193356Acc00900 : List (String × SourceJson) := (fragment0193356Field008Key00, fragment0193356Field008Value00) :: fragment0193356Acc00800
noncomputable def fragment0193356Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '4', '9', '4', '4', '1', '5', '7', '3', '4', '9', '6', '9', '0', '9', '"', ',']

theorem object_fragment0193356_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 487) (SourceJson.white (fragment0193356Field008Chars00 ++ tail)) fragment0193356Acc00800 =
      SourceJson.object (fuel + 486) (SourceJson.white tail) fragment0193356Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_008"
  err.flush

noncomputable def fragment0193356Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0193356Field009Value00 : SourceJson := .str (String.ofList ['3', '9', '3', '9', '3', '4', '1', '6', '1', '0', '4', '3', '8', '1', '4'])
noncomputable def fragment0193356Acc01000 : List (String × SourceJson) := (fragment0193356Field009Key00, fragment0193356Field009Value00) :: fragment0193356Acc00900
noncomputable def fragment0193356Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '9', '3', '9', '3', '4', '1', '6', '1', '0', '4', '3', '8', '1', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0193356_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 486) (SourceJson.white (fragment0193356Field009Chars00 ++ tail)) fragment0193356Acc00900 =
      .ok (.obj (fragment0193356Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0193356_object_field_009"
  err.flush

noncomputable def fragment0193356Chars : List Char := '{' :: (fragment0193356Field000Chars00 ++ fragment0193356Field001Chars00 ++ fragment0193356Field002Chars00 ++ fragment0193356Field003Chars00 ++ fragment0193356Field004Chars00 ++ fragment0193356Field005Chars00 ++ fragment0193356Field006Chars00 ++ fragment0193356Field007Chars00 ++ fragment0193356Field008Chars00 ++ fragment0193356Field009Chars00)
noncomputable def fragment0193356Value : SourceJson := .obj (fragment0193356Acc01000.reverse)

theorem value_fragment0193356 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 496) (fragment0193356Chars ++ tail) =
      .ok (fragment0193356Value, tail) := by
  have hinput : fragment0193356Chars ++ tail = '{' :: (fragment0193356Field000Chars00 ++ (fragment0193356Field001Chars00 ++ (fragment0193356Field002Chars00 ++ (fragment0193356Field003Chars00 ++ (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0193356Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 496) (fragment0193356Chars ++ tail) =
        SourceJson.value (fuel + 496) ('{' :: (fragment0193356Field000Chars00 ++ (fragment0193356Field001Chars00 ++ (fragment0193356Field002Chars00 ++ (fragment0193356Field003Chars00 ++ (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 496)) hinput
    _ = SourceJson.object (fuel + 495) (SourceJson.white (fragment0193356Field000Chars00 ++ (fragment0193356Field001Chars00 ++ (fragment0193356Field002Chars00 ++ (fragment0193356Field003Chars00 ++ (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))))))))))) fragment0193356Acc00000 := by rfl
    _ = SourceJson.object (fuel + 494) (SourceJson.white (fragment0193356Field001Chars00 ++ (fragment0193356Field002Chars00 ++ (fragment0193356Field003Chars00 ++ (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail))))))))))) fragment0193356Acc00100 := object_fragment0193356_field_000 fuel (fragment0193356Field001Chars00 ++ (fragment0193356Field002Chars00 ++ (fragment0193356Field003Chars00 ++ (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 493) (SourceJson.white (fragment0193356Field002Chars00 ++ (fragment0193356Field003Chars00 ++ (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))))))))) fragment0193356Acc00200 := object_fragment0193356_field_001 fuel (fragment0193356Field002Chars00 ++ (fragment0193356Field003Chars00 ++ (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 492) (SourceJson.white (fragment0193356Field003Chars00 ++ (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail))))))))) fragment0193356Acc00300 := object_fragment0193356_field_002 fuel (fragment0193356Field003Chars00 ++ (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 491) (SourceJson.white (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))))))) fragment0193356Acc00400 := object_fragment0193356_field_003 fuel (fragment0193356Field004Chars00 ++ (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 490) (SourceJson.white (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail))))))) fragment0193356Acc00500 := object_fragment0193356_field_004 fuel (fragment0193356Field005Chars00 ++ (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 489) (SourceJson.white (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))))) fragment0193356Acc00600 := object_fragment0193356_field_005 fuel (fragment0193356Field006Chars00 ++ (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 488) (SourceJson.white (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail))))) fragment0193356Acc00700 := object_fragment0193356_field_006 fuel (fragment0193356Field007Chars00 ++ (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 487) (SourceJson.white (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))) fragment0193356Acc00800 := object_fragment0193356_field_007 fuel (fragment0193356Field008Chars00 ++ (fragment0193356Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 486) (SourceJson.white (fragment0193356Field009Chars00 ++ (tail))) fragment0193356Acc00900 := object_fragment0193356_field_008 fuel (fragment0193356Field009Chars00 ++ (tail))
    _ = .ok (fragment0193356Value, tail) := object_fragment0193356_field_009 fuel (tail)

noncomputable def fragment0195513Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0195513Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0195513Field000Value00 : SourceJson := .number (String.ofList ['3', '7'])
noncomputable def fragment0195513Acc00100 : List (String × SourceJson) := (fragment0195513Field000Key00, fragment0195513Field000Value00) :: fragment0195513Acc00000
noncomputable def fragment0195513Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '7', ',']

theorem object_fragment0195513_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 479) (SourceJson.white (fragment0195513Field000Chars00 ++ tail)) fragment0195513Acc00000 =
      SourceJson.object (fuel + 478) (SourceJson.white tail) fragment0195513Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_000"
  err.flush

noncomputable def fragment0195513Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0195513Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0195513Acc00200 : List (String × SourceJson) := (fragment0195513Field001Key00, fragment0195513Field001Value00) :: fragment0195513Acc00100
noncomputable def fragment0195513Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0195513_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 478) (SourceJson.white (fragment0195513Field001Chars00 ++ tail)) fragment0195513Acc00100 =
      SourceJson.object (fuel + 477) (SourceJson.white tail) fragment0195513Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_001"
  err.flush

noncomputable def fragment0195513Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0195513Field002Value00 : SourceJson := .str (String.ofList ['5', '8', '1', '3', '5', '8', '6', '8', '7', '9', '9', '7', '1', '9', '6', '5', '1', '2', '4', '6', '8', '8', '6', '5', '8', '7', '7', '2', '0', '8', '0', '4', '2', '6', '4', '3', '3', '/', '6', '8', '4', '9', '4', '0', '8', '2', '7', '8', '7', '1', '6', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0195513Acc00300 : List (String × SourceJson) := (fragment0195513Field002Key00, fragment0195513Field002Value00) :: fragment0195513Acc00200
noncomputable def fragment0195513Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '8', '1', '3', '5', '8', '6', '8', '7', '9', '9', '7', '1', '9', '6', '5', '1', '2', '4', '6', '8', '8', '6', '5', '8', '7', '7', '2', '0', '8', '0', '4', '2', '6', '4', '3', '3', '/', '6', '8', '4', '9', '4', '0', '8', '2', '7', '8', '7', '1', '6', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0195513_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 477) (SourceJson.white (fragment0195513Field002Chars00 ++ tail)) fragment0195513Acc00200 =
      SourceJson.object (fuel + 476) (SourceJson.white tail) fragment0195513Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_002"
  err.flush

noncomputable def fragment0195513Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0195513Field003Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0195513Acc00400 : List (String × SourceJson) := (fragment0195513Field003Key00, fragment0195513Field003Value00) :: fragment0195513Acc00300
noncomputable def fragment0195513Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9', '/', '3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0195513_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 476) (SourceJson.white (fragment0195513Field003Chars00 ++ tail)) fragment0195513Acc00300 =
      SourceJson.object (fuel + 475) (SourceJson.white tail) fragment0195513Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_003"
  err.flush

noncomputable def fragment0195513Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0195513Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '2', '8', '2', '3', '3', '/', '1', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0195513Acc00500 : List (String × SourceJson) := (fragment0195513Field004Key00, fragment0195513Field004Value00) :: fragment0195513Acc00400
noncomputable def fragment0195513Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '2', '8', '2', '3', '3', '/', '1', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '4', '3', '7', '9', '/', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0195513_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 475) (SourceJson.white (fragment0195513Field004Chars00 ++ tail)) fragment0195513Acc00400 =
      SourceJson.object (fuel + 474) (SourceJson.white tail) fragment0195513Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_004"
  err.flush

noncomputable def fragment0195513Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0195513Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '9', '3', '9', '9', '7', '0', '6', '8', '1', '1', '1', '1', '3', '7', '0', '9', '5', '6', '2', '0', '9', '9', '3', '3', '3', '7', '/', '2', '1', '7', '6', '0', '2', '1', '5', '2', '1', '3', '9', '7', '9', '0', '1', '1', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '4', '2', '6', '8', '3', '3', '8', '1', '4', '2', '6', '4', '5', '9', '6', '7', '7', '1', '3', '6', '8', '3', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '0', '4', '3', '9', '6', '7', '9', '9', '3', '8', '6', '3', '9', '4', '2', '2', '5', '5', '8', '4', '6', '2', '3', '/', '2', '4', '1', '7', '8', '0', '1', '6', '9', '0', '4', '4', '2', '1', '1', '2', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '1', '3', '8', '7', '4', '8', '2', '9', '7', '4', '4', '8', '0', '2', '1', '2', '2', '1', '2', '8', '6', '3', '6', '3', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '5', '4', '7', '5', '0', '7', '4', '8', '1', '8', '1', '2', '3', '1', '7', '2', '7', '9', '6', '2', '1', '4', '8', '3', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '8', '9', '6', '8', '0', '3', '5', '5', '2', '2', '4', '4', '0', '6', '2', '8', '3', '3', '7', '0', '6', '7', '/', '5', '4', '9', '5', '0', '0', '3', '8', '4', '1', '9', '1', '3', '8', '9', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '9', '8', '4', '0', '1', '1', '5', '5', '8', '4', '8', '0', '3', '8', '6', '1', '9', '7', '9', '7', '8', '1', '/', '1', '2', '3', '6', '3', '7', '5', '8', '6', '4', '4', '3', '0', '6', '2', '5', '6', '7', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '7', '9', '8', '1', '8', '2', '3', '2', '2', '0', '8', '6', '9', '5', '2', '7', '7', '8', '5', '3', '3', '3', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '6', '4', '2', '1', '2', '8', '7', '6', '1', '4', '9', '2', '4', '7', '3', '7', '0', '3', '5', '0', '4', '1', '3', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '9', '3', '2', '7', '4', '1', '3', '5', '2', '8', '1', '3', '6', '0', '0', '5', '7', '7', '6', '0', '1', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0195513Acc00600 : List (String × SourceJson) := (fragment0195513Field005Key00, fragment0195513Field005Value00) :: fragment0195513Acc00500
noncomputable def fragment0195513Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '3', '9', '9', '7', '0', '6', '8', '1', '1', '1', '1', '3', '7', '0', '9', '5', '6', '2', '0', '9', '9', '3', '3', '3', '7', '/', '2', '1', '7', '6', '0', '2', '1', '5', '2', '1', '3', '9', '7', '9', '0', '1', '1', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '4', '2', '6', '8', '3', '3', '8', '1', '4', '2', '6', '4', '5', '9', '6', '7', '7', '1', '3', '6', '8', '3', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '0', '4', '3', '9', '6', '7', '9', '9', '3', '8', '6', '3', '9', '4', '2', '2', '5', '5', '8', '4', '6', '2', '3', '/', '2', '4', '1', '7', '8', '0', '1', '6', '9', '0', '4', '4', '2', '1', '1', '2', '4', '3', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '1', '3', '8', '7', '4', '8', '2', '9', '7', '4', '4', '8', '0', '2', '1', '2', '2', '1', '2', '8', '6', '3', '6', '3', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '5', '4', '7', '5', '0', '7', '4', '8', '1', '8', '1', '2', '3', '1', '7', '2', '7', '9', '6', '2', '1', '4', '8', '3', '/', '1', '0', '8', '8', '0', '1', '0', '7', '6', '0', '6', '9', '8', '9', '5', '0', '5', '9', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '8', '9', '6', '8', '0', '3', '5', '5', '2', '2', '4', '4', '0', '6', '2', '8', '3', '3', '7', '0', '6', '7', '/', '5', '4', '9', '5', '0', '0', '3', '8', '4', '1', '9', '1', '3', '8', '9', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '2', '9', '8', '4', '0', '1', '1', '5', '5', '8', '4', '8', '0', '3', '8', '6', '1', '9', '7', '9', '7', '8', '1', '/', '1', '2', '3', '6', '3', '7', '5', '8', '6', '4', '4', '3', '0', '6', '2', '5', '6', '7', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '1', '7', '9', '8', '1', '8', '2', '3', '2', '2', '0', '8', '6', '9', '5', '2', '7', '7', '8', '5', '3', '3', '3', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '6', '4', '2', '1', '2', '8', '7', '6', '1', '4', '9', '2', '4', '7', '3', '7', '0', '3', '5', '0', '4', '1', '3', '/', '9', '8', '9', '1', '0', '0', '6', '9', '1', '5', '4', '4', '5', '0', '0', '5', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '3', '9', '3', '2', '7', '4', '1', '3', '5', '2', '8', '1', '3', '6', '0', '0', '5', '7', '7', '6', '0', '1', '/', '3', '6', '1', '4', '6', '5', '3', '6', '9', '0', '0', '2', '9', '7', '3', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0195513_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 474) (SourceJson.white (fragment0195513Field005Chars00 ++ tail)) fragment0195513Acc00500 =
      SourceJson.object (fuel + 473) (SourceJson.white tail) fragment0195513Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_005"
  err.flush

noncomputable def fragment0195513Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0195513Field006Value00 : SourceJson := .str (String.ofList ['4', '4', '4', '0', '9', '5', '2', '8', '7', '3', '4', '6', '1', '4', '6', '6', '5', '3', '9', '4', '3', '1', '5', '6', '0', '2', '7', '2', '1', '6', '7', '5', '6', '5', '0', '0', '5', '3', '2', '9', '2', '0', '1', '9', '5', '0', '1', '1', '8', '4', '0', '0', '0', '0', '0', '0', '/', '8', '4', '6', '7', '9', '1', '4', '1', '1', '7', '9', '1', '3', '8', '9', '4', '3', '5', '3', '9', '7', '8', '8', '7', '3', '0', '5', '1', '6', '1', '0', '9', '0', '4', '5', '8', '1', '1', '5', '3', '6', '7', '3', '3', '3', '5', '1', '7', '8', '6', '8', '9', '8', '5', '7', '3', '5', '0', '3', '1', '9', '2', '3', '2', '1', '9', '8', '9', '5', '0', '5', '4', '3', '9'])
noncomputable def fragment0195513Acc00700 : List (String × SourceJson) := (fragment0195513Field006Key00, fragment0195513Field006Value00) :: fragment0195513Acc00600
noncomputable def fragment0195513Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '4', '4', '0', '9', '5', '2', '8', '7', '3', '4', '6', '1', '4', '6', '6', '5', '3', '9', '4', '3', '1', '5', '6', '0', '2', '7', '2', '1', '6', '7', '5', '6', '5', '0', '0', '5', '3', '2', '9', '2', '0', '1', '9', '5', '0', '1', '1', '8', '4', '0', '0', '0', '0', '0', '0', '/', '8', '4', '6', '7', '9', '1', '4', '1', '1', '7', '9', '1', '3', '8', '9', '4', '3', '5', '3', '9', '7', '8', '8', '7', '3', '0', '5', '1', '6', '1', '0', '9', '0', '4', '5', '8', '1', '1', '5', '3', '6', '7', '3', '3', '3', '5', '1', '7', '8', '6', '8', '9', '8', '5', '7', '3', '5', '0', '3', '1', '9', '2', '3', '2', '1', '9', '8', '9', '5', '0', '5', '4', '3', '9', '"', ',']

theorem object_fragment0195513_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 473) (SourceJson.white (fragment0195513Field006Chars00 ++ tail)) fragment0195513Acc00600 =
      SourceJson.object (fuel + 472) (SourceJson.white tail) fragment0195513Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_006"
  err.flush

noncomputable def fragment0195513Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0195513Field007Value00 : SourceJson := .str (String.ofList ['7', '7', '1', '6', '7', '9', '5', '9', '9', '5', '5', '3', '1', '6', '4', '3', '3', '3', '7', '0', '7', '1', '7', '8', '7', '4', '0', '0', '1', '6', '3', '3', '4', '5', '9', '9', '6', '0', '0', '8', '8', '6', '5', '4', '4', '4', '8', '0', '1', '4', '0', '0', '3', '5', '2', '2', '0', '9', '4', '1', '6', '1', '3', '7', '3', '9', '8', '0', '3', '1', '5', '7', '8', '7', '8', '2', '7', '5', '1', '0', '8', '1', '8', '7', '5', '4', '7', '9', '8', '4', '6', '8', '8', '5', '2', '4', '0', '9', '3', '6', '6', '8', '2', '6', '9', '1', '0', '1', '0', '1', '2', '2', '1', '3', '8', '3', '7', '9', '4', '1', '3', '2', '5', '2', '7', '9', '3', '6', '4', '0', '8', '2', '2', '7', '5', '9', '9', '6', '6', '1', '5', '4', '7', '1', '8', '5', '1', '6', '9', '9', '9', '0', '1', '9', '9', '6', '0', '4', '4', '8', '8', '9', '6', '6', '4', '4', '0', '2', '4', '2', '0', '3', '9', '1', '7', '8', '5', '0', '9', '8', '1', '8', '8', '3', '3', '8', '4', '7', '4', '1', '7', '1', '3', '0', '0', '9', '6', '1', '3', '1', '6', '9', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '7', '8', '1', '9', '6', '7', '0', '5', '7', '0', '1', '8', '2', '3', '2', '3', '3', '8', '0', '6', '8', '6', '5', '3', '6', '7', '4', '6', '0', '3', '8', '8', '9', '2', '6', '4', '8', '3', '6', '0', '0', '9', '0', '2', '9', '8', '0', '3', '6', '2', '0', '8', '3', '9', '7', '1', '3', '7', '8', '3', '3', '7', '4', '3', '9', '2', '6', '1', '5', '7', '1', '6', '9', '0', '8', '3', '9', '2', '2', '4', '5', '8', '3', '5', '6', '4', '5', '9', '5', '3', '1', '9', '4', '5', '1', '5', '2', '1', '7', '4', '7', '1', '1', '3', '0', '2', '5', '9', '2', '0', '4', '1', '7', '2', '9', '8', '2', '4', '6', '1', '3', '6', '3', '4', '7', '9', '4', '1', '2', '8', '8', '1', '5', '3', '6', '2', '1', '9', '4', '7', '1', '9', '8', '6', '6', '3', '2', '6', '5', '4', '0', '4', '3', '9', '1', '4', '9', '6', '8', '3', '2', '7', '1', '3', '1', '7', '4', '1', '9', '5', '3', '5', '5', '1', '7', '5', '4', '5', '9', '8', '0', '1', '8', '0', '1', '3', '4', '9', '5', '7', '3', '4', '6', '4', '2', '5', '2', '1', '8', '0', '4', '0', '7', '9', '1', '6', '0', '0', '9', '3', '8', '0', '4', '7', '7', '6', '1', '6', '0', '3', '9', '5', '7', '7', '5', '7', '7', '5', '1', '1', '2', '8', '1', '0', '5', '5', '4', '9', '8', '7', '7'])
noncomputable def fragment0195513Acc00800 : List (String × SourceJson) := (fragment0195513Field007Key00, fragment0195513Field007Value00) :: fragment0195513Acc00700
noncomputable def fragment0195513Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '7', '7', '1', '6', '7', '9', '5', '9', '9', '5', '5', '3', '1', '6', '4', '3', '3', '3', '7', '0', '7', '1', '7', '8', '7', '4', '0', '0', '1', '6', '3', '3', '4', '5', '9', '9', '6', '0', '0', '8', '8', '6', '5', '4', '4', '4', '8', '0', '1', '4', '0', '0', '3', '5', '2', '2', '0', '9', '4', '1', '6', '1', '3', '7', '3', '9', '8', '0', '3', '1', '5', '7', '8', '7', '8', '2', '7', '5', '1', '0', '8', '1', '8', '7', '5', '4', '7', '9', '8', '4', '6', '8', '8', '5', '2', '4', '0', '9', '3', '6', '6', '8', '2', '6', '9', '1', '0', '1', '0', '1', '2', '2', '1', '3', '8', '3', '7', '9', '4', '1', '3', '2', '5', '2', '7', '9', '3', '6', '4', '0', '8', '2', '2', '7', '5', '9', '9', '6', '6', '1', '5', '4', '7', '1', '8', '5', '1', '6', '9', '9', '9', '0', '1', '9', '9', '6', '0', '4', '4', '8', '8', '9', '6', '6', '4', '4', '0', '2', '4', '2', '0', '3', '9', '1', '7', '8', '5', '0', '9', '8', '1', '8', '8', '3', '3', '8', '4', '7', '4', '1', '7', '1', '3', '0', '0', '9', '6', '1', '3', '1', '6', '9', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '7', '8', '1', '9', '6', '7', '0', '5', '7', '0', '1', '8', '2', '3', '2', '3', '3', '8', '0', '6', '8', '6', '5', '3', '6', '7', '4', '6', '0', '3', '8', '8', '9', '2', '6', '4', '8', '3', '6', '0', '0', '9', '0', '2', '9', '8', '0', '3', '6', '2', '0', '8', '3', '9', '7', '1', '3', '7', '8', '3', '3', '7', '4', '3', '9', '2', '6', '1', '5', '7', '1', '6', '9', '0', '8', '3', '9', '2', '2', '4', '5', '8', '3', '5', '6', '4', '5', '9', '5', '3', '1', '9', '4', '5', '1', '5', '2', '1', '7', '4', '7', '1', '1', '3', '0', '2', '5', '9', '2', '0', '4', '1', '7', '2', '9', '8', '2', '4', '6', '1', '3', '6', '3', '4', '7', '9', '4', '1', '2', '8', '8', '1', '5', '3', '6', '2', '1', '9', '4', '7', '1', '9', '8', '6', '6', '3', '2', '6', '5', '4', '0', '4', '3', '9', '1', '4', '9', '6', '8', '3', '2', '7', '1', '3', '1', '7', '4', '1', '9', '5', '3', '5', '5', '1', '7', '5', '4', '5', '9', '8', '0', '1', '8', '0', '1', '3', '4', '9', '5', '7', '3', '4', '6', '4', '2', '5', '2', '1', '8', '0', '4', '0', '7', '9', '1', '6', '0', '0', '9', '3', '8', '0', '4', '7', '7', '6', '1', '6', '0', '3', '9', '5', '7', '7', '5', '7', '7', '5', '1', '1', '2', '8', '1', '0', '5', '5', '4', '9', '8', '7', '7', '"', ',']

theorem object_fragment0195513_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 472) (SourceJson.white (fragment0195513Field007Chars00 ++ tail)) fragment0195513Acc00700 =
      SourceJson.object (fuel + 471) (SourceJson.white tail) fragment0195513Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_007"
  err.flush

noncomputable def fragment0195513Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0195513Field008Value00 : SourceJson := .str (String.ofList ['4', '1', '5', '5', '0', '7', '9', '1', '7', '3', '8'])
noncomputable def fragment0195513Acc00900 : List (String × SourceJson) := (fragment0195513Field008Key00, fragment0195513Field008Value00) :: fragment0195513Acc00800
noncomputable def fragment0195513Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '1', '5', '5', '0', '7', '9', '1', '7', '3', '8', '"', ',']

theorem object_fragment0195513_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 471) (SourceJson.white (fragment0195513Field008Chars00 ++ tail)) fragment0195513Acc00800 =
      SourceJson.object (fuel + 470) (SourceJson.white tail) fragment0195513Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_008"
  err.flush

noncomputable def fragment0195513Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0195513Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '6', '7', '2', '8', '4', '0', '3', '2', '4'])
noncomputable def fragment0195513Acc01000 : List (String × SourceJson) := (fragment0195513Field009Key00, fragment0195513Field009Value00) :: fragment0195513Acc00900
noncomputable def fragment0195513Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '6', '7', '2', '8', '4', '0', '3', '2', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0195513_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 470) (SourceJson.white (fragment0195513Field009Chars00 ++ tail)) fragment0195513Acc00900 =
      .ok (.obj (fragment0195513Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0195513_object_field_009"
  err.flush

noncomputable def fragment0195513Chars : List Char := '{' :: (fragment0195513Field000Chars00 ++ fragment0195513Field001Chars00 ++ fragment0195513Field002Chars00 ++ fragment0195513Field003Chars00 ++ fragment0195513Field004Chars00 ++ fragment0195513Field005Chars00 ++ fragment0195513Field006Chars00 ++ fragment0195513Field007Chars00 ++ fragment0195513Field008Chars00 ++ fragment0195513Field009Chars00)
noncomputable def fragment0195513Value : SourceJson := .obj (fragment0195513Acc01000.reverse)

theorem value_fragment0195513 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 480) (fragment0195513Chars ++ tail) =
      .ok (fragment0195513Value, tail) := by
  have hinput : fragment0195513Chars ++ tail = '{' :: (fragment0195513Field000Chars00 ++ (fragment0195513Field001Chars00 ++ (fragment0195513Field002Chars00 ++ (fragment0195513Field003Chars00 ++ (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0195513Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 480) (fragment0195513Chars ++ tail) =
        SourceJson.value (fuel + 480) ('{' :: (fragment0195513Field000Chars00 ++ (fragment0195513Field001Chars00 ++ (fragment0195513Field002Chars00 ++ (fragment0195513Field003Chars00 ++ (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 480)) hinput
    _ = SourceJson.object (fuel + 479) (SourceJson.white (fragment0195513Field000Chars00 ++ (fragment0195513Field001Chars00 ++ (fragment0195513Field002Chars00 ++ (fragment0195513Field003Chars00 ++ (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))))))))))) fragment0195513Acc00000 := by rfl
    _ = SourceJson.object (fuel + 478) (SourceJson.white (fragment0195513Field001Chars00 ++ (fragment0195513Field002Chars00 ++ (fragment0195513Field003Chars00 ++ (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail))))))))))) fragment0195513Acc00100 := object_fragment0195513_field_000 fuel (fragment0195513Field001Chars00 ++ (fragment0195513Field002Chars00 ++ (fragment0195513Field003Chars00 ++ (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 477) (SourceJson.white (fragment0195513Field002Chars00 ++ (fragment0195513Field003Chars00 ++ (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))))))))) fragment0195513Acc00200 := object_fragment0195513_field_001 fuel (fragment0195513Field002Chars00 ++ (fragment0195513Field003Chars00 ++ (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 476) (SourceJson.white (fragment0195513Field003Chars00 ++ (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail))))))))) fragment0195513Acc00300 := object_fragment0195513_field_002 fuel (fragment0195513Field003Chars00 ++ (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 475) (SourceJson.white (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))))))) fragment0195513Acc00400 := object_fragment0195513_field_003 fuel (fragment0195513Field004Chars00 ++ (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 474) (SourceJson.white (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail))))))) fragment0195513Acc00500 := object_fragment0195513_field_004 fuel (fragment0195513Field005Chars00 ++ (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 473) (SourceJson.white (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))))) fragment0195513Acc00600 := object_fragment0195513_field_005 fuel (fragment0195513Field006Chars00 ++ (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 472) (SourceJson.white (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail))))) fragment0195513Acc00700 := object_fragment0195513_field_006 fuel (fragment0195513Field007Chars00 ++ (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 471) (SourceJson.white (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))) fragment0195513Acc00800 := object_fragment0195513_field_007 fuel (fragment0195513Field008Chars00 ++ (fragment0195513Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 470) (SourceJson.white (fragment0195513Field009Chars00 ++ (tail))) fragment0195513Acc00900 := object_fragment0195513_field_008 fuel (fragment0195513Field009Chars00 ++ (tail))
    _ = .ok (fragment0195513Value, tail) := object_fragment0195513_field_009 fuel (tail)

noncomputable def fragment0197628Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0197628Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0197628Field000Value00 : SourceJson := .number (String.ofList ['3', '8'])
noncomputable def fragment0197628Acc00100 : List (String × SourceJson) := (fragment0197628Field000Key00, fragment0197628Field000Value00) :: fragment0197628Acc00000
noncomputable def fragment0197628Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '8', ',']

theorem object_fragment0197628_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 438) (SourceJson.white (fragment0197628Field000Chars00 ++ tail)) fragment0197628Acc00000 =
      SourceJson.object (fuel + 437) (SourceJson.white tail) fragment0197628Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_000"
  err.flush

noncomputable def fragment0197628Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0197628Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['4']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0197628Acc00200 : List (String × SourceJson) := (fragment0197628Field001Key00, fragment0197628Field001Value00) :: fragment0197628Acc00100
noncomputable def fragment0197628Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0197628_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 437) (SourceJson.white (fragment0197628Field001Chars00 ++ tail)) fragment0197628Acc00100 =
      SourceJson.object (fuel + 436) (SourceJson.white tail) fragment0197628Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_001"
  err.flush

noncomputable def fragment0197628Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0197628Field002Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '5', '0', '2', '3', '9', '3', '8', '6', '4', '9', '3', '9', '1', '8', '0', '3', '9', '8', '1', '8', '3', '6', '2', '4', '8', '9', '3', '6', '7', '8', '0', '1', '5', '1', '3', '/', '7', '4', '9', '1', '5', '4', '0', '3', '0', '4', '8', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0197628Acc00300 : List (String × SourceJson) := (fragment0197628Field002Key00, fragment0197628Field002Value00) :: fragment0197628Acc00200
noncomputable def fragment0197628Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '7', '5', '5', '0', '2', '3', '9', '3', '8', '6', '4', '9', '3', '9', '1', '8', '0', '3', '9', '8', '1', '8', '3', '6', '2', '4', '8', '9', '3', '6', '7', '8', '0', '1', '5', '1', '3', '/', '7', '4', '9', '1', '5', '4', '0', '3', '0', '4', '8', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0197628_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 436) (SourceJson.white (fragment0197628Field002Chars00 ++ tail)) fragment0197628Acc00200 =
      SourceJson.object (fuel + 435) (SourceJson.white tail) fragment0197628Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_002"
  err.flush

noncomputable def fragment0197628Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0197628Field003Value00 : SourceJson := .str (String.ofList ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0197628Acc00400 : List (String × SourceJson) := (fragment0197628Field003Key00, fragment0197628Field003Value00) :: fragment0197628Acc00300
noncomputable def fragment0197628Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '9', '1', '9', '6', '1', '3', '6', '0', '8', '7', '/', '4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0197628_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 435) (SourceJson.white (fragment0197628Field003Chars00 ++ tail)) fragment0197628Acc00300 =
      SourceJson.object (fuel + 434) (SourceJson.white tail) fragment0197628Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_003"
  err.flush

noncomputable def fragment0197628Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0197628Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0197628Acc00500 : List (String × SourceJson) := (fragment0197628Field004Key00, fragment0197628Field004Value00) :: fragment0197628Acc00400
noncomputable def fragment0197628Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '5', '7', '7', '9', '7', '7', '/', '1', '4', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0197628_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 434) (SourceJson.white (fragment0197628Field004Chars00 ++ tail)) fragment0197628Acc00400 =
      SourceJson.object (fuel + 433) (SourceJson.white tail) fragment0197628Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_004"
  err.flush

noncomputable def fragment0197628Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0197628Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '9', '5', '8', '5', '9', '7', '7', '0', '6', '0', '4', '1', '0', '7', '2', '4', '7', '2', '2', '5', '1', '4', '9', '/', '4', '4', '1', '1', '9', '7', '4', '1', '1', '4', '0', '2', '9', '8', '5', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '1', '5', '5', '0', '3', '2', '9', '1', '3', '9', '8', '7', '7', '4', '3', '1', '9', '3', '/', '2', '2', '9', '0', '2', '6', '8', '9', '5', '4', '5', '4', '2', '0', '7', '8', '1', '2', '5', '0', '0']), .str (String.ofList ['1', '9', '8', '6', '6', '1', '9', '8', '8', '4', '1', '2', '5', '5', '2', '3', '7', '0', '8', '0', '4', '3', '/', '1', '7', '0', '5', '1', '1', '0', '7', '6', '8', '7', '0', '7', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '9', '3', '9', '2', '4', '6', '3', '3', '5', '4', '8', '2', '2', '5', '7', '2', '9', '2', '7', '5', '1', '5', '3', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '4', '3', '3', '4', '5', '1', '0', '8', '4', '7', '3', '5', '5', '1', '2', '1', '0', '2', '1', '8', '7', '3', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '0', '0', '3', '1', '3', '8', '9', '6', '1', '8', '6', '9', '8', '3', '7', '0', '7', '9', '0', '9', '/', '1', '7', '8', '2', '6', '1', '5', '8', '0', '3', '6', '4', '8', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '0', '6', '8', '6', '5', '1', '8', '7', '0', '8', '1', '2', '9', '4', '3', '9', '1', '0', '4', '6', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '4', '4', '4', '7', '1', '3', '0', '1', '7', '2', '2', '1', '2', '4', '6', '1', '2', '2', '3', '7', '/', '4', '0', '1', '0', '8', '8', '5', '5', '5', '8', '2', '0', '8', '9', '6', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '2', '6', '4', '3', '3', '7', '4', '9', '9', '0', '0', '2', '6', '4', '7', '9', '0', '8', '5', '7', '/', '4', '0', '1', '0', '8', '8', '5', '5', '5', '8', '2', '0', '8', '9', '6', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '6', '8', '5', '6', '8', '4', '1', '6', '9', '6', '6', '6', '1', '8', '0', '2', '9', '3', '/', '1', '8', '3', '2', '2', '1', '5', '1', '6', '3', '6', '3', '3', '6', '6', '2', '5', '0', '0', '0', '0', '0'])]
noncomputable def fragment0197628Acc00600 : List (String × SourceJson) := (fragment0197628Field005Key00, fragment0197628Field005Value00) :: fragment0197628Acc00500
noncomputable def fragment0197628Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '8', '5', '9', '7', '7', '0', '6', '0', '4', '1', '0', '7', '2', '4', '7', '2', '2', '5', '1', '4', '9', '/', '4', '4', '1', '1', '9', '7', '4', '1', '1', '4', '0', '2', '9', '8', '5', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '1', '5', '5', '0', '3', '2', '9', '1', '3', '9', '8', '7', '7', '4', '3', '1', '9', '3', '/', '2', '2', '9', '0', '2', '6', '8', '9', '5', '4', '5', '4', '2', '0', '7', '8', '1', '2', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '8', '6', '6', '1', '9', '8', '8', '4', '1', '2', '5', '5', '2', '3', '7', '0', '8', '0', '4', '3', '/', '1', '7', '0', '5', '1', '1', '0', '7', '6', '8', '7', '0', '7', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '3', '9', '2', '4', '6', '3', '3', '5', '4', '8', '2', '2', '5', '7', '2', '9', '2', '7', '5', '1', '5', '3', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '4', '3', '3', '4', '5', '1', '0', '8', '4', '7', '3', '5', '5', '1', '2', '1', '0', '2', '1', '8', '7', '3', '/', '1', '7', '6', '4', '7', '8', '9', '6', '4', '5', '6', '1', '1', '9', '4', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '0', '0', '3', '1', '3', '8', '9', '6', '1', '8', '6', '9', '8', '3', '7', '0', '7', '9', '0', '9', '/', '1', '7', '8', '2', '6', '1', '5', '8', '0', '3', '6', '4', '8', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '0', '6', '8', '6', '5', '1', '8', '7', '0', '8', '1', '2', '9', '4', '3', '9', '1', '0', '4', '6', '9', '/', '8', '0', '2', '1', '7', '7', '1', '1', '1', '6', '4', '1', '7', '9', '2', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '9', '4', '4', '4', '7', '1', '3', '0', '1', '7', '2', '2', '1', '2', '4', '6', '1', '2', '2', '3', '7', '/', '4', '0', '1', '0', '8', '8', '5', '5', '5', '8', '2', '0', '8', '9', '6', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '7', '2', '6', '4', '3', '3', '7', '4', '9', '9', '0', '0', '2', '6', '4', '7', '9', '0', '8', '5', '7', '/', '4', '0', '1', '0', '8', '8', '5', '5', '5', '8', '2', '0', '8', '9', '6', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '6', '8', '5', '6', '8', '4', '1', '6', '9', '6', '6', '6', '1', '8', '0', '2', '9', '3', '/', '1', '8', '3', '2', '2', '1', '5', '1', '6', '3', '6', '3', '3', '6', '6', '2', '5', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0197628_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 433) (SourceJson.white (fragment0197628Field005Chars00 ++ tail)) fragment0197628Acc00500 =
      SourceJson.object (fuel + 432) (SourceJson.white tail) fragment0197628Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_005"
  err.flush

noncomputable def fragment0197628Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0197628Field006Value00 : SourceJson := .str (String.ofList ['5', '3', '5', '8', '2', '3', '6', '7', '8', '0', '5', '3', '0', '2', '1', '7', '5', '7', '6', '8', '1', '6', '5', '5', '1', '1', '4', '9', '2', '2', '6', '0', '1', '2', '3', '6', '4', '7', '9', '9', '1', '0', '5', '6', '9', '0', '0', '4', '4', '0', '0', '0', '/', '1', '6', '5', '2', '4', '4', '2', '7', '6', '9', '6', '1', '3', '7', '1', '7', '6', '9', '3', '6', '5', '3', '9', '4', '1', '9', '4', '8', '7', '9', '5', '8', '3', '2', '2', '3', '9', '6', '3', '9', '3', '1', '0', '8', '7', '4', '6', '9', '1', '2', '6', '4', '1', '7', '1', '3', '6', '7', '1', '6', '3', '8', '3', '9', '6', '3', '6', '1', '4', '3'])
noncomputable def fragment0197628Acc00700 : List (String × SourceJson) := (fragment0197628Field006Key00, fragment0197628Field006Value00) :: fragment0197628Acc00600
noncomputable def fragment0197628Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '3', '5', '8', '2', '3', '6', '7', '8', '0', '5', '3', '0', '2', '1', '7', '5', '7', '6', '8', '1', '6', '5', '5', '1', '1', '4', '9', '2', '2', '6', '0', '1', '2', '3', '6', '4', '7', '9', '9', '1', '0', '5', '6', '9', '0', '0', '4', '4', '0', '0', '0', '/', '1', '6', '5', '2', '4', '4', '2', '7', '6', '9', '6', '1', '3', '7', '1', '7', '6', '9', '3', '6', '5', '3', '9', '4', '1', '9', '4', '8', '7', '9', '5', '8', '3', '2', '2', '3', '9', '6', '3', '9', '3', '1', '0', '8', '7', '4', '6', '9', '1', '2', '6', '4', '1', '7', '1', '3', '6', '7', '1', '6', '3', '8', '3', '9', '6', '3', '6', '1', '4', '3', '"', ',']

theorem object_fragment0197628_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 432) (SourceJson.white (fragment0197628Field006Chars00 ++ tail)) fragment0197628Acc00600 =
      SourceJson.object (fuel + 431) (SourceJson.white tail) fragment0197628Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_006"
  err.flush

noncomputable def fragment0197628Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0197628Field007Value00 : SourceJson := .str (String.ofList ['1', '5', '3', '1', '9', '8', '5', '4', '2', '9', '2', '6', '7', '9', '9', '2', '0', '7', '3', '7', '2', '9', '1', '5', '5', '6', '7', '5', '8', '3', '2', '3', '9', '2', '1', '1', '9', '9', '8', '9', '2', '8', '8', '8', '1', '8', '1', '9', '7', '7', '1', '1', '3', '4', '4', '3', '7', '2', '1', '6', '0', '6', '5', '3', '6', '0', '9', '2', '3', '6', '5', '4', '8', '9', '0', '6', '8', '4', '6', '5', '6', '2', '0', '7', '0', '4', '7', '3', '0', '0', '5', '9', '0', '1', '9', '4', '1', '3', '2', '8', '9', '8', '9', '8', '3', '5', '6', '6', '8', '7', '3', '2', '5', '6', '9', '0', '9', '2', '4', '9', '4', '8', '5', '3', '9', '3', '1', '2', '2', '6', '8', '7', '0', '7', '3', '3', '6', '3', '4', '0', '0', '9', '1', '1', '7', '6', '7', '1', '8', '3', '7', '7', '2', '5', '5', '2', '2', '3', '7', '3', '3', '1', '0', '1', '5', '6', '7', '2', '8', '5', '5', '6', '1', '2', '8', '5', '8', '9', '1', '0', '1', '6', '3', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '9', '2', '7', '3', '0', '1', '4', '5', '8', '9', '5', '5', '7', '1', '2', '5', '3', '7', '1', '1', '7', '3', '2', '3', '4', '2', '8', '6', '0', '3', '7', '1', '9', '3', '7', '8', '9', '4', '9', '5', '8', '0', '2', '2', '2', '2', '3', '0', '5', '2', '8', '7', '8', '5', '0', '6', '0', '2', '0', '8', '8', '3', '9', '9', '6', '2', '5', '6', '9', '9', '9', '5', '2', '7', '1', '6', '0', '4', '0', '8', '8', '5', '2', '5', '4', '7', '2', '9', '3', '3', '5', '9', '4', '5', '0', '0', '3', '4', '4', '1', '0', '1', '2', '1', '3', '1', '9', '9', '7', '4', '5', '4', '8', '1', '2', '8', '1', '4', '3', '3', '7', '2', '1', '6', '4', '6', '5', '1', '1', '1', '4', '0', '4', '7', '2', '8', '4', '9', '3', '8', '4', '1', '0', '1', '9', '2', '1', '1', '3', '7', '9', '6', '6', '9', '9', '9', '3', '5', '6', '1', '2', '3', '9', '1', '5', '1', '0', '4', '4', '8', '2', '3', '5', '3', '8', '3', '5', '4', '7', '8', '7', '4', '6', '4', '1', '7', '3', '1', '9', '7', '9', '0', '4', '8', '9', '6', '6', '2', '5', '4', '5', '3', '8', '8', '0', '3', '0', '0', '7', '8', '8', '7', '0', '6', '0', '2', '0', '2', '6', '3'])
noncomputable def fragment0197628Acc00800 : List (String × SourceJson) := (fragment0197628Field007Key00, fragment0197628Field007Value00) :: fragment0197628Acc00700
noncomputable def fragment0197628Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '3', '1', '9', '8', '5', '4', '2', '9', '2', '6', '7', '9', '9', '2', '0', '7', '3', '7', '2', '9', '1', '5', '5', '6', '7', '5', '8', '3', '2', '3', '9', '2', '1', '1', '9', '9', '8', '9', '2', '8', '8', '8', '1', '8', '1', '9', '7', '7', '1', '1', '3', '4', '4', '3', '7', '2', '1', '6', '0', '6', '5', '3', '6', '0', '9', '2', '3', '6', '5', '4', '8', '9', '0', '6', '8', '4', '6', '5', '6', '2', '0', '7', '0', '4', '7', '3', '0', '0', '5', '9', '0', '1', '9', '4', '1', '3', '2', '8', '9', '8', '9', '8', '3', '5', '6', '6', '8', '7', '3', '2', '5', '6', '9', '0', '9', '2', '4', '9', '4', '8', '5', '3', '9', '3', '1', '2', '2', '6', '8', '7', '0', '7', '3', '3', '6', '3', '4', '0', '0', '9', '1', '1', '7', '6', '7', '1', '8', '3', '7', '7', '2', '5', '5', '2', '2', '3', '7', '3', '3', '1', '0', '1', '5', '6', '7', '2', '8', '5', '5', '6', '1', '2', '8', '5', '8', '9', '1', '0', '1', '6', '3', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '9', '2', '7', '3', '0', '1', '4', '5', '8', '9', '5', '5', '7', '1', '2', '5', '3', '7', '1', '1', '7', '3', '2', '3', '4', '2', '8', '6', '0', '3', '7', '1', '9', '3', '7', '8', '9', '4', '9', '5', '8', '0', '2', '2', '2', '2', '3', '0', '5', '2', '8', '7', '8', '5', '0', '6', '0', '2', '0', '8', '8', '3', '9', '9', '6', '2', '5', '6', '9', '9', '9', '5', '2', '7', '1', '6', '0', '4', '0', '8', '8', '5', '2', '5', '4', '7', '2', '9', '3', '3', '5', '9', '4', '5', '0', '0', '3', '4', '4', '1', '0', '1', '2', '1', '3', '1', '9', '9', '7', '4', '5', '4', '8', '1', '2', '8', '1', '4', '3', '3', '7', '2', '1', '6', '4', '6', '5', '1', '1', '1', '4', '0', '4', '7', '2', '8', '4', '9', '3', '8', '4', '1', '0', '1', '9', '2', '1', '1', '3', '7', '9', '6', '6', '9', '9', '9', '3', '5', '6', '1', '2', '3', '9', '1', '5', '1', '0', '4', '4', '8', '2', '3', '5', '3', '8', '3', '5', '4', '7', '8', '7', '4', '6', '4', '1', '7', '3', '1', '9', '7', '9', '0', '4', '8', '9', '6', '6', '2', '5', '4', '5', '3', '8', '8', '0', '3', '0', '0', '7', '8', '8', '7', '0', '6', '0', '2', '0', '2', '6', '3', '"', ',']

theorem object_fragment0197628_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 431) (SourceJson.white (fragment0197628Field007Chars00 ++ tail)) fragment0197628Acc00700 =
      SourceJson.object (fuel + 430) (SourceJson.white tail) fragment0197628Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_007"
  err.flush

noncomputable def fragment0197628Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0197628Field008Value00 : SourceJson := .str (String.ofList ['2', '5', '6', '9', '0', '6', '4', '7', '9', '4', '5', '2'])
noncomputable def fragment0197628Acc00900 : List (String × SourceJson) := (fragment0197628Field008Key00, fragment0197628Field008Value00) :: fragment0197628Acc00800
noncomputable def fragment0197628Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '5', '6', '9', '0', '6', '4', '7', '9', '4', '5', '2', '"', ',']

theorem object_fragment0197628_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 430) (SourceJson.white (fragment0197628Field008Chars00 ++ tail)) fragment0197628Acc00800 =
      SourceJson.object (fuel + 429) (SourceJson.white tail) fragment0197628Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_008"
  err.flush

noncomputable def fragment0197628Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0197628Field009Value00 : SourceJson := .str (String.ofList ['7', '1', '7', '0', '4', '5', '1', '2', '8', '8', '6', '3'])
noncomputable def fragment0197628Acc01000 : List (String × SourceJson) := (fragment0197628Field009Key00, fragment0197628Field009Value00) :: fragment0197628Acc00900
noncomputable def fragment0197628Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '1', '7', '0', '4', '5', '1', '2', '8', '8', '6', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0197628_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 429) (SourceJson.white (fragment0197628Field009Chars00 ++ tail)) fragment0197628Acc00900 =
      .ok (.obj (fragment0197628Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0197628_object_field_009"
  err.flush

noncomputable def fragment0197628Chars : List Char := '{' :: (fragment0197628Field000Chars00 ++ fragment0197628Field001Chars00 ++ fragment0197628Field002Chars00 ++ fragment0197628Field003Chars00 ++ fragment0197628Field004Chars00 ++ fragment0197628Field005Chars00 ++ fragment0197628Field006Chars00 ++ fragment0197628Field007Chars00 ++ fragment0197628Field008Chars00 ++ fragment0197628Field009Chars00)
noncomputable def fragment0197628Value : SourceJson := .obj (fragment0197628Acc01000.reverse)

theorem value_fragment0197628 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 439) (fragment0197628Chars ++ tail) =
      .ok (fragment0197628Value, tail) := by
  have hinput : fragment0197628Chars ++ tail = '{' :: (fragment0197628Field000Chars00 ++ (fragment0197628Field001Chars00 ++ (fragment0197628Field002Chars00 ++ (fragment0197628Field003Chars00 ++ (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0197628Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 439) (fragment0197628Chars ++ tail) =
        SourceJson.value (fuel + 439) ('{' :: (fragment0197628Field000Chars00 ++ (fragment0197628Field001Chars00 ++ (fragment0197628Field002Chars00 ++ (fragment0197628Field003Chars00 ++ (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 439)) hinput
    _ = SourceJson.object (fuel + 438) (SourceJson.white (fragment0197628Field000Chars00 ++ (fragment0197628Field001Chars00 ++ (fragment0197628Field002Chars00 ++ (fragment0197628Field003Chars00 ++ (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))))))))))) fragment0197628Acc00000 := by rfl
    _ = SourceJson.object (fuel + 437) (SourceJson.white (fragment0197628Field001Chars00 ++ (fragment0197628Field002Chars00 ++ (fragment0197628Field003Chars00 ++ (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail))))))))))) fragment0197628Acc00100 := object_fragment0197628_field_000 fuel (fragment0197628Field001Chars00 ++ (fragment0197628Field002Chars00 ++ (fragment0197628Field003Chars00 ++ (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 436) (SourceJson.white (fragment0197628Field002Chars00 ++ (fragment0197628Field003Chars00 ++ (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))))))))) fragment0197628Acc00200 := object_fragment0197628_field_001 fuel (fragment0197628Field002Chars00 ++ (fragment0197628Field003Chars00 ++ (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 435) (SourceJson.white (fragment0197628Field003Chars00 ++ (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail))))))))) fragment0197628Acc00300 := object_fragment0197628_field_002 fuel (fragment0197628Field003Chars00 ++ (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 434) (SourceJson.white (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))))))) fragment0197628Acc00400 := object_fragment0197628_field_003 fuel (fragment0197628Field004Chars00 ++ (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 433) (SourceJson.white (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail))))))) fragment0197628Acc00500 := object_fragment0197628_field_004 fuel (fragment0197628Field005Chars00 ++ (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 432) (SourceJson.white (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))))) fragment0197628Acc00600 := object_fragment0197628_field_005 fuel (fragment0197628Field006Chars00 ++ (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 431) (SourceJson.white (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail))))) fragment0197628Acc00700 := object_fragment0197628_field_006 fuel (fragment0197628Field007Chars00 ++ (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 430) (SourceJson.white (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))) fragment0197628Acc00800 := object_fragment0197628_field_007 fuel (fragment0197628Field008Chars00 ++ (fragment0197628Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 429) (SourceJson.white (fragment0197628Field009Chars00 ++ (tail))) fragment0197628Acc00900 := object_fragment0197628_field_008 fuel (fragment0197628Field009Chars00 ++ (tail))
    _ = .ok (fragment0197628Value, tail) := object_fragment0197628_field_009 fuel (tail)

noncomputable def fragment0199644Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0199644Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0199644Field000Value00 : SourceJson := .number (String.ofList ['3', '9'])
noncomputable def fragment0199644Acc00100 : List (String × SourceJson) := (fragment0199644Field000Key00, fragment0199644Field000Value00) :: fragment0199644Acc00000
noncomputable def fragment0199644Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '3', '9', ',']

theorem object_fragment0199644_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 377) (SourceJson.white (fragment0199644Field000Chars00 ++ tail)) fragment0199644Acc00000 =
      SourceJson.object (fuel + 376) (SourceJson.white tail) fragment0199644Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_000"
  err.flush

noncomputable def fragment0199644Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0199644Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '2']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0199644Acc00200 : List (String × SourceJson) := (fragment0199644Field001Key00, fragment0199644Field001Value00) :: fragment0199644Acc00100
noncomputable def fragment0199644Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0199644_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 376) (SourceJson.white (fragment0199644Field001Chars00 ++ tail)) fragment0199644Acc00100 =
      SourceJson.object (fuel + 375) (SourceJson.white tail) fragment0199644Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_001"
  err.flush

noncomputable def fragment0199644Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0199644Field002Value00 : SourceJson := .str (String.ofList ['9', '5', '8', '5', '8', '7', '8', '8', '4', '7', '7', '1', '2', '3', '2', '3', '8', '0', '5', '8', '6', '0', '0', '4', '7', '2', '6', '1', '5', '9', '0', '8', '7', '9', '0', '0', '7', '9', '/', '1', '0', '4', '5', '3', '3', '1', '2', '0', '5', '3', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0199644Acc00300 : List (String × SourceJson) := (fragment0199644Field002Key00, fragment0199644Field002Value00) :: fragment0199644Acc00200
noncomputable def fragment0199644Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '5', '8', '5', '8', '7', '8', '8', '4', '7', '7', '1', '2', '3', '2', '3', '8', '0', '5', '8', '6', '0', '0', '4', '7', '2', '6', '1', '5', '9', '0', '8', '7', '9', '0', '0', '7', '9', '/', '1', '0', '4', '5', '3', '3', '1', '2', '0', '5', '3', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0199644_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 375) (SourceJson.white (fragment0199644Field002Chars00 ++ tail)) fragment0199644Acc00200 =
      SourceJson.object (fuel + 374) (SourceJson.white tail) fragment0199644Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_002"
  err.flush

noncomputable def fragment0199644Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0199644Field003Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0199644Acc00400 : List (String × SourceJson) := (fragment0199644Field003Key00, fragment0199644Field003Value00) :: fragment0199644Acc00300
noncomputable def fragment0199644Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '7', '2', '2', '9', '/', '9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0199644_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 374) (SourceJson.white (fragment0199644Field003Chars00 ++ tail)) fragment0199644Acc00300 =
      SourceJson.object (fuel + 373) (SourceJson.white tail) fragment0199644Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_003"
  err.flush

noncomputable def fragment0199644Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0199644Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0199644Acc00500 : List (String × SourceJson) := (fragment0199644Field004Key00, fragment0199644Field004Value00) :: fragment0199644Acc00400
noncomputable def fragment0199644Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '0', '2', '7', '6', '1', '/', '2', '7', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '5', '6', '2', '1', '/', '3', '3', '6', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '8', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '5', '6', '1', '9', '/', '2', '0', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0199644_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 373) (SourceJson.white (fragment0199644Field004Chars00 ++ tail)) fragment0199644Acc00400 =
      SourceJson.object (fuel + 372) (SourceJson.white tail) fragment0199644Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_004"
  err.flush

noncomputable def fragment0199644Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0199644Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '4', '4', '5', '2', '8', '3', '9', '6', '8', '7', '9', '3', '0', '3', '5', '8', '2', '6', '6', '1', '/', '1', '5', '9', '9', '5', '9', '1', '1', '8', '4', '1', '2', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '7', '8', '4', '7', '8', '7', '1', '1', '1', '3', '3', '9', '1', '3', '0', '3', '/', '2', '8', '5', '6', '4', '1', '2', '8', '2', '8', '7', '8', '8', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '6', '8', '5', '3', '9', '2', '4', '1', '6', '3', '6', '4', '8', '6', '2', '0', '3', '/', '1', '8', '5', '4', '5', '9', '8', '4', '7', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '2', '2', '8', '5', '2', '6', '8', '9', '2', '6', '2', '0', '3', '7', '2', '6', '9', '0', '7', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '8', '8', '0', '8', '3', '0', '4', '7', '9', '8', '4', '7', '3', '0', '8', '2', '5', '8', '7', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '2', '5', '2', '5', '4', '4', '1', '7', '4', '3', '6', '6', '7', '1', '5', '9', '3', '/', '1', '9', '3', '8', '8', '9', '8', '4', '0', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '5', '0', '8', '5', '2', '7', '3', '2', '8', '0', '5', '5', '0', '0', '2', '1', '9', '/', '7', '2', '7', '0', '8', '6', '9', '0', '1', '8', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '8', '1', '0', '9', '6', '0', '8', '9', '2', '3', '9', '5', '0', '2', '2', '9', '3', '/', '1', '4', '5', '4', '1', '7', '3', '8', '0', '3', '7', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '0', '2', '0', '4', '5', '0', '9', '3', '7', '6', '9', '5', '4', '9', '0', '7', '3', '/', '1', '4', '5', '4', '1', '7', '3', '8', '0', '3', '7', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '4', '7', '7', '9', '2', '8', '2', '8', '0', '3', '8', '2', '5', '4', '7', '9', '/', '7', '1', '4', '1', '0', '3', '2', '0', '7', '1', '9', '7', '1', '8', '7', '5', '0', '0', '0'])]
noncomputable def fragment0199644Acc00600 : List (String × SourceJson) := (fragment0199644Field005Key00, fragment0199644Field005Value00) :: fragment0199644Acc00500
noncomputable def fragment0199644Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '4', '5', '2', '8', '3', '9', '6', '8', '7', '9', '3', '0', '3', '5', '8', '2', '6', '6', '1', '/', '1', '5', '9', '9', '5', '9', '1', '1', '8', '4', '1', '2', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '7', '8', '4', '7', '8', '7', '1', '1', '1', '3', '3', '9', '1', '3', '0', '3', '/', '2', '8', '5', '6', '4', '1', '2', '8', '2', '8', '7', '8', '8', '7', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '6', '8', '5', '3', '9', '2', '4', '1', '6', '3', '6', '4', '8', '6', '2', '0', '3', '/', '1', '8', '5', '4', '5', '9', '8', '4', '7', '4', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '2', '2', '8', '5', '2', '6', '8', '9', '2', '6', '2', '0', '3', '7', '2', '6', '9', '0', '7', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '8', '8', '0', '8', '3', '0', '4', '7', '9', '8', '4', '7', '3', '0', '8', '2', '5', '8', '7', '/', '6', '3', '9', '8', '3', '6', '4', '7', '3', '6', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '2', '5', '2', '5', '4', '4', '1', '7', '4', '3', '6', '6', '7', '1', '5', '9', '3', '/', '1', '9', '3', '8', '8', '9', '8', '4', '0', '4', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '5', '0', '8', '5', '2', '7', '3', '2', '8', '0', '5', '5', '0', '0', '2', '1', '9', '/', '7', '2', '7', '0', '8', '6', '9', '0', '1', '8', '7', '3', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '8', '1', '0', '9', '6', '0', '8', '9', '2', '3', '9', '5', '0', '2', '2', '9', '3', '/', '1', '4', '5', '4', '1', '7', '3', '8', '0', '3', '7', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '0', '2', '0', '4', '5', '0', '9', '3', '7', '6', '9', '5', '4', '9', '0', '7', '3', '/', '1', '4', '5', '4', '1', '7', '3', '8', '0', '3', '7', '4', '7', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '2', '4', '7', '7', '9', '2', '8', '2', '8', '0', '3', '8', '2', '5', '4', '7', '9', '/', '7', '1', '4', '1', '0', '3', '2', '0', '7', '1', '9', '7', '1', '8', '7', '5', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0199644_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 372) (SourceJson.white (fragment0199644Field005Chars00 ++ tail)) fragment0199644Acc00500 =
      SourceJson.object (fuel + 371) (SourceJson.white tail) fragment0199644Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_005"
  err.flush

noncomputable def fragment0199644Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0199644Field006Value00 : SourceJson := .str (String.ofList ['3', '4', '3', '4', '5', '8', '5', '5', '8', '0', '6', '9', '1', '6', '9', '5', '8', '7', '7', '5', '9', '9', '0', '1', '6', '1', '5', '6', '7', '0', '5', '0', '7', '7', '5', '1', '0', '7', '2', '0', '3', '8', '2', '3', '1', '6', '8', '0', '/', '1', '8', '0', '2', '5', '1', '9', '0', '9', '7', '0', '2', '3', '6', '0', '9', '0', '0', '3', '6', '6', '8', '8', '6', '3', '1', '6', '4', '7', '5', '0', '5', '1', '5', '6', '2', '2', '6', '1', '4', '4', '2', '7', '1', '5', '4', '0', '6', '5', '7', '3', '7', '9', '8', '9', '3', '6', '5', '1', '3', '5', '9', '7', '3', '3'])
noncomputable def fragment0199644Acc00700 : List (String × SourceJson) := (fragment0199644Field006Key00, fragment0199644Field006Value00) :: fragment0199644Acc00600
noncomputable def fragment0199644Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '3', '4', '5', '8', '5', '5', '8', '0', '6', '9', '1', '6', '9', '5', '8', '7', '7', '5', '9', '9', '0', '1', '6', '1', '5', '6', '7', '0', '5', '0', '7', '7', '5', '1', '0', '7', '2', '0', '3', '8', '2', '3', '1', '6', '8', '0', '/', '1', '8', '0', '2', '5', '1', '9', '0', '9', '7', '0', '2', '3', '6', '0', '9', '0', '0', '3', '6', '6', '8', '8', '6', '3', '1', '6', '4', '7', '5', '0', '5', '1', '5', '6', '2', '2', '6', '1', '4', '4', '2', '7', '1', '5', '4', '0', '6', '5', '7', '3', '7', '9', '8', '9', '3', '6', '5', '1', '3', '5', '9', '7', '3', '3', '"', ',']

theorem object_fragment0199644_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 371) (SourceJson.white (fragment0199644Field006Chars00 ++ tail)) fragment0199644Acc00600 =
      SourceJson.object (fuel + 370) (SourceJson.white tail) fragment0199644Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_006"
  err.flush

noncomputable def fragment0199644Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0199644Field007Value00 : SourceJson := .str (String.ofList ['4', '0', '0', '2', '9', '4', '3', '7', '3', '8', '1', '7', '0', '1', '8', '6', '3', '2', '4', '3', '0', '1', '6', '7', '5', '6', '5', '4', '4', '3', '1', '0', '5', '7', '6', '5', '3', '2', '9', '3', '6', '3', '5', '1', '3', '6', '3', '4', '3', '7', '1', '3', '5', '1', '0', '0', '7', '2', '5', '4', '3', '2', '1', '6', '0', '3', '7', '0', '0', '6', '6', '3', '1', '1', '5', '0', '6', '6', '8', '5', '3', '9', '1', '8', '0', '9', '0', '3', '9', '2', '5', '9', '4', '4', '2', '5', '2', '9', '7', '5', '2', '8', '3', '7', '2', '7', '9', '6', '7', '9', '6', '5', '3', '3', '0', '5', '7', '4', '7', '7', '9', '6', '4', '4', '9', '5', '9', '8', '2', '6', '6', '3', '2', '2', '2', '9', '5', '3', '5', '2', '7', '1', '8', '3', '4', '3', '6', '8', '3', '8', '5', '9', '9', '2', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '0', '9', '1', '2', '5', '5', '3', '7', '7', '1', '8', '5', '3', '2', '6', '3', '9', '1', '6', '4', '4', '1', '5', '3', '7', '9', '6', '9', '3', '0', '1', '9', '9', '4', '2', '4', '8', '8', '4', '2', '7', '7', '6', '7', '4', '8', '2', '8', '4', '9', '9', '1', '6', '8', '3', '8', '4', '4', '0', '6', '1', '1', '2', '8', '8', '7', '3', '8', '0', '7', '8', '4', '3', '1', '8', '3', '9', '8', '0', '7', '6', '4', '1', '8', '1', '4', '9', '0', '3', '3', '4', '4', '5', '5', '9', '4', '3', '2', '8', '6', '1', '6', '0', '5', '4', '9', '7', '4', '5', '0', '8', '4', '1', '9', '0', '2', '5', '7', '3', '7', '4', '3', '5', '3', '8', '7', '6', '3', '7', '7', '7', '1', '8', '6', '6', '2', '9', '6', '0', '2', '1', '3', '7', '7', '4', '9', '5', '9', '3', '3', '0', '3', '7', '2', '8', '5', '7', '5', '0', '7', '6', '7', '6', '9', '0', '3', '1', '4', '7', '7', '2', '0', '3', '3', '5', '8', '8', '6', '2', '8', '8', '2', '5', '9', '7', '2', '2', '5', '7'])
noncomputable def fragment0199644Acc00800 : List (String × SourceJson) := (fragment0199644Field007Key00, fragment0199644Field007Value00) :: fragment0199644Acc00700
noncomputable def fragment0199644Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '0', '0', '2', '9', '4', '3', '7', '3', '8', '1', '7', '0', '1', '8', '6', '3', '2', '4', '3', '0', '1', '6', '7', '5', '6', '5', '4', '4', '3', '1', '0', '5', '7', '6', '5', '3', '2', '9', '3', '6', '3', '5', '1', '3', '6', '3', '4', '3', '7', '1', '3', '5', '1', '0', '0', '7', '2', '5', '4', '3', '2', '1', '6', '0', '3', '7', '0', '0', '6', '6', '3', '1', '1', '5', '0', '6', '6', '8', '5', '3', '9', '1', '8', '0', '9', '0', '3', '9', '2', '5', '9', '4', '4', '2', '5', '2', '9', '7', '5', '2', '8', '3', '7', '2', '7', '9', '6', '7', '9', '6', '5', '3', '3', '0', '5', '7', '4', '7', '7', '9', '6', '4', '4', '9', '5', '9', '8', '2', '6', '6', '3', '2', '2', '2', '9', '5', '3', '5', '2', '7', '1', '8', '3', '4', '3', '6', '8', '3', '8', '5', '9', '9', '2', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '6', '0', '9', '1', '2', '5', '5', '3', '7', '7', '1', '8', '5', '3', '2', '6', '3', '9', '1', '6', '4', '4', '1', '5', '3', '7', '9', '6', '9', '3', '0', '1', '9', '9', '4', '2', '4', '8', '8', '4', '2', '7', '7', '6', '7', '4', '8', '2', '8', '4', '9', '9', '1', '6', '8', '3', '8', '4', '4', '0', '6', '1', '1', '2', '8', '8', '7', '3', '8', '0', '7', '8', '4', '3', '1', '8', '3', '9', '8', '0', '7', '6', '4', '1', '8', '1', '4', '9', '0', '3', '3', '4', '4', '5', '5', '9', '4', '3', '2', '8', '6', '1', '6', '0', '5', '4', '9', '7', '4', '5', '0', '8', '4', '1', '9', '0', '2', '5', '7', '3', '7', '4', '3', '5', '3', '8', '7', '6', '3', '7', '7', '7', '1', '8', '6', '6', '2', '9', '6', '0', '2', '1', '3', '7', '7', '4', '9', '5', '9', '3', '3', '0', '3', '7', '2', '8', '5', '7', '5', '0', '7', '6', '7', '6', '9', '0', '3', '1', '4', '7', '7', '2', '0', '3', '3', '5', '8', '8', '6', '2', '8', '8', '2', '5', '9', '7', '2', '2', '5', '7', '"', ',']

theorem object_fragment0199644_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 370) (SourceJson.white (fragment0199644Field007Chars00 ++ tail)) fragment0199644Acc00700 =
      SourceJson.object (fuel + 369) (SourceJson.white tail) fragment0199644Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_007"
  err.flush

noncomputable def fragment0199644Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0199644Field008Value00 : SourceJson := .str (String.ofList ['1', '5', '0', '9', '6', '4', '2', '2', '8', '3', '4', '3', '2'])
noncomputable def fragment0199644Acc00900 : List (String × SourceJson) := (fragment0199644Field008Key00, fragment0199644Field008Value00) :: fragment0199644Acc00800
noncomputable def fragment0199644Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '0', '9', '6', '4', '2', '2', '8', '3', '4', '3', '2', '"', ',']

theorem object_fragment0199644_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 369) (SourceJson.white (fragment0199644Field008Chars00 ++ tail)) fragment0199644Acc00800 =
      SourceJson.object (fuel + 368) (SourceJson.white tail) fragment0199644Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_008"
  err.flush

noncomputable def fragment0199644Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0199644Field009Value00 : SourceJson := .str (String.ofList ['5', '6', '5', '4', '1', '0', '5', '5', '2', '6', '6', '2', '0'])
noncomputable def fragment0199644Acc01000 : List (String × SourceJson) := (fragment0199644Field009Key00, fragment0199644Field009Value00) :: fragment0199644Acc00900
noncomputable def fragment0199644Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '5', '4', '1', '0', '5', '5', '2', '6', '6', '2', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0199644_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 368) (SourceJson.white (fragment0199644Field009Chars00 ++ tail)) fragment0199644Acc00900 =
      .ok (.obj (fragment0199644Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0199644_object_field_009"
  err.flush

noncomputable def fragment0199644Chars : List Char := '{' :: (fragment0199644Field000Chars00 ++ fragment0199644Field001Chars00 ++ fragment0199644Field002Chars00 ++ fragment0199644Field003Chars00 ++ fragment0199644Field004Chars00 ++ fragment0199644Field005Chars00 ++ fragment0199644Field006Chars00 ++ fragment0199644Field007Chars00 ++ fragment0199644Field008Chars00 ++ fragment0199644Field009Chars00)
noncomputable def fragment0199644Value : SourceJson := .obj (fragment0199644Acc01000.reverse)

theorem value_fragment0199644 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 378) (fragment0199644Chars ++ tail) =
      .ok (fragment0199644Value, tail) := by
  have hinput : fragment0199644Chars ++ tail = '{' :: (fragment0199644Field000Chars00 ++ (fragment0199644Field001Chars00 ++ (fragment0199644Field002Chars00 ++ (fragment0199644Field003Chars00 ++ (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0199644Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 378) (fragment0199644Chars ++ tail) =
        SourceJson.value (fuel + 378) ('{' :: (fragment0199644Field000Chars00 ++ (fragment0199644Field001Chars00 ++ (fragment0199644Field002Chars00 ++ (fragment0199644Field003Chars00 ++ (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 378)) hinput
    _ = SourceJson.object (fuel + 377) (SourceJson.white (fragment0199644Field000Chars00 ++ (fragment0199644Field001Chars00 ++ (fragment0199644Field002Chars00 ++ (fragment0199644Field003Chars00 ++ (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))))))))))) fragment0199644Acc00000 := by rfl
    _ = SourceJson.object (fuel + 376) (SourceJson.white (fragment0199644Field001Chars00 ++ (fragment0199644Field002Chars00 ++ (fragment0199644Field003Chars00 ++ (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail))))))))))) fragment0199644Acc00100 := object_fragment0199644_field_000 fuel (fragment0199644Field001Chars00 ++ (fragment0199644Field002Chars00 ++ (fragment0199644Field003Chars00 ++ (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 375) (SourceJson.white (fragment0199644Field002Chars00 ++ (fragment0199644Field003Chars00 ++ (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))))))))) fragment0199644Acc00200 := object_fragment0199644_field_001 fuel (fragment0199644Field002Chars00 ++ (fragment0199644Field003Chars00 ++ (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 374) (SourceJson.white (fragment0199644Field003Chars00 ++ (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail))))))))) fragment0199644Acc00300 := object_fragment0199644_field_002 fuel (fragment0199644Field003Chars00 ++ (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 373) (SourceJson.white (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))))))) fragment0199644Acc00400 := object_fragment0199644_field_003 fuel (fragment0199644Field004Chars00 ++ (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 372) (SourceJson.white (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail))))))) fragment0199644Acc00500 := object_fragment0199644_field_004 fuel (fragment0199644Field005Chars00 ++ (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 371) (SourceJson.white (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))))) fragment0199644Acc00600 := object_fragment0199644_field_005 fuel (fragment0199644Field006Chars00 ++ (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 370) (SourceJson.white (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail))))) fragment0199644Acc00700 := object_fragment0199644_field_006 fuel (fragment0199644Field007Chars00 ++ (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 369) (SourceJson.white (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))) fragment0199644Acc00800 := object_fragment0199644_field_007 fuel (fragment0199644Field008Chars00 ++ (fragment0199644Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 368) (SourceJson.white (fragment0199644Field009Chars00 ++ (tail))) fragment0199644Acc00900 := object_fragment0199644_field_008 fuel (fragment0199644Field009Chars00 ++ (tail))
    _ = .ok (fragment0199644Value, tail) := object_fragment0199644_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_before_reader"
  err.flush

noncomputable def chunk0032LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0032SuffixChars00 : List Char := [',']
noncomputable def chunk0032Chars00 : List Char := chunk0032LeadChars00 ++ fragment0185897Chars ++ chunk0032SuffixChars00
noncomputable def chunk0032Push00 (acc : List SourceJson) : List SourceJson := fragment0185897Value :: acc

noncomputable def chunk0032AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0032_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 625)
      (SourceJson.white (chunk0032LeadChars00 ++ (fragment0185897Chars ++ rest))) acc =
      (SourceJson.value (fuel + 624) (fragment0185897Chars ++ rest)).bind
        (chunk0032AfterValue00 (fuel + 624) acc) := by rfl

theorem array_chunk0032 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 625) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 624) (SourceJson.white tail) (chunk0032Push00 acc) := by
  have hinput : chunk0032Chars00 ++ tail = chunk0032LeadChars00 ++ (fragment0185897Chars ++ (chunk0032SuffixChars00 ++ tail)) := by
    simp only [chunk0032Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 625) (SourceJson.white (chunk0032Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 625)
          (SourceJson.white (chunk0032LeadChars00 ++ (fragment0185897Chars ++ (chunk0032SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 625) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 624) (fragment0185897Chars ++ (chunk0032SuffixChars00 ++ tail))).bind
        (chunk0032AfterValue00 (fuel + 624) acc) := array_chunk0032_head fuel (chunk0032SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0185897Value, chunk0032SuffixChars00 ++ tail)).bind
        (chunk0032AfterValue00 (fuel + 624) acc) :=
      congrArg (fun result => result.bind (chunk0032AfterValue00 (fuel + 624) acc))
        (value_fragment0185897 (fuel + 139) (chunk0032SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 624) (SourceJson.white tail) (chunk0032Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0032_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_before_reader"
  err.flush

noncomputable def chunk0033LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0033SuffixChars00 : List Char := [',']
noncomputable def chunk0033Chars00 : List Char := chunk0033LeadChars00 ++ fragment0188025Chars ++ chunk0033SuffixChars00
noncomputable def chunk0033Push00 (acc : List SourceJson) : List SourceJson := fragment0188025Value :: acc

noncomputable def chunk0033AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0033_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 624)
      (SourceJson.white (chunk0033LeadChars00 ++ (fragment0188025Chars ++ rest))) acc =
      (SourceJson.value (fuel + 623) (fragment0188025Chars ++ rest)).bind
        (chunk0033AfterValue00 (fuel + 623) acc) := by rfl

theorem array_chunk0033 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 624) (SourceJson.white (chunk0033Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 623) (SourceJson.white tail) (chunk0033Push00 acc) := by
  have hinput : chunk0033Chars00 ++ tail = chunk0033LeadChars00 ++ (fragment0188025Chars ++ (chunk0033SuffixChars00 ++ tail)) := by
    simp only [chunk0033Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 624) (SourceJson.white (chunk0033Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 624)
          (SourceJson.white (chunk0033LeadChars00 ++ (fragment0188025Chars ++ (chunk0033SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 624) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 623) (fragment0188025Chars ++ (chunk0033SuffixChars00 ++ tail))).bind
        (chunk0033AfterValue00 (fuel + 623) acc) := array_chunk0033_head fuel (chunk0033SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0188025Value, chunk0033SuffixChars00 ++ tail)).bind
        (chunk0033AfterValue00 (fuel + 623) acc) :=
      congrArg (fun result => result.bind (chunk0033AfterValue00 (fuel + 623) acc))
        (value_fragment0188025 (fuel + 198) (chunk0033SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 623) (SourceJson.white tail) (chunk0033Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0033_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_before_reader"
  err.flush

noncomputable def chunk0034LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0034SuffixChars00 : List Char := [',']
noncomputable def chunk0034Chars00 : List Char := chunk0034LeadChars00 ++ fragment0190021Chars ++ chunk0034SuffixChars00
noncomputable def chunk0034Push00 (acc : List SourceJson) : List SourceJson := fragment0190021Value :: acc

noncomputable def chunk0034AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0034_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 623)
      (SourceJson.white (chunk0034LeadChars00 ++ (fragment0190021Chars ++ rest))) acc =
      (SourceJson.value (fuel + 622) (fragment0190021Chars ++ rest)).bind
        (chunk0034AfterValue00 (fuel + 622) acc) := by rfl

theorem array_chunk0034 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 623) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 622) (SourceJson.white tail) (chunk0034Push00 acc) := by
  have hinput : chunk0034Chars00 ++ tail = chunk0034LeadChars00 ++ (fragment0190021Chars ++ (chunk0034SuffixChars00 ++ tail)) := by
    simp only [chunk0034Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 623) (SourceJson.white (chunk0034Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 623)
          (SourceJson.white (chunk0034LeadChars00 ++ (fragment0190021Chars ++ (chunk0034SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 623) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 622) (fragment0190021Chars ++ (chunk0034SuffixChars00 ++ tail))).bind
        (chunk0034AfterValue00 (fuel + 622) acc) := array_chunk0034_head fuel (chunk0034SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0190021Value, chunk0034SuffixChars00 ++ tail)).bind
        (chunk0034AfterValue00 (fuel + 622) acc) :=
      congrArg (fun result => result.bind (chunk0034AfterValue00 (fuel + 622) acc))
        (value_fragment0190021 (fuel + 361) (chunk0034SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 622) (SourceJson.white tail) (chunk0034Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0034_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_before_reader"
  err.flush

noncomputable def chunk0035LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0035SuffixChars00 : List Char := [',']
noncomputable def chunk0035Chars00 : List Char := chunk0035LeadChars00 ++ fragment0191697Chars ++ chunk0035SuffixChars00
noncomputable def chunk0035Push00 (acc : List SourceJson) : List SourceJson := fragment0191697Value :: acc

noncomputable def chunk0035AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0035_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 622)
      (SourceJson.white (chunk0035LeadChars00 ++ (fragment0191697Chars ++ rest))) acc =
      (SourceJson.value (fuel + 621) (fragment0191697Chars ++ rest)).bind
        (chunk0035AfterValue00 (fuel + 621) acc) := by rfl

theorem array_chunk0035 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 622) (SourceJson.white (chunk0035Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 621) (SourceJson.white tail) (chunk0035Push00 acc) := by
  have hinput : chunk0035Chars00 ++ tail = chunk0035LeadChars00 ++ (fragment0191697Chars ++ (chunk0035SuffixChars00 ++ tail)) := by
    simp only [chunk0035Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 622) (SourceJson.white (chunk0035Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 622)
          (SourceJson.white (chunk0035LeadChars00 ++ (fragment0191697Chars ++ (chunk0035SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 622) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 621) (fragment0191697Chars ++ (chunk0035SuffixChars00 ++ tail))).bind
        (chunk0035AfterValue00 (fuel + 621) acc) := array_chunk0035_head fuel (chunk0035SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0191697Value, chunk0035SuffixChars00 ++ tail)).bind
        (chunk0035AfterValue00 (fuel + 621) acc) :=
      congrArg (fun result => result.bind (chunk0035AfterValue00 (fuel + 621) acc))
        (value_fragment0191697 (fuel + 359) (chunk0035SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 621) (SourceJson.white tail) (chunk0035Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0035_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_before_reader"
  err.flush

noncomputable def chunk0036LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0036SuffixChars00 : List Char := [',']
noncomputable def chunk0036Chars00 : List Char := chunk0036LeadChars00 ++ fragment0193356Chars ++ chunk0036SuffixChars00
noncomputable def chunk0036Push00 (acc : List SourceJson) : List SourceJson := fragment0193356Value :: acc

noncomputable def chunk0036AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0036_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 621)
      (SourceJson.white (chunk0036LeadChars00 ++ (fragment0193356Chars ++ rest))) acc =
      (SourceJson.value (fuel + 620) (fragment0193356Chars ++ rest)).bind
        (chunk0036AfterValue00 (fuel + 620) acc) := by rfl

theorem array_chunk0036 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 621) (SourceJson.white (chunk0036Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 620) (SourceJson.white tail) (chunk0036Push00 acc) := by
  have hinput : chunk0036Chars00 ++ tail = chunk0036LeadChars00 ++ (fragment0193356Chars ++ (chunk0036SuffixChars00 ++ tail)) := by
    simp only [chunk0036Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 621) (SourceJson.white (chunk0036Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 621)
          (SourceJson.white (chunk0036LeadChars00 ++ (fragment0193356Chars ++ (chunk0036SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 621) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 620) (fragment0193356Chars ++ (chunk0036SuffixChars00 ++ tail))).bind
        (chunk0036AfterValue00 (fuel + 620) acc) := array_chunk0036_head fuel (chunk0036SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0193356Value, chunk0036SuffixChars00 ++ tail)).bind
        (chunk0036AfterValue00 (fuel + 620) acc) :=
      congrArg (fun result => result.bind (chunk0036AfterValue00 (fuel + 620) acc))
        (value_fragment0193356 (fuel + 124) (chunk0036SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 620) (SourceJson.white tail) (chunk0036Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0036_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_before_reader"
  err.flush

noncomputable def chunk0037LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0037SuffixChars00 : List Char := [',']
noncomputable def chunk0037Chars00 : List Char := chunk0037LeadChars00 ++ fragment0195513Chars ++ chunk0037SuffixChars00
noncomputable def chunk0037Push00 (acc : List SourceJson) : List SourceJson := fragment0195513Value :: acc

noncomputable def chunk0037AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0037_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 620)
      (SourceJson.white (chunk0037LeadChars00 ++ (fragment0195513Chars ++ rest))) acc =
      (SourceJson.value (fuel + 619) (fragment0195513Chars ++ rest)).bind
        (chunk0037AfterValue00 (fuel + 619) acc) := by rfl

theorem array_chunk0037 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 620) (SourceJson.white (chunk0037Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 619) (SourceJson.white tail) (chunk0037Push00 acc) := by
  have hinput : chunk0037Chars00 ++ tail = chunk0037LeadChars00 ++ (fragment0195513Chars ++ (chunk0037SuffixChars00 ++ tail)) := by
    simp only [chunk0037Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 620) (SourceJson.white (chunk0037Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 620)
          (SourceJson.white (chunk0037LeadChars00 ++ (fragment0195513Chars ++ (chunk0037SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 620) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 619) (fragment0195513Chars ++ (chunk0037SuffixChars00 ++ tail))).bind
        (chunk0037AfterValue00 (fuel + 619) acc) := array_chunk0037_head fuel (chunk0037SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0195513Value, chunk0037SuffixChars00 ++ tail)).bind
        (chunk0037AfterValue00 (fuel + 619) acc) :=
      congrArg (fun result => result.bind (chunk0037AfterValue00 (fuel + 619) acc))
        (value_fragment0195513 (fuel + 139) (chunk0037SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 619) (SourceJson.white tail) (chunk0037Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0037_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0038_before_reader"
  err.flush

noncomputable def chunk0038LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0038SuffixChars00 : List Char := [',']
noncomputable def chunk0038Chars00 : List Char := chunk0038LeadChars00 ++ fragment0197628Chars ++ chunk0038SuffixChars00
noncomputable def chunk0038Push00 (acc : List SourceJson) : List SourceJson := fragment0197628Value :: acc

noncomputable def chunk0038AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0038_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 619)
      (SourceJson.white (chunk0038LeadChars00 ++ (fragment0197628Chars ++ rest))) acc =
      (SourceJson.value (fuel + 618) (fragment0197628Chars ++ rest)).bind
        (chunk0038AfterValue00 (fuel + 618) acc) := by rfl

theorem array_chunk0038 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 619) (SourceJson.white (chunk0038Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 618) (SourceJson.white tail) (chunk0038Push00 acc) := by
  have hinput : chunk0038Chars00 ++ tail = chunk0038LeadChars00 ++ (fragment0197628Chars ++ (chunk0038SuffixChars00 ++ tail)) := by
    simp only [chunk0038Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 619) (SourceJson.white (chunk0038Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 619)
          (SourceJson.white (chunk0038LeadChars00 ++ (fragment0197628Chars ++ (chunk0038SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 619) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 618) (fragment0197628Chars ++ (chunk0038SuffixChars00 ++ tail))).bind
        (chunk0038AfterValue00 (fuel + 618) acc) := array_chunk0038_head fuel (chunk0038SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0197628Value, chunk0038SuffixChars00 ++ tail)).bind
        (chunk0038AfterValue00 (fuel + 618) acc) :=
      congrArg (fun result => result.bind (chunk0038AfterValue00 (fuel + 618) acc))
        (value_fragment0197628 (fuel + 179) (chunk0038SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 618) (SourceJson.white tail) (chunk0038Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0038_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0039_before_reader"
  err.flush

noncomputable def chunk0039LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0039SuffixChars00 : List Char := [',']
noncomputable def chunk0039Chars00 : List Char := chunk0039LeadChars00 ++ fragment0199644Chars ++ chunk0039SuffixChars00
noncomputable def chunk0039Push00 (acc : List SourceJson) : List SourceJson := fragment0199644Value :: acc

noncomputable def chunk0039AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0039_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 618)
      (SourceJson.white (chunk0039LeadChars00 ++ (fragment0199644Chars ++ rest))) acc =
      (SourceJson.value (fuel + 617) (fragment0199644Chars ++ rest)).bind
        (chunk0039AfterValue00 (fuel + 617) acc) := by rfl

theorem array_chunk0039 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 618) (SourceJson.white (chunk0039Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 617) (SourceJson.white tail) (chunk0039Push00 acc) := by
  have hinput : chunk0039Chars00 ++ tail = chunk0039LeadChars00 ++ (fragment0199644Chars ++ (chunk0039SuffixChars00 ++ tail)) := by
    simp only [chunk0039Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 618) (SourceJson.white (chunk0039Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 618)
          (SourceJson.white (chunk0039LeadChars00 ++ (fragment0199644Chars ++ (chunk0039SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 618) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 617) (fragment0199644Chars ++ (chunk0039SuffixChars00 ++ tail))).bind
        (chunk0039AfterValue00 (fuel + 617) acc) := array_chunk0039_head fuel (chunk0039SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0199644Value, chunk0039SuffixChars00 ++ tail)).bind
        (chunk0039AfterValue00 (fuel + 617) acc) :=
      congrArg (fun result => result.bind (chunk0039AfterValue00 (fuel + 617) acc))
        (value_fragment0199644 (fuel + 239) (chunk0039SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 617) (SourceJson.white tail) (chunk0039Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0039_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0032Chars00 ++ chunk0033Chars00 ++ chunk0034Chars00 ++ chunk0035Chars00 ++ chunk0036Chars00 ++ chunk0037Chars00 ++ chunk0038Chars00 ++ chunk0039Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0039Push00 (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 625) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 617) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 625) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 625) (SourceJson.white (chunk0032Chars00 ++ (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 625) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 624) (SourceJson.white (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))))) (chunk0032Push00 (acc)) := array_chunk0032 fuel (chunk0033Chars00 ++ (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 623) (SourceJson.white (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))))) (chunk0033Push00 (chunk0032Push00 (acc))) := array_chunk0033 fuel (chunk0034Chars00 ++ (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))) (chunk0032Push00 (acc))
    _ = SourceJson.array (fuel + 622) (SourceJson.white (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))))) (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))) := array_chunk0034 fuel (chunk0035Chars00 ++ (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))) (chunk0033Push00 (chunk0032Push00 (acc)))
    _ = SourceJson.array (fuel + 621) (SourceJson.white (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))))) (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))) := array_chunk0035 fuel (chunk0036Chars00 ++ (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))) (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))
    _ = SourceJson.array (fuel + 620) (SourceJson.white (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))))) (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))) := array_chunk0036 fuel (chunk0037Chars00 ++ (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))) (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))
    _ = SourceJson.array (fuel + 619) (SourceJson.white (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail)))) (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))) := array_chunk0037 fuel (chunk0038Chars00 ++ (chunk0039Chars00 ++ (tail))) (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))
    _ = SourceJson.array (fuel + 618) (SourceJson.white (chunk0039Chars00 ++ (tail))) (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))))) := array_chunk0038 fuel (chunk0039Chars00 ++ (tail)) (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc)))))))
    _ = SourceJson.array (fuel + 617) (SourceJson.white tail) (blockPush acc) := array_chunk0039 fuel (tail) (chunk0038Push00 (chunk0037Push00 (chunk0036Push00 (chunk0035Push00 (chunk0034Push00 (chunk0033Push00 (chunk0032Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 185891).take 15627 = blockChars := by rfl

theorem block_original_split : sourceRest 185891 = blockChars ++ sourceRest 201518 := by
  calc
    sourceRest 185891 = (sourceRest 185891).take 15627 ++ (sourceRest 185891).drop 15627 :=
      (List.take_append_drop 15627 (sourceRest 185891)).symm
    _ = blockChars ++ (sourceRest 185891).drop 15627 :=
      congrArg (fun part => part ++ (sourceRest 185891).drop 15627) block_original_prefix
    _ = blockChars ++ sourceRest 201518 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 185891 15627)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 625) (SourceJson.white (sourceRest 185891)) acc =
      SourceJson.array (fuel + 617) (SourceJson.white (sourceRest 201518)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 625) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 201518) acc)

#print axioms object_fragment0185897_field_000
#print axioms object_fragment0185897_field_001
#print axioms object_fragment0185897_field_002
#print axioms object_fragment0185897_field_003
#print axioms object_fragment0185897_field_004
#print axioms object_fragment0185897_field_005
#print axioms object_fragment0185897_field_006
#print axioms object_fragment0185897_field_007
#print axioms object_fragment0185897_field_008
#print axioms object_fragment0185897_field_009
#print axioms value_fragment0185897
#print axioms object_fragment0188025_field_000
#print axioms object_fragment0188025_field_001
#print axioms object_fragment0188025_field_002
#print axioms object_fragment0188025_field_003
#print axioms object_fragment0188025_field_004
#print axioms object_fragment0188025_field_005
#print axioms object_fragment0188025_field_006
#print axioms object_fragment0188025_field_007
#print axioms object_fragment0188025_field_008
#print axioms object_fragment0188025_field_009
#print axioms value_fragment0188025
#print axioms object_fragment0190021_field_000
#print axioms object_fragment0190021_field_001
#print axioms object_fragment0190021_field_002
#print axioms object_fragment0190021_field_003
#print axioms object_fragment0190021_field_004
#print axioms object_fragment0190021_field_005
#print axioms object_fragment0190021_field_006
#print axioms object_fragment0190021_field_007
#print axioms object_fragment0190021_field_008
#print axioms object_fragment0190021_field_009
#print axioms value_fragment0190021
#print axioms object_fragment0191697_field_000
#print axioms object_fragment0191697_field_001
#print axioms object_fragment0191697_field_002
#print axioms object_fragment0191697_field_003
#print axioms object_fragment0191697_field_004
#print axioms object_fragment0191697_field_005
#print axioms object_fragment0191697_field_006
#print axioms object_fragment0191697_field_007
#print axioms object_fragment0191697_field_008
#print axioms object_fragment0191697_field_009
#print axioms value_fragment0191697
#print axioms object_fragment0193356_field_000
#print axioms object_fragment0193356_field_001
#print axioms object_fragment0193356_field_002
#print axioms object_fragment0193356_field_003
#print axioms object_fragment0193356_field_004
#print axioms object_fragment0193356_field_005
#print axioms object_fragment0193356_field_006
#print axioms object_fragment0193356_field_007
#print axioms object_fragment0193356_field_008
#print axioms object_fragment0193356_field_009
#print axioms value_fragment0193356
#print axioms object_fragment0195513_field_000
#print axioms object_fragment0195513_field_001
#print axioms object_fragment0195513_field_002
#print axioms object_fragment0195513_field_003
#print axioms object_fragment0195513_field_004
#print axioms object_fragment0195513_field_005
#print axioms object_fragment0195513_field_006
#print axioms object_fragment0195513_field_007
#print axioms object_fragment0195513_field_008
#print axioms object_fragment0195513_field_009
#print axioms value_fragment0195513
#print axioms object_fragment0197628_field_000
#print axioms object_fragment0197628_field_001
#print axioms object_fragment0197628_field_002
#print axioms object_fragment0197628_field_003
#print axioms object_fragment0197628_field_004
#print axioms object_fragment0197628_field_005
#print axioms object_fragment0197628_field_006
#print axioms object_fragment0197628_field_007
#print axioms object_fragment0197628_field_008
#print axioms object_fragment0197628_field_009
#print axioms value_fragment0197628
#print axioms object_fragment0199644_field_000
#print axioms object_fragment0199644_field_001
#print axioms object_fragment0199644_field_002
#print axioms object_fragment0199644_field_003
#print axioms object_fragment0199644_field_004
#print axioms object_fragment0199644_field_005
#print axioms object_fragment0199644_field_006
#print axioms object_fragment0199644_field_007
#print axioms object_fragment0199644_field_008
#print axioms object_fragment0199644_field_009
#print axioms value_fragment0199644
#print axioms array_chunk0032_head
#print axioms array_chunk0032
#print axioms array_chunk0033_head
#print axioms array_chunk0033
#print axioms array_chunk0034_head
#print axioms array_chunk0034
#print axioms array_chunk0035_head
#print axioms array_chunk0035
#print axioms array_chunk0036_head
#print axioms array_chunk0036
#print axioms array_chunk0037_head
#print axioms array_chunk0037
#print axioms array_chunk0038_head
#print axioms array_chunk0038
#print axioms array_chunk0039_head
#print axioms array_chunk0039
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock004

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
