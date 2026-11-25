import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput

/-! Original simplices grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace SimplicesBlock021

noncomputable def fragment0296439Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0296439Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0296439Field000Value00 : SourceJson := .number (String.ofList ['4', '2'])
noncomputable def fragment0296439Acc00100 : List (String × SourceJson) := (fragment0296439Field000Key00, fragment0296439Field000Value00) :: fragment0296439Acc00000
noncomputable def fragment0296439Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '4', '2', ',']

theorem object_fragment0296439_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 421) (SourceJson.white (fragment0296439Field000Chars00 ++ tail)) fragment0296439Acc00000 =
      SourceJson.object (fuel + 420) (SourceJson.white tail) fragment0296439Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_000"
  err.flush

noncomputable def fragment0296439Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0296439Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]
noncomputable def fragment0296439Acc00200 : List (String × SourceJson) := (fragment0296439Field001Key00, fragment0296439Field001Value00) :: fragment0296439Acc00100
noncomputable def fragment0296439Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0296439_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 420) (SourceJson.white (fragment0296439Field001Chars00 ++ tail)) fragment0296439Acc00100 =
      SourceJson.object (fuel + 419) (SourceJson.white tail) fragment0296439Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_001"
  err.flush

noncomputable def fragment0296439Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0296439Field002Value00 : SourceJson := .str (String.ofList ['6', '2', '4', '5', '6', '5', '8', '0', '1', '1', '7', '8', '9', '0', '3', '8', '7', '3', '1', '7', '3', '1', '5', '6', '0', '7', '9', '2', '4', '8', '9', '0', '1', '6', '9', '7', '7', '5', '2', '9', '/', '1', '8', '7', '1', '8', '3', '6', '0', '1', '2', '7', '0', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0296439Acc00300 : List (String × SourceJson) := (fragment0296439Field002Key00, fragment0296439Field002Value00) :: fragment0296439Acc00200
noncomputable def fragment0296439Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '6', '2', '4', '5', '6', '5', '8', '0', '1', '1', '7', '8', '9', '0', '3', '8', '7', '3', '1', '7', '3', '1', '5', '6', '0', '7', '9', '2', '4', '8', '9', '0', '1', '6', '9', '7', '7', '5', '2', '9', '/', '1', '8', '7', '1', '8', '3', '6', '0', '1', '2', '7', '0', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0296439_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 419) (SourceJson.white (fragment0296439Field002Chars00 ++ tail)) fragment0296439Acc00200 =
      SourceJson.object (fuel + 418) (SourceJson.white tail) fragment0296439Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_002"
  err.flush

noncomputable def fragment0296439Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0296439Field003Value00 : SourceJson := .str (String.ofList ['6', '6', '3', '6', '9', '1', '0', '9', '/', '9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0296439Acc00400 : List (String × SourceJson) := (fragment0296439Field003Key00, fragment0296439Field003Value00) :: fragment0296439Acc00300
noncomputable def fragment0296439Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '6', '3', '6', '9', '1', '0', '9', '/', '9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0296439_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 418) (SourceJson.white (fragment0296439Field003Chars00 ++ tail)) fragment0296439Acc00300 =
      SourceJson.object (fuel + 417) (SourceJson.white tail) fragment0296439Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_003"
  err.flush

noncomputable def fragment0296439Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0296439Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4'])]
noncomputable def fragment0296439Acc00500 : List (String × SourceJson) := (fragment0296439Field004Key00, fragment0296439Field004Value00) :: fragment0296439Acc00400
noncomputable def fragment0296439Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0296439_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 417) (SourceJson.white (fragment0296439Field004Chars00 ++ tail)) fragment0296439Acc00400 =
      SourceJson.object (fuel + 416) (SourceJson.white tail) fragment0296439Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_004"
  err.flush

noncomputable def fragment0296439Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0296439Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '0', '3', '2', '0', '0', '9', '8', '5', '7', '1', '8', '3', '0', '4', '2', '3', '1', '3', '7', '/', '2', '5', '4', '7', '6', '2', '0', '8', '6', '4', '9', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '1', '1', '1', '5', '7', '5', '5', '6', '6', '0', '7', '7', '3', '1', '4', '4', '9', '9', '1', '/', '4', '8', '4', '0', '4', '7', '9', '6', '4', '3', '3', '4', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '6', '7', '1', '1', '5', '4', '0', '7', '9', '4', '8', '8', '0', '3', '9', '0', '6', '8', '8', '1', '/', '4', '3', '5', '6', '4', '3', '1', '6', '7', '9', '0', '1', '1', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '9', '5', '7', '3', '7', '3', '2', '7', '7', '9', '4', '1', '5', '3', '0', '8', '6', '9', '9', '3', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '6', '6', '5', '4', '3', '4', '3', '4', '4', '9', '7', '6', '8', '7', '2', '3', '9', '4', '1', '/', '1', '2', '8', '1', '3', '0', '3', '4', '3', '5', '0', '0', '3', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '2', '6', '0', '0', '4', '7', '0', '2', '4', '9', '0', '5', '3', '6', '1', '4', '6', '8', '3', '1', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '7', '7', '8', '7', '9', '3', '8', '8', '0', '7', '2', '1', '6', '2', '9', '1', '6', '2', '2', '9', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '6', '1', '5', '6', '9', '7', '3', '1', '8', '9', '0', '4', '4', '7', '1', '5', '2', '6', '0', '9', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '1', '4', '6', '8', '1', '7', '3', '2', '1', '0', '3', '3', '5', '1', '7', '9', '8', '8', '8', '7', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '1', '4', '6', '3', '8', '1', '6', '7', '7', '8', '6', '5', '6', '1', '6', '8', '0', '5', '6', '7', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0296439Acc00600 : List (String × SourceJson) := (fragment0296439Field005Key00, fragment0296439Field005Value00) :: fragment0296439Acc00500
noncomputable def fragment0296439Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '2', '0', '0', '9', '8', '5', '7', '1', '8', '3', '0', '4', '2', '3', '1', '3', '7', '/', '2', '5', '4', '7', '6', '2', '0', '8', '6', '4', '9', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '1', '1', '1', '5', '7', '5', '5', '6', '6', '0', '7', '7', '3', '1', '4', '4', '9', '9', '1', '/', '4', '8', '4', '0', '4', '7', '9', '6', '4', '3', '3', '4', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '2', '6', '7', '1', '1', '5', '4', '0', '7', '9', '4', '8', '8', '0', '3', '9', '0', '6', '8', '8', '1', '/', '4', '3', '5', '6', '4', '3', '1', '6', '7', '9', '0', '1', '1', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '9', '5', '7', '3', '7', '3', '2', '7', '7', '9', '4', '1', '5', '3', '0', '8', '6', '9', '9', '3', '/', '3', '6', '3', '0', '3', '5', '9', '7', '3', '2', '5', '0', '9', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '5', '6', '6', '5', '4', '3', '4', '3', '4', '4', '9', '7', '6', '8', '7', '2', '3', '9', '4', '1', '/', '1', '2', '8', '1', '3', '0', '3', '4', '3', '5', '0', '0', '3', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '2', '6', '0', '0', '4', '7', '0', '2', '4', '9', '0', '5', '3', '6', '1', '4', '6', '8', '3', '1', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '7', '7', '8', '7', '9', '3', '8', '8', '0', '7', '2', '1', '6', '2', '9', '1', '6', '2', '2', '9', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '6', '6', '1', '5', '6', '9', '7', '3', '1', '8', '9', '0', '4', '4', '7', '1', '5', '2', '6', '0', '9', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '1', '4', '6', '8', '1', '7', '3', '2', '1', '0', '3', '3', '5', '1', '7', '9', '8', '8', '8', '7', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '1', '4', '6', '3', '8', '1', '6', '7', '7', '8', '6', '5', '6', '1', '6', '8', '0', '5', '6', '7', '/', '2', '1', '7', '8', '2', '1', '5', '8', '3', '9', '5', '0', '5', '9', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0296439_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 416) (SourceJson.white (fragment0296439Field005Chars00 ++ tail)) fragment0296439Acc00500 =
      SourceJson.object (fuel + 415) (SourceJson.white tail) fragment0296439Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_005"
  err.flush

noncomputable def fragment0296439Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0296439Field006Value00 : SourceJson := .str (String.ofList ['5', '0', '1', '8', '4', '9', '5', '3', '8', '6', '9', '2', '5', '6', '0', '8', '0', '0', '1', '1', '0', '7', '9', '3', '8', '2', '0', '1', '4', '2', '7', '4', '0', '8', '3', '1', '2', '3', '4', '0', '3', '9', '0', '0', '3', '2', '/', '3', '3', '7', '8', '8', '0', '4', '8', '7', '6', '6', '8', '8', '2', '9', '6', '2', '4', '0', '5', '8', '0', '5', '3', '8', '9', '5', '5', '3', '9', '3', '4', '3', '7', '4', '5', '2', '4', '8', '1', '5', '1', '7', '5', '0', '7', '0', '2', '2', '7', '1', '3', '3', '2', '7', '5', '9', '7', '6', '5', '6', '2', '5'])
noncomputable def fragment0296439Acc00700 : List (String × SourceJson) := (fragment0296439Field006Key00, fragment0296439Field006Value00) :: fragment0296439Acc00600
noncomputable def fragment0296439Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '0', '1', '8', '4', '9', '5', '3', '8', '6', '9', '2', '5', '6', '0', '8', '0', '0', '1', '1', '0', '7', '9', '3', '8', '2', '0', '1', '4', '2', '7', '4', '0', '8', '3', '1', '2', '3', '4', '0', '3', '9', '0', '0', '3', '2', '/', '3', '3', '7', '8', '8', '0', '4', '8', '7', '6', '6', '8', '8', '2', '9', '6', '2', '4', '0', '5', '8', '0', '5', '3', '8', '9', '5', '5', '3', '9', '3', '4', '3', '7', '4', '5', '2', '4', '8', '1', '5', '1', '7', '5', '0', '7', '0', '2', '2', '7', '1', '3', '3', '2', '7', '5', '9', '7', '6', '5', '6', '2', '5', '"', ',']

theorem object_fragment0296439_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 415) (SourceJson.white (fragment0296439Field006Chars00 ++ tail)) fragment0296439Acc00600 =
      SourceJson.object (fuel + 414) (SourceJson.white tail) fragment0296439Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_006"
  err.flush

noncomputable def fragment0296439Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0296439Field007Value00 : SourceJson := .str (String.ofList ['9', '8', '9', '1', '5', '6', '4', '3', '8', '4', '6', '2', '3', '7', '5', '4', '4', '3', '3', '4', '9', '4', '5', '7', '9', '8', '1', '2', '1', '1', '3', '9', '5', '0', '3', '3', '9', '5', '7', '7', '3', '1', '2', '5', '5', '2', '7', '2', '9', '3', '8', '2', '9', '2', '2', '1', '9', '3', '4', '2', '6', '7', '0', '2', '2', '5', '5', '1', '0', '5', '7', '6', '5', '9', '3', '7', '1', '3', '6', '2', '1', '5', '6', '5', '9', '7', '7', '5', '1', '6', '2', '9', '2', '5', '9', '0', '6', '2', '2', '5', '0', '7', '7', '0', '1', '9', '7', '3', '5', '7', '4', '9', '6', '4', '3', '3', '4', '1', '0', '1', '9', '4', '5', '6', '4', '3', '3', '8', '8', '8', '2', '4', '9', '0', '9', '6', '2', '9', '9', '0', '6', '5', '8', '1', '0', '4', '5', '3', '0', '8', '9', '5', '7', '7', '1', '6', '4', '6', '8', '1', '1', '2', '4', '9', '0', '3', '2', '8', '4', '5', '3', '5', '6', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '7', '0', '7', '0', '9', '4', '1', '3', '3', '1', '8', '5', '8', '2', '7', '4', '5', '5', '2', '5', '6', '1', '4', '6', '6', '4', '2', '4', '2', '7', '7', '1', '4', '6', '9', '1', '5', '6', '5', '3', '1', '3', '3', '5', '1', '3', '2', '5', '6', '8', '3', '6', '7', '9', '5', '2', '7', '1', '5', '3', '8', '9', '1', '3', '5', '9', '6', '4', '8', '3', '6', '5', '6', '6', '4', '3', '1', '6', '6', '2', '4', '3', '3', '5', '4', '4', '0', '4', '8', '9', '4', '2', '2', '1', '3', '0', '8', '0', '9', '3', '2', '6', '7', '2', '0', '5', '4', '8', '7', '7', '7', '5', '1', '5', '4', '0', '0', '8', '4', '4', '7', '5', '8', '4', '1', '1', '1', '1', '0', '6', '1', '9', '0', '3', '2', '5', '9', '3', '8', '0', '2', '9', '2', '1', '2', '2', '4', '3', '8', '7', '2', '4', '6', '0', '8', '3', '4', '2', '1', '1', '8', '5', '8', '3', '4', '4', '9', '5', '8', '5', '7', '5', '1', '6', '3', '5', '4', '3', '1', '2', '1', '6', '6', '7', '8', '2', '5', '5', '9', '5', '3', '2', '9', '0', '0', '0', '1', '9', '7', '8', '0', '1', '9', '5', '9', '3', '3', '7', '2', '2', '9', '9'])
noncomputable def fragment0296439Acc00800 : List (String × SourceJson) := (fragment0296439Field007Key00, fragment0296439Field007Value00) :: fragment0296439Acc00700
noncomputable def fragment0296439Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '8', '9', '1', '5', '6', '4', '3', '8', '4', '6', '2', '3', '7', '5', '4', '4', '3', '3', '4', '9', '4', '5', '7', '9', '8', '1', '2', '1', '1', '3', '9', '5', '0', '3', '3', '9', '5', '7', '7', '3', '1', '2', '5', '5', '2', '7', '2', '9', '3', '8', '2', '9', '2', '2', '1', '9', '3', '4', '2', '6', '7', '0', '2', '2', '5', '5', '1', '0', '5', '7', '6', '5', '9', '3', '7', '1', '3', '6', '2', '1', '5', '6', '5', '9', '7', '7', '5', '1', '6', '2', '9', '2', '5', '9', '0', '6', '2', '2', '5', '0', '7', '7', '0', '1', '9', '7', '3', '5', '7', '4', '9', '6', '4', '3', '3', '4', '1', '0', '1', '9', '4', '5', '6', '4', '3', '3', '8', '8', '8', '2', '4', '9', '0', '9', '6', '2', '9', '9', '0', '6', '5', '8', '1', '0', '4', '5', '3', '0', '8', '9', '5', '7', '7', '1', '6', '4', '6', '8', '1', '1', '2', '4', '9', '0', '3', '2', '8', '4', '5', '3', '5', '6', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '7', '0', '7', '0', '9', '4', '1', '3', '3', '1', '8', '5', '8', '2', '7', '4', '5', '5', '2', '5', '6', '1', '4', '6', '6', '4', '2', '4', '2', '7', '7', '1', '4', '6', '9', '1', '5', '6', '5', '3', '1', '3', '3', '5', '1', '3', '2', '5', '6', '8', '3', '6', '7', '9', '5', '2', '7', '1', '5', '3', '8', '9', '1', '3', '5', '9', '6', '4', '8', '3', '6', '5', '6', '6', '4', '3', '1', '6', '6', '2', '4', '3', '3', '5', '4', '4', '0', '4', '8', '9', '4', '2', '2', '1', '3', '0', '8', '0', '9', '3', '2', '6', '7', '2', '0', '5', '4', '8', '7', '7', '7', '5', '1', '5', '4', '0', '0', '8', '4', '4', '7', '5', '8', '4', '1', '1', '1', '1', '0', '6', '1', '9', '0', '3', '2', '5', '9', '3', '8', '0', '2', '9', '2', '1', '2', '2', '4', '3', '8', '7', '2', '4', '6', '0', '8', '3', '4', '2', '1', '1', '8', '5', '8', '3', '4', '4', '9', '5', '8', '5', '7', '5', '1', '6', '3', '5', '4', '3', '1', '2', '1', '6', '6', '7', '8', '2', '5', '5', '9', '5', '3', '2', '9', '0', '0', '0', '1', '9', '7', '8', '0', '1', '9', '5', '9', '3', '3', '7', '2', '2', '9', '9', '"', ',']

theorem object_fragment0296439_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 414) (SourceJson.white (fragment0296439Field007Chars00 ++ tail)) fragment0296439Acc00700 =
      SourceJson.object (fuel + 413) (SourceJson.white tail) fragment0296439Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_007"
  err.flush

noncomputable def fragment0296439Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0296439Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '6', '7', '6', '5', '6', '9', '8', '5', '3', '3'])
noncomputable def fragment0296439Acc00900 : List (String × SourceJson) := (fragment0296439Field008Key00, fragment0296439Field008Value00) :: fragment0296439Acc00800
noncomputable def fragment0296439Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '7', '6', '7', '6', '5', '6', '9', '8', '5', '3', '3', '"', ',']

theorem object_fragment0296439_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 413) (SourceJson.white (fragment0296439Field008Chars00 ++ tail)) fragment0296439Acc00800 =
      SourceJson.object (fuel + 412) (SourceJson.white tail) fragment0296439Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_008"
  err.flush

noncomputable def fragment0296439Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0296439Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '1', '6', '8', '4', '2', '9', '9', '8', '2', '0', '7', '0'])
noncomputable def fragment0296439Acc01000 : List (String × SourceJson) := (fragment0296439Field009Key00, fragment0296439Field009Value00) :: fragment0296439Acc00900
noncomputable def fragment0296439Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '1', '6', '8', '4', '2', '9', '9', '8', '2', '0', '7', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0296439_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 412) (SourceJson.white (fragment0296439Field009Chars00 ++ tail)) fragment0296439Acc00900 =
      .ok (.obj (fragment0296439Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0296439_object_field_009"
  err.flush

noncomputable def fragment0296439Chars : List Char := '{' :: (fragment0296439Field000Chars00 ++ fragment0296439Field001Chars00 ++ fragment0296439Field002Chars00 ++ fragment0296439Field003Chars00 ++ fragment0296439Field004Chars00 ++ fragment0296439Field005Chars00 ++ fragment0296439Field006Chars00 ++ fragment0296439Field007Chars00 ++ fragment0296439Field008Chars00 ++ fragment0296439Field009Chars00)
noncomputable def fragment0296439Value : SourceJson := .obj (fragment0296439Acc01000.reverse)

theorem value_fragment0296439 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 422) (fragment0296439Chars ++ tail) =
      .ok (fragment0296439Value, tail) := by
  have hinput : fragment0296439Chars ++ tail = '{' :: (fragment0296439Field000Chars00 ++ (fragment0296439Field001Chars00 ++ (fragment0296439Field002Chars00 ++ (fragment0296439Field003Chars00 ++ (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0296439Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 422) (fragment0296439Chars ++ tail) =
        SourceJson.value (fuel + 422) ('{' :: (fragment0296439Field000Chars00 ++ (fragment0296439Field001Chars00 ++ (fragment0296439Field002Chars00 ++ (fragment0296439Field003Chars00 ++ (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 422)) hinput
    _ = SourceJson.object (fuel + 421) (SourceJson.white (fragment0296439Field000Chars00 ++ (fragment0296439Field001Chars00 ++ (fragment0296439Field002Chars00 ++ (fragment0296439Field003Chars00 ++ (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))))))))))) fragment0296439Acc00000 := by rfl
    _ = SourceJson.object (fuel + 420) (SourceJson.white (fragment0296439Field001Chars00 ++ (fragment0296439Field002Chars00 ++ (fragment0296439Field003Chars00 ++ (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail))))))))))) fragment0296439Acc00100 := object_fragment0296439_field_000 fuel (fragment0296439Field001Chars00 ++ (fragment0296439Field002Chars00 ++ (fragment0296439Field003Chars00 ++ (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 419) (SourceJson.white (fragment0296439Field002Chars00 ++ (fragment0296439Field003Chars00 ++ (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))))))))) fragment0296439Acc00200 := object_fragment0296439_field_001 fuel (fragment0296439Field002Chars00 ++ (fragment0296439Field003Chars00 ++ (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 418) (SourceJson.white (fragment0296439Field003Chars00 ++ (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail))))))))) fragment0296439Acc00300 := object_fragment0296439_field_002 fuel (fragment0296439Field003Chars00 ++ (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 417) (SourceJson.white (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))))))) fragment0296439Acc00400 := object_fragment0296439_field_003 fuel (fragment0296439Field004Chars00 ++ (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 416) (SourceJson.white (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail))))))) fragment0296439Acc00500 := object_fragment0296439_field_004 fuel (fragment0296439Field005Chars00 ++ (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 415) (SourceJson.white (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))))) fragment0296439Acc00600 := object_fragment0296439_field_005 fuel (fragment0296439Field006Chars00 ++ (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 414) (SourceJson.white (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail))))) fragment0296439Acc00700 := object_fragment0296439_field_006 fuel (fragment0296439Field007Chars00 ++ (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 413) (SourceJson.white (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))) fragment0296439Acc00800 := object_fragment0296439_field_007 fuel (fragment0296439Field008Chars00 ++ (fragment0296439Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 412) (SourceJson.white (fragment0296439Field009Chars00 ++ (tail))) fragment0296439Acc00900 := object_fragment0296439_field_008 fuel (fragment0296439Field009Chars00 ++ (tail))
    _ = .ok (fragment0296439Value, tail) := object_fragment0296439_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_before_reader"
  err.flush

noncomputable def chunk0042LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0042SuffixChars00 : List Char := [',']
noncomputable def chunk0042Chars00 : List Char := chunk0042LeadChars00 ++ fragment0296439Chars ++ chunk0042SuffixChars00
noncomputable def chunk0042Push00 (acc : List SourceJson) : List SourceJson := fragment0296439Value :: acc

noncomputable def chunk0042AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0042_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 562)
      (SourceJson.white (chunk0042LeadChars00 ++ (fragment0296439Chars ++ rest))) acc =
      (SourceJson.value (fuel + 561) (fragment0296439Chars ++ rest)).bind
        (chunk0042AfterValue00 (fuel + 561) acc) := by rfl

theorem array_chunk0042 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 562) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 561) (SourceJson.white tail) (chunk0042Push00 acc) := by
  have hinput : chunk0042Chars00 ++ tail = chunk0042LeadChars00 ++ (fragment0296439Chars ++ (chunk0042SuffixChars00 ++ tail)) := by
    simp only [chunk0042Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 562) (SourceJson.white (chunk0042Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 562)
          (SourceJson.white (chunk0042LeadChars00 ++ (fragment0296439Chars ++ (chunk0042SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 562) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 561) (fragment0296439Chars ++ (chunk0042SuffixChars00 ++ tail))).bind
        (chunk0042AfterValue00 (fuel + 561) acc) := array_chunk0042_head fuel (chunk0042SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0296439Value, chunk0042SuffixChars00 ++ tail)).bind
        (chunk0042AfterValue00 (fuel + 561) acc) :=
      congrArg (fun result => result.bind (chunk0042AfterValue00 (fuel + 561) acc))
        (value_fragment0296439 (fuel + 139) (chunk0042SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 561) (SourceJson.white tail) (chunk0042Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0042_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0042Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0042Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 562) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 561) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0042Chars00 ++ (tail) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 562) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 562) (SourceJson.white (chunk0042Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 562) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 561) (SourceJson.white tail) (blockPush acc) := array_chunk0042 fuel (tail) (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 296433).take 1961 = blockChars := by rfl

theorem block_original_split : sourceRest 296433 = blockChars ++ sourceRest 298394 := by
  calc
    sourceRest 296433 = (sourceRest 296433).take 1961 ++ (sourceRest 296433).drop 1961 :=
      (List.take_append_drop 1961 (sourceRest 296433)).symm
    _ = blockChars ++ (sourceRest 296433).drop 1961 :=
      congrArg (fun part => part ++ (sourceRest 296433).drop 1961) block_original_prefix
    _ = blockChars ++ sourceRest 298394 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 296433 1961)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 562) (SourceJson.white (sourceRest 296433)) acc =
      SourceJson.array (fuel + 561) (SourceJson.white (sourceRest 298394)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 562) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 298394) acc)

#print axioms object_fragment0296439_field_000
#print axioms object_fragment0296439_field_001
#print axioms object_fragment0296439_field_002
#print axioms object_fragment0296439_field_003
#print axioms object_fragment0296439_field_004
#print axioms object_fragment0296439_field_005
#print axioms object_fragment0296439_field_006
#print axioms object_fragment0296439_field_007
#print axioms object_fragment0296439_field_008
#print axioms object_fragment0296439_field_009
#print axioms value_fragment0296439
#print axioms array_chunk0042_head
#print axioms array_chunk0042
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock021

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
