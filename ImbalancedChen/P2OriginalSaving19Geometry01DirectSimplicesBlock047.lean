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

namespace SimplicesBlock047

noncomputable def fragment0384476Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0384476Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0384476Field000Value00 : SourceJson := .number (String.ofList ['9', '3'])
noncomputable def fragment0384476Acc00100 : List (String × SourceJson) := (fragment0384476Field000Key00, fragment0384476Field000Value00) :: fragment0384476Acc00000
noncomputable def fragment0384476Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '9', '3', ',']

theorem object_fragment0384476_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 509) (SourceJson.white (fragment0384476Field000Chars00 ++ tail)) fragment0384476Acc00000 =
      SourceJson.object (fuel + 508) (SourceJson.white tail) fragment0384476Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_000"
  err.flush

noncomputable def fragment0384476Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0384476Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0384476Acc00200 : List (String × SourceJson) := (fragment0384476Field001Key00, fragment0384476Field001Value00) :: fragment0384476Acc00100
noncomputable def fragment0384476Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0384476_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 508) (SourceJson.white (fragment0384476Field001Chars00 ++ tail)) fragment0384476Acc00100 =
      SourceJson.object (fuel + 507) (SourceJson.white tail) fragment0384476Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_001"
  err.flush

noncomputable def fragment0384476Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0384476Field002Value00 : SourceJson := .str (String.ofList ['1', '4', '6', '4', '5', '9', '4', '2', '9', '7', '9', '4', '0', '9', '6', '7', '3', '1', '6', '7', '5', '1', '8', '5', '9', '9', '5', '8', '7', '5', '5', '1', '0', '9', '5', '3', '7', '3', '6', '0', '5', '7', '6', '1', '/', '5', '0', '7', '9', '9', '5', '1', '4', '6', '0', '6', '5', '8', '5', '2', '2', '0', '4', '3', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0384476Acc00300 : List (String × SourceJson) := (fragment0384476Field002Key00, fragment0384476Field002Value00) :: fragment0384476Acc00200
noncomputable def fragment0384476Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '4', '6', '4', '5', '9', '4', '2', '9', '7', '9', '4', '0', '9', '6', '7', '3', '1', '6', '7', '5', '1', '8', '5', '9', '9', '5', '8', '7', '5', '5', '1', '0', '9', '5', '3', '7', '3', '6', '0', '5', '7', '6', '1', '/', '5', '0', '7', '9', '9', '5', '1', '4', '6', '0', '6', '5', '8', '5', '2', '2', '0', '4', '3', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0384476_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 507) (SourceJson.white (fragment0384476Field002Chars00 ++ tail)) fragment0384476Acc00200 =
      SourceJson.object (fuel + 506) (SourceJson.white tail) fragment0384476Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_002"
  err.flush

noncomputable def fragment0384476Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0384476Field003Value00 : SourceJson := .str (String.ofList ['8', '9', '9', '1', '5', '3', '1', '1', '3', '/', '1', '1', '1', '0', '1', '9', '3', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0384476Acc00400 : List (String × SourceJson) := (fragment0384476Field003Key00, fragment0384476Field003Value00) :: fragment0384476Acc00300
noncomputable def fragment0384476Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '8', '9', '9', '1', '5', '3', '1', '1', '3', '/', '1', '1', '1', '0', '1', '9', '3', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0384476_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 506) (SourceJson.white (fragment0384476Field003Chars00 ++ tail)) fragment0384476Acc00300 =
      SourceJson.object (fuel + 505) (SourceJson.white tail) fragment0384476Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_003"
  err.flush

noncomputable def fragment0384476Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0384476Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['9', '5', '7', '/', '2', '0', '8', '6', '4'])]
noncomputable def fragment0384476Acc00500 : List (String × SourceJson) := (fragment0384476Field004Key00, fragment0384476Field004Value00) :: fragment0384476Acc00400
noncomputable def fragment0384476Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '9', '8', '4', '4', '4', '3', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '7', '/', '2', '0', '8', '6', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0384476_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 505) (SourceJson.white (fragment0384476Field004Chars00 ++ tail)) fragment0384476Acc00400 =
      SourceJson.object (fuel + 504) (SourceJson.white tail) fragment0384476Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_004"
  err.flush

noncomputable def fragment0384476Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0384476Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '5', '2', '2', '6', '1', '8', '3', '4', '2', '0', '1', '4', '3', '2', '1', '9', '8', '9', '2', '6', '8', '3', '4', '7', '/', '4', '3', '6', '6', '1', '5', '1', '0', '6', '1', '2', '5', '1', '5', '7', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '3', '4', '6', '9', '1', '8', '7', '1', '2', '3', '5', '1', '3', '3', '1', '2', '0', '9', '1', '0', '8', '1', '1', '1', '/', '7', '1', '3', '1', '3', '8', '0', '0', '6', '6', '7', '1', '0', '8', '9', '9', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '4', '0', '8', '7', '6', '2', '1', '7', '4', '4', '7', '1', '7', '0', '6', '8', '6', '7', '8', '3', '3', '0', '6', '1', '1', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '8', '2', '2', '9', '0', '0', '3', '0', '2', '9', '9', '0', '9', '3', '6', '5', '6', '9', '7', '4', '4', '7', '6', '9', '7', '/', '3', '2', '0', '9', '1', '2', '1', '0', '3', '0', '0', '1', '9', '9', '0', '4', '7', '7', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '3', '6', '0', '1', '1', '8', '1', '9', '9', '5', '7', '7', '9', '6', '8', '5', '4', '0', '8', '9', '4', '9', '9', '4', '1', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '4', '0', '3', '6', '4', '3', '7', '8', '1', '8', '2', '1', '0', '2', '5', '8', '3', '0', '7', '0', '0', '5', '8', '3', '3', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '2', '1', '6', '2', '5', '1', '3', '9', '5', '8', '6', '6', '5', '2', '4', '5', '1', '7', '7', '0', '5', '1', '/', '6', '7', '5', '6', '0', '4', '4', '2', '7', '3', '7', '2', '6', '1', '1', '5', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '9', '8', '5', '6', '6', '1', '1', '7', '5', '4', '7', '5', '4', '0', '9', '3', '0', '9', '8', '5', '2', '8', '7', '3', '/', '1', '2', '8', '3', '6', '4', '8', '4', '1', '2', '0', '0', '7', '9', '6', '1', '9', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '5', '5', '1', '3', '2', '4', '9', '2', '1', '3', '8', '5', '1', '3', '3', '9', '3', '9', '4', '5', '8', '4', '0', '9', '/', '2', '1', '3', '9', '4', '1', '4', '0', '2', '0', '0', '1', '3', '2', '6', '9', '8', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '0', '2', '6', '3', '5', '5', '1', '5', '9', '9', '0', '3', '5', '2', '3', '7', '5', '7', '9', '5', '3', '3', '3', '3', '/', '7', '1', '3', '1', '3', '8', '0', '0', '6', '6', '7', '1', '0', '8', '9', '9', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0384476Acc00600 : List (String × SourceJson) := (fragment0384476Field005Key00, fragment0384476Field005Value00) :: fragment0384476Acc00500
noncomputable def fragment0384476Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '5', '2', '2', '6', '1', '8', '3', '4', '2', '0', '1', '4', '3', '2', '1', '9', '8', '9', '2', '6', '8', '3', '4', '7', '/', '4', '3', '6', '6', '1', '5', '1', '0', '6', '1', '2', '5', '1', '5', '7', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '8', '3', '4', '6', '9', '1', '8', '7', '1', '2', '3', '5', '1', '3', '3', '1', '2', '0', '9', '1', '0', '8', '1', '1', '1', '/', '7', '1', '3', '1', '3', '8', '0', '0', '6', '6', '7', '1', '0', '8', '9', '9', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '3', '4', '0', '8', '7', '6', '2', '1', '7', '4', '4', '7', '1', '7', '0', '6', '8', '6', '7', '8', '3', '3', '0', '6', '1', '1', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '8', '2', '2', '9', '0', '0', '3', '0', '2', '9', '9', '0', '9', '3', '6', '5', '6', '9', '7', '4', '4', '7', '6', '9', '7', '/', '3', '2', '0', '9', '1', '2', '1', '0', '3', '0', '0', '1', '9', '9', '0', '4', '7', '7', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '3', '6', '0', '1', '1', '8', '1', '9', '9', '5', '7', '7', '9', '6', '8', '5', '4', '0', '8', '9', '4', '9', '9', '4', '1', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '4', '0', '3', '6', '4', '3', '7', '8', '1', '8', '2', '1', '0', '2', '5', '8', '3', '0', '7', '0', '0', '5', '8', '3', '3', '/', '6', '4', '1', '8', '2', '4', '2', '0', '6', '0', '0', '3', '9', '8', '0', '9', '5', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '7', '2', '1', '6', '2', '5', '1', '3', '9', '5', '8', '6', '6', '5', '2', '4', '5', '1', '7', '7', '0', '5', '1', '/', '6', '7', '5', '6', '0', '4', '4', '2', '7', '3', '7', '2', '6', '1', '1', '5', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '9', '8', '5', '6', '6', '1', '1', '7', '5', '4', '7', '5', '4', '0', '9', '3', '0', '9', '8', '5', '2', '8', '7', '3', '/', '1', '2', '8', '3', '6', '4', '8', '4', '1', '2', '0', '0', '7', '9', '6', '1', '9', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '5', '5', '5', '1', '3', '2', '4', '9', '2', '1', '3', '8', '5', '1', '3', '3', '9', '3', '9', '4', '5', '8', '4', '0', '9', '/', '2', '1', '3', '9', '4', '1', '4', '0', '2', '0', '0', '1', '3', '2', '6', '9', '8', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '0', '2', '6', '3', '5', '5', '1', '5', '9', '9', '0', '3', '5', '2', '3', '7', '5', '7', '9', '5', '3', '3', '3', '3', '/', '7', '1', '3', '1', '3', '8', '0', '0', '6', '6', '7', '1', '0', '8', '9', '9', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0384476_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 504) (SourceJson.white (fragment0384476Field005Chars00 ++ tail)) fragment0384476Acc00500 =
      SourceJson.object (fuel + 503) (SourceJson.white tail) fragment0384476Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_005"
  err.flush

noncomputable def fragment0384476Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0384476Field006Value00 : SourceJson := .str (String.ofList ['2', '6', '4', '2', '0', '4', '5', '4', '3', '6', '5', '4', '0', '5', '2', '9', '6', '6', '1', '3', '6', '9', '1', '6', '2', '4', '9', '3', '7', '0', '2', '2', '3', '6', '1', '7', '8', '4', '0', '5', '0', '1', '9', '2', '9', '2', '8', '6', '7', '0', '0', '8', '/', '1', '3', '8', '6', '2', '7', '7', '4', '4', '3', '5', '0', '8', '1', '8', '5', '2', '7', '1', '3', '2', '1', '1', '8', '4', '7', '5', '1', '4', '8', '4', '9', '1', '0', '7', '9', '2', '8', '7', '5', '6', '0', '5', '7', '4', '1', '5', '0', '6', '6', '3', '1', '6', '4', '7', '9', '3', '0', '1', '8', '7', '3', '4', '8', '7', '5'])
noncomputable def fragment0384476Acc00700 : List (String × SourceJson) := (fragment0384476Field006Key00, fragment0384476Field006Value00) :: fragment0384476Acc00600
noncomputable def fragment0384476Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '6', '4', '2', '0', '4', '5', '4', '3', '6', '5', '4', '0', '5', '2', '9', '6', '6', '1', '3', '6', '9', '1', '6', '2', '4', '9', '3', '7', '0', '2', '2', '3', '6', '1', '7', '8', '4', '0', '5', '0', '1', '9', '2', '9', '2', '8', '6', '7', '0', '0', '8', '/', '1', '3', '8', '6', '2', '7', '7', '4', '4', '3', '5', '0', '8', '1', '8', '5', '2', '7', '1', '3', '2', '1', '1', '8', '4', '7', '5', '1', '4', '8', '4', '9', '1', '0', '7', '9', '2', '8', '7', '5', '6', '0', '5', '7', '4', '1', '5', '0', '6', '6', '3', '1', '6', '4', '7', '9', '3', '0', '1', '8', '7', '3', '4', '8', '7', '5', '"', ',']

theorem object_fragment0384476_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 503) (SourceJson.white (fragment0384476Field006Chars00 ++ tail)) fragment0384476Acc00600 =
      SourceJson.object (fuel + 502) (SourceJson.white tail) fragment0384476Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_006"
  err.flush

noncomputable def fragment0384476Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0384476Field007Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '7', '2', '0', '4', '6', '7', '5', '9', '4', '3', '2', '2', '7', '5', '3', '0', '1', '3', '8', '7', '3', '4', '4', '7', '3', '3', '8', '4', '6', '1', '3', '2', '4', '0', '8', '3', '6', '2', '7', '9', '0', '6', '0', '8', '0', '5', '1', '2', '6', '1', '2', '0', '8', '6', '1', '0', '0', '7', '6', '8', '8', '4', '5', '1', '6', '6', '8', '4', '9', '4', '3', '1', '3', '5', '7', '8', '4', '9', '8', '3', '5', '0', '5', '2', '0', '0', '9', '0', '8', '1', '5', '6', '8', '9', '8', '5', '9', '9', '5', '3', '6', '3', '9', '5', '0', '2', '9', '2', '3', '4', '1', '2', '8', '2', '1', '3', '9', '7', '4', '6', '4', '4', '4', '8', '9', '2', '7', '3', '7', '4', '8', '3', '9', '8', '6', '1', '6', '7', '0', '0', '8', '3', '3', '1', '4', '1', '8', '2', '2', '4', '2', '0', '3', '1', '1', '5', '1', '1', '2', '9', '8', '1', '2', '5', '6', '5', '9', '4', '0', '1', '3', '7', '7', '8', '1', '7', '0', '2', '0', '7', '4', '5', '6', '3', '2', '8', '0', '9', '2', '3', '8', '0', '0', '9', '4', '4', '0', '5', '0', '3', '1', '2', '4', '6', '1', '9', '9', '0', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '0', '3', '6', '3', '0', '9', '3', '5', '7', '1', '2', '7', '5', '3', '2', '9', '9', '0', '2', '6', '8', '1', '3', '4', '9', '0', '1', '1', '2', '1', '6', '4', '1', '9', '5', '1', '9', '8', '0', '9', '4', '4', '1', '9', '2', '5', '0', '4', '7', '7', '3', '3', '2', '7', '1', '8', '2', '0', '7', '8', '1', '1', '5', '9', '2', '9', '2', '6', '2', '5', '8', '6', '6', '5', '8', '9', '6', '8', '6', '5', '5', '2', '5', '6', '7', '3', '7', '8', '5', '2', '7', '4', '5', '3', '3', '0', '0', '7', '2', '5', '2', '2', '9', '4', '2', '5', '8', '3', '6', '5', '4', '0', '2', '0', '5', '6', '2', '7', '5', '2', '3', '2', '5', '3', '7', '7', '2', '0', '8', '4', '9', '6', '7', '0', '2', '4', '8', '1', '1', '4', '4', '9', '9', '0', '8', '2', '7', '9', '7', '3', '8', '0', '7', '5', '8', '2', '4', '7', '4', '0', '9', '1', '1', '6', '4', '6', '1', '7', '2', '0', '7', '4', '2', '2', '3', '4', '2', '4', '2', '7', '7', '7', '6', '2', '7', '5', '3', '4', '4', '7', '6', '2', '6', '3', '5', '8', '9', '7', '5', '5', '0', '5', '9', '8', '1', '5', '7', '9', '5', '8', '3', '1', '6', '1', '0', '4', '8', '7', '5', '9', '5', '9', '9', '8', '1', '0', '0', '2', '0', '8', '1', '7', '0', '8', '0', '4', '8', '3', '1', '6', '9', '8', '5', '6', '0', '8', '2', '9', '1', '5', '8', '9', '5', '9'])
noncomputable def fragment0384476Acc00800 : List (String × SourceJson) := (fragment0384476Field007Key00, fragment0384476Field007Value00) :: fragment0384476Acc00700
noncomputable def fragment0384476Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '0', '8', '7', '2', '0', '4', '6', '7', '5', '9', '4', '3', '2', '2', '7', '5', '3', '0', '1', '3', '8', '7', '3', '4', '4', '7', '3', '3', '8', '4', '6', '1', '3', '2', '4', '0', '8', '3', '6', '2', '7', '9', '0', '6', '0', '8', '0', '5', '1', '2', '6', '1', '2', '0', '8', '6', '1', '0', '0', '7', '6', '8', '8', '4', '5', '1', '6', '6', '8', '4', '9', '4', '3', '1', '3', '5', '7', '8', '4', '9', '8', '3', '5', '0', '5', '2', '0', '0', '9', '0', '8', '1', '5', '6', '8', '9', '8', '5', '9', '9', '5', '3', '6', '3', '9', '5', '0', '2', '9', '2', '3', '4', '1', '2', '8', '2', '1', '3', '9', '7', '4', '6', '4', '4', '4', '8', '9', '2', '7', '3', '7', '4', '8', '3', '9', '8', '6', '1', '6', '7', '0', '0', '8', '3', '3', '1', '4', '1', '8', '2', '2', '4', '2', '0', '3', '1', '1', '5', '1', '1', '2', '9', '8', '1', '2', '5', '6', '5', '9', '4', '0', '1', '3', '7', '7', '8', '1', '7', '0', '2', '0', '7', '4', '5', '6', '3', '2', '8', '0', '9', '2', '3', '8', '0', '0', '9', '4', '4', '0', '5', '0', '3', '1', '2', '4', '6', '1', '9', '9', '0', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '0', '3', '6', '3', '0', '9', '3', '5', '7', '1', '2', '7', '5', '3', '2', '9', '9', '0', '2', '6', '8', '1', '3', '4', '9', '0', '1', '1', '2', '1', '6', '4', '1', '9', '5', '1', '9', '8', '0', '9', '4', '4', '1', '9', '2', '5', '0', '4', '7', '7', '3', '3', '2', '7', '1', '8', '2', '0', '7', '8', '1', '1', '5', '9', '2', '9', '2', '6', '2', '5', '8', '6', '6', '5', '8', '9', '6', '8', '6', '5', '5', '2', '5', '6', '7', '3', '7', '8', '5', '2', '7', '4', '5', '3', '3', '0', '0', '7', '2', '5', '2', '2', '9', '4', '2', '5', '8', '3', '6', '5', '4', '0', '2', '0', '5', '6', '2', '7', '5', '2', '3', '2', '5', '3', '7', '7', '2', '0', '8', '4', '9', '6', '7', '0', '2', '4', '8', '1', '1', '4', '4', '9', '9', '0', '8', '2', '7', '9', '7', '3', '8', '0', '7', '5', '8', '2', '4', '7', '4', '0', '9', '1', '1', '6', '4', '6', '1', '7', '2', '0', '7', '4', '2', '2', '3', '4', '2', '4', '2', '7', '7', '7', '6', '2', '7', '5', '3', '4', '4', '7', '6', '2', '6', '3', '5', '8', '9', '7', '5', '5', '0', '5', '9', '8', '1', '5', '7', '9', '5', '8', '3', '1', '6', '1', '0', '4', '8', '7', '5', '9', '5', '9', '9', '8', '1', '0', '0', '2', '0', '8', '1', '7', '0', '8', '0', '4', '8', '3', '1', '6', '9', '8', '5', '6', '0', '8', '2', '9', '1', '5', '8', '9', '5', '9', '"', ',']

theorem object_fragment0384476_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 502) (SourceJson.white (fragment0384476Field007Chars00 ++ tail)) fragment0384476Acc00700 =
      SourceJson.object (fuel + 501) (SourceJson.white tail) fragment0384476Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_007"
  err.flush

noncomputable def fragment0384476Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0384476Field008Value00 : SourceJson := .str (String.ofList ['1', '5', '0', '9', '9', '7', '4', '8', '3', '3', '6', '5', '6', '5', '0', '3'])
noncomputable def fragment0384476Acc00900 : List (String × SourceJson) := (fragment0384476Field008Key00, fragment0384476Field008Value00) :: fragment0384476Acc00800
noncomputable def fragment0384476Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '5', '0', '9', '9', '7', '4', '8', '3', '3', '6', '5', '6', '5', '0', '3', '"', ',']

theorem object_fragment0384476_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 501) (SourceJson.white (fragment0384476Field008Chars00 ++ tail)) fragment0384476Acc00800 =
      SourceJson.object (fuel + 500) (SourceJson.white tail) fragment0384476Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_008"
  err.flush

noncomputable def fragment0384476Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0384476Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '7', '1', '8', '5', '0', '5', '8', '3', '6', '9', '4', '8', '8', '5', '0'])
noncomputable def fragment0384476Acc01000 : List (String × SourceJson) := (fragment0384476Field009Key00, fragment0384476Field009Value00) :: fragment0384476Acc00900
noncomputable def fragment0384476Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '7', '1', '8', '5', '0', '5', '8', '3', '6', '9', '4', '8', '8', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0384476_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 500) (SourceJson.white (fragment0384476Field009Chars00 ++ tail)) fragment0384476Acc00900 =
      .ok (.obj (fragment0384476Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0384476_object_field_009"
  err.flush

noncomputable def fragment0384476Chars : List Char := '{' :: (fragment0384476Field000Chars00 ++ fragment0384476Field001Chars00 ++ fragment0384476Field002Chars00 ++ fragment0384476Field003Chars00 ++ fragment0384476Field004Chars00 ++ fragment0384476Field005Chars00 ++ fragment0384476Field006Chars00 ++ fragment0384476Field007Chars00 ++ fragment0384476Field008Chars00 ++ fragment0384476Field009Chars00)
noncomputable def fragment0384476Value : SourceJson := .obj (fragment0384476Acc01000.reverse)

theorem value_fragment0384476 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 510) (fragment0384476Chars ++ tail) =
      .ok (fragment0384476Value, tail) := by
  have hinput : fragment0384476Chars ++ tail = '{' :: (fragment0384476Field000Chars00 ++ (fragment0384476Field001Chars00 ++ (fragment0384476Field002Chars00 ++ (fragment0384476Field003Chars00 ++ (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0384476Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 510) (fragment0384476Chars ++ tail) =
        SourceJson.value (fuel + 510) ('{' :: (fragment0384476Field000Chars00 ++ (fragment0384476Field001Chars00 ++ (fragment0384476Field002Chars00 ++ (fragment0384476Field003Chars00 ++ (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 510)) hinput
    _ = SourceJson.object (fuel + 509) (SourceJson.white (fragment0384476Field000Chars00 ++ (fragment0384476Field001Chars00 ++ (fragment0384476Field002Chars00 ++ (fragment0384476Field003Chars00 ++ (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))))))))))) fragment0384476Acc00000 := by rfl
    _ = SourceJson.object (fuel + 508) (SourceJson.white (fragment0384476Field001Chars00 ++ (fragment0384476Field002Chars00 ++ (fragment0384476Field003Chars00 ++ (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail))))))))))) fragment0384476Acc00100 := object_fragment0384476_field_000 fuel (fragment0384476Field001Chars00 ++ (fragment0384476Field002Chars00 ++ (fragment0384476Field003Chars00 ++ (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 507) (SourceJson.white (fragment0384476Field002Chars00 ++ (fragment0384476Field003Chars00 ++ (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))))))))) fragment0384476Acc00200 := object_fragment0384476_field_001 fuel (fragment0384476Field002Chars00 ++ (fragment0384476Field003Chars00 ++ (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 506) (SourceJson.white (fragment0384476Field003Chars00 ++ (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail))))))))) fragment0384476Acc00300 := object_fragment0384476_field_002 fuel (fragment0384476Field003Chars00 ++ (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 505) (SourceJson.white (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))))))) fragment0384476Acc00400 := object_fragment0384476_field_003 fuel (fragment0384476Field004Chars00 ++ (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 504) (SourceJson.white (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail))))))) fragment0384476Acc00500 := object_fragment0384476_field_004 fuel (fragment0384476Field005Chars00 ++ (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 503) (SourceJson.white (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))))) fragment0384476Acc00600 := object_fragment0384476_field_005 fuel (fragment0384476Field006Chars00 ++ (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 502) (SourceJson.white (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail))))) fragment0384476Acc00700 := object_fragment0384476_field_006 fuel (fragment0384476Field007Chars00 ++ (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 501) (SourceJson.white (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))) fragment0384476Acc00800 := object_fragment0384476_field_007 fuel (fragment0384476Field008Chars00 ++ (fragment0384476Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 500) (SourceJson.white (fragment0384476Field009Chars00 ++ (tail))) fragment0384476Acc00900 := object_fragment0384476_field_008 fuel (fragment0384476Field009Chars00 ++ (tail))
    _ = .ok (fragment0384476Value, tail) := object_fragment0384476_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0093_before_reader"
  err.flush

noncomputable def chunk0093LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0093SuffixChars00 : List Char := [',']
noncomputable def chunk0093Chars00 : List Char := chunk0093LeadChars00 ++ fragment0384476Chars ++ chunk0093SuffixChars00
noncomputable def chunk0093Push00 (acc : List SourceJson) : List SourceJson := fragment0384476Value :: acc

noncomputable def chunk0093AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0093_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 511)
      (SourceJson.white (chunk0093LeadChars00 ++ (fragment0384476Chars ++ rest))) acc =
      (SourceJson.value (fuel + 510) (fragment0384476Chars ++ rest)).bind
        (chunk0093AfterValue00 (fuel + 510) acc) := by rfl

theorem array_chunk0093 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 511) (SourceJson.white (chunk0093Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 510) (SourceJson.white tail) (chunk0093Push00 acc) := by
  have hinput : chunk0093Chars00 ++ tail = chunk0093LeadChars00 ++ (fragment0384476Chars ++ (chunk0093SuffixChars00 ++ tail)) := by
    simp only [chunk0093Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 511) (SourceJson.white (chunk0093Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 511)
          (SourceJson.white (chunk0093LeadChars00 ++ (fragment0384476Chars ++ (chunk0093SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 511) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 510) (fragment0384476Chars ++ (chunk0093SuffixChars00 ++ tail))).bind
        (chunk0093AfterValue00 (fuel + 510) acc) := array_chunk0093_head fuel (chunk0093SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0384476Value, chunk0093SuffixChars00 ++ tail)).bind
        (chunk0093AfterValue00 (fuel + 510) acc) :=
      congrArg (fun result => result.bind (chunk0093AfterValue00 (fuel + 510) acc))
        (value_fragment0384476 (fuel + 0) (chunk0093SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 510) (SourceJson.white tail) (chunk0093Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0093_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0093Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0093Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 511) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 510) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0093Chars00 ++ (tail) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 511) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 511) (SourceJson.white (chunk0093Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 511) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 510) (SourceJson.white tail) (blockPush acc) := array_chunk0093 fuel (tail) (acc)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 384470).take 2164 = blockChars := by rfl

theorem block_original_split : sourceRest 384470 = blockChars ++ sourceRest 386634 := by
  calc
    sourceRest 384470 = (sourceRest 384470).take 2164 ++ (sourceRest 384470).drop 2164 :=
      (List.take_append_drop 2164 (sourceRest 384470)).symm
    _ = blockChars ++ (sourceRest 384470).drop 2164 :=
      congrArg (fun part => part ++ (sourceRest 384470).drop 2164) block_original_prefix
    _ = blockChars ++ sourceRest 386634 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 384470 2164)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 511) (SourceJson.white (sourceRest 384470)) acc =
      SourceJson.array (fuel + 510) (SourceJson.white (sourceRest 386634)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 511) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 386634) acc)

#print axioms object_fragment0384476_field_000
#print axioms object_fragment0384476_field_001
#print axioms object_fragment0384476_field_002
#print axioms object_fragment0384476_field_003
#print axioms object_fragment0384476_field_004
#print axioms object_fragment0384476_field_005
#print axioms object_fragment0384476_field_006
#print axioms object_fragment0384476_field_007
#print axioms object_fragment0384476_field_008
#print axioms object_fragment0384476_field_009
#print axioms value_fragment0384476
#print axioms array_chunk0093_head
#print axioms array_chunk0093
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock047

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
