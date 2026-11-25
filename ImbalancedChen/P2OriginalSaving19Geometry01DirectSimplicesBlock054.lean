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

namespace SimplicesBlock054

noncomputable def fragment0407298Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0407298Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0407298Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '6'])
noncomputable def fragment0407298Acc00100 : List (String × SourceJson) := (fragment0407298Field000Key00, fragment0407298Field000Value00) :: fragment0407298Acc00000
noncomputable def fragment0407298Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '6', ',']

theorem object_fragment0407298_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 218) (SourceJson.white (fragment0407298Field000Chars00 ++ tail)) fragment0407298Acc00000 =
      SourceJson.object (fuel + 217) (SourceJson.white tail) fragment0407298Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_000"
  err.flush

noncomputable def fragment0407298Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0407298Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['7'])]
noncomputable def fragment0407298Acc00200 : List (String × SourceJson) := (fragment0407298Field001Key00, fragment0407298Field001Value00) :: fragment0407298Acc00100
noncomputable def fragment0407298Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0407298_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 217) (SourceJson.white (fragment0407298Field001Chars00 ++ tail)) fragment0407298Acc00100 =
      SourceJson.object (fuel + 216) (SourceJson.white tail) fragment0407298Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_001"
  err.flush

noncomputable def fragment0407298Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0407298Field002Value00 : SourceJson := .str (String.ofList ['3', '1', '3', '5', '6', '9', '9', '5', '8', '7', '9', '1', '8', '6', '1', '4', '0', '2', '6', '9', '5', '5', '8', '2', '2', '6', '6', '8', '7', '2', '3', '9', '4', '8', '3', '1', '6', '8', '2', '5', '9', '/', '4', '3', '8', '5', '4', '3', '1', '2', '6', '7', '7', '7', '2', '7', '9', '2', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0407298Acc00300 : List (String × SourceJson) := (fragment0407298Field002Key00, fragment0407298Field002Value00) :: fragment0407298Acc00200
noncomputable def fragment0407298Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '3', '1', '3', '5', '6', '9', '9', '5', '8', '7', '9', '1', '8', '6', '1', '4', '0', '2', '6', '9', '5', '5', '8', '2', '2', '6', '6', '8', '7', '2', '3', '9', '4', '8', '3', '1', '6', '8', '2', '5', '9', '/', '4', '3', '8', '5', '4', '3', '1', '2', '6', '7', '7', '7', '2', '7', '9', '2', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0407298_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 216) (SourceJson.white (fragment0407298Field002Chars00 ++ tail)) fragment0407298Acc00200 =
      SourceJson.object (fuel + 215) (SourceJson.white tail) fragment0407298Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_002"
  err.flush

noncomputable def fragment0407298Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0407298Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0407298Acc00400 : List (String × SourceJson) := (fragment0407298Field003Key00, fragment0407298Field003Value00) :: fragment0407298Acc00300
noncomputable def fragment0407298Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '8', '1', '9', '/', '5', '0', '0', '4', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0407298_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 215) (SourceJson.white (fragment0407298Field003Chars00 ++ tail)) fragment0407298Acc00300 =
      SourceJson.object (fuel + 214) (SourceJson.white tail) fragment0407298Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_003"
  err.flush

noncomputable def fragment0407298Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0407298Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '3', '1', '1', '7', '/', '7', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '0', '5', '/', '4', '4', '4', '8']), .str (String.ofList ['2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0407298Acc00500 : List (String × SourceJson) := (fragment0407298Field004Key00, fragment0407298Field004Value00) :: fragment0407298Acc00400
noncomputable def fragment0407298Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '4', '3', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '3', '1', '1', '7', '/', '7', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '6', '3', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '5', '/', '4', '4', '4', '8', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '4', '3', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0407298_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 214) (SourceJson.white (fragment0407298Field004Chars00 ++ tail)) fragment0407298Acc00400 =
      SourceJson.object (fuel + 213) (SourceJson.white tail) fragment0407298Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_004"
  err.flush

noncomputable def fragment0407298Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0407298Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '4', '3', '0', '2', '7', '5', '9', '3', '3', '9', '1', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '4', '4', '4', '0', '2', '5', '5', '8', '7', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '1', '4', '2', '3', '2', '3', '9', '3', '9', '7', '/', '5', '7', '0', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '9', '5', '0', '1', '9', '8', '2', '4', '9', '/', '3', '6', '9', '7', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '6', '0', '9', '6', '3', '0', '0', '9', '2', '7', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '8', '9', '8', '9', '3', '3', '6', '7', '1', '9', '/', '5', '7', '0', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '7', '8', '4', '0', '4', '2', '0', '9', '3', '9', '/', '7', '9', '8', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '6', '5', '5', '4', '0', '4', '3', '5', '1', '9', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '6', '5', '5', '1', '3', '8', '1', '3', '9', '1', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '9', '2', '9', '1', '1', '2', '8', '0', '9', '5', '9', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0407298Acc00600 : List (String × SourceJson) := (fragment0407298Field005Key00, fragment0407298Field005Value00) :: fragment0407298Acc00500
noncomputable def fragment0407298Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '0', '2', '7', '5', '9', '3', '3', '9', '1', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '3', '4', '4', '4', '0', '2', '5', '5', '8', '7', '/', '1', '9', '0', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '4', '1', '4', '2', '3', '2', '3', '9', '3', '9', '7', '/', '5', '7', '0', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '9', '5', '0', '1', '9', '8', '2', '4', '9', '/', '3', '6', '9', '7', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '0', '3', '6', '0', '9', '6', '3', '0', '0', '9', '2', '7', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '8', '9', '8', '9', '3', '3', '6', '7', '1', '9', '/', '5', '7', '0', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '7', '8', '4', '0', '4', '2', '0', '9', '3', '9', '/', '7', '9', '8', '6', '3', '8', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '6', '5', '5', '4', '0', '4', '3', '5', '1', '9', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '6', '5', '5', '1', '3', '8', '1', '3', '9', '1', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '9', '2', '9', '1', '1', '2', '8', '0', '9', '5', '9', '/', '3', '9', '9', '3', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0407298_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 213) (SourceJson.white (fragment0407298Field005Chars00 ++ tail)) fragment0407298Acc00500 =
      SourceJson.object (fuel + 212) (SourceJson.white tail) fragment0407298Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_005"
  err.flush

noncomputable def fragment0407298Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0407298Field006Value00 : SourceJson := .str (String.ofList ['3', '8', '9', '5', '2', '7', '3', '3', '8', '7', '9', '1', '4', '7', '5', '7', '5', '4', '5', '9', '6', '4', '5', '3', '1', '7', '3', '0', '9', '7', '2', '9', '5', '5', '4', '9', '9', '4', '9', '3', '2', '2', '1', '/', '4', '3', '9', '4', '0', '4', '1', '0', '1', '1', '6', '0', '0', '0', '6', '0', '7', '2', '0', '6', '4', '9', '6', '8', '1', '6', '6', '2', '2', '7', '1', '3', '1', '6', '3', '8', '1', '9', '9', '6', '6', '0', '6', '4', '3', '8', '9', '2', '9', '3', '2', '4', '5', '9', '9', '6', '0', '9', '3', '7', '5'])
noncomputable def fragment0407298Acc00700 : List (String × SourceJson) := (fragment0407298Field006Key00, fragment0407298Field006Value00) :: fragment0407298Acc00600
noncomputable def fragment0407298Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '8', '9', '5', '2', '7', '3', '3', '8', '7', '9', '1', '4', '7', '5', '7', '5', '4', '5', '9', '6', '4', '5', '3', '1', '7', '3', '0', '9', '7', '2', '9', '5', '5', '4', '9', '9', '4', '9', '3', '2', '2', '1', '/', '4', '3', '9', '4', '0', '4', '1', '0', '1', '1', '6', '0', '0', '0', '6', '0', '7', '2', '0', '6', '4', '9', '6', '8', '1', '6', '6', '2', '2', '7', '1', '3', '1', '6', '3', '8', '1', '9', '9', '6', '6', '0', '6', '4', '3', '8', '9', '2', '9', '3', '2', '4', '5', '9', '9', '6', '0', '9', '3', '7', '5', '"', ',']

theorem object_fragment0407298_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 212) (SourceJson.white (fragment0407298Field006Chars00 ++ tail)) fragment0407298Acc00600 =
      SourceJson.object (fuel + 211) (SourceJson.white tail) fragment0407298Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_006"
  err.flush

noncomputable def fragment0407298Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0407298Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '9', '5', '2', '7', '4', '7', '5', '8', '4', '8', '1', '2', '1', '6', '8', '4', '2', '6', '1', '4', '2', '3', '0', '7', '8', '1', '9', '6', '8', '6', '2', '0', '9', '8', '8', '9', '4', '9', '4', '6', '2', '0', '5', '8', '9', '8', '3', '9', '8', '1', '3', '2', '9', '5', '6', '3', '2', '6', '1', '6', '2', '3', '5', '9', '4', '7', '5', '5', '8', '6', '1', '8', '8', '3', '2', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '2', '1', '9', '1', '9', '0', '2', '0', '8', '8', '5', '1', '0', '8', '7', '8', '4', '9', '3', '8', '4', '9', '7', '5', '1', '7', '4', '1', '0', '9', '2', '6', '0', '3', '3', '4', '4', '5', '3', '6', '7', '1', '5', '7', '4', '8', '9', '6', '4', '8', '9', '4', '8', '3', '4', '5', '0', '7', '6', '5', '1', '5', '4', '0', '2', '4', '7', '2', '5', '0', '4', '2', '8', '4', '4', '8', '0', '4', '3', '3', '1', '2', '6', '8', '0', '9', '1', '2', '9', '8', '9', '4', '7', '9', '3', '6', '5', '2', '1', '7', '8', '1', '9', '4', '1', '0', '4', '0', '2', '1'])
noncomputable def fragment0407298Acc00800 : List (String × SourceJson) := (fragment0407298Field007Key00, fragment0407298Field007Value00) :: fragment0407298Acc00700
noncomputable def fragment0407298Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '9', '5', '2', '7', '4', '7', '5', '8', '4', '8', '1', '2', '1', '6', '8', '4', '2', '6', '1', '4', '2', '3', '0', '7', '8', '1', '9', '6', '8', '6', '2', '0', '9', '8', '8', '9', '4', '9', '4', '6', '2', '0', '5', '8', '9', '8', '3', '9', '8', '1', '3', '2', '9', '5', '6', '3', '2', '6', '1', '6', '2', '3', '5', '9', '4', '7', '5', '5', '8', '6', '1', '8', '8', '3', '2', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '3', '2', '1', '9', '1', '9', '0', '2', '0', '8', '8', '5', '1', '0', '8', '7', '8', '4', '9', '3', '8', '4', '9', '7', '5', '1', '7', '4', '1', '0', '9', '2', '6', '0', '3', '3', '4', '4', '5', '3', '6', '7', '1', '5', '7', '4', '8', '9', '6', '4', '8', '9', '4', '8', '3', '4', '5', '0', '7', '6', '5', '1', '5', '4', '0', '2', '4', '7', '2', '5', '0', '4', '2', '8', '4', '4', '8', '0', '4', '3', '3', '1', '2', '6', '8', '0', '9', '1', '2', '9', '8', '9', '4', '7', '9', '3', '6', '5', '2', '1', '7', '8', '1', '9', '4', '1', '0', '4', '0', '2', '1', '"', ',']

theorem object_fragment0407298_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0407298Field007Chars00 ++ tail)) fragment0407298Acc00700 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0407298Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_007"
  err.flush

noncomputable def fragment0407298Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0407298Field008Value00 : SourceJson := .str (String.ofList ['7', '0', '2', '3', '4', '9', '7', '3', '2', '7', '4'])
noncomputable def fragment0407298Acc00900 : List (String × SourceJson) := (fragment0407298Field008Key00, fragment0407298Field008Value00) :: fragment0407298Acc00800
noncomputable def fragment0407298Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '7', '0', '2', '3', '4', '9', '7', '3', '2', '7', '4', '"', ',']

theorem object_fragment0407298_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0407298Field008Chars00 ++ tail)) fragment0407298Acc00800 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0407298Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_008"
  err.flush

noncomputable def fragment0407298Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0407298Field009Value00 : SourceJson := .str (String.ofList ['4', '0', '4', '3', '2', '5', '0', '3', '9', '9', '1', '4'])
noncomputable def fragment0407298Acc01000 : List (String × SourceJson) := (fragment0407298Field009Key00, fragment0407298Field009Value00) :: fragment0407298Acc00900
noncomputable def fragment0407298Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '4', '0', '4', '3', '2', '5', '0', '3', '9', '9', '1', '4', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0407298_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0407298Field009Chars00 ++ tail)) fragment0407298Acc00900 =
      .ok (.obj (fragment0407298Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0407298_object_field_009"
  err.flush

noncomputable def fragment0407298Chars : List Char := '{' :: (fragment0407298Field000Chars00 ++ fragment0407298Field001Chars00 ++ fragment0407298Field002Chars00 ++ fragment0407298Field003Chars00 ++ fragment0407298Field004Chars00 ++ fragment0407298Field005Chars00 ++ fragment0407298Field006Chars00 ++ fragment0407298Field007Chars00 ++ fragment0407298Field008Chars00 ++ fragment0407298Field009Chars00)
noncomputable def fragment0407298Value : SourceJson := .obj (fragment0407298Acc01000.reverse)

theorem value_fragment0407298 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 219) (fragment0407298Chars ++ tail) =
      .ok (fragment0407298Value, tail) := by
  have hinput : fragment0407298Chars ++ tail = '{' :: (fragment0407298Field000Chars00 ++ (fragment0407298Field001Chars00 ++ (fragment0407298Field002Chars00 ++ (fragment0407298Field003Chars00 ++ (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0407298Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 219) (fragment0407298Chars ++ tail) =
        SourceJson.value (fuel + 219) ('{' :: (fragment0407298Field000Chars00 ++ (fragment0407298Field001Chars00 ++ (fragment0407298Field002Chars00 ++ (fragment0407298Field003Chars00 ++ (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 219)) hinput
    _ = SourceJson.object (fuel + 218) (SourceJson.white (fragment0407298Field000Chars00 ++ (fragment0407298Field001Chars00 ++ (fragment0407298Field002Chars00 ++ (fragment0407298Field003Chars00 ++ (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))))))))))) fragment0407298Acc00000 := by rfl
    _ = SourceJson.object (fuel + 217) (SourceJson.white (fragment0407298Field001Chars00 ++ (fragment0407298Field002Chars00 ++ (fragment0407298Field003Chars00 ++ (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail))))))))))) fragment0407298Acc00100 := object_fragment0407298_field_000 fuel (fragment0407298Field001Chars00 ++ (fragment0407298Field002Chars00 ++ (fragment0407298Field003Chars00 ++ (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 216) (SourceJson.white (fragment0407298Field002Chars00 ++ (fragment0407298Field003Chars00 ++ (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))))))))) fragment0407298Acc00200 := object_fragment0407298_field_001 fuel (fragment0407298Field002Chars00 ++ (fragment0407298Field003Chars00 ++ (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 215) (SourceJson.white (fragment0407298Field003Chars00 ++ (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail))))))))) fragment0407298Acc00300 := object_fragment0407298_field_002 fuel (fragment0407298Field003Chars00 ++ (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 214) (SourceJson.white (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))))))) fragment0407298Acc00400 := object_fragment0407298_field_003 fuel (fragment0407298Field004Chars00 ++ (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 213) (SourceJson.white (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail))))))) fragment0407298Acc00500 := object_fragment0407298_field_004 fuel (fragment0407298Field005Chars00 ++ (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 212) (SourceJson.white (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))))) fragment0407298Acc00600 := object_fragment0407298_field_005 fuel (fragment0407298Field006Chars00 ++ (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail))))) fragment0407298Acc00700 := object_fragment0407298_field_006 fuel (fragment0407298Field007Chars00 ++ (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))) fragment0407298Acc00800 := object_fragment0407298_field_007 fuel (fragment0407298Field008Chars00 ++ (fragment0407298Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0407298Field009Chars00 ++ (tail))) fragment0407298Acc00900 := object_fragment0407298_field_008 fuel (fragment0407298Field009Chars00 ++ (tail))
    _ = .ok (fragment0407298Value, tail) := object_fragment0407298_field_009 fuel (tail)

noncomputable def fragment0408854Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0408854Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0408854Field000Value00 : SourceJson := .number (String.ofList ['1', '0', '7'])
noncomputable def fragment0408854Acc00100 : List (String × SourceJson) := (fragment0408854Field000Key00, fragment0408854Field000Value00) :: fragment0408854Acc00000
noncomputable def fragment0408854Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '0', '7', ',']

theorem object_fragment0408854_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0408854Field000Chars00 ++ tail)) fragment0408854Acc00000 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0408854Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_000"
  err.flush

noncomputable def fragment0408854Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0408854Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '7']), .number (String.ofList ['3', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0408854Acc00200 : List (String × SourceJson) := (fragment0408854Field001Key00, fragment0408854Field001Value00) :: fragment0408854Acc00100
noncomputable def fragment0408854Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0408854_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0408854Field001Chars00 ++ tail)) fragment0408854Acc00100 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0408854Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_001"
  err.flush

noncomputable def fragment0408854Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0408854Field002Value00 : SourceJson := .str (String.ofList ['1', '5', '0', '4', '5', '7', '2', '5', '7', '8', '6', '2', '5', '6', '4', '7', '4', '6', '5', '5', '8', '4', '4', '4', '0', '2', '7', '3', '0', '2', '4', '4', '3', '/', '4', '7', '6', '2', '8', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0408854Acc00300 : List (String × SourceJson) := (fragment0408854Field002Key00, fragment0408854Field002Value00) :: fragment0408854Acc00200
noncomputable def fragment0408854Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '5', '0', '4', '5', '7', '2', '5', '7', '8', '6', '2', '5', '6', '4', '7', '4', '6', '5', '5', '8', '4', '4', '4', '0', '2', '7', '3', '0', '2', '4', '4', '3', '/', '4', '7', '6', '2', '8', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0408854_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0408854Field002Chars00 ++ tail)) fragment0408854Acc00200 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0408854Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_002"
  err.flush

noncomputable def fragment0408854Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0408854Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0408854Acc00400 : List (String × SourceJson) := (fragment0408854Field003Key00, fragment0408854Field003Value00) :: fragment0408854Acc00300
noncomputable def fragment0408854Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0408854_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0408854Field003Chars00 ++ tail)) fragment0408854Acc00300 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0408854Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_003"
  err.flush

noncomputable def fragment0408854Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0408854Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0408854Acc00500 : List (String × SourceJson) := (fragment0408854Field004Key00, fragment0408854Field004Value00) :: fragment0408854Acc00400
noncomputable def fragment0408854Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0408854_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0408854Field004Chars00 ++ tail)) fragment0408854Acc00400 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0408854Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_004"
  err.flush

noncomputable def fragment0408854Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0408854Field005Value00 : SourceJson := .arr [.str (String.ofList ['6', '5', '6', '7', '8', '6', '2', '8', '1', '8', '1', '9', '/', '7', '0', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '3', '9', '1', '7', '0', '7', '8', '9', '4', '7', '/', '7', '0', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '9', '7', '9', '6', '1', '3', '2', '7', '9', '/', '1', '6', '2', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '6', '1', '0', '8', '4', '7', '4', '7', '5', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '6', '8', '6', '4', '8', '3', '9', '9', '/', '4', '9', '7', '9', '5', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '5', '8', '4', '1', '2', '1', '0', '8', '5', '7', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '3', '5', '0', '0', '3', '7', '1', '3', '2', '9', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '0', '2', '4', '7', '0', '8', '7', '0', '5', '3', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '1', '3', '4', '7', '9', '5', '3', '5', '2', '9', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '1', '3', '4', '5', '1', '3', '1', '8', '0', '1', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0408854Acc00600 : List (String × SourceJson) := (fragment0408854Field005Key00, fragment0408854Field005Value00) :: fragment0408854Acc00500
noncomputable def fragment0408854Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '5', '6', '7', '8', '6', '2', '8', '1', '8', '1', '9', '/', '7', '0', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '6', '3', '9', '1', '7', '0', '7', '8', '9', '4', '7', '/', '7', '0', '5', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '3', '6', '9', '7', '9', '6', '1', '3', '2', '7', '9', '/', '1', '6', '2', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '6', '1', '0', '8', '4', '7', '4', '7', '5', '7', '/', '1', '0', '5', '8', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '8', '6', '4', '8', '3', '9', '9', '/', '4', '9', '7', '9', '5', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '9', '5', '8', '4', '1', '2', '1', '0', '8', '5', '7', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '3', '5', '0', '0', '3', '7', '1', '3', '2', '9', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '7', '0', '2', '4', '7', '0', '8', '7', '0', '5', '3', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '1', '3', '4', '7', '9', '5', '3', '5', '2', '9', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '1', '1', '3', '4', '5', '1', '3', '1', '8', '0', '1', '/', '2', '1', '1', '6', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0408854_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0408854Field005Chars00 ++ tail)) fragment0408854Acc00500 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0408854Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_005"
  err.flush

noncomputable def fragment0408854Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0408854Field006Value00 : SourceJson := .str (String.ofList ['1', '4', '3', '3', '6', '5', '0', '8', '8', '0', '9', '0', '0', '8', '8', '8', '6', '2', '6', '3', '5', '5', '1', '3', '0', '4', '1', '0', '6', '6', '9', '2', '4', '0', '8', '6', '1', '8', '1', '2', '0', '7', '0', '4', '0', '0', '0', '0', '/', '9', '6', '4', '0', '7', '4', '8', '1', '8', '9', '3', '0', '8', '9', '6', '7', '2', '4', '3', '0', '7', '9', '3', '0', '5', '8', '6', '9', '3', '6', '8', '8', '7', '3', '7', '9', '9', '3', '0', '2', '7', '8', '8', '0', '1', '0', '1', '1', '7', '1', '1', '2', '2', '7', '1', '4', '9', '6', '7', '0', '9', '7'])
noncomputable def fragment0408854Acc00700 : List (String × SourceJson) := (fragment0408854Field006Key00, fragment0408854Field006Value00) :: fragment0408854Acc00600
noncomputable def fragment0408854Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '4', '3', '3', '6', '5', '0', '8', '8', '0', '9', '0', '0', '8', '8', '8', '6', '2', '6', '3', '5', '5', '1', '3', '0', '4', '1', '0', '6', '6', '9', '2', '4', '0', '8', '6', '1', '8', '1', '2', '0', '7', '0', '4', '0', '0', '0', '0', '/', '9', '6', '4', '0', '7', '4', '8', '1', '8', '9', '3', '0', '8', '9', '6', '7', '2', '4', '3', '0', '7', '9', '3', '0', '5', '8', '6', '9', '3', '6', '8', '8', '7', '3', '7', '9', '9', '3', '0', '2', '7', '8', '8', '0', '1', '0', '1', '1', '7', '1', '1', '2', '2', '7', '1', '4', '9', '6', '7', '0', '9', '7', '"', ',']

theorem object_fragment0408854_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0408854Field006Chars00 ++ tail)) fragment0408854Acc00600 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0408854Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_006"
  err.flush

noncomputable def fragment0408854Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0408854Field007Value00 : SourceJson := .str (String.ofList ['1', '2', '8', '5', '8', '1', '3', '2', '7', '5', '7', '4', '9', '7', '8', '7', '3', '6', '6', '8', '5', '9', '6', '0', '1', '3', '1', '9', '0', '5', '0', '3', '5', '3', '2', '7', '8', '0', '1', '9', '9', '8', '9', '9', '5', '3', '0', '5', '8', '4', '2', '0', '1', '1', '8', '3', '3', '6', '6', '4', '6', '0', '1', '3', '7', '0', '4', '0', '9', '7', '3', '3', '1', '9', '8', '4', '8', '5', '3', '6', '5', '4', '0', '1', '8', '4', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '6', '0', '0', '6', '8', '4', '6', '4', '6', '3', '4', '8', '6', '9', '3', '8', '0', '2', '6', '8', '0', '0', '1', '8', '3', '5', '2', '5', '0', '7', '5', '1', '4', '7', '3', '9', '9', '6', '5', '0', '6', '6', '1', '9', '3', '0', '2', '5', '4', '8', '4', '4', '9', '1', '8', '5', '3', '0', '8', '5', '8', '7', '0', '7', '3', '8', '5', '2', '0', '9', '8', '2', '7', '7', '7', '4', '4', '4', '4', '8', '9', '9', '1', '6', '3', '0', '9', '5', '5', '5', '2', '9', '3', '4', '5', '8', '7', '3', '3', '4', '1', '8', '0', '7', '3', '8', '4', '5', '1', '5', '1', '4', '8', '1'])
noncomputable def fragment0408854Acc00800 : List (String × SourceJson) := (fragment0408854Field007Key00, fragment0408854Field007Value00) :: fragment0408854Acc00700
noncomputable def fragment0408854Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '8', '5', '8', '1', '3', '2', '7', '5', '7', '4', '9', '7', '8', '7', '3', '6', '6', '8', '5', '9', '6', '0', '1', '3', '1', '9', '0', '5', '0', '3', '5', '3', '2', '7', '8', '0', '1', '9', '9', '8', '9', '9', '5', '3', '0', '5', '8', '4', '2', '0', '1', '1', '8', '3', '3', '6', '6', '4', '6', '0', '1', '3', '7', '0', '4', '0', '9', '7', '3', '3', '1', '9', '8', '4', '8', '5', '3', '6', '5', '4', '0', '1', '8', '4', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '6', '0', '0', '6', '8', '4', '6', '4', '6', '3', '4', '8', '6', '9', '3', '8', '0', '2', '6', '8', '0', '0', '1', '8', '3', '5', '2', '5', '0', '7', '5', '1', '4', '7', '3', '9', '9', '6', '5', '0', '6', '6', '1', '9', '3', '0', '2', '5', '4', '8', '4', '4', '9', '1', '8', '5', '3', '0', '8', '5', '8', '7', '0', '7', '3', '8', '5', '2', '0', '9', '8', '2', '7', '7', '7', '4', '4', '4', '4', '8', '9', '9', '1', '6', '3', '0', '9', '5', '5', '5', '2', '9', '3', '4', '5', '8', '7', '3', '3', '4', '1', '8', '0', '7', '3', '8', '4', '5', '1', '5', '1', '4', '8', '1', '"', ',']

theorem object_fragment0408854_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0408854Field007Chars00 ++ tail)) fragment0408854Acc00700 =
      SourceJson.object (fuel + 223) (SourceJson.white tail) fragment0408854Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_007"
  err.flush

noncomputable def fragment0408854Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0408854Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '8', '1', '8', '1', '6', '3', '8', '5', '0', '2', '8', '4'])
noncomputable def fragment0408854Acc00900 : List (String × SourceJson) := (fragment0408854Field008Key00, fragment0408854Field008Value00) :: fragment0408854Acc00800
noncomputable def fragment0408854Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '7', '8', '1', '8', '1', '6', '3', '8', '5', '0', '2', '8', '4', '"', ',']

theorem object_fragment0408854_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 223) (SourceJson.white (fragment0408854Field008Chars00 ++ tail)) fragment0408854Acc00800 =
      SourceJson.object (fuel + 222) (SourceJson.white tail) fragment0408854Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_008"
  err.flush

noncomputable def fragment0408854Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0408854Field009Value00 : SourceJson := .str (String.ofList ['9', '4', '6', '7', '6', '5', '5', '6', '6', '6', '7', '7', '6', '4', '3'])
noncomputable def fragment0408854Acc01000 : List (String × SourceJson) := (fragment0408854Field009Key00, fragment0408854Field009Value00) :: fragment0408854Acc00900
noncomputable def fragment0408854Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '4', '6', '7', '6', '5', '5', '6', '6', '6', '7', '7', '6', '4', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0408854_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 222) (SourceJson.white (fragment0408854Field009Chars00 ++ tail)) fragment0408854Acc00900 =
      .ok (.obj (fragment0408854Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0408854_object_field_009"
  err.flush

noncomputable def fragment0408854Chars : List Char := '{' :: (fragment0408854Field000Chars00 ++ fragment0408854Field001Chars00 ++ fragment0408854Field002Chars00 ++ fragment0408854Field003Chars00 ++ fragment0408854Field004Chars00 ++ fragment0408854Field005Chars00 ++ fragment0408854Field006Chars00 ++ fragment0408854Field007Chars00 ++ fragment0408854Field008Chars00 ++ fragment0408854Field009Chars00)
noncomputable def fragment0408854Value : SourceJson := .obj (fragment0408854Acc01000.reverse)

theorem value_fragment0408854 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 232) (fragment0408854Chars ++ tail) =
      .ok (fragment0408854Value, tail) := by
  have hinput : fragment0408854Chars ++ tail = '{' :: (fragment0408854Field000Chars00 ++ (fragment0408854Field001Chars00 ++ (fragment0408854Field002Chars00 ++ (fragment0408854Field003Chars00 ++ (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0408854Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 232) (fragment0408854Chars ++ tail) =
        SourceJson.value (fuel + 232) ('{' :: (fragment0408854Field000Chars00 ++ (fragment0408854Field001Chars00 ++ (fragment0408854Field002Chars00 ++ (fragment0408854Field003Chars00 ++ (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 232)) hinput
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0408854Field000Chars00 ++ (fragment0408854Field001Chars00 ++ (fragment0408854Field002Chars00 ++ (fragment0408854Field003Chars00 ++ (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))))))))))) fragment0408854Acc00000 := by rfl
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0408854Field001Chars00 ++ (fragment0408854Field002Chars00 ++ (fragment0408854Field003Chars00 ++ (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail))))))))))) fragment0408854Acc00100 := object_fragment0408854_field_000 fuel (fragment0408854Field001Chars00 ++ (fragment0408854Field002Chars00 ++ (fragment0408854Field003Chars00 ++ (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0408854Field002Chars00 ++ (fragment0408854Field003Chars00 ++ (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))))))))) fragment0408854Acc00200 := object_fragment0408854_field_001 fuel (fragment0408854Field002Chars00 ++ (fragment0408854Field003Chars00 ++ (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0408854Field003Chars00 ++ (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail))))))))) fragment0408854Acc00300 := object_fragment0408854_field_002 fuel (fragment0408854Field003Chars00 ++ (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))))))) fragment0408854Acc00400 := object_fragment0408854_field_003 fuel (fragment0408854Field004Chars00 ++ (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail))))))) fragment0408854Acc00500 := object_fragment0408854_field_004 fuel (fragment0408854Field005Chars00 ++ (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))))) fragment0408854Acc00600 := object_fragment0408854_field_005 fuel (fragment0408854Field006Chars00 ++ (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail))))) fragment0408854Acc00700 := object_fragment0408854_field_006 fuel (fragment0408854Field007Chars00 ++ (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 223) (SourceJson.white (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))) fragment0408854Acc00800 := object_fragment0408854_field_007 fuel (fragment0408854Field008Chars00 ++ (fragment0408854Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 222) (SourceJson.white (fragment0408854Field009Chars00 ++ (tail))) fragment0408854Acc00900 := object_fragment0408854_field_008 fuel (fragment0408854Field009Chars00 ++ (tail))
    _ = .ok (fragment0408854Value, tail) := object_fragment0408854_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0106_before_reader"
  err.flush

noncomputable def chunk0106LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0106SuffixChars00 : List Char := [',']
noncomputable def chunk0106Chars00 : List Char := chunk0106LeadChars00 ++ fragment0407298Chars ++ chunk0106SuffixChars00
noncomputable def chunk0106Push00 (acc : List SourceJson) : List SourceJson := fragment0407298Value :: acc

noncomputable def chunk0106AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0106_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 498)
      (SourceJson.white (chunk0106LeadChars00 ++ (fragment0407298Chars ++ rest))) acc =
      (SourceJson.value (fuel + 497) (fragment0407298Chars ++ rest)).bind
        (chunk0106AfterValue00 (fuel + 497) acc) := by rfl

theorem array_chunk0106 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 498) (SourceJson.white (chunk0106Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 497) (SourceJson.white tail) (chunk0106Push00 acc) := by
  have hinput : chunk0106Chars00 ++ tail = chunk0106LeadChars00 ++ (fragment0407298Chars ++ (chunk0106SuffixChars00 ++ tail)) := by
    simp only [chunk0106Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 498) (SourceJson.white (chunk0106Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 498)
          (SourceJson.white (chunk0106LeadChars00 ++ (fragment0407298Chars ++ (chunk0106SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 498) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 497) (fragment0407298Chars ++ (chunk0106SuffixChars00 ++ tail))).bind
        (chunk0106AfterValue00 (fuel + 497) acc) := array_chunk0106_head fuel (chunk0106SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0407298Value, chunk0106SuffixChars00 ++ tail)).bind
        (chunk0106AfterValue00 (fuel + 497) acc) :=
      congrArg (fun result => result.bind (chunk0106AfterValue00 (fuel + 497) acc))
        (value_fragment0407298 (fuel + 278) (chunk0106SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 497) (SourceJson.white tail) (chunk0106Push00 acc) := by rfl

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
noncomputable def chunk0107Chars00 : List Char := chunk0107LeadChars00 ++ fragment0408854Chars ++ chunk0107SuffixChars00
noncomputable def chunk0107Push00 (acc : List SourceJson) : List SourceJson := fragment0408854Value :: acc

noncomputable def chunk0107AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0107_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 497)
      (SourceJson.white (chunk0107LeadChars00 ++ (fragment0408854Chars ++ rest))) acc =
      (SourceJson.value (fuel + 496) (fragment0408854Chars ++ rest)).bind
        (chunk0107AfterValue00 (fuel + 496) acc) := by rfl

theorem array_chunk0107 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 497) (SourceJson.white (chunk0107Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 496) (SourceJson.white tail) (chunk0107Push00 acc) := by
  have hinput : chunk0107Chars00 ++ tail = chunk0107LeadChars00 ++ (fragment0408854Chars ++ (chunk0107SuffixChars00 ++ tail)) := by
    simp only [chunk0107Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 497) (SourceJson.white (chunk0107Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 497)
          (SourceJson.white (chunk0107LeadChars00 ++ (fragment0408854Chars ++ (chunk0107SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 497) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 496) (fragment0408854Chars ++ (chunk0107SuffixChars00 ++ tail))).bind
        (chunk0107AfterValue00 (fuel + 496) acc) := array_chunk0107_head fuel (chunk0107SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0408854Value, chunk0107SuffixChars00 ++ tail)).bind
        (chunk0107AfterValue00 (fuel + 496) acc) :=
      congrArg (fun result => result.bind (chunk0107AfterValue00 (fuel + 496) acc))
        (value_fragment0408854 (fuel + 264) (chunk0107SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 496) (SourceJson.white tail) (chunk0107Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0107_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0106Chars00 ++ chunk0107Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0107Push00 (chunk0106Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 498) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 496) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0106Chars00 ++ (chunk0107Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 498) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 498) (SourceJson.white (chunk0106Chars00 ++ (chunk0107Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 498) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 497) (SourceJson.white (chunk0107Chars00 ++ (tail))) (chunk0106Push00 (acc)) := array_chunk0106 fuel (chunk0107Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 496) (SourceJson.white tail) (blockPush acc) := array_chunk0107 fuel (tail) (chunk0106Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 407292).take 3124 = blockChars := by rfl

theorem block_original_split : sourceRest 407292 = blockChars ++ sourceRest 410416 := by
  calc
    sourceRest 407292 = (sourceRest 407292).take 3124 ++ (sourceRest 407292).drop 3124 :=
      (List.take_append_drop 3124 (sourceRest 407292)).symm
    _ = blockChars ++ (sourceRest 407292).drop 3124 :=
      congrArg (fun part => part ++ (sourceRest 407292).drop 3124) block_original_prefix
    _ = blockChars ++ sourceRest 410416 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 407292 3124)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 498) (SourceJson.white (sourceRest 407292)) acc =
      SourceJson.array (fuel + 496) (SourceJson.white (sourceRest 410416)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 498) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 410416) acc)

#print axioms object_fragment0407298_field_000
#print axioms object_fragment0407298_field_001
#print axioms object_fragment0407298_field_002
#print axioms object_fragment0407298_field_003
#print axioms object_fragment0407298_field_004
#print axioms object_fragment0407298_field_005
#print axioms object_fragment0407298_field_006
#print axioms object_fragment0407298_field_007
#print axioms object_fragment0407298_field_008
#print axioms object_fragment0407298_field_009
#print axioms value_fragment0407298
#print axioms object_fragment0408854_field_000
#print axioms object_fragment0408854_field_001
#print axioms object_fragment0408854_field_002
#print axioms object_fragment0408854_field_003
#print axioms object_fragment0408854_field_004
#print axioms object_fragment0408854_field_005
#print axioms object_fragment0408854_field_006
#print axioms object_fragment0408854_field_007
#print axioms object_fragment0408854_field_008
#print axioms object_fragment0408854_field_009
#print axioms value_fragment0408854
#print axioms array_chunk0106_head
#print axioms array_chunk0106
#print axioms array_chunk0107_head
#print axioms array_chunk0107
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock054

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
