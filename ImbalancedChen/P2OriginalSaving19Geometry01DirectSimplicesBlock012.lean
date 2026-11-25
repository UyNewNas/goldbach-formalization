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

namespace SimplicesBlock012

noncomputable def fragment0266572Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0266572Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0266572Field000Value00 : SourceJson := .number (String.ofList ['2', '4'])
noncomputable def fragment0266572Acc00100 : List (String × SourceJson) := (fragment0266572Field000Key00, fragment0266572Field000Value00) :: fragment0266572Acc00000
noncomputable def fragment0266572Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '4', ',']

theorem object_fragment0266572_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0266572Field000Chars00 ++ tail)) fragment0266572Acc00000 =
      SourceJson.object (fuel + 200) (SourceJson.white tail) fragment0266572Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_000"
  err.flush

noncomputable def fragment0266572Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0266572Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0266572Acc00200 : List (String × SourceJson) := (fragment0266572Field001Key00, fragment0266572Field001Value00) :: fragment0266572Acc00100
noncomputable def fragment0266572Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0266572_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 200) (SourceJson.white (fragment0266572Field001Chars00 ++ tail)) fragment0266572Acc00100 =
      SourceJson.object (fuel + 199) (SourceJson.white tail) fragment0266572Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_001"
  err.flush

noncomputable def fragment0266572Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0266572Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '1', '9', '9', '4', '0', '2', '1', '4', '9', '0', '0', '2', '0', '7', '6', '7', '9', '1', '6', '9', '0', '5', '7', '6', '2', '4', '7', '0', '5', '1', '3', '2', '8', '7', '2', '4', '4', '9', '/', '6', '4', '2', '3', '7', '3', '5', '4', '3', '5', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0266572Acc00300 : List (String × SourceJson) := (fragment0266572Field002Key00, fragment0266572Field002Value00) :: fragment0266572Acc00200
noncomputable def fragment0266572Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '1', '9', '9', '4', '0', '2', '1', '4', '9', '0', '0', '2', '0', '7', '6', '7', '9', '1', '6', '9', '0', '5', '7', '6', '2', '4', '7', '0', '5', '1', '3', '2', '8', '7', '2', '4', '4', '9', '/', '6', '4', '2', '3', '7', '3', '5', '4', '3', '5', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0266572_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 199) (SourceJson.white (fragment0266572Field002Chars00 ++ tail)) fragment0266572Acc00200 =
      SourceJson.object (fuel + 198) (SourceJson.white tail) fragment0266572Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_002"
  err.flush

noncomputable def fragment0266572Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0266572Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0266572Acc00400 : List (String × SourceJson) := (fragment0266572Field003Key00, fragment0266572Field003Value00) :: fragment0266572Acc00300
noncomputable def fragment0266572Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0266572_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 198) (SourceJson.white (fragment0266572Field003Chars00 ++ tail)) fragment0266572Acc00300 =
      SourceJson.object (fuel + 197) (SourceJson.white tail) fragment0266572Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_003"
  err.flush

noncomputable def fragment0266572Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0266572Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0266572Acc00500 : List (String × SourceJson) := (fragment0266572Field004Key00, fragment0266572Field004Value00) :: fragment0266572Acc00400
noncomputable def fragment0266572Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '2', '3', '3', '7', '7', '1', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0266572_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 197) (SourceJson.white (fragment0266572Field004Chars00 ++ tail)) fragment0266572Acc00400 =
      SourceJson.object (fuel + 196) (SourceJson.white tail) fragment0266572Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_004"
  err.flush

noncomputable def fragment0266572Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0266572Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '7', '7', '4', '1', '9', '6', '5', '7', '1', '/', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '9', '1', '4', '2', '8', '7', '6', '7', '7', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '3', '0', '3', '4', '5', '3', '5', '7', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '8', '4', '5', '1', '8', '9', '4', '0', '1', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '8', '3', '2', '3', '7', '9', '5', '1', '1', '/', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '1', '7', '1', '7', '2', '0', '4', '7', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '1', '5', '2', '5', '9', '1', '4', '3', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '1', '4', '4', '9', '5', '6', '6', '7', '1', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '8', '1', '6', '3', '1', '3', '1', '7', '/', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '0', '3', '7', '4', '6', '3', '7', '8', '9', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0266572Acc00600 : List (String × SourceJson) := (fragment0266572Field005Key00, fragment0266572Field005Value00) :: fragment0266572Acc00500
noncomputable def fragment0266572Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '7', '4', '1', '9', '6', '5', '7', '1', '/', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '9', '1', '4', '2', '8', '7', '6', '7', '7', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '7', '3', '0', '3', '4', '5', '3', '5', '7', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '0', '8', '4', '5', '1', '8', '9', '4', '0', '1', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '8', '3', '2', '3', '7', '9', '5', '1', '1', '/', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '6', '1', '7', '1', '7', '2', '0', '4', '7', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '7', '1', '5', '2', '5', '9', '1', '4', '3', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '1', '4', '4', '9', '5', '6', '6', '7', '1', '/', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '8', '1', '6', '3', '1', '3', '1', '7', '/', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '0', '3', '7', '4', '6', '3', '7', '8', '9', '/', '1', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0266572_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 196) (SourceJson.white (fragment0266572Field005Chars00 ++ tail)) fragment0266572Acc00500 =
      SourceJson.object (fuel + 195) (SourceJson.white tail) fragment0266572Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_005"
  err.flush

noncomputable def fragment0266572Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0266572Field006Value00 : SourceJson := .str (String.ofList ['1', '9', '5', '2', '5', '2', '3', '4', '4', '7', '7', '6', '5', '2', '7', '8', '9', '3', '5', '2', '4', '6', '9', '9', '0', '8', '4', '5', '8', '1', '9', '5', '8', '3', '6', '2', '2', '1', '2', '2', '9', '6', '9', '3', '4', '4', '3', '7', '5', '0', '/', '1', '1', '8', '0', '7', '1', '7', '9', '3', '9', '1', '6', '1', '1', '2', '2', '9', '2', '8', '6', '1', '2', '6', '4', '0', '2', '5', '7', '4', '9', '3', '0', '1', '9', '5', '0', '9', '5', '1', '3', '2', '7', '7', '1', '9', '9', '3', '0', '8', '5', '7', '4', '7', '3', '4', '9', '9', '0', '8', '0', '0', '2', '6', '4', '9'])
noncomputable def fragment0266572Acc00700 : List (String × SourceJson) := (fragment0266572Field006Key00, fragment0266572Field006Value00) :: fragment0266572Acc00600
noncomputable def fragment0266572Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '9', '5', '2', '5', '2', '3', '4', '4', '7', '7', '6', '5', '2', '7', '8', '9', '3', '5', '2', '4', '6', '9', '9', '0', '8', '4', '5', '8', '1', '9', '5', '8', '3', '6', '2', '2', '1', '2', '2', '9', '6', '9', '3', '4', '4', '3', '7', '5', '0', '/', '1', '1', '8', '0', '7', '1', '7', '9', '3', '9', '1', '6', '1', '1', '2', '2', '9', '2', '8', '6', '1', '2', '6', '4', '0', '2', '5', '7', '4', '9', '3', '0', '1', '9', '5', '0', '9', '5', '1', '3', '2', '7', '7', '1', '9', '9', '3', '0', '8', '5', '7', '4', '7', '3', '4', '9', '9', '0', '8', '0', '0', '2', '6', '4', '9', '"', ',']

theorem object_fragment0266572_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 195) (SourceJson.white (fragment0266572Field006Chars00 ++ tail)) fragment0266572Acc00600 =
      SourceJson.object (fuel + 194) (SourceJson.white tail) fragment0266572Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_006"
  err.flush

noncomputable def fragment0266572Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0266572Field007Value00 : SourceJson := .str (String.ofList ['4', '6', '4', '2', '9', '3', '4', '8', '6', '1', '6', '8', '1', '2', '5', '9', '8', '8', '5', '1', '1', '6', '3', '5', '3', '4', '8', '9', '0', '4', '3', '4', '3', '3', '6', '9', '5', '6', '1', '3', '5', '4', '3', '5', '5', '5', '5', '0', '7', '9', '2', '8', '6', '1', '3', '6', '8', '9', '6', '4', '8', '7', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '1', '9', '7', '3', '9', '3', '5', '1', '0', '5', '8', '0', '3', '1', '5', '4', '3', '8', '3', '6', '6', '0', '3', '5', '5', '0', '5', '9', '7', '1', '1', '1', '5', '1', '6', '9', '8', '9', '1', '5', '8', '2', '6', '8', '9', '1', '6', '1', '4', '6', '4', '5', '1', '6', '6', '6', '2', '8', '5', '5', '0', '9', '4', '6', '5', '2', '5', '1', '0', '7', '6', '0', '9', '0', '9', '1', '7', '6', '3', '0', '6', '0', '6', '3', '9', '9', '3', '9', '2', '3', '8', '1', '7', '0', '5', '9', '7', '8', '4', '9'])
noncomputable def fragment0266572Acc00800 : List (String × SourceJson) := (fragment0266572Field007Key00, fragment0266572Field007Value00) :: fragment0266572Acc00700
noncomputable def fragment0266572Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '6', '4', '2', '9', '3', '4', '8', '6', '1', '6', '8', '1', '2', '5', '9', '8', '8', '5', '1', '1', '6', '3', '5', '3', '4', '8', '9', '0', '4', '3', '4', '3', '3', '6', '9', '5', '6', '1', '3', '5', '4', '3', '5', '5', '5', '5', '0', '7', '9', '2', '8', '6', '1', '3', '6', '8', '9', '6', '4', '8', '7', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '1', '9', '7', '3', '9', '3', '5', '1', '0', '5', '8', '0', '3', '1', '5', '4', '3', '8', '3', '6', '6', '0', '3', '5', '5', '0', '5', '9', '7', '1', '1', '1', '5', '1', '6', '9', '8', '9', '1', '5', '8', '2', '6', '8', '9', '1', '6', '1', '4', '6', '4', '5', '1', '6', '6', '6', '2', '8', '5', '5', '0', '9', '4', '6', '5', '2', '5', '1', '0', '7', '6', '0', '9', '0', '9', '1', '7', '6', '3', '0', '6', '0', '6', '3', '9', '9', '3', '9', '2', '3', '8', '1', '7', '0', '5', '9', '7', '8', '4', '9', '"', ',']

theorem object_fragment0266572_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 194) (SourceJson.white (fragment0266572Field007Chars00 ++ tail)) fragment0266572Acc00700 =
      SourceJson.object (fuel + 193) (SourceJson.white tail) fragment0266572Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_007"
  err.flush

noncomputable def fragment0266572Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0266572Field008Value00 : SourceJson := .str (String.ofList ['1', '3', '1', '0', '1', '7', '6', '1', '2', '1', '6', '7', '7', '0', '1'])
noncomputable def fragment0266572Acc00900 : List (String × SourceJson) := (fragment0266572Field008Key00, fragment0266572Field008Value00) :: fragment0266572Acc00800
noncomputable def fragment0266572Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '1', '0', '1', '7', '6', '1', '2', '1', '6', '7', '7', '0', '1', '"', ',']

theorem object_fragment0266572_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 193) (SourceJson.white (fragment0266572Field008Chars00 ++ tail)) fragment0266572Acc00800 =
      SourceJson.object (fuel + 192) (SourceJson.white tail) fragment0266572Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_008"
  err.flush

noncomputable def fragment0266572Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0266572Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '1', '6', '2', '3', '6', '7', '0', '1', '2', '8', '8', '7', '4', '1'])
noncomputable def fragment0266572Acc01000 : List (String × SourceJson) := (fragment0266572Field009Key00, fragment0266572Field009Value00) :: fragment0266572Acc00900
noncomputable def fragment0266572Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '1', '6', '2', '3', '6', '7', '0', '1', '2', '8', '8', '7', '4', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0266572_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 192) (SourceJson.white (fragment0266572Field009Chars00 ++ tail)) fragment0266572Acc00900 =
      .ok (.obj (fragment0266572Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0266572_object_field_009"
  err.flush

noncomputable def fragment0266572Chars : List Char := '{' :: (fragment0266572Field000Chars00 ++ fragment0266572Field001Chars00 ++ fragment0266572Field002Chars00 ++ fragment0266572Field003Chars00 ++ fragment0266572Field004Chars00 ++ fragment0266572Field005Chars00 ++ fragment0266572Field006Chars00 ++ fragment0266572Field007Chars00 ++ fragment0266572Field008Chars00 ++ fragment0266572Field009Chars00)
noncomputable def fragment0266572Value : SourceJson := .obj (fragment0266572Acc01000.reverse)

theorem value_fragment0266572 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 202) (fragment0266572Chars ++ tail) =
      .ok (fragment0266572Value, tail) := by
  have hinput : fragment0266572Chars ++ tail = '{' :: (fragment0266572Field000Chars00 ++ (fragment0266572Field001Chars00 ++ (fragment0266572Field002Chars00 ++ (fragment0266572Field003Chars00 ++ (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0266572Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 202) (fragment0266572Chars ++ tail) =
        SourceJson.value (fuel + 202) ('{' :: (fragment0266572Field000Chars00 ++ (fragment0266572Field001Chars00 ++ (fragment0266572Field002Chars00 ++ (fragment0266572Field003Chars00 ++ (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 202)) hinput
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0266572Field000Chars00 ++ (fragment0266572Field001Chars00 ++ (fragment0266572Field002Chars00 ++ (fragment0266572Field003Chars00 ++ (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))))))))))) fragment0266572Acc00000 := by rfl
    _ = SourceJson.object (fuel + 200) (SourceJson.white (fragment0266572Field001Chars00 ++ (fragment0266572Field002Chars00 ++ (fragment0266572Field003Chars00 ++ (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail))))))))))) fragment0266572Acc00100 := object_fragment0266572_field_000 fuel (fragment0266572Field001Chars00 ++ (fragment0266572Field002Chars00 ++ (fragment0266572Field003Chars00 ++ (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 199) (SourceJson.white (fragment0266572Field002Chars00 ++ (fragment0266572Field003Chars00 ++ (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))))))))) fragment0266572Acc00200 := object_fragment0266572_field_001 fuel (fragment0266572Field002Chars00 ++ (fragment0266572Field003Chars00 ++ (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 198) (SourceJson.white (fragment0266572Field003Chars00 ++ (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail))))))))) fragment0266572Acc00300 := object_fragment0266572_field_002 fuel (fragment0266572Field003Chars00 ++ (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 197) (SourceJson.white (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))))))) fragment0266572Acc00400 := object_fragment0266572_field_003 fuel (fragment0266572Field004Chars00 ++ (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 196) (SourceJson.white (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail))))))) fragment0266572Acc00500 := object_fragment0266572_field_004 fuel (fragment0266572Field005Chars00 ++ (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 195) (SourceJson.white (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))))) fragment0266572Acc00600 := object_fragment0266572_field_005 fuel (fragment0266572Field006Chars00 ++ (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 194) (SourceJson.white (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail))))) fragment0266572Acc00700 := object_fragment0266572_field_006 fuel (fragment0266572Field007Chars00 ++ (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 193) (SourceJson.white (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))) fragment0266572Acc00800 := object_fragment0266572_field_007 fuel (fragment0266572Field008Chars00 ++ (fragment0266572Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 192) (SourceJson.white (fragment0266572Field009Chars00 ++ (tail))) fragment0266572Acc00900 := object_fragment0266572_field_008 fuel (fragment0266572Field009Chars00 ++ (tail))
    _ = .ok (fragment0266572Value, tail) := object_fragment0266572_field_009 fuel (tail)

noncomputable def fragment0268103Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0268103Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0268103Field000Value00 : SourceJson := .number (String.ofList ['2', '5'])
noncomputable def fragment0268103Acc00100 : List (String × SourceJson) := (fragment0268103Field000Key00, fragment0268103Field000Value00) :: fragment0268103Acc00000
noncomputable def fragment0268103Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '2', '5', ',']

theorem object_fragment0268103_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0268103Field000Chars00 ++ tail)) fragment0268103Acc00000 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0268103Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_000"
  err.flush

noncomputable def fragment0268103Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0268103Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '2']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0268103Acc00200 : List (String × SourceJson) := (fragment0268103Field001Key00, fragment0268103Field001Value00) :: fragment0268103Acc00100
noncomputable def fragment0268103Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0268103_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0268103Field001Chars00 ++ tail)) fragment0268103Acc00100 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0268103Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_001"
  err.flush

noncomputable def fragment0268103Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0268103Field002Value00 : SourceJson := .str (String.ofList ['4', '3', '5', '1', '3', '7', '6', '8', '1', '9', '9', '9', '8', '7', '0', '6', '0', '3', '3', '4', '6', '4', '0', '9', '4', '2', '2', '4', '3', '7', '1', '1', '0', '1', '1', '5', '9', '3', '6', '9', '/', '1', '9', '2', '2', '3', '6', '2', '3', '0', '8', '0', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0268103Acc00300 : List (String × SourceJson) := (fragment0268103Field002Key00, fragment0268103Field002Value00) :: fragment0268103Acc00200
noncomputable def fragment0268103Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '4', '3', '5', '1', '3', '7', '6', '8', '1', '9', '9', '9', '8', '7', '0', '6', '0', '3', '3', '4', '6', '4', '0', '9', '4', '2', '2', '4', '3', '7', '1', '1', '0', '1', '1', '5', '9', '3', '6', '9', '/', '1', '9', '2', '2', '3', '6', '2', '3', '0', '8', '0', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0268103_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0268103Field002Chars00 ++ tail)) fragment0268103Acc00200 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0268103Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_002"
  err.flush

noncomputable def fragment0268103Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0268103Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0268103Acc00400 : List (String × SourceJson) := (fragment0268103Field003Key00, fragment0268103Field003Value00) :: fragment0268103Acc00300
noncomputable def fragment0268103Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0268103_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0268103Field003Chars00 ++ tail)) fragment0268103Acc00300 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0268103Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_003"
  err.flush

noncomputable def fragment0268103Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0268103Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0268103Acc00500 : List (String × SourceJson) := (fragment0268103Field004Key00, fragment0268103Field004Value00) :: fragment0268103Acc00400
noncomputable def fragment0268103Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '9', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0268103_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0268103Field004Chars00 ++ tail)) fragment0268103Acc00400 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0268103Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_004"
  err.flush

noncomputable def fragment0268103Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0268103Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '1', '1', '6', '4', '6', '4', '9', '7', '1', '9', '/', '3', '3', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '9', '3', '1', '4', '5', '5', '8', '7', '8', '7', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '2', '5', '3', '4', '8', '0', '0', '2', '5', '0', '1', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '5', '1', '3', '2', '2', '8', '0', '3', '7', '1', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '2', '1', '4', '0', '1', '3', '9', '9', '8', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '1', '6', '7', '1', '0', '1', '2', '1', '7', '9', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '1', '1', '1', '8', '2', '9', '8', '0', '2', '9', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '3', '6', '6', '1', '8', '4', '4', '9', '2', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '1', '2', '2', '0', '0', '8', '7', '0', '8', '1', '/', '7', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '0', '8', '6', '5', '9', '8', '1', '5', '2', '9', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0268103Acc00600 : List (String × SourceJson) := (fragment0268103Field005Key00, fragment0268103Field005Value00) :: fragment0268103Acc00500
noncomputable def fragment0268103Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '1', '6', '4', '6', '4', '9', '7', '1', '9', '/', '3', '3', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '3', '1', '4', '5', '5', '8', '7', '8', '7', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '2', '5', '3', '4', '8', '0', '0', '2', '5', '0', '1', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '5', '1', '3', '2', '2', '8', '0', '3', '7', '1', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '2', '1', '4', '0', '1', '3', '9', '9', '8', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '1', '6', '7', '1', '0', '1', '2', '1', '7', '9', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '4', '1', '1', '1', '8', '2', '9', '8', '0', '2', '9', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '3', '6', '6', '1', '8', '4', '4', '9', '2', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '1', '2', '2', '0', '0', '8', '7', '0', '8', '1', '/', '7', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '0', '8', '6', '5', '9', '8', '1', '5', '2', '9', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0268103_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0268103Field005Chars00 ++ tail)) fragment0268103Acc00500 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0268103Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_005"
  err.flush

noncomputable def fragment0268103Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0268103Field006Value00 : SourceJson := .str (String.ofList ['5', '4', '5', '6', '6', '2', '3', '0', '0', '4', '1', '3', '5', '0', '0', '9', '7', '9', '9', '4', '4', '5', '5', '6', '8', '6', '4', '5', '9', '3', '3', '6', '1', '1', '3', '6', '3', '7', '6', '6', '7', '0', '4', '8', '9', '0', '0', '0', '0', '0', '0', '/', '3', '6', '8', '2', '3', '4', '4', '5', '0', '0', '8', '9', '6', '1', '7', '7', '3', '9', '9', '4', '5', '7', '7', '4', '4', '2', '0', '8', '2', '7', '9', '6', '1', '9', '8', '3', '8', '9', '4', '3', '9', '7', '3', '5', '4', '1', '1', '5', '1', '5', '5', '2', '5', '4', '7', '4', '4', '6', '9', '7', '9', '8', '2', '6', '3', '3'])
noncomputable def fragment0268103Acc00700 : List (String × SourceJson) := (fragment0268103Field006Key00, fragment0268103Field006Value00) :: fragment0268103Acc00600
noncomputable def fragment0268103Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '4', '5', '6', '6', '2', '3', '0', '0', '4', '1', '3', '5', '0', '0', '9', '7', '9', '9', '4', '4', '5', '5', '6', '8', '6', '4', '5', '9', '3', '3', '6', '1', '1', '3', '6', '3', '7', '6', '6', '7', '0', '4', '8', '9', '0', '0', '0', '0', '0', '0', '/', '3', '6', '8', '2', '3', '4', '4', '5', '0', '0', '8', '9', '6', '1', '7', '7', '3', '9', '9', '4', '5', '7', '7', '4', '4', '2', '0', '8', '2', '7', '9', '6', '1', '9', '8', '3', '8', '9', '4', '3', '9', '7', '3', '5', '4', '1', '1', '5', '1', '5', '5', '2', '5', '4', '7', '4', '4', '6', '9', '7', '9', '8', '2', '6', '3', '3', '"', ',']

theorem object_fragment0268103_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0268103Field006Chars00 ++ tail)) fragment0268103Acc00600 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0268103Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_006"
  err.flush

noncomputable def fragment0268103Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0268103Field007Value00 : SourceJson := .str (String.ofList ['4', '3', '8', '4', '8', '8', '0', '3', '0', '9', '7', '6', '1', '5', '7', '3', '0', '5', '5', '0', '3', '8', '7', '3', '6', '6', '8', '0', '1', '6', '1', '7', '7', '9', '1', '7', '2', '9', '8', '7', '5', '5', '7', '7', '5', '5', '0', '1', '2', '1', '1', '6', '7', '8', '5', '5', '8', '6', '4', '4', '2', '2', '4', '5', '8', '5', '6', '6', '5', '8', '8', '6', '6', '2', '3', '4', '9', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '9', '8', '0', '9', '6', '5', '1', '0', '0', '9', '0', '9', '0', '4', '4', '2', '7', '0', '1', '4', '1', '6', '0', '6', '7', '8', '7', '7', '8', '1', '6', '5', '3', '1', '1', '6', '9', '0', '3', '2', '4', '0', '2', '6', '9', '2', '2', '8', '5', '9', '2', '2', '1', '5', '0', '5', '2', '9', '8', '1', '3', '3', '3', '9', '3', '2', '2', '2', '5', '2', '3', '5', '6', '2', '5', '5', '8', '0', '1', '9', '1', '0', '0', '3', '9', '8', '7', '1', '3', '0', '3', '0', '8', '6', '8', '9', '9', '9', '3', '9', '9', '7', '6', '4', '5', '8', '6', '6', '6', '7', '7', '6', '7', '2', '4', '9', '3', '9'])
noncomputable def fragment0268103Acc00800 : List (String × SourceJson) := (fragment0268103Field007Key00, fragment0268103Field007Value00) :: fragment0268103Acc00700
noncomputable def fragment0268103Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '4', '3', '8', '4', '8', '8', '0', '3', '0', '9', '7', '6', '1', '5', '7', '3', '0', '5', '5', '0', '3', '8', '7', '3', '6', '6', '8', '0', '1', '6', '1', '7', '7', '9', '1', '7', '2', '9', '8', '7', '5', '5', '7', '7', '5', '5', '0', '1', '2', '1', '1', '6', '7', '8', '5', '5', '8', '6', '4', '4', '2', '2', '4', '5', '8', '5', '6', '6', '5', '8', '8', '6', '6', '2', '3', '4', '9', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '9', '8', '0', '9', '6', '5', '1', '0', '0', '9', '0', '9', '0', '4', '4', '2', '7', '0', '1', '4', '1', '6', '0', '6', '7', '8', '7', '7', '8', '1', '6', '5', '3', '1', '1', '6', '9', '0', '3', '2', '4', '0', '2', '6', '9', '2', '2', '8', '5', '9', '2', '2', '1', '5', '0', '5', '2', '9', '8', '1', '3', '3', '3', '9', '3', '2', '2', '2', '5', '2', '3', '5', '6', '2', '5', '5', '8', '0', '1', '9', '1', '0', '0', '3', '9', '8', '7', '1', '3', '0', '3', '0', '8', '6', '8', '9', '9', '9', '3', '9', '9', '7', '6', '4', '5', '8', '6', '6', '6', '7', '7', '6', '7', '2', '4', '9', '3', '9', '"', ',']

theorem object_fragment0268103_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0268103Field007Chars00 ++ tail)) fragment0268103Acc00700 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0268103Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_007"
  err.flush

noncomputable def fragment0268103Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0268103Field008Value00 : SourceJson := .str (String.ofList ['1', '1', '7', '4', '0', '2', '9', '7', '9', '0', '1', '1', '1', '8', '9'])
noncomputable def fragment0268103Acc00900 : List (String × SourceJson) := (fragment0268103Field008Key00, fragment0268103Field008Value00) :: fragment0268103Acc00800
noncomputable def fragment0268103Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '1', '7', '4', '0', '2', '9', '7', '9', '0', '1', '1', '1', '8', '9', '"', ',']

theorem object_fragment0268103_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0268103Field008Chars00 ++ tail)) fragment0268103Acc00800 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0268103Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_008"
  err.flush

noncomputable def fragment0268103Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0268103Field009Value00 : SourceJson := .str (String.ofList ['8', '7', '2', '6', '6', '7', '8', '1', '0', '3', '9', '6', '1', '7', '3'])
noncomputable def fragment0268103Acc01000 : List (String × SourceJson) := (fragment0268103Field009Key00, fragment0268103Field009Value00) :: fragment0268103Acc00900
noncomputable def fragment0268103Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '8', '7', '2', '6', '6', '7', '8', '1', '0', '3', '9', '6', '1', '7', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0268103_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0268103Field009Chars00 ++ tail)) fragment0268103Acc00900 =
      .ok (.obj (fragment0268103Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0268103_object_field_009"
  err.flush

noncomputable def fragment0268103Chars : List Char := '{' :: (fragment0268103Field000Chars00 ++ fragment0268103Field001Chars00 ++ fragment0268103Field002Chars00 ++ fragment0268103Field003Chars00 ++ fragment0268103Field004Chars00 ++ fragment0268103Field005Chars00 ++ fragment0268103Field006Chars00 ++ fragment0268103Field007Chars00 ++ fragment0268103Field008Chars00 ++ fragment0268103Field009Chars00)
noncomputable def fragment0268103Value : SourceJson := .obj (fragment0268103Acc01000.reverse)

theorem value_fragment0268103 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 236) (fragment0268103Chars ++ tail) =
      .ok (fragment0268103Value, tail) := by
  have hinput : fragment0268103Chars ++ tail = '{' :: (fragment0268103Field000Chars00 ++ (fragment0268103Field001Chars00 ++ (fragment0268103Field002Chars00 ++ (fragment0268103Field003Chars00 ++ (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0268103Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 236) (fragment0268103Chars ++ tail) =
        SourceJson.value (fuel + 236) ('{' :: (fragment0268103Field000Chars00 ++ (fragment0268103Field001Chars00 ++ (fragment0268103Field002Chars00 ++ (fragment0268103Field003Chars00 ++ (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 236)) hinput
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0268103Field000Chars00 ++ (fragment0268103Field001Chars00 ++ (fragment0268103Field002Chars00 ++ (fragment0268103Field003Chars00 ++ (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))))))))))) fragment0268103Acc00000 := by rfl
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0268103Field001Chars00 ++ (fragment0268103Field002Chars00 ++ (fragment0268103Field003Chars00 ++ (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail))))))))))) fragment0268103Acc00100 := object_fragment0268103_field_000 fuel (fragment0268103Field001Chars00 ++ (fragment0268103Field002Chars00 ++ (fragment0268103Field003Chars00 ++ (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0268103Field002Chars00 ++ (fragment0268103Field003Chars00 ++ (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))))))))) fragment0268103Acc00200 := object_fragment0268103_field_001 fuel (fragment0268103Field002Chars00 ++ (fragment0268103Field003Chars00 ++ (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0268103Field003Chars00 ++ (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail))))))))) fragment0268103Acc00300 := object_fragment0268103_field_002 fuel (fragment0268103Field003Chars00 ++ (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))))))) fragment0268103Acc00400 := object_fragment0268103_field_003 fuel (fragment0268103Field004Chars00 ++ (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail))))))) fragment0268103Acc00500 := object_fragment0268103_field_004 fuel (fragment0268103Field005Chars00 ++ (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))))) fragment0268103Acc00600 := object_fragment0268103_field_005 fuel (fragment0268103Field006Chars00 ++ (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail))))) fragment0268103Acc00700 := object_fragment0268103_field_006 fuel (fragment0268103Field007Chars00 ++ (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))) fragment0268103Acc00800 := object_fragment0268103_field_007 fuel (fragment0268103Field008Chars00 ++ (fragment0268103Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0268103Field009Chars00 ++ (tail))) fragment0268103Acc00900 := object_fragment0268103_field_008 fuel (fragment0268103Field009Chars00 ++ (tail))
    _ = .ok (fragment0268103Value, tail) := object_fragment0268103_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_before_reader"
  err.flush

noncomputable def chunk0024LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0024SuffixChars00 : List Char := [',']
noncomputable def chunk0024Chars00 : List Char := chunk0024LeadChars00 ++ fragment0266572Chars ++ chunk0024SuffixChars00
noncomputable def chunk0024Push00 (acc : List SourceJson) : List SourceJson := fragment0266572Value :: acc

noncomputable def chunk0024AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0024_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 580)
      (SourceJson.white (chunk0024LeadChars00 ++ (fragment0266572Chars ++ rest))) acc =
      (SourceJson.value (fuel + 579) (fragment0266572Chars ++ rest)).bind
        (chunk0024AfterValue00 (fuel + 579) acc) := by rfl

theorem array_chunk0024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 580) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 579) (SourceJson.white tail) (chunk0024Push00 acc) := by
  have hinput : chunk0024Chars00 ++ tail = chunk0024LeadChars00 ++ (fragment0266572Chars ++ (chunk0024SuffixChars00 ++ tail)) := by
    simp only [chunk0024Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 580) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 580)
          (SourceJson.white (chunk0024LeadChars00 ++ (fragment0266572Chars ++ (chunk0024SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 580) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 579) (fragment0266572Chars ++ (chunk0024SuffixChars00 ++ tail))).bind
        (chunk0024AfterValue00 (fuel + 579) acc) := array_chunk0024_head fuel (chunk0024SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0266572Value, chunk0024SuffixChars00 ++ tail)).bind
        (chunk0024AfterValue00 (fuel + 579) acc) :=
      congrArg (fun result => result.bind (chunk0024AfterValue00 (fuel + 579) acc))
        (value_fragment0266572 (fuel + 377) (chunk0024SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 579) (SourceJson.white tail) (chunk0024Push00 acc) := by rfl

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
noncomputable def chunk0025Chars00 : List Char := chunk0025LeadChars00 ++ fragment0268103Chars ++ chunk0025SuffixChars00
noncomputable def chunk0025Push00 (acc : List SourceJson) : List SourceJson := fragment0268103Value :: acc

noncomputable def chunk0025AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0025_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 579)
      (SourceJson.white (chunk0025LeadChars00 ++ (fragment0268103Chars ++ rest))) acc =
      (SourceJson.value (fuel + 578) (fragment0268103Chars ++ rest)).bind
        (chunk0025AfterValue00 (fuel + 578) acc) := by rfl

theorem array_chunk0025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 579) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 578) (SourceJson.white tail) (chunk0025Push00 acc) := by
  have hinput : chunk0025Chars00 ++ tail = chunk0025LeadChars00 ++ (fragment0268103Chars ++ (chunk0025SuffixChars00 ++ tail)) := by
    simp only [chunk0025Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 579) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 579)
          (SourceJson.white (chunk0025LeadChars00 ++ (fragment0268103Chars ++ (chunk0025SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 579) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 578) (fragment0268103Chars ++ (chunk0025SuffixChars00 ++ tail))).bind
        (chunk0025AfterValue00 (fuel + 578) acc) := array_chunk0025_head fuel (chunk0025SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0268103Value, chunk0025SuffixChars00 ++ tail)).bind
        (chunk0025AfterValue00 (fuel + 578) acc) :=
      congrArg (fun result => result.bind (chunk0025AfterValue00 (fuel + 578) acc))
        (value_fragment0268103 (fuel + 342) (chunk0025SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 578) (SourceJson.white tail) (chunk0025Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0024Chars00 ++ chunk0025Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0025Push00 (chunk0024Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 580) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 578) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0024Chars00 ++ (chunk0025Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 580) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 580) (SourceJson.white (chunk0024Chars00 ++ (chunk0025Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 580) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 579) (SourceJson.white (chunk0025Chars00 ++ (tail))) (chunk0024Push00 (acc)) := array_chunk0024 fuel (chunk0025Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 578) (SourceJson.white tail) (blockPush acc) := array_chunk0025 fuel (tail) (chunk0024Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 266566).take 3141 = blockChars := by rfl

theorem block_original_split : sourceRest 266566 = blockChars ++ sourceRest 269707 := by
  calc
    sourceRest 266566 = (sourceRest 266566).take 3141 ++ (sourceRest 266566).drop 3141 :=
      (List.take_append_drop 3141 (sourceRest 266566)).symm
    _ = blockChars ++ (sourceRest 266566).drop 3141 :=
      congrArg (fun part => part ++ (sourceRest 266566).drop 3141) block_original_prefix
    _ = blockChars ++ sourceRest 269707 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 266566 3141)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 580) (SourceJson.white (sourceRest 266566)) acc =
      SourceJson.array (fuel + 578) (SourceJson.white (sourceRest 269707)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 580) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 269707) acc)

#print axioms object_fragment0266572_field_000
#print axioms object_fragment0266572_field_001
#print axioms object_fragment0266572_field_002
#print axioms object_fragment0266572_field_003
#print axioms object_fragment0266572_field_004
#print axioms object_fragment0266572_field_005
#print axioms object_fragment0266572_field_006
#print axioms object_fragment0266572_field_007
#print axioms object_fragment0266572_field_008
#print axioms object_fragment0266572_field_009
#print axioms value_fragment0266572
#print axioms object_fragment0268103_field_000
#print axioms object_fragment0268103_field_001
#print axioms object_fragment0268103_field_002
#print axioms object_fragment0268103_field_003
#print axioms object_fragment0268103_field_004
#print axioms object_fragment0268103_field_005
#print axioms object_fragment0268103_field_006
#print axioms object_fragment0268103_field_007
#print axioms object_fragment0268103_field_008
#print axioms object_fragment0268103_field_009
#print axioms value_fragment0268103
#print axioms array_chunk0024_head
#print axioms array_chunk0024
#print axioms array_chunk0025_head
#print axioms array_chunk0025
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock012

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
