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

namespace SimplicesBlock068

noncomputable def fragment0453699Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0453699Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0453699Field000Value00 : SourceJson := .number (String.ofList ['1', '3', '4'])
noncomputable def fragment0453699Acc00100 : List (String × SourceJson) := (fragment0453699Field000Key00, fragment0453699Field000Value00) :: fragment0453699Acc00000
noncomputable def fragment0453699Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '4', ',']

theorem object_fragment0453699_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 245) (SourceJson.white (fragment0453699Field000Chars00 ++ tail)) fragment0453699Acc00000 =
      SourceJson.object (fuel + 244) (SourceJson.white tail) fragment0453699Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_000"
  err.flush

noncomputable def fragment0453699Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0453699Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6']), .number (String.ofList ['1'])]
noncomputable def fragment0453699Acc00200 : List (String × SourceJson) := (fragment0453699Field001Key00, fragment0453699Field001Value00) :: fragment0453699Acc00100
noncomputable def fragment0453699Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0453699_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 244) (SourceJson.white (fragment0453699Field001Chars00 ++ tail)) fragment0453699Acc00100 =
      SourceJson.object (fuel + 243) (SourceJson.white tail) fragment0453699Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_001"
  err.flush

noncomputable def fragment0453699Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0453699Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '3', '7', '8', '0', '5', '0', '4', '2', '4', '0', '9', '9', '1', '6', '7', '5', '3', '0', '7', '5', '9', '8', '3', '1', '7', '3', '6', '9', '8', '9', '6', '6', '4', '2', '4', '1', '/', '3', '1', '2', '9', '3', '8', '5', '2', '8', '4', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0453699Acc00300 : List (String × SourceJson) := (fragment0453699Field002Key00, fragment0453699Field002Value00) :: fragment0453699Acc00200
noncomputable def fragment0453699Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '3', '7', '8', '0', '5', '0', '4', '2', '4', '0', '9', '9', '1', '6', '7', '5', '3', '0', '7', '5', '9', '8', '3', '1', '7', '3', '6', '9', '8', '9', '6', '6', '4', '2', '4', '1', '/', '3', '1', '2', '9', '3', '8', '5', '2', '8', '4', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0453699_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 243) (SourceJson.white (fragment0453699Field002Chars00 ++ tail)) fragment0453699Acc00200 =
      SourceJson.object (fuel + 242) (SourceJson.white tail) fragment0453699Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_002"
  err.flush

noncomputable def fragment0453699Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0453699Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0453699Acc00400 : List (String × SourceJson) := (fragment0453699Field003Key00, fragment0453699Field003Value00) :: fragment0453699Acc00300
noncomputable def fragment0453699Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0453699_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 242) (SourceJson.white (fragment0453699Field003Chars00 ++ tail)) fragment0453699Acc00300 =
      SourceJson.object (fuel + 241) (SourceJson.white tail) fragment0453699Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_003"
  err.flush

noncomputable def fragment0453699Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0453699Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0453699Acc00500 : List (String × SourceJson) := (fragment0453699Field004Key00, fragment0453699Field004Value00) :: fragment0453699Acc00400
noncomputable def fragment0453699Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '1', '5', '6', '2', '9', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0453699_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 241) (SourceJson.white (fragment0453699Field004Chars00 ++ tail)) fragment0453699Acc00400 =
      SourceJson.object (fuel + 240) (SourceJson.white tail) fragment0453699Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_004"
  err.flush

noncomputable def fragment0453699Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0453699Field005Value00 : SourceJson := .arr [.str (String.ofList ['5', '1', '6', '5', '0', '9', '4', '3', '0', '0', '8', '5', '3', '/', '6', '5', '5', '0', '1', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '5', '4', '6', '5', '0', '1', '3', '5', '4', '6', '1', '/', '1', '3', '1', '0', '0', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '3', '1', '5', '0', '5', '1', '9', '1', '3', '9', '9', '/', '4', '9', '1', '2', '6', '1', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '6', '4', '2', '1', '0', '1', '6', '6', '6', '0', '9', '/', '8', '7', '3', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '4', '9', '0', '5', '3', '8', '6', '8', '8', '9', '1', '/', '1', '9', '6', '5', '0', '4', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '9', '0', '9', '1', '3', '1', '3', '4', '5', '3', '9', '1', '/', '3', '9', '3', '0', '0', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '6', '3', '2', '3', '7', '6', '8', '7', '/', '6', '4', '6', '3', '9', '6', '8', '7', '5', '0', '0']), .str (String.ofList ['6', '3', '9', '3', '0', '5', '2', '3', '7', '0', '5', '3', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '5', '2', '1', '3', '5', '4', '4', '0', '6', '4', '0', '3', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '5', '2', '1', '3', '0', '2', '0', '0', '5', '1', '6', '3', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0453699Acc00600 : List (String × SourceJson) := (fragment0453699Field005Key00, fragment0453699Field005Value00) :: fragment0453699Acc00500
noncomputable def fragment0453699Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '6', '5', '0', '9', '4', '3', '0', '0', '8', '5', '3', '/', '6', '5', '5', '0', '1', '5', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '3', '5', '4', '6', '5', '0', '1', '3', '5', '4', '6', '1', '/', '1', '3', '1', '0', '0', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '3', '3', '1', '5', '0', '5', '1', '9', '1', '3', '9', '9', '/', '4', '9', '1', '2', '6', '1', '6', '2', '5', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '9', '5', '6', '4', '2', '1', '0', '1', '6', '6', '6', '0', '9', '/', '8', '7', '3', '3', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '4', '9', '0', '5', '3', '8', '6', '8', '8', '9', '1', '/', '1', '9', '6', '5', '0', '4', '6', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '9', '0', '9', '1', '3', '1', '3', '4', '5', '3', '9', '1', '/', '3', '9', '3', '0', '0', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '6', '3', '2', '3', '7', '6', '8', '7', '/', '6', '4', '6', '3', '9', '6', '8', '7', '5', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '9', '3', '0', '5', '2', '3', '7', '0', '5', '3', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '5', '2', '1', '3', '5', '4', '4', '0', '6', '4', '0', '3', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '1', '5', '2', '1', '3', '0', '2', '0', '0', '5', '1', '6', '3', '/', '7', '8', '6', '0', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0453699_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0453699Field005Chars00 ++ tail)) fragment0453699Acc00500 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0453699Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_005"
  err.flush

noncomputable def fragment0453699Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0453699Field006Value00 : SourceJson := .str (String.ofList ['2', '8', '3', '6', '3', '7', '0', '3', '2', '6', '4', '9', '7', '2', '9', '3', '4', '4', '6', '6', '7', '6', '8', '3', '3', '9', '9', '0', '3', '7', '1', '6', '9', '7', '6', '6', '6', '9', '8', '8', '8', '7', '6', '2', '2', '7', '1', '0', '4', '0', '0', '/', '5', '9', '8', '4', '5', '9', '4', '9', '1', '4', '5', '2', '7', '6', '3', '3', '6', '2', '1', '4', '6', '9', '8', '0', '0', '6', '6', '1', '0', '6', '4', '6', '3', '0', '8', '8', '0', '8', '1', '2', '2', '3', '6', '5', '0', '4', '4', '2', '3', '5', '2', '5', '9', '6', '0', '8', '3', '0', '3', '6', '6', '8', '4', '0', '5', '2', '2', '7', '7'])
noncomputable def fragment0453699Acc00700 : List (String × SourceJson) := (fragment0453699Field006Key00, fragment0453699Field006Value00) :: fragment0453699Acc00600
noncomputable def fragment0453699Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '8', '3', '6', '3', '7', '0', '3', '2', '6', '4', '9', '7', '2', '9', '3', '4', '4', '6', '6', '7', '6', '8', '3', '3', '9', '9', '0', '3', '7', '1', '6', '9', '7', '6', '6', '6', '9', '8', '8', '8', '7', '6', '2', '2', '7', '1', '0', '4', '0', '0', '/', '5', '9', '8', '4', '5', '9', '4', '9', '1', '4', '5', '2', '7', '6', '3', '3', '6', '2', '1', '4', '6', '9', '8', '0', '0', '6', '6', '1', '0', '6', '4', '6', '3', '0', '8', '8', '0', '8', '1', '2', '2', '3', '6', '5', '0', '4', '4', '2', '3', '5', '2', '5', '9', '6', '0', '8', '3', '0', '3', '6', '6', '8', '4', '0', '5', '2', '2', '7', '7', '"', ',']

theorem object_fragment0453699_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0453699Field006Chars00 ++ tail)) fragment0453699Acc00600 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0453699Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_006"
  err.flush

noncomputable def fragment0453699Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0453699Field007Value00 : SourceJson := .str (String.ofList ['5', '8', '7', '5', '8', '8', '4', '5', '0', '7', '3', '4', '7', '6', '2', '7', '8', '6', '9', '0', '7', '7', '0', '7', '6', '1', '6', '7', '5', '5', '0', '4', '6', '3', '4', '9', '2', '5', '4', '3', '6', '1', '6', '3', '3', '8', '1', '3', '1', '0', '3', '4', '0', '4', '4', '5', '6', '0', '9', '5', '2', '8', '1', '1', '8', '7', '4', '1', '6', '1', '1', '1', '4', '7', '4', '0', '7', '9', '0', '8', '7', '7', '5', '7', '3', '8', '8', '9', '5', '8', '4', '7', '6', '0', '6', '6', '5', '8', '9', '3', '5', '5', '4', '6', '8', '7', '5', '0', '/', '1', '6', '6', '3', '5', '7', '8', '9', '1', '3', '6', '1', '8', '1', '2', '6', '4', '5', '3', '5', '7', '5', '4', '6', '2', '0', '5', '9', '0', '9', '2', '4', '2', '4', '2', '7', '3', '7', '7', '1', '7', '4', '8', '3', '4', '7', '7', '4', '1', '0', '6', '8', '9', '4', '4', '2', '8', '8', '7', '6', '7', '9', '4', '0', '5', '8', '5', '9', '0', '2', '4', '4', '4', '3', '3', '3', '0', '8', '9', '0', '1', '7', '5', '2', '6', '9', '8', '5', '6', '1', '0', '3', '7', '0', '2', '3', '8', '2', '1', '9', '5', '3', '4', '0', '9', '2', '7', '6', '1', '5', '1', '8', '4', '3', '5', '1', '1', '3', '1', '6', '2', '0', '4', '6', '7', '1'])
noncomputable def fragment0453699Acc00800 : List (String × SourceJson) := (fragment0453699Field007Key00, fragment0453699Field007Value00) :: fragment0453699Acc00700
noncomputable def fragment0453699Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '8', '7', '5', '8', '8', '4', '5', '0', '7', '3', '4', '7', '6', '2', '7', '8', '6', '9', '0', '7', '7', '0', '7', '6', '1', '6', '7', '5', '5', '0', '4', '6', '3', '4', '9', '2', '5', '4', '3', '6', '1', '6', '3', '3', '8', '1', '3', '1', '0', '3', '4', '0', '4', '4', '5', '6', '0', '9', '5', '2', '8', '1', '1', '8', '7', '4', '1', '6', '1', '1', '1', '4', '7', '4', '0', '7', '9', '0', '8', '7', '7', '5', '7', '3', '8', '8', '9', '5', '8', '4', '7', '6', '0', '6', '6', '5', '8', '9', '3', '5', '5', '4', '6', '8', '7', '5', '0', '/', '1', '6', '6', '3', '5', '7', '8', '9', '1', '3', '6', '1', '8', '1', '2', '6', '4', '5', '3', '5', '7', '5', '4', '6', '2', '0', '5', '9', '0', '9', '2', '4', '2', '4', '2', '7', '3', '7', '7', '1', '7', '4', '8', '3', '4', '7', '7', '4', '1', '0', '6', '8', '9', '4', '4', '2', '8', '8', '7', '6', '7', '9', '4', '0', '5', '8', '5', '9', '0', '2', '4', '4', '4', '3', '3', '3', '0', '8', '9', '0', '1', '7', '5', '2', '6', '9', '8', '5', '6', '1', '0', '3', '7', '0', '2', '3', '8', '2', '1', '9', '5', '3', '4', '0', '9', '2', '7', '6', '1', '5', '1', '8', '4', '3', '5', '1', '1', '3', '1', '6', '2', '0', '4', '6', '7', '1', '"', ',']

theorem object_fragment0453699_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0453699Field007Chars00 ++ tail)) fragment0453699Acc00700 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0453699Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_007"
  err.flush

noncomputable def fragment0453699Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0453699Field008Value00 : SourceJson := .str (String.ofList ['3', '7', '5', '4', '9', '8', '1', '1', '2', '0', '4'])
noncomputable def fragment0453699Acc00900 : List (String × SourceJson) := (fragment0453699Field008Key00, fragment0453699Field008Value00) :: fragment0453699Acc00800
noncomputable def fragment0453699Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '3', '7', '5', '4', '9', '8', '1', '1', '2', '0', '4', '"', ',']

theorem object_fragment0453699_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0453699Field008Chars00 ++ tail)) fragment0453699Acc00800 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0453699Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_008"
  err.flush

noncomputable def fragment0453699Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0453699Field009Value00 : SourceJson := .str (String.ofList ['2', '7', '9', '8', '3', '9', '7', '6', '5', '2', '5', '0'])
noncomputable def fragment0453699Acc01000 : List (String × SourceJson) := (fragment0453699Field009Key00, fragment0453699Field009Value00) :: fragment0453699Acc00900
noncomputable def fragment0453699Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '7', '9', '8', '3', '9', '7', '6', '5', '2', '5', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0453699_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0453699Field009Chars00 ++ tail)) fragment0453699Acc00900 =
      .ok (.obj (fragment0453699Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0453699_object_field_009"
  err.flush

noncomputable def fragment0453699Chars : List Char := '{' :: (fragment0453699Field000Chars00 ++ fragment0453699Field001Chars00 ++ fragment0453699Field002Chars00 ++ fragment0453699Field003Chars00 ++ fragment0453699Field004Chars00 ++ fragment0453699Field005Chars00 ++ fragment0453699Field006Chars00 ++ fragment0453699Field007Chars00 ++ fragment0453699Field008Chars00 ++ fragment0453699Field009Chars00)
noncomputable def fragment0453699Value : SourceJson := .obj (fragment0453699Acc01000.reverse)

theorem value_fragment0453699 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 246) (fragment0453699Chars ++ tail) =
      .ok (fragment0453699Value, tail) := by
  have hinput : fragment0453699Chars ++ tail = '{' :: (fragment0453699Field000Chars00 ++ (fragment0453699Field001Chars00 ++ (fragment0453699Field002Chars00 ++ (fragment0453699Field003Chars00 ++ (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0453699Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 246) (fragment0453699Chars ++ tail) =
        SourceJson.value (fuel + 246) ('{' :: (fragment0453699Field000Chars00 ++ (fragment0453699Field001Chars00 ++ (fragment0453699Field002Chars00 ++ (fragment0453699Field003Chars00 ++ (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 246)) hinput
    _ = SourceJson.object (fuel + 245) (SourceJson.white (fragment0453699Field000Chars00 ++ (fragment0453699Field001Chars00 ++ (fragment0453699Field002Chars00 ++ (fragment0453699Field003Chars00 ++ (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))))))))))) fragment0453699Acc00000 := by rfl
    _ = SourceJson.object (fuel + 244) (SourceJson.white (fragment0453699Field001Chars00 ++ (fragment0453699Field002Chars00 ++ (fragment0453699Field003Chars00 ++ (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail))))))))))) fragment0453699Acc00100 := object_fragment0453699_field_000 fuel (fragment0453699Field001Chars00 ++ (fragment0453699Field002Chars00 ++ (fragment0453699Field003Chars00 ++ (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 243) (SourceJson.white (fragment0453699Field002Chars00 ++ (fragment0453699Field003Chars00 ++ (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))))))))) fragment0453699Acc00200 := object_fragment0453699_field_001 fuel (fragment0453699Field002Chars00 ++ (fragment0453699Field003Chars00 ++ (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 242) (SourceJson.white (fragment0453699Field003Chars00 ++ (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail))))))))) fragment0453699Acc00300 := object_fragment0453699_field_002 fuel (fragment0453699Field003Chars00 ++ (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 241) (SourceJson.white (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))))))) fragment0453699Acc00400 := object_fragment0453699_field_003 fuel (fragment0453699Field004Chars00 ++ (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail))))))) fragment0453699Acc00500 := object_fragment0453699_field_004 fuel (fragment0453699Field005Chars00 ++ (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))))) fragment0453699Acc00600 := object_fragment0453699_field_005 fuel (fragment0453699Field006Chars00 ++ (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail))))) fragment0453699Acc00700 := object_fragment0453699_field_006 fuel (fragment0453699Field007Chars00 ++ (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))) fragment0453699Acc00800 := object_fragment0453699_field_007 fuel (fragment0453699Field008Chars00 ++ (fragment0453699Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0453699Field009Chars00 ++ (tail))) fragment0453699Acc00900 := object_fragment0453699_field_008 fuel (fragment0453699Field009Chars00 ++ (tail))
    _ = .ok (fragment0453699Value, tail) := object_fragment0453699_field_009 fuel (tail)

noncomputable def fragment0455323Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0455323Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0455323Field000Value00 : SourceJson := .number (String.ofList ['1', '3', '5'])
noncomputable def fragment0455323Acc00100 : List (String × SourceJson) := (fragment0455323Field000Key00, fragment0455323Field000Value00) :: fragment0455323Acc00000
noncomputable def fragment0455323Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '3', '5', ',']

theorem object_fragment0455323_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 263) (SourceJson.white (fragment0455323Field000Chars00 ++ tail)) fragment0455323Acc00000 =
      SourceJson.object (fuel + 262) (SourceJson.white tail) fragment0455323Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_000"
  err.flush

noncomputable def fragment0455323Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0455323Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '6'])]
noncomputable def fragment0455323Acc00200 : List (String × SourceJson) := (fragment0455323Field001Key00, fragment0455323Field001Value00) :: fragment0455323Acc00100
noncomputable def fragment0455323Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0455323_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 262) (SourceJson.white (fragment0455323Field001Chars00 ++ tail)) fragment0455323Acc00100 =
      SourceJson.object (fuel + 261) (SourceJson.white tail) fragment0455323Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_001"
  err.flush

noncomputable def fragment0455323Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0455323Field002Value00 : SourceJson := .str (String.ofList ['9', '0', '4', '9', '1', '1', '8', '0', '3', '9', '6', '1', '4', '1', '2', '9', '6', '4', '6', '5', '5', '8', '3', '5', '5', '0', '5', '0', '8', '4', '3', '0', '7', '9', '0', '2', '9', '7', '4', '7', '/', '8', '2', '8', '0', '3', '5', '3', '4', '6', '2', '5', '3', '0', '8', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0455323Acc00300 : List (String × SourceJson) := (fragment0455323Field002Key00, fragment0455323Field002Value00) :: fragment0455323Acc00200
noncomputable def fragment0455323Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '9', '0', '4', '9', '1', '1', '8', '0', '3', '9', '6', '1', '4', '1', '2', '9', '6', '4', '6', '5', '5', '8', '3', '5', '5', '0', '5', '0', '8', '4', '3', '0', '7', '9', '0', '2', '9', '7', '4', '7', '/', '8', '2', '8', '0', '3', '5', '3', '4', '6', '2', '5', '3', '0', '8', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0455323_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 261) (SourceJson.white (fragment0455323Field002Chars00 ++ tail)) fragment0455323Acc00200 =
      SourceJson.object (fuel + 260) (SourceJson.white tail) fragment0455323Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_002"
  err.flush

noncomputable def fragment0455323Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0455323Field003Value00 : SourceJson := .str (String.ofList ['6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0455323Acc00400 : List (String × SourceJson) := (fragment0455323Field003Key00, fragment0455323Field003Value00) :: fragment0455323Acc00300
noncomputable def fragment0455323Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '6', '0', '8', '7', '2', '3', '/', '5', '8', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0455323_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 260) (SourceJson.white (fragment0455323Field003Chars00 ++ tail)) fragment0455323Acc00300 =
      SourceJson.object (fuel + 259) (SourceJson.white tail) fragment0455323Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_003"
  err.flush

noncomputable def fragment0455323Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0455323Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '4', '5', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0455323Acc00500 : List (String × SourceJson) := (fragment0455323Field004Key00, fragment0455323Field004Value00) :: fragment0455323Acc00400
noncomputable def fragment0455323Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '4', '5', '1', '/', '4', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '7', '8', '1', '7', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '6', '7', '/', '5', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0455323_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 259) (SourceJson.white (fragment0455323Field004Chars00 ++ tail)) fragment0455323Acc00400 =
      SourceJson.object (fuel + 258) (SourceJson.white tail) fragment0455323Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_004"
  err.flush

noncomputable def fragment0455323Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0455323Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '9', '5', '1', '2', '5', '8', '3', '3', '9', '1', '2', '7', '9', '/', '5', '2', '4', '0', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '6', '1', '0', '4', '2', '9', '5', '2', '6', '2', '9', '9', '/', '5', '2', '4', '0', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '6', '6', '9', '3', '2', '0', '2', '7', '9', '8', '7', '/', '1', '7', '4', '6', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '2', '6', '0', '4', '5', '8', '5', '2', '7', '6', '3', '3', '/', '3', '9', '3', '0', '0', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '1', '0', '9', '1', '2', '0', '9', '1', '5', '5', '7', '/', '1', '7', '4', '6', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '6', '0', '2', '5', '5', '9', '1', '7', '1', '6', '1', '/', '1', '7', '4', '6', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '0', '8', '2', '2', '2', '2', '6', '9', '8', '3', '/', '1', '6', '5', '4', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '4', '7', '7', '3', '8', '9', '4', '4', '1', '6', '9', '/', '3', '1', '4', '4', '0', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '8', '5', '0', '8', '7', '9', '8', '2', '8', '3', '5', '1', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '8', '5', '0', '7', '7', '5', '0', '2', '5', '8', '7', '1', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0455323Acc00600 : List (String × SourceJson) := (fragment0455323Field005Key00, fragment0455323Field005Value00) :: fragment0455323Acc00500
noncomputable def fragment0455323Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '5', '1', '2', '5', '8', '3', '3', '9', '1', '2', '7', '9', '/', '5', '2', '4', '0', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '6', '1', '0', '4', '2', '9', '5', '2', '6', '2', '9', '9', '/', '5', '2', '4', '0', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '6', '3', '6', '6', '9', '3', '2', '0', '2', '7', '9', '8', '7', '/', '1', '7', '4', '6', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '2', '6', '0', '4', '5', '8', '5', '2', '7', '6', '3', '3', '/', '3', '9', '3', '0', '0', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '8', '1', '0', '9', '1', '2', '0', '9', '1', '5', '5', '7', '/', '1', '7', '4', '6', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '6', '6', '0', '2', '5', '5', '9', '1', '7', '1', '6', '1', '/', '1', '7', '4', '6', '7', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '0', '0', '8', '2', '2', '2', '2', '6', '9', '8', '3', '/', '1', '6', '5', '4', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '1', '4', '7', '7', '3', '8', '9', '4', '4', '1', '6', '9', '/', '3', '1', '4', '4', '0', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '8', '5', '0', '8', '7', '9', '8', '2', '8', '3', '5', '1', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '4', '8', '5', '0', '7', '7', '5', '0', '2', '5', '8', '7', '1', '/', '1', '5', '7', '2', '0', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0455323_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 258) (SourceJson.white (fragment0455323Field005Chars00 ++ tail)) fragment0455323Acc00500 =
      SourceJson.object (fuel + 257) (SourceJson.white tail) fragment0455323Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_005"
  err.flush

noncomputable def fragment0455323Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0455323Field006Value00 : SourceJson := .str (String.ofList ['1', '2', '6', '3', '7', '7', '6', '8', '1', '8', '2', '3', '6', '2', '9', '3', '7', '1', '2', '0', '8', '3', '6', '3', '8', '0', '7', '1', '3', '9', '6', '9', '3', '2', '5', '2', '5', '4', '7', '4', '6', '7', '0', '0', '0', '/', '1', '0', '3', '8', '0', '1', '4', '7', '1', '7', '9', '7', '7', '8', '1', '3', '3', '3', '7', '7', '9', '6', '7', '8', '8', '6', '9', '1', '0', '1', '5', '2', '9', '5', '6', '7', '2', '4', '1', '9', '3', '0', '4', '8', '8', '9', '7', '1', '0', '3', '4', '9', '5', '8', '6', '3', '2', '1', '3', '5', '4', '4', '3', '1'])
noncomputable def fragment0455323Acc00700 : List (String × SourceJson) := (fragment0455323Field006Key00, fragment0455323Field006Value00) :: fragment0455323Acc00600
noncomputable def fragment0455323Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '2', '6', '3', '7', '7', '6', '8', '1', '8', '2', '3', '6', '2', '9', '3', '7', '1', '2', '0', '8', '3', '6', '3', '8', '0', '7', '1', '3', '9', '6', '9', '3', '2', '5', '2', '5', '4', '7', '4', '6', '7', '0', '0', '0', '/', '1', '0', '3', '8', '0', '1', '4', '7', '1', '7', '9', '7', '7', '8', '1', '3', '3', '3', '7', '7', '9', '6', '7', '8', '8', '6', '9', '1', '0', '1', '5', '2', '9', '5', '6', '7', '2', '4', '1', '9', '3', '0', '4', '8', '8', '9', '7', '1', '0', '3', '4', '9', '5', '8', '6', '3', '2', '1', '3', '5', '4', '4', '3', '1', '"', ',']

theorem object_fragment0455323_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 257) (SourceJson.white (fragment0455323Field006Chars00 ++ tail)) fragment0455323Acc00600 =
      SourceJson.object (fuel + 256) (SourceJson.white tail) fragment0455323Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_006"
  err.flush

noncomputable def fragment0455323Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0455323Field007Value00 : SourceJson := .str (String.ofList ['1', '6', '4', '3', '0', '3', '7', '9', '8', '6', '0', '9', '0', '4', '5', '6', '8', '9', '4', '5', '5', '0', '0', '4', '8', '7', '3', '9', '2', '9', '0', '9', '6', '9', '1', '2', '8', '1', '6', '7', '7', '1', '2', '0', '5', '2', '9', '4', '8', '2', '7', '4', '3', '1', '9', '4', '3', '5', '8', '6', '9', '3', '5', '7', '6', '4', '7', '9', '9', '0', '1', '4', '3', '4', '7', '4', '7', '3', '9', '9', '3', '8', '0', '4', '9', '4', '6', '4', '9', '8', '2', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '8', '7', '9', '4', '6', '7', '1', '1', '8', '9', '8', '7', '2', '7', '3', '5', '4', '6', '6', '2', '9', '6', '9', '4', '6', '0', '7', '4', '3', '1', '2', '7', '2', '3', '3', '3', '3', '0', '8', '7', '1', '9', '0', '5', '9', '9', '0', '2', '6', '8', '3', '2', '6', '6', '0', '0', '5', '5', '4', '2', '1', '1', '8', '3', '9', '8', '0', '7', '8', '6', '7', '0', '3', '6', '3', '6', '1', '5', '4', '6', '1', '4', '3', '5', '4', '0', '6', '0', '9', '9', '6', '9', '4', '6', '2', '6', '8', '3', '7', '1', '6', '1', '4', '9', '8', '8', '9', '3', '2', '1', '6', '7', '7', '3', '8', '0', '7', '5', '5', '2', '8', '0', '8', '2', '9', '3', '6', '9', '4', '0', '7', '8', '1'])
noncomputable def fragment0455323Acc00800 : List (String × SourceJson) := (fragment0455323Field007Key00, fragment0455323Field007Value00) :: fragment0455323Acc00700
noncomputable def fragment0455323Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '6', '4', '3', '0', '3', '7', '9', '8', '6', '0', '9', '0', '4', '5', '6', '8', '9', '4', '5', '5', '0', '0', '4', '8', '7', '3', '9', '2', '9', '0', '9', '6', '9', '1', '2', '8', '1', '6', '7', '7', '1', '2', '0', '5', '2', '9', '4', '8', '2', '7', '4', '3', '1', '9', '4', '3', '5', '8', '6', '9', '3', '5', '7', '6', '4', '7', '9', '9', '0', '1', '4', '3', '4', '7', '4', '7', '3', '9', '9', '3', '8', '0', '4', '9', '4', '6', '4', '9', '8', '2', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '2', '8', '7', '9', '4', '6', '7', '1', '1', '8', '9', '8', '7', '2', '7', '3', '5', '4', '6', '6', '2', '9', '6', '9', '4', '6', '0', '7', '4', '3', '1', '2', '7', '2', '3', '3', '3', '3', '0', '8', '7', '1', '9', '0', '5', '9', '9', '0', '2', '6', '8', '3', '2', '6', '6', '0', '0', '5', '5', '4', '2', '1', '1', '8', '3', '9', '8', '0', '7', '8', '6', '7', '0', '3', '6', '3', '6', '1', '5', '4', '6', '1', '4', '3', '5', '4', '0', '6', '0', '9', '9', '6', '9', '4', '6', '2', '6', '8', '3', '7', '1', '6', '1', '4', '9', '8', '8', '9', '3', '2', '1', '6', '7', '7', '3', '8', '0', '7', '5', '5', '2', '8', '0', '8', '2', '9', '3', '6', '9', '4', '0', '7', '8', '1', '"', ',']

theorem object_fragment0455323_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 256) (SourceJson.white (fragment0455323Field007Chars00 ++ tail)) fragment0455323Acc00700 =
      SourceJson.object (fuel + 255) (SourceJson.white tail) fragment0455323Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_007"
  err.flush

noncomputable def fragment0455323Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0455323Field008Value00 : SourceJson := .str (String.ofList ['9', '6', '4', '5', '9', '8', '2', '2', '1', '9'])
noncomputable def fragment0455323Acc00900 : List (String × SourceJson) := (fragment0455323Field008Key00, fragment0455323Field008Value00) :: fragment0455323Acc00800
noncomputable def fragment0455323Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '6', '4', '5', '9', '8', '2', '2', '1', '9', '"', ',']

theorem object_fragment0455323_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 255) (SourceJson.white (fragment0455323Field008Chars00 ++ tail)) fragment0455323Acc00800 =
      SourceJson.object (fuel + 254) (SourceJson.white tail) fragment0455323Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_008"
  err.flush

noncomputable def fragment0455323Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0455323Field009Value00 : SourceJson := .str (String.ofList ['5', '6', '8', '9', '5', '9', '4', '0', '7', '5', '8'])
noncomputable def fragment0455323Acc01000 : List (String × SourceJson) := (fragment0455323Field009Key00, fragment0455323Field009Value00) :: fragment0455323Acc00900
noncomputable def fragment0455323Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '6', '8', '9', '5', '9', '4', '0', '7', '5', '8', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0455323_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 254) (SourceJson.white (fragment0455323Field009Chars00 ++ tail)) fragment0455323Acc00900 =
      .ok (.obj (fragment0455323Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0455323_object_field_009"
  err.flush

noncomputable def fragment0455323Chars : List Char := '{' :: (fragment0455323Field000Chars00 ++ fragment0455323Field001Chars00 ++ fragment0455323Field002Chars00 ++ fragment0455323Field003Chars00 ++ fragment0455323Field004Chars00 ++ fragment0455323Field005Chars00 ++ fragment0455323Field006Chars00 ++ fragment0455323Field007Chars00 ++ fragment0455323Field008Chars00 ++ fragment0455323Field009Chars00)
noncomputable def fragment0455323Value : SourceJson := .obj (fragment0455323Acc01000.reverse)

theorem value_fragment0455323 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 264) (fragment0455323Chars ++ tail) =
      .ok (fragment0455323Value, tail) := by
  have hinput : fragment0455323Chars ++ tail = '{' :: (fragment0455323Field000Chars00 ++ (fragment0455323Field001Chars00 ++ (fragment0455323Field002Chars00 ++ (fragment0455323Field003Chars00 ++ (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0455323Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 264) (fragment0455323Chars ++ tail) =
        SourceJson.value (fuel + 264) ('{' :: (fragment0455323Field000Chars00 ++ (fragment0455323Field001Chars00 ++ (fragment0455323Field002Chars00 ++ (fragment0455323Field003Chars00 ++ (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 264)) hinput
    _ = SourceJson.object (fuel + 263) (SourceJson.white (fragment0455323Field000Chars00 ++ (fragment0455323Field001Chars00 ++ (fragment0455323Field002Chars00 ++ (fragment0455323Field003Chars00 ++ (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))))))))))) fragment0455323Acc00000 := by rfl
    _ = SourceJson.object (fuel + 262) (SourceJson.white (fragment0455323Field001Chars00 ++ (fragment0455323Field002Chars00 ++ (fragment0455323Field003Chars00 ++ (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail))))))))))) fragment0455323Acc00100 := object_fragment0455323_field_000 fuel (fragment0455323Field001Chars00 ++ (fragment0455323Field002Chars00 ++ (fragment0455323Field003Chars00 ++ (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 261) (SourceJson.white (fragment0455323Field002Chars00 ++ (fragment0455323Field003Chars00 ++ (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))))))))) fragment0455323Acc00200 := object_fragment0455323_field_001 fuel (fragment0455323Field002Chars00 ++ (fragment0455323Field003Chars00 ++ (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 260) (SourceJson.white (fragment0455323Field003Chars00 ++ (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail))))))))) fragment0455323Acc00300 := object_fragment0455323_field_002 fuel (fragment0455323Field003Chars00 ++ (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 259) (SourceJson.white (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))))))) fragment0455323Acc00400 := object_fragment0455323_field_003 fuel (fragment0455323Field004Chars00 ++ (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 258) (SourceJson.white (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail))))))) fragment0455323Acc00500 := object_fragment0455323_field_004 fuel (fragment0455323Field005Chars00 ++ (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 257) (SourceJson.white (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))))) fragment0455323Acc00600 := object_fragment0455323_field_005 fuel (fragment0455323Field006Chars00 ++ (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 256) (SourceJson.white (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail))))) fragment0455323Acc00700 := object_fragment0455323_field_006 fuel (fragment0455323Field007Chars00 ++ (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 255) (SourceJson.white (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))) fragment0455323Acc00800 := object_fragment0455323_field_007 fuel (fragment0455323Field008Chars00 ++ (fragment0455323Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 254) (SourceJson.white (fragment0455323Field009Chars00 ++ (tail))) fragment0455323Acc00900 := object_fragment0455323_field_008 fuel (fragment0455323Field009Chars00 ++ (tail))
    _ = .ok (fragment0455323Value, tail) := object_fragment0455323_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0134_before_reader"
  err.flush

noncomputable def chunk0134LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0134SuffixChars00 : List Char := [',']
noncomputable def chunk0134Chars00 : List Char := chunk0134LeadChars00 ++ fragment0453699Chars ++ chunk0134SuffixChars00
noncomputable def chunk0134Push00 (acc : List SourceJson) : List SourceJson := fragment0453699Value :: acc

noncomputable def chunk0134AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0134_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 470)
      (SourceJson.white (chunk0134LeadChars00 ++ (fragment0453699Chars ++ rest))) acc =
      (SourceJson.value (fuel + 469) (fragment0453699Chars ++ rest)).bind
        (chunk0134AfterValue00 (fuel + 469) acc) := by rfl

theorem array_chunk0134 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 470) (SourceJson.white (chunk0134Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 469) (SourceJson.white tail) (chunk0134Push00 acc) := by
  have hinput : chunk0134Chars00 ++ tail = chunk0134LeadChars00 ++ (fragment0453699Chars ++ (chunk0134SuffixChars00 ++ tail)) := by
    simp only [chunk0134Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 470) (SourceJson.white (chunk0134Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 470)
          (SourceJson.white (chunk0134LeadChars00 ++ (fragment0453699Chars ++ (chunk0134SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 470) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 469) (fragment0453699Chars ++ (chunk0134SuffixChars00 ++ tail))).bind
        (chunk0134AfterValue00 (fuel + 469) acc) := array_chunk0134_head fuel (chunk0134SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0453699Value, chunk0134SuffixChars00 ++ tail)).bind
        (chunk0134AfterValue00 (fuel + 469) acc) :=
      congrArg (fun result => result.bind (chunk0134AfterValue00 (fuel + 469) acc))
        (value_fragment0453699 (fuel + 223) (chunk0134SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 469) (SourceJson.white tail) (chunk0134Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0134_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0135_before_reader"
  err.flush

noncomputable def chunk0135LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0135SuffixChars00 : List Char := [',']
noncomputable def chunk0135Chars00 : List Char := chunk0135LeadChars00 ++ fragment0455323Chars ++ chunk0135SuffixChars00
noncomputable def chunk0135Push00 (acc : List SourceJson) : List SourceJson := fragment0455323Value :: acc

noncomputable def chunk0135AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0135_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 469)
      (SourceJson.white (chunk0135LeadChars00 ++ (fragment0455323Chars ++ rest))) acc =
      (SourceJson.value (fuel + 468) (fragment0455323Chars ++ rest)).bind
        (chunk0135AfterValue00 (fuel + 468) acc) := by rfl

theorem array_chunk0135 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 469) (SourceJson.white (chunk0135Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 468) (SourceJson.white tail) (chunk0135Push00 acc) := by
  have hinput : chunk0135Chars00 ++ tail = chunk0135LeadChars00 ++ (fragment0455323Chars ++ (chunk0135SuffixChars00 ++ tail)) := by
    simp only [chunk0135Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 469) (SourceJson.white (chunk0135Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 469)
          (SourceJson.white (chunk0135LeadChars00 ++ (fragment0455323Chars ++ (chunk0135SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 469) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 468) (fragment0455323Chars ++ (chunk0135SuffixChars00 ++ tail))).bind
        (chunk0135AfterValue00 (fuel + 468) acc) := array_chunk0135_head fuel (chunk0135SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0455323Value, chunk0135SuffixChars00 ++ tail)).bind
        (chunk0135AfterValue00 (fuel + 468) acc) :=
      congrArg (fun result => result.bind (chunk0135AfterValue00 (fuel + 468) acc))
        (value_fragment0455323 (fuel + 204) (chunk0135SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 468) (SourceJson.white tail) (chunk0135Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0135_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0134Chars00 ++ chunk0135Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0135Push00 (chunk0134Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 470) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 468) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0134Chars00 ++ (chunk0135Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 470) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 470) (SourceJson.white (chunk0134Chars00 ++ (chunk0135Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 470) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 469) (SourceJson.white (chunk0135Chars00 ++ (tail))) (chunk0134Push00 (acc)) := array_chunk0134 fuel (chunk0135Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 468) (SourceJson.white tail) (blockPush acc) := array_chunk0135 fuel (tail) (chunk0134Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 453693).take 3276 = blockChars := by rfl

theorem block_original_split : sourceRest 453693 = blockChars ++ sourceRest 456969 := by
  calc
    sourceRest 453693 = (sourceRest 453693).take 3276 ++ (sourceRest 453693).drop 3276 :=
      (List.take_append_drop 3276 (sourceRest 453693)).symm
    _ = blockChars ++ (sourceRest 453693).drop 3276 :=
      congrArg (fun part => part ++ (sourceRest 453693).drop 3276) block_original_prefix
    _ = blockChars ++ sourceRest 456969 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 453693 3276)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 470) (SourceJson.white (sourceRest 453693)) acc =
      SourceJson.array (fuel + 468) (SourceJson.white (sourceRest 456969)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 470) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 456969) acc)

#print axioms object_fragment0453699_field_000
#print axioms object_fragment0453699_field_001
#print axioms object_fragment0453699_field_002
#print axioms object_fragment0453699_field_003
#print axioms object_fragment0453699_field_004
#print axioms object_fragment0453699_field_005
#print axioms object_fragment0453699_field_006
#print axioms object_fragment0453699_field_007
#print axioms object_fragment0453699_field_008
#print axioms object_fragment0453699_field_009
#print axioms value_fragment0453699
#print axioms object_fragment0455323_field_000
#print axioms object_fragment0455323_field_001
#print axioms object_fragment0455323_field_002
#print axioms object_fragment0455323_field_003
#print axioms object_fragment0455323_field_004
#print axioms object_fragment0455323_field_005
#print axioms object_fragment0455323_field_006
#print axioms object_fragment0455323_field_007
#print axioms object_fragment0455323_field_008
#print axioms object_fragment0455323_field_009
#print axioms value_fragment0455323
#print axioms array_chunk0134_head
#print axioms array_chunk0134
#print axioms array_chunk0135_head
#print axioms array_chunk0135
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock068

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
