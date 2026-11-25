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

namespace SimplicesBlock009

noncomputable def fragment0256799Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0256799Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0256799Field000Value00 : SourceJson := .number (String.ofList ['1', '8'])
noncomputable def fragment0256799Acc00100 : List (String × SourceJson) := (fragment0256799Field000Key00, fragment0256799Field000Value00) :: fragment0256799Acc00000
noncomputable def fragment0256799Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '8', ',']

theorem object_fragment0256799_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 240) (SourceJson.white (fragment0256799Field000Chars00 ++ tail)) fragment0256799Acc00000 =
      SourceJson.object (fuel + 239) (SourceJson.white tail) fragment0256799Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_000"
  err.flush

noncomputable def fragment0256799Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0256799Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0256799Acc00200 : List (String × SourceJson) := (fragment0256799Field001Key00, fragment0256799Field001Value00) :: fragment0256799Acc00100
noncomputable def fragment0256799Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0256799_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0256799Field001Chars00 ++ tail)) fragment0256799Acc00100 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0256799Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_001"
  err.flush

noncomputable def fragment0256799Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0256799Field002Value00 : SourceJson := .str (String.ofList ['1', '1', '3', '6', '5', '2', '4', '5', '3', '5', '5', '1', '6', '9', '1', '4', '1', '4', '8', '8', '1', '7', '8', '8', '0', '2', '9', '8', '2', '3', '5', '7', '0', '6', '3', '2', '4', '3', '3', '4', '6', '8', '4', '7', '4', '8', '8', '9', '/', '4', '6', '1', '3', '6', '6', '9', '5', '3', '9', '2', '8', '2', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0256799Acc00300 : List (String × SourceJson) := (fragment0256799Field002Key00, fragment0256799Field002Value00) :: fragment0256799Acc00200
noncomputable def fragment0256799Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '1', '3', '6', '5', '2', '4', '5', '3', '5', '5', '1', '6', '9', '1', '4', '1', '4', '8', '8', '1', '7', '8', '8', '0', '2', '9', '8', '2', '3', '5', '7', '0', '6', '3', '2', '4', '3', '3', '4', '6', '8', '4', '7', '4', '8', '8', '9', '/', '4', '6', '1', '3', '6', '6', '9', '5', '3', '9', '2', '8', '2', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0256799_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0256799Field002Chars00 ++ tail)) fragment0256799Acc00200 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0256799Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_002"
  err.flush

noncomputable def fragment0256799Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0256799Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0256799Acc00400 : List (String × SourceJson) := (fragment0256799Field003Key00, fragment0256799Field003Value00) :: fragment0256799Acc00300
noncomputable def fragment0256799Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0256799_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0256799Field003Chars00 ++ tail)) fragment0256799Acc00300 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0256799Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_003"
  err.flush

noncomputable def fragment0256799Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0256799Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0256799Acc00500 : List (String × SourceJson) := (fragment0256799Field004Key00, fragment0256799Field004Value00) :: fragment0256799Acc00400
noncomputable def fragment0256799Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '0', '9', '3', '5', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0256799_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0256799Field004Chars00 ++ tail)) fragment0256799Acc00400 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0256799Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_004"
  err.flush

noncomputable def fragment0256799Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0256799Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '1', '3', '9', '2', '1', '1', '4', '2', '4', '3', '/', '3', '3', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '9', '4', '7', '3', '7', '8', '3', '9', '5', '4', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '4', '2', '3', '4', '5', '6', '5', '9', '1', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '2', '4', '6', '7', '9', '5', '1', '4', '3', '7', '3', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '8', '6', '9', '1', '7', '0', '4', '5', '0', '3', '/', '7', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '7', '0', '9', '8', '6', '2', '1', '1', '8', '1', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '5', '2', '6', '6', '8', '3', '3', '1', '1', '9', '/', '3', '1', '6', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '8', '6', '5', '1', '9', '8', '6', '8', '8', '7', '/', '9', '5', '0', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '7', '5', '1', '6', '2', '6', '5', '3', '0', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '2', '4', '5', '8', '2', '3', '3', '1', '9', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0256799Acc00600 : List (String × SourceJson) := (fragment0256799Field005Key00, fragment0256799Field005Value00) :: fragment0256799Acc00500
noncomputable def fragment0256799Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '3', '9', '2', '1', '1', '4', '2', '4', '3', '/', '3', '3', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '4', '7', '3', '7', '8', '3', '9', '5', '4', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '4', '2', '3', '4', '5', '6', '5', '9', '1', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '2', '4', '6', '7', '9', '5', '1', '4', '3', '7', '3', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '3', '8', '6', '9', '1', '7', '0', '4', '5', '0', '3', '/', '7', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '5', '7', '0', '9', '8', '6', '2', '1', '1', '8', '1', '/', '1', '1', '8', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '5', '2', '6', '6', '8', '3', '3', '1', '1', '9', '/', '3', '1', '6', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '3', '2', '8', '6', '5', '1', '9', '8', '6', '8', '8', '7', '/', '9', '5', '0', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '0', '7', '5', '1', '6', '2', '6', '5', '3', '0', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '2', '4', '5', '8', '2', '3', '3', '1', '9', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0256799_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0256799Field005Chars00 ++ tail)) fragment0256799Acc00500 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0256799Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_005"
  err.flush

noncomputable def fragment0256799Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0256799Field006Value00 : SourceJson := .str (String.ofList ['3', '6', '6', '1', '9', '7', '4', '3', '9', '6', '0', '5', '4', '0', '0', '8', '1', '3', '6', '7', '6', '5', '8', '0', '1', '7', '7', '3', '6', '8', '9', '6', '7', '7', '4', '2', '8', '1', '4', '5', '2', '0', '6', '4', '5', '4', '0', '5', '9', '4', '2', '7', '3', '1', '2', '5', '/', '2', '2', '0', '2', '4', '3', '0', '7', '4', '5', '6', '2', '8', '2', '4', '2', '3', '0', '9', '3', '0', '5', '5', '3', '4', '7', '5', '4', '8', '5', '4', '3', '5', '0', '7', '5', '2', '8', '1', '9', '8', '5', '0', '2', '2', '7', '5', '8', '2', '0', '6', '3', '5', '1', '3', '4', '4', '7', '8', '3', '4', '8', '4', '1', '2', '6', '1'])
noncomputable def fragment0256799Acc00700 : List (String × SourceJson) := (fragment0256799Field006Key00, fragment0256799Field006Value00) :: fragment0256799Acc00600
noncomputable def fragment0256799Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '6', '6', '1', '9', '7', '4', '3', '9', '6', '0', '5', '4', '0', '0', '8', '1', '3', '6', '7', '6', '5', '8', '0', '1', '7', '7', '3', '6', '8', '9', '6', '7', '7', '4', '2', '8', '1', '4', '5', '2', '0', '6', '4', '5', '4', '0', '5', '9', '4', '2', '7', '3', '1', '2', '5', '/', '2', '2', '0', '2', '4', '3', '0', '7', '4', '5', '6', '2', '8', '2', '4', '2', '3', '0', '9', '3', '0', '5', '5', '3', '4', '7', '5', '4', '8', '5', '4', '3', '5', '0', '7', '5', '2', '8', '1', '9', '8', '5', '0', '2', '2', '7', '5', '8', '2', '0', '6', '3', '5', '1', '3', '4', '4', '7', '8', '3', '4', '8', '4', '1', '2', '6', '1', '"', ',']

theorem object_fragment0256799_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0256799Field006Chars00 ++ tail)) fragment0256799Acc00600 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0256799Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_006"
  err.flush

noncomputable def fragment0256799Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0256799Field007Value00 : SourceJson := .str (String.ofList ['1', '1', '4', '1', '4', '1', '9', '0', '7', '7', '3', '4', '6', '1', '6', '1', '6', '5', '2', '0', '4', '7', '9', '2', '0', '2', '1', '6', '3', '5', '1', '8', '0', '2', '6', '0', '9', '4', '4', '1', '5', '6', '1', '1', '5', '4', '2', '3', '7', '2', '0', '2', '9', '2', '5', '7', '2', '0', '3', '8', '6', '4', '4', '7', '3', '4', '9', '3', '2', '8', '4', '5', '2', '3', '1', '9', '4', '9', '7', '6', '3', '5', '2', '3', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '9', '4', '6', '4', '7', '1', '9', '9', '7', '0', '2', '2', '1', '0', '0', '6', '7', '9', '3', '8', '8', '6', '5', '0', '5', '5', '1', '0', '5', '0', '5', '3', '5', '3', '7', '3', '0', '7', '4', '6', '7', '7', '5', '5', '4', '0', '6', '1', '7', '1', '6', '7', '2', '2', '6', '9', '2', '5', '2', '6', '8', '2', '3', '0', '1', '1', '6', '4', '1', '0', '6', '3', '2', '3', '5', '2', '1', '4', '7', '6', '4', '8', '3', '0', '1', '9', '6', '9', '3', '8', '6', '6', '5', '4', '5', '2', '7', '7', '3', '5', '8', '4', '8', '7', '5', '0', '6', '9', '1', '8', '6', '3', '4', '9', '8', '6', '3', '7'])
noncomputable def fragment0256799Acc00800 : List (String × SourceJson) := (fragment0256799Field007Key00, fragment0256799Field007Value00) :: fragment0256799Acc00700
noncomputable def fragment0256799Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '1', '4', '1', '4', '1', '9', '0', '7', '7', '3', '4', '6', '1', '6', '1', '6', '5', '2', '0', '4', '7', '9', '2', '0', '2', '1', '6', '3', '5', '1', '8', '0', '2', '6', '0', '9', '4', '4', '1', '5', '6', '1', '1', '5', '4', '2', '3', '7', '2', '0', '2', '9', '2', '5', '7', '2', '0', '3', '8', '6', '4', '4', '7', '3', '4', '9', '3', '2', '8', '4', '5', '2', '3', '1', '9', '4', '9', '7', '6', '3', '5', '2', '3', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '9', '4', '6', '4', '7', '1', '9', '9', '7', '0', '2', '2', '1', '0', '0', '6', '7', '9', '3', '8', '8', '6', '5', '0', '5', '5', '1', '0', '5', '0', '5', '3', '5', '3', '7', '3', '0', '7', '4', '6', '7', '7', '5', '5', '4', '0', '6', '1', '7', '1', '6', '7', '2', '2', '6', '9', '2', '5', '2', '6', '8', '2', '3', '0', '1', '1', '6', '4', '1', '0', '6', '3', '2', '3', '5', '2', '1', '4', '7', '6', '4', '8', '3', '0', '1', '9', '6', '9', '3', '8', '6', '6', '5', '4', '5', '2', '7', '7', '3', '5', '8', '4', '8', '7', '5', '0', '6', '9', '1', '8', '6', '3', '4', '9', '8', '6', '3', '7', '"', ',']

theorem object_fragment0256799_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0256799Field007Chars00 ++ tail)) fragment0256799Acc00700 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0256799Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_007"
  err.flush

noncomputable def fragment0256799Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0256799Field008Value00 : SourceJson := .str (String.ofList ['1', '3', '1', '7', '3', '2', '4', '0', '6', '6', '3', '7', '3', '2', '2', '9', '2', '8', '9'])
noncomputable def fragment0256799Acc00900 : List (String × SourceJson) := (fragment0256799Field008Key00, fragment0256799Field008Value00) :: fragment0256799Acc00800
noncomputable def fragment0256799Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '1', '7', '3', '2', '4', '0', '6', '6', '3', '7', '3', '2', '2', '9', '2', '8', '9', '"', ',']

theorem object_fragment0256799_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0256799Field008Chars00 ++ tail)) fragment0256799Acc00800 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0256799Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_008"
  err.flush

noncomputable def fragment0256799Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0256799Field009Value00 : SourceJson := .str (String.ofList ['9', '0', '9', '1', '9', '2', '0', '8', '5', '2', '3', '3', '2', '1', '8', '1', '3', '1', '0'])
noncomputable def fragment0256799Acc01000 : List (String × SourceJson) := (fragment0256799Field009Key00, fragment0256799Field009Value00) :: fragment0256799Acc00900
noncomputable def fragment0256799Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '9', '0', '9', '1', '9', '2', '0', '8', '5', '2', '3', '3', '2', '1', '8', '1', '3', '1', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0256799_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0256799Field009Chars00 ++ tail)) fragment0256799Acc00900 =
      .ok (.obj (fragment0256799Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0256799_object_field_009"
  err.flush

noncomputable def fragment0256799Chars : List Char := '{' :: (fragment0256799Field000Chars00 ++ fragment0256799Field001Chars00 ++ fragment0256799Field002Chars00 ++ fragment0256799Field003Chars00 ++ fragment0256799Field004Chars00 ++ fragment0256799Field005Chars00 ++ fragment0256799Field006Chars00 ++ fragment0256799Field007Chars00 ++ fragment0256799Field008Chars00 ++ fragment0256799Field009Chars00)
noncomputable def fragment0256799Value : SourceJson := .obj (fragment0256799Acc01000.reverse)

theorem value_fragment0256799 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 241) (fragment0256799Chars ++ tail) =
      .ok (fragment0256799Value, tail) := by
  have hinput : fragment0256799Chars ++ tail = '{' :: (fragment0256799Field000Chars00 ++ (fragment0256799Field001Chars00 ++ (fragment0256799Field002Chars00 ++ (fragment0256799Field003Chars00 ++ (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0256799Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 241) (fragment0256799Chars ++ tail) =
        SourceJson.value (fuel + 241) ('{' :: (fragment0256799Field000Chars00 ++ (fragment0256799Field001Chars00 ++ (fragment0256799Field002Chars00 ++ (fragment0256799Field003Chars00 ++ (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 241)) hinput
    _ = SourceJson.object (fuel + 240) (SourceJson.white (fragment0256799Field000Chars00 ++ (fragment0256799Field001Chars00 ++ (fragment0256799Field002Chars00 ++ (fragment0256799Field003Chars00 ++ (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))))))))))) fragment0256799Acc00000 := by rfl
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0256799Field001Chars00 ++ (fragment0256799Field002Chars00 ++ (fragment0256799Field003Chars00 ++ (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail))))))))))) fragment0256799Acc00100 := object_fragment0256799_field_000 fuel (fragment0256799Field001Chars00 ++ (fragment0256799Field002Chars00 ++ (fragment0256799Field003Chars00 ++ (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0256799Field002Chars00 ++ (fragment0256799Field003Chars00 ++ (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))))))))) fragment0256799Acc00200 := object_fragment0256799_field_001 fuel (fragment0256799Field002Chars00 ++ (fragment0256799Field003Chars00 ++ (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0256799Field003Chars00 ++ (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail))))))))) fragment0256799Acc00300 := object_fragment0256799_field_002 fuel (fragment0256799Field003Chars00 ++ (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))))))) fragment0256799Acc00400 := object_fragment0256799_field_003 fuel (fragment0256799Field004Chars00 ++ (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail))))))) fragment0256799Acc00500 := object_fragment0256799_field_004 fuel (fragment0256799Field005Chars00 ++ (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))))) fragment0256799Acc00600 := object_fragment0256799_field_005 fuel (fragment0256799Field006Chars00 ++ (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail))))) fragment0256799Acc00700 := object_fragment0256799_field_006 fuel (fragment0256799Field007Chars00 ++ (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))) fragment0256799Acc00800 := object_fragment0256799_field_007 fuel (fragment0256799Field008Chars00 ++ (fragment0256799Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0256799Field009Chars00 ++ (tail))) fragment0256799Acc00900 := object_fragment0256799_field_008 fuel (fragment0256799Field009Chars00 ++ (tail))
    _ = .ok (fragment0256799Value, tail) := object_fragment0256799_field_009 fuel (tail)

noncomputable def fragment0258437Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0258437Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0258437Field000Value00 : SourceJson := .number (String.ofList ['1', '9'])
noncomputable def fragment0258437Acc00100 : List (String × SourceJson) := (fragment0258437Field000Key00, fragment0258437Field000Value00) :: fragment0258437Acc00000
noncomputable def fragment0258437Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '9', ',']

theorem object_fragment0258437_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 211) (SourceJson.white (fragment0258437Field000Chars00 ++ tail)) fragment0258437Acc00000 =
      SourceJson.object (fuel + 210) (SourceJson.white tail) fragment0258437Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_000"
  err.flush

noncomputable def fragment0258437Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0258437Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0258437Acc00200 : List (String × SourceJson) := (fragment0258437Field001Key00, fragment0258437Field001Value00) :: fragment0258437Acc00100
noncomputable def fragment0258437Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0258437_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0258437Field001Chars00 ++ tail)) fragment0258437Acc00100 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0258437Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_001"
  err.flush

noncomputable def fragment0258437Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0258437Field002Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '1', '6', '8', '0', '2', '7', '5', '7', '2', '5', '7', '5', '5', '1', '3', '1', '2', '9', '2', '5', '5', '4', '6', '7', '8', '0', '6', '3', '6', '0', '6', '7', '3', '7', '3', '8', '0', '7', '4', '6', '1', '9', '/', '1', '5', '2', '2', '6', '6', '3', '2', '1', '4', '2', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0258437Acc00300 : List (String × SourceJson) := (fragment0258437Field002Key00, fragment0258437Field002Value00) :: fragment0258437Acc00200
noncomputable def fragment0258437Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '5', '7', '5', '1', '6', '8', '0', '2', '7', '5', '7', '2', '5', '7', '5', '5', '1', '3', '1', '2', '9', '2', '5', '5', '4', '6', '7', '8', '0', '6', '3', '6', '0', '6', '7', '3', '7', '3', '8', '0', '7', '4', '6', '1', '9', '/', '1', '5', '2', '2', '6', '6', '3', '2', '1', '4', '2', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0258437_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0258437Field002Chars00 ++ tail)) fragment0258437Acc00200 =
      SourceJson.object (fuel + 208) (SourceJson.white tail) fragment0258437Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_002"
  err.flush

noncomputable def fragment0258437Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0258437Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0258437Acc00400 : List (String × SourceJson) := (fragment0258437Field003Key00, fragment0258437Field003Value00) :: fragment0258437Acc00300
noncomputable def fragment0258437Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0258437_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0258437Field003Chars00 ++ tail)) fragment0258437Acc00300 =
      SourceJson.object (fuel + 207) (SourceJson.white tail) fragment0258437Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_003"
  err.flush

noncomputable def fragment0258437Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0258437Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0258437Acc00500 : List (String × SourceJson) := (fragment0258437Field004Key00, fragment0258437Field004Value00) :: fragment0258437Acc00400
noncomputable def fragment0258437Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '4', '9', '8', '9', '/', '9', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0258437_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 207) (SourceJson.white (fragment0258437Field004Chars00 ++ tail)) fragment0258437Acc00400 =
      SourceJson.object (fuel + 206) (SourceJson.white tail) fragment0258437Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_004"
  err.flush

noncomputable def fragment0258437Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0258437Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '7', '8', '7', '2', '3', '1', '0', '2', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '7', '5', '8', '0', '7', '3', '0', '0', '1', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '9', '1', '9', '5', '4', '7', '5', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '0', '8', '6', '0', '3', '2', '7', '5', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '8', '7', '3', '5', '1', '3', '0', '6', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '4', '3', '5', '7', '4', '4', '6', '3', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '6', '3', '2', '7', '4', '9', '6', '9', '7', '1', '/', '2', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '4', '7', '1', '6', '0', '0', '5', '6', '1', '/', '2', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '3', '8', '5', '8', '1', '9', '0', '0', '9', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '3', '1', '9', '6', '6', '1', '0', '5', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0258437Acc00600 : List (String × SourceJson) := (fragment0258437Field005Key00, fragment0258437Field005Value00) :: fragment0258437Acc00500
noncomputable def fragment0258437Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '7', '2', '3', '1', '0', '2', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '5', '8', '0', '7', '3', '0', '0', '1', '/', '2', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '1', '9', '1', '9', '5', '4', '7', '5', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '0', '8', '6', '0', '3', '2', '7', '5', '3', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '6', '8', '7', '3', '5', '1', '3', '0', '6', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '9', '4', '3', '5', '7', '4', '4', '6', '3', '/', '3', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '6', '3', '2', '7', '4', '9', '6', '9', '7', '1', '/', '2', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '0', '4', '7', '1', '6', '0', '0', '5', '6', '1', '/', '2', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '3', '8', '5', '8', '1', '9', '0', '0', '9', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '3', '1', '9', '6', '6', '1', '0', '5', '7', '/', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0258437_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0258437Field005Chars00 ++ tail)) fragment0258437Acc00500 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0258437Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_005"
  err.flush

noncomputable def fragment0258437Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0258437Field006Value00 : SourceJson := .str (String.ofList ['1', '5', '0', '1', '1', '2', '2', '8', '7', '4', '9', '6', '5', '2', '7', '3', '6', '4', '5', '8', '0', '0', '9', '5', '1', '3', '2', '4', '1', '1', '5', '8', '7', '1', '2', '1', '9', '6', '4', '6', '9', '4', '2', '2', '8', '9', '1', '9', '4', '4', '4', '2', '9', '3', '7', '5', '/', '6', '5', '1', '1', '4', '0', '6', '2', '7', '0', '0', '7', '0', '5', '9', '6', '9', '0', '1', '6', '1', '9', '0', '0', '1', '8', '6', '7', '1', '1', '7', '5', '9', '9', '2', '5', '5', '8', '4', '5', '5', '3', '0', '8', '7', '6', '9', '1', '4', '6', '3', '1', '9', '4', '2', '5', '0', '4', '3', '9', '1', '8', '2', '7', '6', '8'])
noncomputable def fragment0258437Acc00700 : List (String × SourceJson) := (fragment0258437Field006Key00, fragment0258437Field006Value00) :: fragment0258437Acc00600
noncomputable def fragment0258437Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '1', '5', '0', '1', '1', '2', '2', '8', '7', '4', '9', '6', '5', '2', '7', '3', '6', '4', '5', '8', '0', '0', '9', '5', '1', '3', '2', '4', '1', '1', '5', '8', '7', '1', '2', '1', '9', '6', '4', '6', '9', '4', '2', '2', '8', '9', '1', '9', '4', '4', '4', '2', '9', '3', '7', '5', '/', '6', '5', '1', '1', '4', '0', '6', '2', '7', '0', '0', '7', '0', '5', '9', '6', '9', '0', '1', '6', '1', '9', '0', '0', '1', '8', '6', '7', '1', '1', '7', '5', '9', '9', '2', '5', '5', '8', '4', '5', '5', '3', '0', '8', '7', '6', '9', '1', '4', '6', '3', '1', '9', '4', '2', '5', '0', '4', '3', '9', '1', '8', '2', '7', '6', '8', '"', ',']

theorem object_fragment0258437_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0258437Field006Chars00 ++ tail)) fragment0258437Acc00600 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0258437Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_006"
  err.flush

noncomputable def fragment0258437Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0258437Field007Value00 : SourceJson := .str (String.ofList ['3', '4', '3', '0', '6', '3', '0', '2', '7', '5', '3', '7', '2', '6', '0', '4', '3', '9', '3', '7', '8', '9', '2', '3', '1', '9', '4', '9', '1', '5', '0', '9', '4', '4', '5', '4', '6', '8', '1', '0', '6', '7', '7', '1', '5', '2', '3', '6', '9', '6', '9', '4', '7', '5', '2', '4', '2', '1', '3', '3', '5', '2', '3', '6', '1', '4', '7', '1', '5', '0', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '3', '2', '2', '7', '9', '3', '2', '8', '4', '1', '1', '8', '5', '9', '3', '2', '6', '6', '4', '7', '2', '5', '0', '0', '4', '7', '4', '8', '7', '2', '7', '7', '5', '4', '4', '0', '4', '5', '0', '5', '3', '5', '2', '6', '8', '7', '4', '3', '8', '3', '7', '1', '5', '7', '8', '6', '1', '1', '7', '8', '1', '7', '2', '0', '4', '6', '3', '3', '8', '4', '5', '5', '9', '4', '3', '0', '9', '4', '0', '4', '1', '1', '5', '3', '7', '9', '6', '1', '6', '2', '0', '9', '1', '9', '0', '0', '2', '6', '7', '7', '4', '2', '9'])
noncomputable def fragment0258437Acc00800 : List (String × SourceJson) := (fragment0258437Field007Key00, fragment0258437Field007Value00) :: fragment0258437Acc00700
noncomputable def fragment0258437Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '4', '3', '0', '6', '3', '0', '2', '7', '5', '3', '7', '2', '6', '0', '4', '3', '9', '3', '7', '8', '9', '2', '3', '1', '9', '4', '9', '1', '5', '0', '9', '4', '4', '5', '4', '6', '8', '1', '0', '6', '7', '7', '1', '5', '2', '3', '6', '9', '6', '9', '4', '7', '5', '2', '4', '2', '1', '3', '3', '5', '2', '3', '6', '1', '4', '7', '1', '5', '0', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '3', '2', '2', '7', '9', '3', '2', '8', '4', '1', '1', '8', '5', '9', '3', '2', '6', '6', '4', '7', '2', '5', '0', '0', '4', '7', '4', '8', '7', '2', '7', '7', '5', '4', '4', '0', '4', '5', '0', '5', '3', '5', '2', '6', '8', '7', '4', '3', '8', '3', '7', '1', '5', '7', '8', '6', '1', '1', '7', '8', '1', '7', '2', '0', '4', '6', '3', '3', '8', '4', '5', '5', '9', '4', '3', '0', '9', '4', '0', '4', '1', '1', '5', '3', '7', '9', '6', '1', '6', '2', '0', '9', '1', '9', '0', '0', '2', '6', '7', '7', '4', '2', '9', '"', ',']

theorem object_fragment0258437_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0258437Field007Chars00 ++ tail)) fragment0258437Acc00700 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0258437Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_007"
  err.flush

noncomputable def fragment0258437Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0258437Field008Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '6', '5', '0', '5', '7', '0', '6', '4', '2', '9', '2', '0', '3', '4', '9', '1'])
noncomputable def fragment0258437Acc00900 : List (String × SourceJson) := (fragment0258437Field008Key00, fragment0258437Field008Value00) :: fragment0258437Acc00800
noncomputable def fragment0258437Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '2', '6', '5', '0', '5', '7', '0', '6', '4', '2', '9', '2', '0', '3', '4', '9', '1', '"', ',']

theorem object_fragment0258437_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0258437Field008Chars00 ++ tail)) fragment0258437Acc00800 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0258437Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_008"
  err.flush

noncomputable def fragment0258437Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0258437Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '3', '7', '4', '2', '7', '0', '4', '1', '5', '6', '7', '0', '5', '8', '3', '3', '1', '5'])
noncomputable def fragment0258437Acc01000 : List (String × SourceJson) := (fragment0258437Field009Key00, fragment0258437Field009Value00) :: fragment0258437Acc00900
noncomputable def fragment0258437Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '3', '7', '4', '2', '7', '0', '4', '1', '5', '6', '7', '0', '5', '8', '3', '3', '1', '5', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0258437_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0258437Field009Chars00 ++ tail)) fragment0258437Acc00900 =
      .ok (.obj (fragment0258437Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0258437_object_field_009"
  err.flush

noncomputable def fragment0258437Chars : List Char := '{' :: (fragment0258437Field000Chars00 ++ fragment0258437Field001Chars00 ++ fragment0258437Field002Chars00 ++ fragment0258437Field003Chars00 ++ fragment0258437Field004Chars00 ++ fragment0258437Field005Chars00 ++ fragment0258437Field006Chars00 ++ fragment0258437Field007Chars00 ++ fragment0258437Field008Chars00 ++ fragment0258437Field009Chars00)
noncomputable def fragment0258437Value : SourceJson := .obj (fragment0258437Acc01000.reverse)

theorem value_fragment0258437 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 212) (fragment0258437Chars ++ tail) =
      .ok (fragment0258437Value, tail) := by
  have hinput : fragment0258437Chars ++ tail = '{' :: (fragment0258437Field000Chars00 ++ (fragment0258437Field001Chars00 ++ (fragment0258437Field002Chars00 ++ (fragment0258437Field003Chars00 ++ (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0258437Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 212) (fragment0258437Chars ++ tail) =
        SourceJson.value (fuel + 212) ('{' :: (fragment0258437Field000Chars00 ++ (fragment0258437Field001Chars00 ++ (fragment0258437Field002Chars00 ++ (fragment0258437Field003Chars00 ++ (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 212)) hinput
    _ = SourceJson.object (fuel + 211) (SourceJson.white (fragment0258437Field000Chars00 ++ (fragment0258437Field001Chars00 ++ (fragment0258437Field002Chars00 ++ (fragment0258437Field003Chars00 ++ (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))))))))))) fragment0258437Acc00000 := by rfl
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0258437Field001Chars00 ++ (fragment0258437Field002Chars00 ++ (fragment0258437Field003Chars00 ++ (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail))))))))))) fragment0258437Acc00100 := object_fragment0258437_field_000 fuel (fragment0258437Field001Chars00 ++ (fragment0258437Field002Chars00 ++ (fragment0258437Field003Chars00 ++ (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0258437Field002Chars00 ++ (fragment0258437Field003Chars00 ++ (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))))))))) fragment0258437Acc00200 := object_fragment0258437_field_001 fuel (fragment0258437Field002Chars00 ++ (fragment0258437Field003Chars00 ++ (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0258437Field003Chars00 ++ (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail))))))))) fragment0258437Acc00300 := object_fragment0258437_field_002 fuel (fragment0258437Field003Chars00 ++ (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 207) (SourceJson.white (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))))))) fragment0258437Acc00400 := object_fragment0258437_field_003 fuel (fragment0258437Field004Chars00 ++ (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail))))))) fragment0258437Acc00500 := object_fragment0258437_field_004 fuel (fragment0258437Field005Chars00 ++ (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))))) fragment0258437Acc00600 := object_fragment0258437_field_005 fuel (fragment0258437Field006Chars00 ++ (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail))))) fragment0258437Acc00700 := object_fragment0258437_field_006 fuel (fragment0258437Field007Chars00 ++ (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))) fragment0258437Acc00800 := object_fragment0258437_field_007 fuel (fragment0258437Field008Chars00 ++ (fragment0258437Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0258437Field009Chars00 ++ (tail))) fragment0258437Acc00900 := object_fragment0258437_field_008 fuel (fragment0258437Field009Chars00 ++ (tail))
    _ = .ok (fragment0258437Value, tail) := object_fragment0258437_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_before_reader"
  err.flush

noncomputable def chunk0018LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0018SuffixChars00 : List Char := [',']
noncomputable def chunk0018Chars00 : List Char := chunk0018LeadChars00 ++ fragment0256799Chars ++ chunk0018SuffixChars00
noncomputable def chunk0018Push00 (acc : List SourceJson) : List SourceJson := fragment0256799Value :: acc

noncomputable def chunk0018AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0018_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 586)
      (SourceJson.white (chunk0018LeadChars00 ++ (fragment0256799Chars ++ rest))) acc =
      (SourceJson.value (fuel + 585) (fragment0256799Chars ++ rest)).bind
        (chunk0018AfterValue00 (fuel + 585) acc) := by rfl

theorem array_chunk0018 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 586) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 585) (SourceJson.white tail) (chunk0018Push00 acc) := by
  have hinput : chunk0018Chars00 ++ tail = chunk0018LeadChars00 ++ (fragment0256799Chars ++ (chunk0018SuffixChars00 ++ tail)) := by
    simp only [chunk0018Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 586) (SourceJson.white (chunk0018Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 586)
          (SourceJson.white (chunk0018LeadChars00 ++ (fragment0256799Chars ++ (chunk0018SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 586) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 585) (fragment0256799Chars ++ (chunk0018SuffixChars00 ++ tail))).bind
        (chunk0018AfterValue00 (fuel + 585) acc) := array_chunk0018_head fuel (chunk0018SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0256799Value, chunk0018SuffixChars00 ++ tail)).bind
        (chunk0018AfterValue00 (fuel + 585) acc) :=
      congrArg (fun result => result.bind (chunk0018AfterValue00 (fuel + 585) acc))
        (value_fragment0256799 (fuel + 344) (chunk0018SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 585) (SourceJson.white tail) (chunk0018Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0018_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_before_reader"
  err.flush

noncomputable def chunk0019LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0019SuffixChars00 : List Char := [',']
noncomputable def chunk0019Chars00 : List Char := chunk0019LeadChars00 ++ fragment0258437Chars ++ chunk0019SuffixChars00
noncomputable def chunk0019Push00 (acc : List SourceJson) : List SourceJson := fragment0258437Value :: acc

noncomputable def chunk0019AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0019_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 585)
      (SourceJson.white (chunk0019LeadChars00 ++ (fragment0258437Chars ++ rest))) acc =
      (SourceJson.value (fuel + 584) (fragment0258437Chars ++ rest)).bind
        (chunk0019AfterValue00 (fuel + 584) acc) := by rfl

theorem array_chunk0019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 585) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 584) (SourceJson.white tail) (chunk0019Push00 acc) := by
  have hinput : chunk0019Chars00 ++ tail = chunk0019LeadChars00 ++ (fragment0258437Chars ++ (chunk0019SuffixChars00 ++ tail)) := by
    simp only [chunk0019Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 585) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 585)
          (SourceJson.white (chunk0019LeadChars00 ++ (fragment0258437Chars ++ (chunk0019SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 585) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 584) (fragment0258437Chars ++ (chunk0019SuffixChars00 ++ tail))).bind
        (chunk0019AfterValue00 (fuel + 584) acc) := array_chunk0019_head fuel (chunk0019SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0258437Value, chunk0019SuffixChars00 ++ tail)).bind
        (chunk0019AfterValue00 (fuel + 584) acc) :=
      congrArg (fun result => result.bind (chunk0019AfterValue00 (fuel + 584) acc))
        (value_fragment0258437 (fuel + 372) (chunk0019SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 584) (SourceJson.white tail) (chunk0019Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0018Chars00 ++ chunk0019Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0019Push00 (chunk0018Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 586) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 584) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 586) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 586) (SourceJson.white (chunk0018Chars00 ++ (chunk0019Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 586) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 585) (SourceJson.white (chunk0019Chars00 ++ (tail))) (chunk0018Push00 (acc)) := array_chunk0018 fuel (chunk0019Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 584) (SourceJson.white tail) (blockPush acc) := array_chunk0019 fuel (tail) (chunk0018Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 256793).take 3206 = blockChars := by rfl

theorem block_original_split : sourceRest 256793 = blockChars ++ sourceRest 259999 := by
  calc
    sourceRest 256793 = (sourceRest 256793).take 3206 ++ (sourceRest 256793).drop 3206 :=
      (List.take_append_drop 3206 (sourceRest 256793)).symm
    _ = blockChars ++ (sourceRest 256793).drop 3206 :=
      congrArg (fun part => part ++ (sourceRest 256793).drop 3206) block_original_prefix
    _ = blockChars ++ sourceRest 259999 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 256793 3206)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 586) (SourceJson.white (sourceRest 256793)) acc =
      SourceJson.array (fuel + 584) (SourceJson.white (sourceRest 259999)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 586) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 259999) acc)

#print axioms object_fragment0256799_field_000
#print axioms object_fragment0256799_field_001
#print axioms object_fragment0256799_field_002
#print axioms object_fragment0256799_field_003
#print axioms object_fragment0256799_field_004
#print axioms object_fragment0256799_field_005
#print axioms object_fragment0256799_field_006
#print axioms object_fragment0256799_field_007
#print axioms object_fragment0256799_field_008
#print axioms object_fragment0256799_field_009
#print axioms value_fragment0256799
#print axioms object_fragment0258437_field_000
#print axioms object_fragment0258437_field_001
#print axioms object_fragment0258437_field_002
#print axioms object_fragment0258437_field_003
#print axioms object_fragment0258437_field_004
#print axioms object_fragment0258437_field_005
#print axioms object_fragment0258437_field_006
#print axioms object_fragment0258437_field_007
#print axioms object_fragment0258437_field_008
#print axioms object_fragment0258437_field_009
#print axioms value_fragment0258437
#print axioms array_chunk0018_head
#print axioms array_chunk0018
#print axioms array_chunk0019_head
#print axioms array_chunk0019
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock009

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
