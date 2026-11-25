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

namespace SimplicesBlock008

noncomputable def fragment0253297Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0253297Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0253297Field000Value00 : SourceJson := .number (String.ofList ['1', '6'])
noncomputable def fragment0253297Acc00100 : List (String × SourceJson) := (fragment0253297Field000Key00, fragment0253297Field000Value00) :: fragment0253297Acc00000
noncomputable def fragment0253297Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '6', ',']

theorem object_fragment0253297_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 239) (SourceJson.white (fragment0253297Field000Chars00 ++ tail)) fragment0253297Acc00000 =
      SourceJson.object (fuel + 238) (SourceJson.white tail) fragment0253297Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_000"
  err.flush

noncomputable def fragment0253297Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0253297Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '2']), .number (String.ofList ['2']), .number (String.ofList ['0'])]
noncomputable def fragment0253297Acc00200 : List (String × SourceJson) := (fragment0253297Field001Key00, fragment0253297Field001Value00) :: fragment0253297Acc00100
noncomputable def fragment0253297Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0253297_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 238) (SourceJson.white (fragment0253297Field001Chars00 ++ tail)) fragment0253297Acc00100 =
      SourceJson.object (fuel + 237) (SourceJson.white tail) fragment0253297Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_001"
  err.flush

noncomputable def fragment0253297Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0253297Field002Value00 : SourceJson := .str (String.ofList ['1', '7', '3', '3', '5', '0', '9', '7', '6', '4', '2', '2', '3', '2', '8', '5', '8', '5', '7', '1', '5', '2', '1', '5', '3', '4', '2', '5', '9', '1', '4', '7', '0', '6', '6', '0', '8', '4', '4', '2', '7', '3', '7', '3', '0', '9', '1', '/', '4', '9', '2', '1', '2', '4', '7', '5', '0', '8', '5', '6', '8', '4', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0253297Acc00300 : List (String × SourceJson) := (fragment0253297Field002Key00, fragment0253297Field002Value00) :: fragment0253297Acc00200
noncomputable def fragment0253297Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '1', '7', '3', '3', '5', '0', '9', '7', '6', '4', '2', '2', '3', '2', '8', '5', '8', '5', '7', '1', '5', '2', '1', '5', '3', '4', '2', '5', '9', '1', '4', '7', '0', '6', '6', '0', '8', '4', '4', '2', '7', '3', '7', '3', '0', '9', '1', '/', '4', '9', '2', '1', '2', '4', '7', '5', '0', '8', '5', '6', '8', '4', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0253297_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 237) (SourceJson.white (fragment0253297Field002Chars00 ++ tail)) fragment0253297Acc00200 =
      SourceJson.object (fuel + 236) (SourceJson.white tail) fragment0253297Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_002"
  err.flush

noncomputable def fragment0253297Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0253297Field003Value00 : SourceJson := .str (String.ofList ['5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0253297Acc00400 : List (String × SourceJson) := (fragment0253297Field003Key00, fragment0253297Field003Value00) :: fragment0253297Acc00300
noncomputable def fragment0253297Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '1', '5', '5', '3', '3', '/', '8', '8', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0253297_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 236) (SourceJson.white (fragment0253297Field003Chars00 ++ tail)) fragment0253297Acc00300 =
      SourceJson.object (fuel + 235) (SourceJson.white tail) fragment0253297Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_003"
  err.flush

noncomputable def fragment0253297Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0253297Field004Value00 : SourceJson := .arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0253297Acc00500 : List (String × SourceJson) := (fragment0253297Field004Key00, fragment0253297Field004Value00) :: fragment0253297Acc00400
noncomputable def fragment0253297Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '8', '4', '3', '3', '1', '/', '2', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '7', '0', '3', '/', '7', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0253297_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 235) (SourceJson.white (fragment0253297Field004Chars00 ++ tail)) fragment0253297Acc00400 =
      SourceJson.object (fuel + 234) (SourceJson.white tail) fragment0253297Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_004"
  err.flush

noncomputable def fragment0253297Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0253297Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '8', '1', '1', '6', '4', '7', '7', '6', '9', '7', '9', '/', '3', '3', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '9', '3', '1', '4', '6', '4', '7', '8', '6', '9', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '5', '1', '1', '6', '0', '3', '3', '8', '2', '7', '/', '3', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '5', '1', '3', '2', '2', '5', '0', '6', '7', '7', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '2', '1', '4', '0', '2', '3', '8', '9', '6', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '7', '2', '2', '3', '6', '3', '7', '7', '3', '3', '/', '3', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '3', '0', '3', '7', '1', '3', '3', '6', '1', '5', '7', '/', '9', '5', '0', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '7', '7', '4', '0', '9', '4', '1', '2', '2', '9', '/', '3', '1', '6', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '3', '6', '5', '8', '9', '7', '4', '5', '0', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '0', '8', '6', '6', '8', '7', '2', '3', '4', '9', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0253297Acc00600 : List (String × SourceJson) := (fragment0253297Field005Key00, fragment0253297Field005Value00) :: fragment0253297Acc00500
noncomputable def fragment0253297Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '1', '1', '6', '4', '7', '7', '6', '9', '7', '9', '/', '3', '3', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '9', '3', '1', '4', '6', '4', '7', '8', '6', '9', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '7', '5', '1', '1', '6', '0', '3', '3', '8', '2', '7', '/', '3', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '3', '5', '1', '3', '2', '2', '5', '0', '6', '7', '7', '7', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '6', '7', '2', '1', '4', '0', '2', '3', '8', '9', '6', '1', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '8', '7', '2', '2', '3', '6', '3', '7', '7', '3', '3', '/', '3', '9', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '4', '3', '0', '3', '7', '1', '3', '3', '6', '1', '5', '7', '/', '9', '5', '0', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '7', '7', '7', '4', '0', '9', '4', '1', '2', '2', '9', '/', '3', '1', '6', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '8', '3', '6', '5', '8', '9', '7', '4', '5', '0', '3', '/', '2', '3', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '5', '0', '8', '6', '6', '8', '7', '2', '3', '4', '9', '/', '7', '1', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0253297_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 234) (SourceJson.white (fragment0253297Field005Chars00 ++ tail)) fragment0253297Acc00500 =
      SourceJson.object (fuel + 233) (SourceJson.white tail) fragment0253297Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_005"
  err.flush

noncomputable def fragment0253297Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0253297Field006Value00 : SourceJson := .str (String.ofList ['3', '3', '9', '6', '5', '9', '3', '4', '9', '8', '1', '0', '5', '5', '3', '5', '9', '1', '6', '4', '5', '1', '4', '3', '1', '5', '9', '1', '6', '8', '0', '2', '2', '7', '1', '8', '6', '5', '4', '2', '5', '6', '2', '1', '7', '8', '4', '4', '1', '8', '2', '9', '6', '8', '7', '5', '/', '1', '4', '7', '2', '9', '3', '5', '2', '0', '8', '6', '6', '3', '2', '8', '6', '2', '6', '0', '1', '0', '3', '2', '5', '1', '0', '3', '9', '4', '9', '8', '3', '7', '0', '2', '2', '2', '7', '4', '7', '6', '3', '2', '0', '3', '0', '1', '9', '8', '9', '6', '0', '1', '1', '1', '8', '8', '4', '9', '6', '9', '0', '3', '6', '2', '2', '8'])
noncomputable def fragment0253297Acc00700 : List (String × SourceJson) := (fragment0253297Field006Key00, fragment0253297Field006Value00) :: fragment0253297Acc00600
noncomputable def fragment0253297Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '3', '9', '6', '5', '9', '3', '4', '9', '8', '1', '0', '5', '5', '3', '5', '9', '1', '6', '4', '5', '1', '4', '3', '1', '5', '9', '1', '6', '8', '0', '2', '2', '7', '1', '8', '6', '5', '4', '2', '5', '6', '2', '1', '7', '8', '4', '4', '1', '8', '2', '9', '6', '8', '7', '5', '/', '1', '4', '7', '2', '9', '3', '5', '2', '0', '8', '6', '6', '3', '2', '8', '6', '2', '6', '0', '1', '0', '3', '2', '5', '1', '0', '3', '9', '4', '9', '8', '3', '7', '0', '2', '2', '2', '7', '4', '7', '6', '3', '2', '0', '3', '0', '1', '9', '8', '9', '6', '0', '1', '1', '1', '8', '8', '4', '9', '6', '9', '0', '3', '6', '2', '2', '8', '"', ',']

theorem object_fragment0253297_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0253297Field006Chars00 ++ tail)) fragment0253297Acc00600 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0253297Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_006"
  err.flush

noncomputable def fragment0253297Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0253297Field007Value00 : SourceJson := .str (String.ofList ['2', '0', '9', '2', '5', '1', '8', '3', '5', '9', '2', '5', '2', '8', '5', '2', '0', '2', '6', '3', '8', '6', '9', '6', '9', '1', '4', '4', '2', '0', '5', '2', '6', '0', '1', '3', '7', '7', '7', '9', '3', '8', '1', '3', '3', '4', '0', '2', '5', '0', '8', '3', '1', '8', '8', '8', '7', '7', '5', '3', '4', '2', '2', '8', '2', '9', '5', '0', '8', '9', '9', '6', '8', '4', '6', '9', '5', '0', '5', '3', '9', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '2', '4', '0', '0', '4', '7', '5', '2', '7', '3', '2', '0', '2', '1', '6', '7', '6', '1', '1', '8', '2', '0', '6', '8', '8', '7', '4', '3', '0', '4', '8', '9', '2', '7', '4', '0', '0', '9', '2', '3', '1', '7', '3', '3', '8', '1', '9', '0', '8', '4', '3', '6', '9', '5', '7', '9', '2', '2', '1', '2', '8', '5', '8', '5', '8', '1', '7', '4', '5', '2', '8', '6', '4', '5', '1', '8', '0', '3', '9', '3', '0', '4', '0', '1', '6', '8', '2', '5', '1', '5', '5', '3', '0', '1', '2', '9', '4', '3', '5', '0', '5', '4', '2', '4', '1', '3', '8', '8', '9', '5', '2', '4', '9', '0', '1', '5', '1'])
noncomputable def fragment0253297Acc00800 : List (String × SourceJson) := (fragment0253297Field007Key00, fragment0253297Field007Value00) :: fragment0253297Acc00700
noncomputable def fragment0253297Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '0', '9', '2', '5', '1', '8', '3', '5', '9', '2', '5', '2', '8', '5', '2', '0', '2', '6', '3', '8', '6', '9', '6', '9', '1', '4', '4', '2', '0', '5', '2', '6', '0', '1', '3', '7', '7', '7', '9', '3', '8', '1', '3', '3', '4', '0', '2', '5', '0', '8', '3', '1', '8', '8', '8', '7', '7', '5', '3', '4', '2', '2', '8', '2', '9', '5', '0', '8', '9', '9', '6', '8', '4', '6', '9', '5', '0', '5', '3', '9', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '2', '4', '0', '0', '4', '7', '5', '2', '7', '3', '2', '0', '2', '1', '6', '7', '6', '1', '1', '8', '2', '0', '6', '8', '8', '7', '4', '3', '0', '4', '8', '9', '2', '7', '4', '0', '0', '9', '2', '3', '1', '7', '3', '3', '8', '1', '9', '0', '8', '4', '3', '6', '9', '5', '7', '9', '2', '2', '1', '2', '8', '5', '8', '5', '8', '1', '7', '4', '5', '2', '8', '6', '4', '5', '1', '8', '0', '3', '9', '3', '0', '4', '0', '1', '6', '8', '2', '5', '1', '5', '5', '3', '0', '1', '2', '9', '4', '3', '5', '0', '5', '4', '2', '4', '1', '3', '8', '8', '9', '5', '2', '4', '9', '0', '1', '5', '1', '"', ',']

theorem object_fragment0253297_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0253297Field007Chars00 ++ tail)) fragment0253297Acc00700 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0253297Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_007"
  err.flush

noncomputable def fragment0253297Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0253297Field008Value00 : SourceJson := .str (String.ofList ['1', '8', '2', '7', '0', '0', '4', '0', '6', '6', '9', '8', '1', '4', '4', '6', '8', '0', '7'])
noncomputable def fragment0253297Acc00900 : List (String × SourceJson) := (fragment0253297Field008Key00, fragment0253297Field008Value00) :: fragment0253297Acc00800
noncomputable def fragment0253297Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '8', '2', '7', '0', '0', '4', '0', '6', '6', '9', '8', '1', '4', '4', '6', '8', '0', '7', '"', ',']

theorem object_fragment0253297_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0253297Field008Chars00 ++ tail)) fragment0253297Acc00800 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0253297Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_008"
  err.flush

noncomputable def fragment0253297Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0253297Field009Value00 : SourceJson := .str (String.ofList ['1', '3', '5', '4', '4', '5', '8', '6', '6', '7', '4', '2', '6', '9', '4', '9', '8', '0', '0', '2'])
noncomputable def fragment0253297Acc01000 : List (String × SourceJson) := (fragment0253297Field009Key00, fragment0253297Field009Value00) :: fragment0253297Acc00900
noncomputable def fragment0253297Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '3', '5', '4', '4', '5', '8', '6', '6', '7', '4', '2', '6', '9', '4', '9', '8', '0', '0', '2', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0253297_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0253297Field009Chars00 ++ tail)) fragment0253297Acc00900 =
      .ok (.obj (fragment0253297Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0253297_object_field_009"
  err.flush

noncomputable def fragment0253297Chars : List Char := '{' :: (fragment0253297Field000Chars00 ++ fragment0253297Field001Chars00 ++ fragment0253297Field002Chars00 ++ fragment0253297Field003Chars00 ++ fragment0253297Field004Chars00 ++ fragment0253297Field005Chars00 ++ fragment0253297Field006Chars00 ++ fragment0253297Field007Chars00 ++ fragment0253297Field008Chars00 ++ fragment0253297Field009Chars00)
noncomputable def fragment0253297Value : SourceJson := .obj (fragment0253297Acc01000.reverse)

theorem value_fragment0253297 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 240) (fragment0253297Chars ++ tail) =
      .ok (fragment0253297Value, tail) := by
  have hinput : fragment0253297Chars ++ tail = '{' :: (fragment0253297Field000Chars00 ++ (fragment0253297Field001Chars00 ++ (fragment0253297Field002Chars00 ++ (fragment0253297Field003Chars00 ++ (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0253297Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 240) (fragment0253297Chars ++ tail) =
        SourceJson.value (fuel + 240) ('{' :: (fragment0253297Field000Chars00 ++ (fragment0253297Field001Chars00 ++ (fragment0253297Field002Chars00 ++ (fragment0253297Field003Chars00 ++ (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 240)) hinput
    _ = SourceJson.object (fuel + 239) (SourceJson.white (fragment0253297Field000Chars00 ++ (fragment0253297Field001Chars00 ++ (fragment0253297Field002Chars00 ++ (fragment0253297Field003Chars00 ++ (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))))))))))) fragment0253297Acc00000 := by rfl
    _ = SourceJson.object (fuel + 238) (SourceJson.white (fragment0253297Field001Chars00 ++ (fragment0253297Field002Chars00 ++ (fragment0253297Field003Chars00 ++ (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail))))))))))) fragment0253297Acc00100 := object_fragment0253297_field_000 fuel (fragment0253297Field001Chars00 ++ (fragment0253297Field002Chars00 ++ (fragment0253297Field003Chars00 ++ (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 237) (SourceJson.white (fragment0253297Field002Chars00 ++ (fragment0253297Field003Chars00 ++ (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))))))))) fragment0253297Acc00200 := object_fragment0253297_field_001 fuel (fragment0253297Field002Chars00 ++ (fragment0253297Field003Chars00 ++ (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 236) (SourceJson.white (fragment0253297Field003Chars00 ++ (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail))))))))) fragment0253297Acc00300 := object_fragment0253297_field_002 fuel (fragment0253297Field003Chars00 ++ (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 235) (SourceJson.white (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))))))) fragment0253297Acc00400 := object_fragment0253297_field_003 fuel (fragment0253297Field004Chars00 ++ (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 234) (SourceJson.white (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail))))))) fragment0253297Acc00500 := object_fragment0253297_field_004 fuel (fragment0253297Field005Chars00 ++ (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))))) fragment0253297Acc00600 := object_fragment0253297_field_005 fuel (fragment0253297Field006Chars00 ++ (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail))))) fragment0253297Acc00700 := object_fragment0253297_field_006 fuel (fragment0253297Field007Chars00 ++ (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))) fragment0253297Acc00800 := object_fragment0253297_field_007 fuel (fragment0253297Field008Chars00 ++ (fragment0253297Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0253297Field009Chars00 ++ (tail))) fragment0253297Acc00900 := object_fragment0253297_field_008 fuel (fragment0253297Field009Chars00 ++ (tail))
    _ = .ok (fragment0253297Value, tail) := object_fragment0253297_field_009 fuel (tail)

noncomputable def fragment0254935Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0254935Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0254935Field000Value00 : SourceJson := .number (String.ofList ['1', '7'])
noncomputable def fragment0254935Acc00100 : List (String × SourceJson) := (fragment0254935Field000Key00, fragment0254935Field000Value00) :: fragment0254935Acc00000
noncomputable def fragment0254935Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '1', '7', ',']

theorem object_fragment0254935_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 353) (SourceJson.white (fragment0254935Field000Chars00 ++ tail)) fragment0254935Acc00000 =
      SourceJson.object (fuel + 352) (SourceJson.white tail) fragment0254935Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_000"
  err.flush

noncomputable def fragment0254935Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0254935Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '2']), .number (String.ofList ['4']), .number (String.ofList ['2'])]
noncomputable def fragment0254935Acc00200 : List (String × SourceJson) := (fragment0254935Field001Key00, fragment0254935Field001Value00) :: fragment0254935Acc00100
noncomputable def fragment0254935Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0254935_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 352) (SourceJson.white (fragment0254935Field001Chars00 ++ tail)) fragment0254935Acc00100 =
      SourceJson.object (fuel + 351) (SourceJson.white tail) fragment0254935Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_001"
  err.flush

noncomputable def fragment0254935Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0254935Field002Value00 : SourceJson := .str (String.ofList ['2', '7', '0', '9', '1', '8', '7', '7', '6', '2', '9', '4', '5', '7', '9', '9', '3', '0', '3', '4', '6', '4', '6', '8', '5', '7', '4', '3', '2', '5', '2', '7', '0', '0', '2', '3', '6', '7', '2', '9', '7', '3', '3', '5', '6', '9', '/', '3', '6', '4', '5', '3', '6', '8', '5', '2', '4', '8', '6', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0254935Acc00300 : List (String × SourceJson) := (fragment0254935Field002Key00, fragment0254935Field002Value00) :: fragment0254935Acc00200
noncomputable def fragment0254935Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '7', '0', '9', '1', '8', '7', '7', '6', '2', '9', '4', '5', '7', '9', '9', '3', '0', '3', '4', '6', '4', '6', '8', '5', '7', '4', '3', '2', '5', '2', '7', '0', '0', '2', '3', '6', '7', '2', '9', '7', '3', '3', '5', '6', '9', '/', '3', '6', '4', '5', '3', '6', '8', '5', '2', '4', '8', '6', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0254935_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 351) (SourceJson.white (fragment0254935Field002Chars00 ++ tail)) fragment0254935Acc00200 =
      SourceJson.object (fuel + 350) (SourceJson.white tail) fragment0254935Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_002"
  err.flush

noncomputable def fragment0254935Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0254935Field003Value00 : SourceJson := .str (String.ofList ['5', '9', '1', '6', '2', '9', '/', '5', '1', '7', '4', '4', '0', '0', '0', '0'])
noncomputable def fragment0254935Acc00400 : List (String × SourceJson) := (fragment0254935Field003Key00, fragment0254935Field003Value00) :: fragment0254935Acc00300
noncomputable def fragment0254935Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '9', '1', '6', '2', '9', '/', '5', '1', '7', '4', '4', '0', '0', '0', '0', '"', ',']

theorem object_fragment0254935_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 350) (SourceJson.white (fragment0254935Field003Chars00 ++ tail)) fragment0254935Acc00300 =
      SourceJson.object (fuel + 349) (SourceJson.white tail) fragment0254935Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_003"
  err.flush

noncomputable def fragment0254935Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0254935Field004Value00 : SourceJson := .arr [.str (String.ofList ['1', '0', '2', '1', '8', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '2', '7', '8', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '5', '2', '9', '7', '7', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0254935Acc00500 : List (String × SourceJson) := (fragment0254935Field004Key00, fragment0254935Field004Value00) :: fragment0254935Acc00400
noncomputable def fragment0254935Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '2', '1', '8', '7', '9', '/', '1', '1', '2', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '8', '2', '7', '8', '9', '7', '/', '3', '9', '2', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '3', '3', '6', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '9', '5', '2', '9', '7', '7', '/', '1', '6', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '5', '4', '6', '6', '3', '1', '/', '9', '6', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0254935_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 349) (SourceJson.white (fragment0254935Field004Chars00 ++ tail)) fragment0254935Acc00400 =
      SourceJson.object (fuel + 348) (SourceJson.white tail) fragment0254935Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_004"
  err.flush

noncomputable def fragment0254935Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0254935Field005Value00 : SourceJson := .arr [.str (String.ofList ['3', '0', '8', '9', '7', '7', '5', '2', '4', '7', '5', '1', '4', '8', '9', '8', '6', '1', '/', '3', '8', '0', '7', '8', '0', '5', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '9', '3', '2', '8', '3', '8', '3', '6', '4', '8', '3', '7', '8', '2', '9', '/', '1', '7', '7', '6', '9', '7', '6', '0', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '4', '4', '5', '6', '0', '2', '0', '6', '7', '5', '0', '6', '2', '1', '1', '4', '7', '/', '1', '3', '3', '2', '7', '3', '2', '0', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '5', '5', '6', '3', '8', '0', '3', '3', '2', '3', '0', '6', '1', '5', '2', '1', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '9', '5', '2', '5', '1', '8', '9', '9', '8', '1', '2', '6', '9', '6', '8', '3', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '5', '6', '6', '3', '0', '5', '1', '2', '4', '7', '7', '8', '6', '0', '3', '/', '8', '8', '8', '4', '8', '8', '0', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '4', '0', '7', '7', '9', '0', '1', '2', '4', '0', '7', '1', '4', '6', '2', '8', '3', '/', '1', '0', '6', '6', '1', '8', '5', '6', '3', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '6', '5', '2', '2', '5', '1', '2', '7', '4', '9', '2', '0', '6', '8', '1', '1', '/', '3', '5', '5', '3', '9', '5', '2', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '7', '2', '3', '6', '8', '9', '6', '3', '3', '9', '8', '3', '9', '5', '7', '7', '/', '2', '6', '6', '5', '4', '6', '4', '0', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '7', '3', '0', '9', '0', '2', '1', '1', '8', '4', '1', '6', '7', '0', '1', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0254935Acc00600 : List (String × SourceJson) := (fragment0254935Field005Key00, fragment0254935Field005Value00) :: fragment0254935Acc00500
noncomputable def fragment0254935Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '8', '9', '7', '7', '5', '2', '4', '7', '5', '1', '4', '8', '9', '8', '6', '1', '/', '3', '8', '0', '7', '8', '0', '5', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '6', '9', '3', '2', '8', '3', '8', '3', '6', '4', '8', '3', '7', '8', '2', '9', '/', '1', '7', '7', '6', '9', '7', '6', '0', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '4', '4', '5', '6', '0', '2', '0', '6', '7', '5', '0', '6', '2', '1', '1', '4', '7', '/', '1', '3', '3', '2', '7', '3', '2', '0', '4', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '3', '5', '5', '6', '3', '8', '0', '3', '3', '2', '3', '0', '6', '1', '5', '2', '1', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '7', '9', '5', '2', '5', '1', '8', '9', '9', '8', '1', '2', '6', '9', '6', '8', '3', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '0', '5', '6', '6', '3', '0', '5', '1', '2', '4', '7', '7', '8', '6', '0', '3', '/', '8', '8', '8', '4', '8', '8', '0', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '8', '4', '0', '7', '7', '9', '0', '1', '2', '4', '0', '7', '1', '4', '6', '2', '8', '3', '/', '1', '0', '6', '6', '1', '8', '5', '6', '3', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '0', '6', '5', '2', '2', '5', '1', '2', '7', '4', '9', '2', '0', '6', '8', '1', '1', '/', '3', '5', '5', '3', '9', '5', '2', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '7', '7', '2', '3', '6', '8', '9', '6', '3', '3', '9', '8', '3', '9', '5', '7', '7', '/', '2', '6', '6', '5', '4', '6', '4', '0', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '7', '3', '0', '9', '0', '2', '1', '1', '8', '4', '1', '6', '7', '0', '1', '/', '5', '3', '3', '0', '9', '2', '8', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0254935_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 348) (SourceJson.white (fragment0254935Field005Chars00 ++ tail)) fragment0254935Acc00500 =
      SourceJson.object (fuel + 347) (SourceJson.white tail) fragment0254935Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_005"
  err.flush

noncomputable def fragment0254935Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0254935Field006Value00 : SourceJson := .str (String.ofList ['9', '7', '9', '9', '9', '3', '6', '4', '2', '8', '6', '9', '2', '0', '8', '0', '6', '1', '4', '7', '9', '9', '9', '8', '4', '4', '1', '1', '9', '2', '5', '0', '4', '4', '9', '0', '1', '6', '3', '4', '2', '2', '5', '4', '5', '8', '7', '2', '6', '2', '9', '6', '8', '7', '5', '/', '7', '1', '4', '0', '3', '6', '5', '1', '6', '0', '0', '1', '2', '9', '0', '2', '7', '5', '6', '6', '6', '2', '0', '5', '7', '6', '0', '6', '6', '2', '5', '7', '3', '8', '3', '6', '7', '8', '2', '3', '2', '6', '1', '2', '2', '3', '7', '0', '6', '3', '3', '6', '4', '3', '7', '9', '3', '6', '0', '2', '7', '1', '2', '7', '6', '8'])
noncomputable def fragment0254935Acc00700 : List (String × SourceJson) := (fragment0254935Field006Key00, fragment0254935Field006Value00) :: fragment0254935Acc00600
noncomputable def fragment0254935Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '9', '7', '9', '9', '9', '3', '6', '4', '2', '8', '6', '9', '2', '0', '8', '0', '6', '1', '4', '7', '9', '9', '9', '8', '4', '4', '1', '1', '9', '2', '5', '0', '4', '4', '9', '0', '1', '6', '3', '4', '2', '2', '5', '4', '5', '8', '7', '2', '6', '2', '9', '6', '8', '7', '5', '/', '7', '1', '4', '0', '3', '6', '5', '1', '6', '0', '0', '1', '2', '9', '0', '2', '7', '5', '6', '6', '6', '2', '0', '5', '7', '6', '0', '6', '6', '2', '5', '7', '3', '8', '3', '6', '7', '8', '2', '3', '2', '6', '1', '2', '2', '3', '7', '0', '6', '3', '3', '6', '4', '3', '7', '9', '3', '6', '0', '2', '7', '1', '2', '7', '6', '8', '"', ',']

theorem object_fragment0254935_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 347) (SourceJson.white (fragment0254935Field006Chars00 ++ tail)) fragment0254935Acc00600 =
      SourceJson.object (fuel + 346) (SourceJson.white tail) fragment0254935Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_006"
  err.flush

noncomputable def fragment0254935Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0254935Field007Value00 : SourceJson := .str (String.ofList ['3', '2', '0', '5', '3', '8', '5', '6', '7', '0', '9', '6', '2', '3', '6', '3', '6', '7', '7', '9', '6', '9', '8', '8', '0', '4', '5', '6', '5', '2', '1', '9', '8', '0', '8', '6', '0', '7', '0', '5', '6', '6', '8', '1', '0', '8', '2', '8', '5', '6', '2', '6', '7', '3', '1', '8', '7', '2', '7', '0', '8', '3', '6', '5', '9', '2', '6', '3', '8', '1', '0', '0', '4', '8', '2', '4', '5', '6', '9', '6', '2', '7', '2', '8', '6', '3', '4', '1', '4', '6', '9', '8', '7', '9', '9', '7', '6', '8', '0', '2', '3', '8', '7', '0', '6', '2', '4', '1', '9', '6', '3', '8', '0', '1', '2', '7', '2', '4', '1', '4', '6', '0', '3', '4', '8', '6', '5', '7', '3', '4', '7', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '2', '8', '7', '6', '7', '7', '7', '5', '5', '5', '3', '9', '2', '4', '9', '8', '1', '4', '0', '3', '9', '7', '3', '6', '7', '9', '6', '9', '1', '4', '5', '0', '1', '0', '5', '5', '7', '9', '8', '1', '2', '6', '4', '7', '6', '5', '9', '0', '7', '8', '1', '3', '1', '6', '2', '6', '3', '8', '8', '5', '2', '3', '1', '3', '7', '7', '9', '2', '0', '7', '6', '4', '2', '6', '7', '7', '6', '6', '3', '4', '2', '6', '0', '7', '1', '6', '1', '2', '9', '7', '7', '1', '3', '2', '0', '6', '6', '0', '5', '4', '1', '6', '1', '5', '2', '1', '2', '4', '3', '2', '6', '8', '1', '2', '6', '7', '5', '5', '5', '0', '6', '2', '4', '0', '6', '8', '9', '5', '6', '3', '6', '2', '2', '5', '3', '6', '5', '4', '7', '8', '6', '9', '1', '2', '9', '5', '8', '9', '4', '1', '5', '5', '2', '6', '8', '3', '3', '9', '0', '4', '8', '9', '4', '8', '0', '3', '4', '4', '2', '1', '7', '3', '6', '1', '9'])
noncomputable def fragment0254935Acc00800 : List (String × SourceJson) := (fragment0254935Field007Key00, fragment0254935Field007Value00) :: fragment0254935Acc00700
noncomputable def fragment0254935Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '3', '2', '0', '5', '3', '8', '5', '6', '7', '0', '9', '6', '2', '3', '6', '3', '6', '7', '7', '9', '6', '9', '8', '8', '0', '4', '5', '6', '5', '2', '1', '9', '8', '0', '8', '6', '0', '7', '0', '5', '6', '6', '8', '1', '0', '8', '2', '8', '5', '6', '2', '6', '7', '3', '1', '8', '7', '2', '7', '0', '8', '3', '6', '5', '9', '2', '6', '3', '8', '1', '0', '0', '4', '8', '2', '4', '5', '6', '9', '6', '2', '7', '2', '8', '6', '3', '4', '1', '4', '6', '9', '8', '7', '9', '9', '7', '6', '8', '0', '2', '3', '8', '7', '0', '6', '2', '4', '1', '9', '6', '3', '8', '0', '1', '2', '7', '2', '4', '1', '4', '6', '0', '3', '4', '8', '6', '5', '7', '3', '4', '7', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '2', '8', '7', '6', '7', '7', '7', '5', '5', '5', '3', '9', '2', '4', '9', '8', '1', '4', '0', '3', '9', '7', '3', '6', '7', '9', '6', '9', '1', '4', '5', '0', '1', '0', '5', '5', '7', '9', '8', '1', '2', '6', '4', '7', '6', '5', '9', '0', '7', '8', '1', '3', '1', '6', '2', '6', '3', '8', '8', '5', '2', '3', '1', '3', '7', '7', '9', '2', '0', '7', '6', '4', '2', '6', '7', '7', '6', '6', '3', '4', '2', '6', '0', '7', '1', '6', '1', '2', '9', '7', '7', '1', '3', '2', '0', '6', '6', '0', '5', '4', '1', '6', '1', '5', '2', '1', '2', '4', '3', '2', '6', '8', '1', '2', '6', '7', '5', '5', '5', '0', '6', '2', '4', '0', '6', '8', '9', '5', '6', '3', '6', '2', '2', '5', '3', '6', '5', '4', '7', '8', '6', '9', '1', '2', '9', '5', '8', '9', '4', '1', '5', '5', '2', '6', '8', '3', '3', '9', '0', '4', '8', '9', '4', '8', '0', '3', '4', '4', '2', '1', '7', '3', '6', '1', '9', '"', ',']

theorem object_fragment0254935_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 346) (SourceJson.white (fragment0254935Field007Chars00 ++ tail)) fragment0254935Acc00700 =
      SourceJson.object (fuel + 345) (SourceJson.white tail) fragment0254935Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_007"
  err.flush

noncomputable def fragment0254935Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0254935Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '8', '7', '3', '8', '2', '7', '0', '1', '8', '6', '7', '9', '7', '0', '5', '7', '8'])
noncomputable def fragment0254935Acc00900 : List (String × SourceJson) := (fragment0254935Field008Key00, fragment0254935Field008Value00) :: fragment0254935Acc00800
noncomputable def fragment0254935Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '8', '7', '3', '8', '2', '7', '0', '1', '8', '6', '7', '9', '7', '0', '5', '7', '8', '"', ',']

theorem object_fragment0254935_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 345) (SourceJson.white (fragment0254935Field008Chars00 ++ tail)) fragment0254935Acc00800 =
      SourceJson.object (fuel + 344) (SourceJson.white tail) fragment0254935Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_008"
  err.flush

noncomputable def fragment0254935Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0254935Field009Value00 : SourceJson := .str (String.ofList ['5', '9', '2', '2', '9', '4', '5', '5', '0', '4', '2', '8', '4', '0', '7', '6', '3', '0', '1'])
noncomputable def fragment0254935Acc01000 : List (String × SourceJson) := (fragment0254935Field009Key00, fragment0254935Field009Value00) :: fragment0254935Acc00900
noncomputable def fragment0254935Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '5', '9', '2', '2', '9', '4', '5', '5', '0', '4', '2', '8', '4', '0', '7', '6', '3', '0', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0254935_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 344) (SourceJson.white (fragment0254935Field009Chars00 ++ tail)) fragment0254935Acc00900 =
      .ok (.obj (fragment0254935Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0254935_object_field_009"
  err.flush

noncomputable def fragment0254935Chars : List Char := '{' :: (fragment0254935Field000Chars00 ++ fragment0254935Field001Chars00 ++ fragment0254935Field002Chars00 ++ fragment0254935Field003Chars00 ++ fragment0254935Field004Chars00 ++ fragment0254935Field005Chars00 ++ fragment0254935Field006Chars00 ++ fragment0254935Field007Chars00 ++ fragment0254935Field008Chars00 ++ fragment0254935Field009Chars00)
noncomputable def fragment0254935Value : SourceJson := .obj (fragment0254935Acc01000.reverse)

theorem value_fragment0254935 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 354) (fragment0254935Chars ++ tail) =
      .ok (fragment0254935Value, tail) := by
  have hinput : fragment0254935Chars ++ tail = '{' :: (fragment0254935Field000Chars00 ++ (fragment0254935Field001Chars00 ++ (fragment0254935Field002Chars00 ++ (fragment0254935Field003Chars00 ++ (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0254935Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 354) (fragment0254935Chars ++ tail) =
        SourceJson.value (fuel + 354) ('{' :: (fragment0254935Field000Chars00 ++ (fragment0254935Field001Chars00 ++ (fragment0254935Field002Chars00 ++ (fragment0254935Field003Chars00 ++ (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 354)) hinput
    _ = SourceJson.object (fuel + 353) (SourceJson.white (fragment0254935Field000Chars00 ++ (fragment0254935Field001Chars00 ++ (fragment0254935Field002Chars00 ++ (fragment0254935Field003Chars00 ++ (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))))))))))) fragment0254935Acc00000 := by rfl
    _ = SourceJson.object (fuel + 352) (SourceJson.white (fragment0254935Field001Chars00 ++ (fragment0254935Field002Chars00 ++ (fragment0254935Field003Chars00 ++ (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail))))))))))) fragment0254935Acc00100 := object_fragment0254935_field_000 fuel (fragment0254935Field001Chars00 ++ (fragment0254935Field002Chars00 ++ (fragment0254935Field003Chars00 ++ (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 351) (SourceJson.white (fragment0254935Field002Chars00 ++ (fragment0254935Field003Chars00 ++ (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))))))))) fragment0254935Acc00200 := object_fragment0254935_field_001 fuel (fragment0254935Field002Chars00 ++ (fragment0254935Field003Chars00 ++ (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 350) (SourceJson.white (fragment0254935Field003Chars00 ++ (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail))))))))) fragment0254935Acc00300 := object_fragment0254935_field_002 fuel (fragment0254935Field003Chars00 ++ (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 349) (SourceJson.white (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))))))) fragment0254935Acc00400 := object_fragment0254935_field_003 fuel (fragment0254935Field004Chars00 ++ (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 348) (SourceJson.white (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail))))))) fragment0254935Acc00500 := object_fragment0254935_field_004 fuel (fragment0254935Field005Chars00 ++ (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 347) (SourceJson.white (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))))) fragment0254935Acc00600 := object_fragment0254935_field_005 fuel (fragment0254935Field006Chars00 ++ (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 346) (SourceJson.white (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail))))) fragment0254935Acc00700 := object_fragment0254935_field_006 fuel (fragment0254935Field007Chars00 ++ (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 345) (SourceJson.white (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))) fragment0254935Acc00800 := object_fragment0254935_field_007 fuel (fragment0254935Field008Chars00 ++ (fragment0254935Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 344) (SourceJson.white (fragment0254935Field009Chars00 ++ (tail))) fragment0254935Acc00900 := object_fragment0254935_field_008 fuel (fragment0254935Field009Chars00 ++ (tail))
    _ = .ok (fragment0254935Value, tail) := object_fragment0254935_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_before_reader"
  err.flush

noncomputable def chunk0016LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0016SuffixChars00 : List Char := [',']
noncomputable def chunk0016Chars00 : List Char := chunk0016LeadChars00 ++ fragment0253297Chars ++ chunk0016SuffixChars00
noncomputable def chunk0016Push00 (acc : List SourceJson) : List SourceJson := fragment0253297Value :: acc

noncomputable def chunk0016AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0016_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 588)
      (SourceJson.white (chunk0016LeadChars00 ++ (fragment0253297Chars ++ rest))) acc =
      (SourceJson.value (fuel + 587) (fragment0253297Chars ++ rest)).bind
        (chunk0016AfterValue00 (fuel + 587) acc) := by rfl

theorem array_chunk0016 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 588) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 587) (SourceJson.white tail) (chunk0016Push00 acc) := by
  have hinput : chunk0016Chars00 ++ tail = chunk0016LeadChars00 ++ (fragment0253297Chars ++ (chunk0016SuffixChars00 ++ tail)) := by
    simp only [chunk0016Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 588) (SourceJson.white (chunk0016Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 588)
          (SourceJson.white (chunk0016LeadChars00 ++ (fragment0253297Chars ++ (chunk0016SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 588) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 587) (fragment0253297Chars ++ (chunk0016SuffixChars00 ++ tail))).bind
        (chunk0016AfterValue00 (fuel + 587) acc) := array_chunk0016_head fuel (chunk0016SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0253297Value, chunk0016SuffixChars00 ++ tail)).bind
        (chunk0016AfterValue00 (fuel + 587) acc) :=
      congrArg (fun result => result.bind (chunk0016AfterValue00 (fuel + 587) acc))
        (value_fragment0253297 (fuel + 347) (chunk0016SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 587) (SourceJson.white tail) (chunk0016Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0016_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_before_reader"
  err.flush

noncomputable def chunk0017LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0017SuffixChars00 : List Char := [',']
noncomputable def chunk0017Chars00 : List Char := chunk0017LeadChars00 ++ fragment0254935Chars ++ chunk0017SuffixChars00
noncomputable def chunk0017Push00 (acc : List SourceJson) : List SourceJson := fragment0254935Value :: acc

noncomputable def chunk0017AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0017_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 587)
      (SourceJson.white (chunk0017LeadChars00 ++ (fragment0254935Chars ++ rest))) acc =
      (SourceJson.value (fuel + 586) (fragment0254935Chars ++ rest)).bind
        (chunk0017AfterValue00 (fuel + 586) acc) := by rfl

theorem array_chunk0017 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 587) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 586) (SourceJson.white tail) (chunk0017Push00 acc) := by
  have hinput : chunk0017Chars00 ++ tail = chunk0017LeadChars00 ++ (fragment0254935Chars ++ (chunk0017SuffixChars00 ++ tail)) := by
    simp only [chunk0017Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 587) (SourceJson.white (chunk0017Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 587)
          (SourceJson.white (chunk0017LeadChars00 ++ (fragment0254935Chars ++ (chunk0017SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 587) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 586) (fragment0254935Chars ++ (chunk0017SuffixChars00 ++ tail))).bind
        (chunk0017AfterValue00 (fuel + 586) acc) := array_chunk0017_head fuel (chunk0017SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0254935Value, chunk0017SuffixChars00 ++ tail)).bind
        (chunk0017AfterValue00 (fuel + 586) acc) :=
      congrArg (fun result => result.bind (chunk0017AfterValue00 (fuel + 586) acc))
        (value_fragment0254935 (fuel + 232) (chunk0017SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 586) (SourceJson.white tail) (chunk0017Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0017_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0016Chars00 ++ chunk0017Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0017Push00 (chunk0016Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 588) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 586) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0016Chars00 ++ (chunk0017Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 588) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 588) (SourceJson.white (chunk0016Chars00 ++ (chunk0017Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 588) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 587) (SourceJson.white (chunk0017Chars00 ++ (tail))) (chunk0016Push00 (acc)) := array_chunk0016 fuel (chunk0017Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 586) (SourceJson.white tail) (blockPush acc) := array_chunk0017 fuel (tail) (chunk0016Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 253291).take 3502 = blockChars := by rfl

theorem block_original_split : sourceRest 253291 = blockChars ++ sourceRest 256793 := by
  calc
    sourceRest 253291 = (sourceRest 253291).take 3502 ++ (sourceRest 253291).drop 3502 :=
      (List.take_append_drop 3502 (sourceRest 253291)).symm
    _ = blockChars ++ (sourceRest 253291).drop 3502 :=
      congrArg (fun part => part ++ (sourceRest 253291).drop 3502) block_original_prefix
    _ = blockChars ++ sourceRest 256793 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 253291 3502)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 588) (SourceJson.white (sourceRest 253291)) acc =
      SourceJson.array (fuel + 586) (SourceJson.white (sourceRest 256793)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 588) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 256793) acc)

#print axioms object_fragment0253297_field_000
#print axioms object_fragment0253297_field_001
#print axioms object_fragment0253297_field_002
#print axioms object_fragment0253297_field_003
#print axioms object_fragment0253297_field_004
#print axioms object_fragment0253297_field_005
#print axioms object_fragment0253297_field_006
#print axioms object_fragment0253297_field_007
#print axioms object_fragment0253297_field_008
#print axioms object_fragment0253297_field_009
#print axioms value_fragment0253297
#print axioms object_fragment0254935_field_000
#print axioms object_fragment0254935_field_001
#print axioms object_fragment0254935_field_002
#print axioms object_fragment0254935_field_003
#print axioms object_fragment0254935_field_004
#print axioms object_fragment0254935_field_005
#print axioms object_fragment0254935_field_006
#print axioms object_fragment0254935_field_007
#print axioms object_fragment0254935_field_008
#print axioms object_fragment0254935_field_009
#print axioms value_fragment0254935
#print axioms array_chunk0016_head
#print axioms array_chunk0016
#print axioms array_chunk0017_head
#print axioms array_chunk0017
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock008

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
