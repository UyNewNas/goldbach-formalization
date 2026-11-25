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

namespace SimplicesBlock033

noncomputable def fragment0336698Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0336698Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0336698Field000Value00 : SourceJson := .number (String.ofList ['6', '5'])
noncomputable def fragment0336698Acc00100 : List (String × SourceJson) := (fragment0336698Field000Key00, fragment0336698Field000Value00) :: fragment0336698Acc00000
noncomputable def fragment0336698Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '5', ',']

theorem object_fragment0336698_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 233) (SourceJson.white (fragment0336698Field000Chars00 ++ tail)) fragment0336698Acc00000 =
      SourceJson.object (fuel + 232) (SourceJson.white tail) fragment0336698Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_000"
  err.flush

noncomputable def fragment0336698Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0336698Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0336698Acc00200 : List (String × SourceJson) := (fragment0336698Field001Key00, fragment0336698Field001Value00) :: fragment0336698Acc00100
noncomputable def fragment0336698Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0336698_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 232) (SourceJson.white (fragment0336698Field001Chars00 ++ tail)) fragment0336698Acc00100 =
      SourceJson.object (fuel + 231) (SourceJson.white tail) fragment0336698Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_001"
  err.flush

noncomputable def fragment0336698Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0336698Field002Value00 : SourceJson := .str (String.ofList ['2', '7', '4', '2', '0', '2', '4', '6', '3', '1', '5', '6', '2', '6', '1', '4', '9', '7', '6', '8', '5', '1', '0', '7', '6', '6', '4', '2', '4', '3', '7', '7', '5', '3', '/', '7', '9', '3', '8', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0336698Acc00300 : List (String × SourceJson) := (fragment0336698Field002Key00, fragment0336698Field002Value00) :: fragment0336698Acc00200
noncomputable def fragment0336698Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '7', '4', '2', '0', '2', '4', '6', '3', '1', '5', '6', '2', '6', '1', '4', '9', '7', '6', '8', '5', '1', '0', '7', '6', '6', '4', '2', '4', '3', '7', '7', '5', '3', '/', '7', '9', '3', '8', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0336698_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 231) (SourceJson.white (fragment0336698Field002Chars00 ++ tail)) fragment0336698Acc00200 =
      SourceJson.object (fuel + 230) (SourceJson.white tail) fragment0336698Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_002"
  err.flush

noncomputable def fragment0336698Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0336698Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0336698Acc00400 : List (String × SourceJson) := (fragment0336698Field003Key00, fragment0336698Field003Value00) :: fragment0336698Acc00300
noncomputable def fragment0336698Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0336698_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 230) (SourceJson.white (fragment0336698Field003Chars00 ++ tail)) fragment0336698Acc00300 =
      SourceJson.object (fuel + 229) (SourceJson.white tail) fragment0336698Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_003"
  err.flush

noncomputable def fragment0336698Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0336698Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0336698Acc00500 : List (String × SourceJson) := (fragment0336698Field004Key00, fragment0336698Field004Value00) :: fragment0336698Acc00400
noncomputable def fragment0336698Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '9', '7', '0', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '7', '0', '3', '1', '9', '3', '/', '3', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0336698_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 229) (SourceJson.white (fragment0336698Field004Chars00 ++ tail)) fragment0336698Acc00400 =
      SourceJson.object (fuel + 228) (SourceJson.white tail) fragment0336698Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_004"
  err.flush

noncomputable def fragment0336698Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0336698Field005Value00 : SourceJson := .arr [.str (String.ofList ['2', '9', '1', '1', '9', '9', '2', '5', '6', '3', '4', '5', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '7', '6', '4', '6', '5', '4', '9', '0', '9', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '8', '3', '1', '2', '0', '6', '7', '1', '3', '/', '9', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '7', '8', '0', '3', '9', '5', '6', '5', '3', '5', '7', '/', '1', '7', '6', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '2', '9', '1', '1', '1', '8', '2', '2', '3', '/', '2', '0', '7', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '3', '9', '5', '8', '8', '5', '9', '1', '1', '1', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '1', '3', '0', '8', '5', '1', '1', '4', '5', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '8', '6', '2', '8', '7', '9', '0', '3', '3', '1', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '1', '7', '7', '2', '1', '1', '4', '8', '4', '5', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '1', '7', '7', '1', '6', '4', '4', '5', '5', '7', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0336698Acc00600 : List (String × SourceJson) := (fragment0336698Field005Key00, fragment0336698Field005Value00) :: fragment0336698Acc00500
noncomputable def fragment0336698Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '1', '1', '9', '9', '2', '5', '6', '3', '4', '5', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '9', '4', '7', '6', '4', '6', '5', '4', '9', '0', '9', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '3', '0', '8', '3', '1', '2', '0', '6', '7', '1', '3', '/', '9', '0', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '9', '7', '8', '0', '3', '9', '5', '6', '5', '3', '5', '7', '/', '1', '7', '6', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '9', '2', '9', '1', '1', '1', '8', '2', '2', '3', '/', '2', '0', '7', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '6', '3', '9', '5', '8', '8', '5', '9', '1', '1', '1', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '4', '2', '1', '3', '0', '8', '5', '1', '1', '4', '5', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '3', '8', '6', '2', '8', '7', '9', '0', '3', '3', '1', '/', '1', '1', '7', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '7', '7', '2', '1', '1', '4', '8', '4', '5', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '1', '7', '7', '1', '6', '4', '4', '5', '5', '7', '3', '/', '3', '5', '2', '7', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0336698_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 228) (SourceJson.white (fragment0336698Field005Chars00 ++ tail)) fragment0336698Acc00500 =
      SourceJson.object (fuel + 227) (SourceJson.white tail) fragment0336698Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_005"
  err.flush

noncomputable def fragment0336698Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0336698Field006Value00 : SourceJson := .str (String.ofList ['8', '9', '0', '7', '1', '7', '9', '3', '6', '4', '2', '8', '5', '0', '0', '5', '5', '7', '5', '6', '9', '3', '6', '5', '2', '7', '2', '2', '6', '3', '2', '3', '4', '1', '1', '3', '5', '9', '5', '9', '1', '0', '4', '0', '0', '0', '/', '6', '7', '7', '6', '3', '5', '3', '6', '0', '5', '9', '6', '2', '9', '0', '4', '0', '5', '2', '5', '5', '7', '3', '3', '0', '2', '8', '9', '9', '9', '3', '7', '9', '5', '3', '4', '8', '3', '8', '8', '8', '5', '3', '2', '6', '9', '5', '5', '5', '6', '5', '6', '8', '2', '8', '7', '1', '6', '9', '6', '1'])
noncomputable def fragment0336698Acc00700 : List (String × SourceJson) := (fragment0336698Field006Key00, fragment0336698Field006Value00) :: fragment0336698Acc00600
noncomputable def fragment0336698Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '8', '9', '0', '7', '1', '7', '9', '3', '6', '4', '2', '8', '5', '0', '0', '5', '5', '7', '5', '6', '9', '3', '6', '5', '2', '7', '2', '2', '6', '3', '2', '3', '4', '1', '1', '3', '5', '9', '5', '9', '1', '0', '4', '0', '0', '0', '/', '6', '7', '7', '6', '3', '5', '3', '6', '0', '5', '9', '6', '2', '9', '0', '4', '0', '5', '2', '5', '5', '7', '3', '3', '0', '2', '8', '9', '9', '9', '3', '7', '9', '5', '3', '4', '8', '3', '8', '8', '8', '5', '3', '2', '6', '9', '5', '5', '5', '6', '5', '6', '8', '2', '8', '7', '1', '6', '9', '6', '1', '"', ',']

theorem object_fragment0336698_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 227) (SourceJson.white (fragment0336698Field006Chars00 ++ tail)) fragment0336698Acc00600 =
      SourceJson.object (fuel + 226) (SourceJson.white tail) fragment0336698Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_006"
  err.flush

noncomputable def fragment0336698Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0336698Field007Value00 : SourceJson := .str (String.ofList ['2', '3', '9', '2', '2', '6', '1', '1', '9', '9', '4', '1', '5', '6', '6', '8', '1', '5', '9', '0', '9', '8', '6', '4', '9', '9', '4', '4', '2', '4', '3', '6', '8', '3', '4', '5', '3', '4', '7', '6', '2', '6', '6', '9', '5', '3', '6', '9', '7', '3', '1', '6', '5', '7', '1', '6', '0', '3', '7', '9', '4', '6', '1', '6', '7', '6', '4', '8', '9', '4', '8', '7', '4', '3', '2', '7', '8', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '4', '8', '5', '1', '3', '3', '6', '9', '7', '5', '8', '2', '0', '6', '8', '2', '1', '2', '6', '2', '4', '1', '4', '5', '5', '1', '7', '0', '0', '4', '6', '6', '3', '0', '7', '6', '9', '4', '3', '3', '5', '5', '6', '3', '7', '6', '5', '3', '7', '0', '2', '0', '2', '7', '7', '4', '0', '8', '4', '2', '4', '0', '8', '8', '7', '6', '1', '6', '7', '7', '2', '5', '7', '8', '6', '1', '7', '9', '7', '4', '8', '7', '5', '9', '4', '3', '6', '8', '6', '1', '9', '2', '5', '6', '1', '6', '0', '6', '6', '6', '1', '6', '6', '9', '3', '8', '5', '3', '6', '5', '0', '5', '1', '8', '1', '9'])
noncomputable def fragment0336698Acc00800 : List (String × SourceJson) := (fragment0336698Field007Key00, fragment0336698Field007Value00) :: fragment0336698Acc00700
noncomputable def fragment0336698Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '3', '9', '2', '2', '6', '1', '1', '9', '9', '4', '1', '5', '6', '6', '8', '1', '5', '9', '0', '9', '8', '6', '4', '9', '9', '4', '4', '2', '4', '3', '6', '8', '3', '4', '5', '3', '4', '7', '6', '2', '6', '6', '9', '5', '3', '6', '9', '7', '3', '1', '6', '5', '7', '1', '6', '0', '3', '7', '9', '4', '6', '1', '6', '7', '6', '4', '8', '9', '4', '8', '7', '4', '3', '2', '7', '8', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '8', '4', '8', '5', '1', '3', '3', '6', '9', '7', '5', '8', '2', '0', '6', '8', '2', '1', '2', '6', '2', '4', '1', '4', '5', '5', '1', '7', '0', '0', '4', '6', '6', '3', '0', '7', '6', '9', '4', '3', '3', '5', '5', '6', '3', '7', '6', '5', '3', '7', '0', '2', '0', '2', '7', '7', '4', '0', '8', '4', '2', '4', '0', '8', '8', '7', '6', '1', '6', '7', '7', '2', '5', '7', '8', '6', '1', '7', '9', '7', '4', '8', '7', '5', '9', '4', '3', '6', '8', '6', '1', '9', '2', '5', '6', '1', '6', '0', '6', '6', '6', '1', '6', '6', '9', '3', '8', '5', '3', '6', '5', '0', '5', '1', '8', '1', '9', '"', ',']

theorem object_fragment0336698_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 226) (SourceJson.white (fragment0336698Field007Chars00 ++ tail)) fragment0336698Acc00700 =
      SourceJson.object (fuel + 225) (SourceJson.white tail) fragment0336698Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_007"
  err.flush

noncomputable def fragment0336698Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0336698Field008Value00 : SourceJson := .str (String.ofList ['1', '0', '4', '1', '4', '1', '4', '7', '4', '1', '9', '8', '7', '9', '1'])
noncomputable def fragment0336698Acc00900 : List (String × SourceJson) := (fragment0336698Field008Key00, fragment0336698Field008Value00) :: fragment0336698Acc00800
noncomputable def fragment0336698Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '4', '1', '4', '1', '4', '7', '4', '1', '9', '8', '7', '9', '1', '"', ',']

theorem object_fragment0336698_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 225) (SourceJson.white (fragment0336698Field008Chars00 ++ tail)) fragment0336698Acc00800 =
      SourceJson.object (fuel + 224) (SourceJson.white tail) fragment0336698Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_008"
  err.flush

noncomputable def fragment0336698Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0336698Field009Value00 : SourceJson := .str (String.ofList ['1', '0', '2', '5', '3', '3', '4', '5', '3', '1', '9', '7', '9', '4', '2', '1'])
noncomputable def fragment0336698Acc01000 : List (String × SourceJson) := (fragment0336698Field009Key00, fragment0336698Field009Value00) :: fragment0336698Acc00900
noncomputable def fragment0336698Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '1', '0', '2', '5', '3', '3', '4', '5', '3', '1', '9', '7', '9', '4', '2', '1', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0336698_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 224) (SourceJson.white (fragment0336698Field009Chars00 ++ tail)) fragment0336698Acc00900 =
      .ok (.obj (fragment0336698Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0336698_object_field_009"
  err.flush

noncomputable def fragment0336698Chars : List Char := '{' :: (fragment0336698Field000Chars00 ++ fragment0336698Field001Chars00 ++ fragment0336698Field002Chars00 ++ fragment0336698Field003Chars00 ++ fragment0336698Field004Chars00 ++ fragment0336698Field005Chars00 ++ fragment0336698Field006Chars00 ++ fragment0336698Field007Chars00 ++ fragment0336698Field008Chars00 ++ fragment0336698Field009Chars00)
noncomputable def fragment0336698Value : SourceJson := .obj (fragment0336698Acc01000.reverse)

theorem value_fragment0336698 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 234) (fragment0336698Chars ++ tail) =
      .ok (fragment0336698Value, tail) := by
  have hinput : fragment0336698Chars ++ tail = '{' :: (fragment0336698Field000Chars00 ++ (fragment0336698Field001Chars00 ++ (fragment0336698Field002Chars00 ++ (fragment0336698Field003Chars00 ++ (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0336698Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 234) (fragment0336698Chars ++ tail) =
        SourceJson.value (fuel + 234) ('{' :: (fragment0336698Field000Chars00 ++ (fragment0336698Field001Chars00 ++ (fragment0336698Field002Chars00 ++ (fragment0336698Field003Chars00 ++ (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 234)) hinput
    _ = SourceJson.object (fuel + 233) (SourceJson.white (fragment0336698Field000Chars00 ++ (fragment0336698Field001Chars00 ++ (fragment0336698Field002Chars00 ++ (fragment0336698Field003Chars00 ++ (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))))))))))) fragment0336698Acc00000 := by rfl
    _ = SourceJson.object (fuel + 232) (SourceJson.white (fragment0336698Field001Chars00 ++ (fragment0336698Field002Chars00 ++ (fragment0336698Field003Chars00 ++ (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail))))))))))) fragment0336698Acc00100 := object_fragment0336698_field_000 fuel (fragment0336698Field001Chars00 ++ (fragment0336698Field002Chars00 ++ (fragment0336698Field003Chars00 ++ (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 231) (SourceJson.white (fragment0336698Field002Chars00 ++ (fragment0336698Field003Chars00 ++ (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))))))))) fragment0336698Acc00200 := object_fragment0336698_field_001 fuel (fragment0336698Field002Chars00 ++ (fragment0336698Field003Chars00 ++ (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 230) (SourceJson.white (fragment0336698Field003Chars00 ++ (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail))))))))) fragment0336698Acc00300 := object_fragment0336698_field_002 fuel (fragment0336698Field003Chars00 ++ (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 229) (SourceJson.white (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))))))) fragment0336698Acc00400 := object_fragment0336698_field_003 fuel (fragment0336698Field004Chars00 ++ (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 228) (SourceJson.white (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail))))))) fragment0336698Acc00500 := object_fragment0336698_field_004 fuel (fragment0336698Field005Chars00 ++ (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 227) (SourceJson.white (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))))) fragment0336698Acc00600 := object_fragment0336698_field_005 fuel (fragment0336698Field006Chars00 ++ (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 226) (SourceJson.white (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail))))) fragment0336698Acc00700 := object_fragment0336698_field_006 fuel (fragment0336698Field007Chars00 ++ (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 225) (SourceJson.white (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))) fragment0336698Acc00800 := object_fragment0336698_field_007 fuel (fragment0336698Field008Chars00 ++ (fragment0336698Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 224) (SourceJson.white (fragment0336698Field009Chars00 ++ (tail))) fragment0336698Acc00900 := object_fragment0336698_field_008 fuel (fragment0336698Field009Chars00 ++ (tail))
    _ = .ok (fragment0336698Value, tail) := object_fragment0336698_field_009 fuel (tail)

noncomputable def fragment0338277Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0338277Field000Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd']
noncomputable def fragment0338277Field000Value00 : SourceJson := .number (String.ofList ['6', '6'])
noncomputable def fragment0338277Acc00100 : List (String × SourceJson) := (fragment0338277Field000Key00, fragment0338277Field000Value00) :: fragment0338277Acc00000
noncomputable def fragment0338277Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'e', 'x', '_', 'i', 'd', '"', ':', ' ', '6', '6', ',']

theorem object_fragment0338277_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 210) (SourceJson.white (fragment0338277Field000Chars00 ++ tail)) fragment0338277Acc00000 =
      SourceJson.object (fuel + 209) (SourceJson.white tail) fragment0338277Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_000"
  err.flush

noncomputable def fragment0338277Field001Key00 : String := String.ofList ['v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's']
noncomputable def fragment0338277Field001Value00 : SourceJson := .arr [.number (String.ofList ['3', '9']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['3']), .number (String.ofList ['1'])]
noncomputable def fragment0338277Acc00200 : List (String × SourceJson) := (fragment0338277Field001Key00, fragment0338277Field001Value00) :: fragment0338277Acc00100
noncomputable def fragment0338277Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'e', 'x', '_', 'i', 'd', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0338277_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 209) (SourceJson.white (fragment0338277Field001Chars00 ++ tail)) fragment0338277Acc00100 =
      SourceJson.object (fuel + 208) (SourceJson.white tail) fragment0338277Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_001"
  err.flush

noncomputable def fragment0338277Field002Key00 : String := String.ofList ['p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e']
noncomputable def fragment0338277Field002Value00 : SourceJson := .str (String.ofList ['2', '0', '3', '9', '7', '5', '7', '3', '7', '4', '7', '9', '9', '8', '1', '6', '2', '9', '7', '8', '7', '8', '1', '8', '3', '9', '5', '0', '8', '9', '1', '6', '4', '8', '9', '3', '/', '2', '7', '1', '4', '8', '1', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0338277Acc00300 : List (String × SourceJson) := (fragment0338277Field002Key00, fragment0338277Field002Value00) :: fragment0338277Acc00200
noncomputable def fragment0338277Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'h', 'y', 's', 'i', 'c', 'a', 'l', '_', 'v', 'o', 'l', 'u', 'm', 'e', '"', ':', ' ', '"', '2', '0', '3', '9', '7', '5', '7', '3', '7', '4', '7', '9', '9', '8', '1', '6', '2', '9', '7', '8', '7', '8', '1', '8', '3', '9', '5', '0', '8', '9', '1', '6', '4', '8', '9', '3', '/', '2', '7', '1', '4', '8', '1', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0338277_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 208) (SourceJson.white (fragment0338277Field002Chars00 ++ tail)) fragment0338277Acc00200 =
      SourceJson.object (fuel + 207) (SourceJson.white tail) fragment0338277Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_002"
  err.flush

noncomputable def fragment0338277Field003Key00 : String := String.ofList ['m', 'e', 'a', 'n', '_', 'g', 'a', 'p']
noncomputable def fragment0338277Field003Value00 : SourceJson := .str (String.ofList ['5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0'])
noncomputable def fragment0338277Acc00400 : List (String × SourceJson) := (fragment0338277Field003Key00, fragment0338277Field003Value00) :: fragment0338277Acc00300
noncomputable def fragment0338277Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'e', 'a', 'n', '_', 'g', 'a', 'p', '"', ':', ' ', '"', '5', '7', '2', '8', '1', '/', '1', '0', '2', '0', '0', '0', '0', '0', '0', '"', ',']

theorem object_fragment0338277_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 207) (SourceJson.white (fragment0338277Field003Chars00 ++ tail)) fragment0338277Acc00300 =
      SourceJson.object (fuel + 206) (SourceJson.white tail) fragment0338277Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_003"
  err.flush

noncomputable def fragment0338277Field004Key00 : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a']
noncomputable def fragment0338277Field004Value00 : SourceJson := .arr [.str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0338277Acc00500 : List (String × SourceJson) := (fragment0338277Field004Key00, fragment0338277Field004Value00) :: fragment0338277Acc00400
noncomputable def fragment0338277Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'm', 'a', 'x', 'i', 'm', 'a', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '8', '2', '8', '1', '1', '3', '/', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '7', '8', '4', '2', '8', '3', '/', '1', '6', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '2', '9', '9', '/', '2', '1', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '1', '8', '4', '7', '/', '1', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '3', '0', '3', '1', '1', '3', '/', '4', '8', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '8', '5', '9', '1', '5', '1', '/', '5', '7', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '0', '8', '2', '7', '8', '8', '1', '/', '2', '2', '8', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '5', '1', '0', '9', '5', '0', '3', '/', '1', '1', '4', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0338277_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 206) (SourceJson.white (fragment0338277Field004Chars00 ++ tail)) fragment0338277Acc00400 =
      SourceJson.object (fuel + 205) (SourceJson.white tail) fragment0338277Acc00500 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_004"
  err.flush

noncomputable def fragment0338277Field005Key00 : String := String.ofList ['g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's']
noncomputable def fragment0338277Field005Value00 : SourceJson := .arr [.str (String.ofList ['1', '1', '7', '8', '0', '4', '1', '5', '0', '4', '9', '7', '/', '1', '4', '6', '9', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '4', '5', '5', '6', '0', '8', '3', '2', '7', '/', '9', '1', '8', '5', '3', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '1', '2', '2', '8', '6', '7', '8', '9', '/', '1', '6', '9', '5', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '0', '2', '7', '5', '2', '4', '3', '7', '6', '3', '/', '4', '4', '0', '8', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '3', '8', '2', '4', '5', '5', '0', '9', '3', '/', '3', '4', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '8', '7', '3', '4', '4', '9', '6', '7', '5', '7', '/', '8', '8', '1', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '3', '6', '4', '2', '9', '6', '1', '7', '/', '3', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '8', '0', '5', '9', '5', '4', '3', '3', '5', '9', '/', '1', '7', '6', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '5', '6', '7', '1', '1', '4', '9', '2', '1', '/', '4', '4', '0', '8', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '5', '6', '6', '5', '2', '7', '0', '6', '1', '/', '4', '4', '0', '8', '9', '5', '0', '0', '0', '0', '0', '0', '0'])]
noncomputable def fragment0338277Acc00600 : List (String × SourceJson) := (fragment0338277Field005Key00, fragment0338277Field005Value00) :: fragment0338277Acc00500
noncomputable def fragment0338277Field005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'g', 'a', 'p', '_', 'w', 'e', 'i', 'g', 'h', 't', 'e', 'd', '_', 'm', 'e', 'a', 'n', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '1', '7', '8', '0', '4', '1', '5', '0', '4', '9', '7', '/', '1', '4', '6', '9', '6', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '7', '4', '5', '5', '6', '0', '8', '3', '2', '7', '/', '9', '1', '8', '5', '3', '1', '2', '5', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '4', '6', '1', '2', '2', '8', '6', '7', '8', '9', '/', '1', '6', '9', '5', '7', '5', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '9', '0', '2', '7', '5', '2', '4', '3', '7', '6', '3', '/', '4', '4', '0', '8', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '2', '1', '3', '8', '2', '4', '5', '5', '0', '9', '3', '/', '3', '4', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '4', '1', '8', '7', '3', '4', '4', '9', '6', '7', '5', '7', '/', '8', '8', '1', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '2', '2', '3', '6', '4', '2', '9', '6', '1', '7', '/', '3', '0', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '6', '8', '8', '0', '5', '9', '5', '4', '3', '3', '5', '9', '/', '1', '7', '6', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '5', '6', '7', '1', '1', '4', '9', '2', '1', '/', '4', '4', '0', '8', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '"', '1', '5', '8', '5', '6', '6', '5', '2', '7', '0', '6', '1', '/', '4', '4', '0', '8', '9', '5', '0', '0', '0', '0', '0', '0', '0', '"', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0338277_field_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 205) (SourceJson.white (fragment0338277Field005Chars00 ++ tail)) fragment0338277Acc00500 =
      SourceJson.object (fuel + 204) (SourceJson.white tail) fragment0338277Acc00600 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_005"
  err.flush

noncomputable def fragment0338277Field006Key00 : String := String.ofList ['m', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0338277Field006Value00 : SourceJson := .str (String.ofList ['2', '4', '8', '4', '7', '2', '6', '6', '9', '4', '4', '4', '2', '2', '8', '6', '5', '0', '0', '5', '4', '3', '6', '4', '2', '6', '2', '7', '8', '3', '1', '5', '9', '9', '0', '1', '3', '1', '8', '4', '8', '4', '9', '8', '4', '0', '0', '0', '/', '8', '4', '0', '3', '7', '7', '8', '3', '5', '0', '2', '2', '1', '0', '8', '0', '1', '1', '7', '1', '3', '0', '8', '2', '6', '0', '9', '4', '8', '1', '3', '0', '3', '9', '1', '7', '0', '1', '0', '0', '9', '9', '5', '7', '9', '1', '6', '2', '5', '5', '1', '5', '8', '8', '4', '9', '9', '8', '0', '7', '7', '8', '7'])
noncomputable def fragment0338277Acc00700 : List (String × SourceJson) := (fragment0338277Field006Key00, fragment0338277Field006Value00) :: fragment0338277Acc00600
noncomputable def fragment0338277Field006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '2', '4', '8', '4', '7', '2', '6', '6', '9', '4', '4', '4', '2', '2', '8', '6', '5', '0', '0', '5', '4', '3', '6', '4', '2', '6', '2', '7', '8', '3', '1', '5', '9', '9', '0', '1', '3', '1', '8', '4', '8', '4', '9', '8', '4', '0', '0', '0', '/', '8', '4', '0', '3', '7', '7', '8', '3', '5', '0', '2', '2', '1', '0', '8', '0', '1', '1', '7', '1', '3', '0', '8', '2', '6', '0', '9', '4', '8', '1', '3', '0', '3', '9', '1', '7', '0', '1', '0', '0', '9', '9', '5', '7', '9', '1', '6', '2', '5', '5', '1', '5', '8', '8', '4', '9', '9', '8', '0', '7', '7', '8', '7', '"', ',']

theorem object_fragment0338277_field_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 204) (SourceJson.white (fragment0338277Field006Chars00 ++ tail)) fragment0338277Acc00600 =
      SourceJson.object (fuel + 203) (SourceJson.white tail) fragment0338277Acc00700 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_006"
  err.flush

noncomputable def fragment0338277Field007Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd']
noncomputable def fragment0338277Field007Value00 : SourceJson := .str (String.ofList ['5', '7', '5', '6', '7', '5', '8', '2', '6', '4', '7', '9', '2', '7', '6', '4', '4', '8', '3', '9', '8', '7', '8', '3', '4', '3', '7', '2', '4', '3', '8', '1', '8', '8', '0', '7', '9', '8', '7', '3', '2', '5', '9', '4', '5', '6', '8', '6', '2', '0', '7', '8', '6', '4', '6', '7', '4', '4', '0', '7', '3', '9', '2', '1', '3', '6', '8', '1', '7', '0', '3', '4', '7', '1', '6', '6', '0', '6', '1', '4', '0', '1', '3', '6', '7', '1', '8', '7', '5', '0', '0', '0', '/', '2', '0', '9', '9', '0', '6', '2', '4', '4', '1', '1', '4', '8', '9', '0', '2', '6', '8', '9', '7', '9', '0', '0', '1', '2', '6', '0', '4', '2', '9', '9', '3', '0', '6', '1', '1', '1', '2', '4', '7', '0', '1', '9', '1', '8', '5', '8', '3', '9', '6', '1', '6', '0', '7', '2', '4', '7', '8', '3', '5', '2', '8', '3', '4', '9', '1', '3', '8', '0', '9', '8', '8', '2', '9', '2', '3', '9', '2', '7', '4', '2', '5', '5', '6', '4', '1', '2', '6', '0', '6', '5', '2', '2', '8', '6', '9', '2', '5', '6', '7', '9', '5', '3', '9', '1', '6', '7'])
noncomputable def fragment0338277Acc00800 : List (String × SourceJson) := (fragment0338277Field007Key00, fragment0338277Field007Value00) :: fragment0338277Acc00700
noncomputable def fragment0338277Field007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'b', 'o', 'u', 'n', 'd', '"', ':', ' ', '"', '5', '7', '5', '6', '7', '5', '8', '2', '6', '4', '7', '9', '2', '7', '6', '4', '4', '8', '3', '9', '8', '7', '8', '3', '4', '3', '7', '2', '4', '3', '8', '1', '8', '8', '0', '7', '9', '8', '7', '3', '2', '5', '9', '4', '5', '6', '8', '6', '2', '0', '7', '8', '6', '4', '6', '7', '4', '4', '0', '7', '3', '9', '2', '1', '3', '6', '8', '1', '7', '0', '3', '4', '7', '1', '6', '6', '0', '6', '1', '4', '0', '1', '3', '6', '7', '1', '8', '7', '5', '0', '0', '0', '/', '2', '0', '9', '9', '0', '6', '2', '4', '4', '1', '1', '4', '8', '9', '0', '2', '6', '8', '9', '7', '9', '0', '0', '1', '2', '6', '0', '4', '2', '9', '9', '3', '0', '6', '1', '1', '1', '2', '4', '7', '0', '1', '9', '1', '8', '5', '8', '3', '9', '6', '1', '6', '0', '7', '2', '4', '7', '8', '3', '5', '2', '8', '3', '4', '9', '1', '3', '8', '0', '9', '8', '8', '2', '9', '2', '3', '9', '2', '7', '4', '2', '5', '5', '6', '4', '1', '2', '6', '0', '6', '5', '2', '2', '8', '6', '9', '2', '5', '6', '7', '9', '5', '3', '9', '1', '6', '7', '"', ',']

theorem object_fragment0338277_field_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 203) (SourceJson.white (fragment0338277Field007Chars00 ++ tail)) fragment0338277Acc00700 =
      SourceJson.object (fuel + 202) (SourceJson.white tail) fragment0338277Acc00800 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_007"
  err.flush

noncomputable def fragment0338277Field008Key00 : String := String.ofList ['m', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0338277Field008Value00 : SourceJson := .str (String.ofList ['2', '3', '4', '2', '5', '2', '1', '6', '8', '6', '6', '3', '6', '6'])
noncomputable def fragment0338277Acc00900 : List (String × SourceJson) := (fragment0338277Field008Key00, fragment0338277Field008Value00) :: fragment0338277Acc00800
noncomputable def fragment0338277Field008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'm', 'a', 'x', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '3', '4', '2', '5', '2', '1', '6', '8', '6', '6', '3', '6', '6', '"', ',']

theorem object_fragment0338277_field_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 202) (SourceJson.white (fragment0338277Field008Chars00 ++ tail)) fragment0338277Acc00800 =
      SourceJson.object (fuel + 201) (SourceJson.white tail) fragment0338277Acc00900 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_008"
  err.flush

noncomputable def fragment0338277Field009Key00 : String := String.ofList ['j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6']
noncomputable def fragment0338277Field009Value00 : SourceJson := .str (String.ofList ['2', '1', '7', '2', '8', '6', '2', '3', '7', '1', '3', '9', '6', '1', '3'])
noncomputable def fragment0338277Acc01000 : List (String × SourceJson) := (fragment0338277Field009Key00, fragment0338277Field009Value00) :: fragment0338277Acc00900
noncomputable def fragment0338277Field009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'j', 'e', 'n', 's', 'e', 'n', '_', 'f', 'l', 'o', 'o', 'r', '_', 'Q', '9', '6', '"', ':', ' ', '"', '2', '1', '7', '2', '8', '6', '2', '3', '7', '1', '3', '9', '6', '1', '3', '"', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0338277_field_009 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 201) (SourceJson.white (fragment0338277Field009Chars00 ++ tail)) fragment0338277Acc00900 =
      .ok (.obj (fragment0338277Acc01000.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0338277_object_field_009"
  err.flush

noncomputable def fragment0338277Chars : List Char := '{' :: (fragment0338277Field000Chars00 ++ fragment0338277Field001Chars00 ++ fragment0338277Field002Chars00 ++ fragment0338277Field003Chars00 ++ fragment0338277Field004Chars00 ++ fragment0338277Field005Chars00 ++ fragment0338277Field006Chars00 ++ fragment0338277Field007Chars00 ++ fragment0338277Field008Chars00 ++ fragment0338277Field009Chars00)
noncomputable def fragment0338277Value : SourceJson := .obj (fragment0338277Acc01000.reverse)

theorem value_fragment0338277 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 211) (fragment0338277Chars ++ tail) =
      .ok (fragment0338277Value, tail) := by
  have hinput : fragment0338277Chars ++ tail = '{' :: (fragment0338277Field000Chars00 ++ (fragment0338277Field001Chars00 ++ (fragment0338277Field002Chars00 ++ (fragment0338277Field003Chars00 ++ (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail))))))))))) := by
    simp only [fragment0338277Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 211) (fragment0338277Chars ++ tail) =
        SourceJson.value (fuel + 211) ('{' :: (fragment0338277Field000Chars00 ++ (fragment0338277Field001Chars00 ++ (fragment0338277Field002Chars00 ++ (fragment0338277Field003Chars00 ++ (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))))))))))) :=
      congrArg (SourceJson.value (fuel + 211)) hinput
    _ = SourceJson.object (fuel + 210) (SourceJson.white (fragment0338277Field000Chars00 ++ (fragment0338277Field001Chars00 ++ (fragment0338277Field002Chars00 ++ (fragment0338277Field003Chars00 ++ (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))))))))))) fragment0338277Acc00000 := by rfl
    _ = SourceJson.object (fuel + 209) (SourceJson.white (fragment0338277Field001Chars00 ++ (fragment0338277Field002Chars00 ++ (fragment0338277Field003Chars00 ++ (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail))))))))))) fragment0338277Acc00100 := object_fragment0338277_field_000 fuel (fragment0338277Field001Chars00 ++ (fragment0338277Field002Chars00 ++ (fragment0338277Field003Chars00 ++ (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail))))))))))
    _ = SourceJson.object (fuel + 208) (SourceJson.white (fragment0338277Field002Chars00 ++ (fragment0338277Field003Chars00 ++ (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))))))))) fragment0338277Acc00200 := object_fragment0338277_field_001 fuel (fragment0338277Field002Chars00 ++ (fragment0338277Field003Chars00 ++ (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))))))))
    _ = SourceJson.object (fuel + 207) (SourceJson.white (fragment0338277Field003Chars00 ++ (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail))))))))) fragment0338277Acc00300 := object_fragment0338277_field_002 fuel (fragment0338277Field003Chars00 ++ (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail))))))))
    _ = SourceJson.object (fuel + 206) (SourceJson.white (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))))))) fragment0338277Acc00400 := object_fragment0338277_field_003 fuel (fragment0338277Field004Chars00 ++ (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))))))
    _ = SourceJson.object (fuel + 205) (SourceJson.white (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail))))))) fragment0338277Acc00500 := object_fragment0338277_field_004 fuel (fragment0338277Field005Chars00 ++ (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail))))))
    _ = SourceJson.object (fuel + 204) (SourceJson.white (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))))) fragment0338277Acc00600 := object_fragment0338277_field_005 fuel (fragment0338277Field006Chars00 ++ (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 203) (SourceJson.white (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail))))) fragment0338277Acc00700 := object_fragment0338277_field_006 fuel (fragment0338277Field007Chars00 ++ (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 202) (SourceJson.white (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))) fragment0338277Acc00800 := object_fragment0338277_field_007 fuel (fragment0338277Field008Chars00 ++ (fragment0338277Field009Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 201) (SourceJson.white (fragment0338277Field009Chars00 ++ (tail))) fragment0338277Acc00900 := object_fragment0338277_field_008 fuel (fragment0338277Field009Chars00 ++ (tail))
    _ = .ok (fragment0338277Value, tail) := object_fragment0338277_field_009 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0065_before_reader"
  err.flush

noncomputable def chunk0065LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0065SuffixChars00 : List Char := [',']
noncomputable def chunk0065Chars00 : List Char := chunk0065LeadChars00 ++ fragment0336698Chars ++ chunk0065SuffixChars00
noncomputable def chunk0065Push00 (acc : List SourceJson) : List SourceJson := fragment0336698Value :: acc

noncomputable def chunk0065AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0065_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 539)
      (SourceJson.white (chunk0065LeadChars00 ++ (fragment0336698Chars ++ rest))) acc =
      (SourceJson.value (fuel + 538) (fragment0336698Chars ++ rest)).bind
        (chunk0065AfterValue00 (fuel + 538) acc) := by rfl

theorem array_chunk0065 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 539) (SourceJson.white (chunk0065Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 538) (SourceJson.white tail) (chunk0065Push00 acc) := by
  have hinput : chunk0065Chars00 ++ tail = chunk0065LeadChars00 ++ (fragment0336698Chars ++ (chunk0065SuffixChars00 ++ tail)) := by
    simp only [chunk0065Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 539) (SourceJson.white (chunk0065Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 539)
          (SourceJson.white (chunk0065LeadChars00 ++ (fragment0336698Chars ++ (chunk0065SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 539) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 538) (fragment0336698Chars ++ (chunk0065SuffixChars00 ++ tail))).bind
        (chunk0065AfterValue00 (fuel + 538) acc) := array_chunk0065_head fuel (chunk0065SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0336698Value, chunk0065SuffixChars00 ++ tail)).bind
        (chunk0065AfterValue00 (fuel + 538) acc) :=
      congrArg (fun result => result.bind (chunk0065AfterValue00 (fuel + 538) acc))
        (value_fragment0336698 (fuel + 304) (chunk0065SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 538) (SourceJson.white tail) (chunk0065Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0065_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0066_before_reader"
  err.flush

noncomputable def chunk0066LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0066SuffixChars00 : List Char := [',']
noncomputable def chunk0066Chars00 : List Char := chunk0066LeadChars00 ++ fragment0338277Chars ++ chunk0066SuffixChars00
noncomputable def chunk0066Push00 (acc : List SourceJson) : List SourceJson := fragment0338277Value :: acc

noncomputable def chunk0066AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0066_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 538)
      (SourceJson.white (chunk0066LeadChars00 ++ (fragment0338277Chars ++ rest))) acc =
      (SourceJson.value (fuel + 537) (fragment0338277Chars ++ rest)).bind
        (chunk0066AfterValue00 (fuel + 537) acc) := by rfl

theorem array_chunk0066 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 538) (SourceJson.white (chunk0066Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 537) (SourceJson.white tail) (chunk0066Push00 acc) := by
  have hinput : chunk0066Chars00 ++ tail = chunk0066LeadChars00 ++ (fragment0338277Chars ++ (chunk0066SuffixChars00 ++ tail)) := by
    simp only [chunk0066Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 538) (SourceJson.white (chunk0066Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 538)
          (SourceJson.white (chunk0066LeadChars00 ++ (fragment0338277Chars ++ (chunk0066SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 538) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 537) (fragment0338277Chars ++ (chunk0066SuffixChars00 ++ tail))).bind
        (chunk0066AfterValue00 (fuel + 537) acc) := array_chunk0066_head fuel (chunk0066SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0338277Value, chunk0066SuffixChars00 ++ tail)).bind
        (chunk0066AfterValue00 (fuel + 537) acc) :=
      congrArg (fun result => result.bind (chunk0066AfterValue00 (fuel + 537) acc))
        (value_fragment0338277 (fuel + 326) (chunk0066SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 537) (SourceJson.white tail) (chunk0066Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0066_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0065Chars00 ++ chunk0066Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0066Push00 (chunk0065Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 539) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 537) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0065Chars00 ++ (chunk0066Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 539) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 539) (SourceJson.white (chunk0065Chars00 ++ (chunk0066Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 539) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 538) (SourceJson.white (chunk0066Chars00 ++ (tail))) (chunk0065Push00 (acc)) := array_chunk0065 fuel (chunk0066Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 537) (SourceJson.white tail) (blockPush acc) := array_chunk0066 fuel (tail) (chunk0065Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 336692).take 3124 = blockChars := by rfl

theorem block_original_split : sourceRest 336692 = blockChars ++ sourceRest 339816 := by
  calc
    sourceRest 336692 = (sourceRest 336692).take 3124 ++ (sourceRest 336692).drop 3124 :=
      (List.take_append_drop 3124 (sourceRest 336692)).symm
    _ = blockChars ++ (sourceRest 336692).drop 3124 :=
      congrArg (fun part => part ++ (sourceRest 336692).drop 3124) block_original_prefix
    _ = blockChars ++ sourceRest 339816 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 336692 3124)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 539) (SourceJson.white (sourceRest 336692)) acc =
      SourceJson.array (fuel + 537) (SourceJson.white (sourceRest 339816)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 539) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 339816) acc)

#print axioms object_fragment0336698_field_000
#print axioms object_fragment0336698_field_001
#print axioms object_fragment0336698_field_002
#print axioms object_fragment0336698_field_003
#print axioms object_fragment0336698_field_004
#print axioms object_fragment0336698_field_005
#print axioms object_fragment0336698_field_006
#print axioms object_fragment0336698_field_007
#print axioms object_fragment0336698_field_008
#print axioms object_fragment0336698_field_009
#print axioms value_fragment0336698
#print axioms object_fragment0338277_field_000
#print axioms object_fragment0338277_field_001
#print axioms object_fragment0338277_field_002
#print axioms object_fragment0338277_field_003
#print axioms object_fragment0338277_field_004
#print axioms object_fragment0338277_field_005
#print axioms object_fragment0338277_field_006
#print axioms object_fragment0338277_field_007
#print axioms object_fragment0338277_field_008
#print axioms object_fragment0338277_field_009
#print axioms value_fragment0338277
#print axioms array_chunk0065_head
#print axioms array_chunk0065
#print axioms array_chunk0066_head
#print axioms array_chunk0066
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end SimplicesBlock033

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
